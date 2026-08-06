/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#include "stp/Simplifier/DifficultyScore.h"
#include "stp/AST/AST.h"
#include "stp/AST/ASTKind.h"
#include "stp/Util/NodeIterator.h"
#include <algorithm>
#include <list>

/* Estimates how many AIG AND-nodes the bit-blaster will build for a formula.
 *
 * Every number below was measured, not guessed: each operation was built over
 * fresh symbols, bit-blasted on its own with BBNodeManagerAIG, and the
 * resulting AND-node count fitted against the bit-width. See
 * bench-hard/reports/2026-08-06-difficulty-scorer-vs-aig-size.md for the
 * sweep, the fits and the residuals.
 *
 * Two properties of the estimate are deliberate.
 *
 * Standalone, with no sharing. A node is costed as though it were the only
 * consumer of its children and nothing downstream re-used it. The real AIG is
 * hash-consed, so a formula whose operations overlap builds fewer nodes than
 * the sum of the per-node costs. Modelling that would need the share counts
 * the score is used to compare, so the estimate is an upper bound that stays
 * proportional as long as sharing does not change wildly between the two
 * formulas being compared.
 *
 * Constant operands are recognised. A multiply, an add or a comparison
 * against a constant is several times cheaper than the symmetric one -- a
 * shift by a constant, and a bitwise operation with a constant, are free --
 * and the old scorer costed them all at the symbolic price. That mattered:
 * simplifications that fold a constant into an operation looked neutral.
 *
 * The costs model the default bit-blaster settings (in particular
 * multiplication_variant 1, which is a shift-and-add array rather than a
 * Booth-recoded one). UserDefinedFlags is not reachable from here, so a
 * non-default backend configuration is scored as though it were the default.
 */

namespace stp
{

namespace
{

// ceil(log2(w)), the number of stages in a barrel shifter over w bits.
unsigned log2ceil(unsigned w)
{
  unsigned r = 0;
  while (r < 31 && (1u << r) < w)
    r++;
  return r;
}

unsigned constantChildren(const ASTNode& b)
{
  unsigned count = 0;
  for (unsigned i = 0, degree = b.Degree(); i < degree; i++)
    if (b[i].isConstant())
      count++;
  return count;
}

bool anyConstantChild(const ASTNode& b)
{
  return constantChildren(b) > 0;
}

// A ripple-carry adder over w bits costs 11w-7; adding a constant instead
// costs 4w-6, because a known addend fixes one input of every full adder.
// Subtracting a constant is cheaper again -- the negation of a constant is
// itself a constant, so no carry chain is built for it.
long addCost(const ASTNode& b, long w, bool subtract)
{
  const unsigned degree = b.Degree();
  const unsigned constants = constantChildren(b);
  const unsigned symbolic = degree - constants;

  long score = 0;
  if (symbolic >= 2)
    score += (11L * w - 7) * (symbolic - 1);
  if (constants > 0 && symbolic > 0)
    score += subtract ? (3L * w - 1) : (4L * w - 6);
  return std::max(0L, score);
}

// One binary multiply of width w.
//
// The default bit-blaster walks the bits of the first operand, and for each
// set bit adds the other operand shifted left by that bit's position. The
// lowest set bit seeds the accumulator for free; every later set bit i pays
// for an add over the (w-i) columns above it, 11(w-i)-7 nodes. With a
// constant operand only its set bits are built, which is why multiplying by
// a constant with few -- or high -- set bits is so much cheaper than the
// symbolic case. Summing that series over every bit gives the symmetric
// case, 6(w-1)^2+1, which the measurements reproduce exactly out to w=256.
long multiplyCost(const ASTNode& b, long w)
{
  const ASTNode* constant = NULL;
  if (b.Degree() == 2)
  {
    if (b[0].isConstant())
      constant = &b[0];
    else if (b[1].isConstant())
      constant = &b[1];
  }

  if (constant == NULL)
    return 6L * (w - 1) * (w - 1) + 1;

  const CBV cbv = constant->GetBVConst();
  long score = 0;
  bool seenLowestSetBit = false;
  for (long i = 0; i < w; i++)
  {
    if (!CONSTANTBV::BitVector_bit_test(cbv, (unsigned)i))
      continue;
    if (!seenLowestSetBit)
    {
      seenLowestSetBit = true;
      continue;
    }
    score += 11L * (w - i) - 7;
  }
  return score;
}

// Where a constant's set bits start and stop, both 0 for zero. Long division
// prunes against whichever operand is fixed, and against both ends of it: the
// highest set bit bounds how many quotient bits can be non-zero, the lowest
// bounds how much of each subtract survives.
void setBitRange(const ASTNode& constant, long w, long& lowest, long& highest)
{
  const CBV cbv = constant.GetBVConst();
  lowest = 0;
  highest = 0;
  bool seen = false;
  for (long i = w - 1; i >= 0; i--)
    if (CONSTANTBV::BitVector_bit_test(cbv, (unsigned)i))
    {
      if (!seen)
      {
        highest = i;
        seen = true;
      }
      lowest = i;
    }
}

// A division with one constant operand.
//
// Only the quotient bits that can be non-zero get built, so both cases turn
// on the constant's magnitude -- but in opposite directions. When the
// *dividend* is fixed it bounds the whole computation and the cost is linear
// in its magnitude. When the *divisor* is fixed, the quotient is at most
// w-highest bits wide and each subtract is only as wide as the divisor's own
// span, so the cost tapers from both ends: at w=32, dividing by 1 costs 5752
// nodes, by 2^31-1 costs 2357, and by 2^30 costs 181.
long constantDivisionCost(bool dividendIsConstant, const ASTNode& constant,
                          long w)
{
  long lowest = 0, highest = 0;
  setBitRange(constant, w, lowest, highest);

  if (dividendIsConstant)
    return 16L * w * highest + 6L * w;

  // Two independent taperings of the symmetric cost, applied in steps so
  // that a wide bit-vector cannot overflow the product.
  long score = 3L * (w - 1) * (w - 1);
  score = score * (2 * w - highest) / w;
  score = score * (w - lowest) / w;
  return score;
}

// The exponent and significand widths of a floating-point node. Lowering
// leaves the natively-encoded predicates over packed bit-vector operands, so
// the source sort is not always still there to ask; fall back to the standard
// interchange format for the packed width.
void fpFormat(const ASTNode& n, unsigned& eb, unsigned& sb)
{
  const SourceSort sort = n.GetSourceSort();
  if (sort.kind() == SourceSort::Kind::FloatingPoint)
  {
    eb = sort.exponentWidth();
    sb = sort.significandWidth();
    return;
  }

  const unsigned w = std::max(3u, n.GetValueWidth());
  switch (w)
  {
    case 16: eb = 5; break;
    case 32: eb = 8; break;
    case 64: eb = 11; break;
    case 128: eb = 15; break;
    default: eb = std::min(w - 1, std::max(2u, log2ceil(w) + 1)); break;
  }
  sb = w - eb;
}

// The packed width a floating-point operand occupies.
unsigned fpWidth(const ASTNode& n)
{
  unsigned eb = 0, sb = 0;
  fpFormat(n, eb, sb);
  return eb + sb;
}

long fpEval(const ASTNode& b, const Kind k)
{
  switch (k)
  {
    // Sign manipulation of an unpacked value is wiring.
    case FP_ABS:
    case FP_NEG:
      return 0;

    // The predicates. The four orderings and the two equalities are encoded
    // natively over the packed bits; the classifications are field tests.
    case FP_LEQ:
    case FP_LT:
    case FP_GEQ:
    case FP_GT:
    {
      const unsigned w = fpWidth(b[0]);
      return anyConstantChild(b) ? 5L * w : 15L * w;
    }
    case FP_EQ:
    case FP_SMT_EQ:
    {
      const unsigned w = fpWidth(b[0]);
      return anyConstantChild(b) ? (3L * w) / 2 : 6L * w;
    }
    case FP_ISNORMAL:
    {
      // Two exponent field tests: all-ones and all-zeros.
      unsigned eb = 0, sb = 0;
      fpFormat(b[0], eb, sb);
      return std::max(1L, 2L * eb - 1);
    }
    case FP_ISSUBNORMAL:
    case FP_ISZERO:
    case FP_ISINFINITE:
    case FP_ISNAN:
      return std::max(1L, (long)fpWidth(b[0]) - 2);
    case FP_ISNEGATIVE:
    case FP_ISPOSITIVE:
      return std::max(1L, (long)fpWidth(b[0]) - 1);

    default:
      break;
  }

  // The terms. Every one of these is costed at the format of its *result*.
  unsigned eb = 0, sb = 0;
  fpFormat(b, eb, sb);
  const long w = eb + sb;
  const long sig = sb;

  switch (k)
  {
    // Unpacking an operand and packing a result.
    case FP_TO_IEEE_BV:
      return 35L * b.GetValueWidth();

    case FP_ADD:
    case FP_SUB:
      // Alignment and normalisation shifters over the significand, then one
      // round: linear in the format with a barrel-shifter term on top.
      return 85L * w + 11L * w * log2ceil(w);

    case FP_MUL:
      return 12L * sig * sig + 50L * w;

    case FP_DIV:
      return 53L * sig * sig + 100L * w;

    case FP_FMA:
      return 12L * sig * sig + 260L * w;

    case FP_SQRT:
    {
      // A restoring square root: one subtract-and-select per result bit over
      // a growing remainder. Cubic, so the significand is clamped before it
      // is cubed rather than after.
      const long s = std::min(sig, 1000000L);
      return 4L * s * s * s + 25L * s * s;
    }

    case FP_REM:
    {
      // Exact remainder needs the whole quotient, so the circuit is
      // exponential in the exponent width. Clamped so the estimate stays a
      // number rather than an overflow.
      const unsigned shift = std::min(eb, 40u);
      return 25L * (1L << shift) * sig;
    }

    case FP_ROUNDTOINTEGRAL:
      return 6L * w * log2ceil(w);

    case FP_MIN:
    case FP_MAX:
      return 14L * w * log2ceil(w);

    case FP_TOFP:
    {
      // Reformatting another float. Widening is exact -- the circuit is
      // wiring -- so only narrowing pays for a round.
      const long src = fpWidth(b[b.Degree() - 1]);
      return src <= w ? (5L * src) / 4 : 25L * (src + w);
    }

    case FP_TOFP_SIGNED:
    case FP_TOFP_UNSIGNED:
    {
      // An integer narrower than the significand converts exactly.
      const long src = std::max(1u, b[b.Degree() - 1].GetValueWidth());
      const long perBit = (k == FP_TOFP_SIGNED) ? 35L : 20L;
      const long exact = (k == FP_TOFP_SIGNED) ? 8L : 1L;
      return src <= sig ? exact * src : perBit * src;
    }

    case FP_TO_UBV:
    case FP_TO_SBV:
      // Children are (target width, rounding mode, operand [, default]).
      return (k == FP_TO_SBV ? 26L : 23L) *
             ((long)std::max(1u, b.GetValueWidth()) + (long)fpWidth(b[2]));

    default:
      break;
  }

  return std::max(1L, w) * b.Degree();
}

} // namespace

long eval(const ASTNode& b)
{
  const Kind k = b.GetKind();

  if (b.Degree() == 0)
    return 0; // consts & symbols don't count.

  const unsigned w = b.GetValueWidth();
  const unsigned degree = b.Degree();
  // Booleans report a width of zero; the arithmetic below wants one bit.
  const long lw = std::max(1u, w);

  // An operation over constants alone is evaluated by the bit-blaster, not
  // built: every bit of it comes back as the AIG's true or false. That is
  // worth testing for even though the simplifying node factory folds most of
  // them on creation, because the floating-point operations are folded later
  // -- during lowering -- and the score is taken before that.
  if (constantChildren(b) == degree)
    return 0;

  // Likewise a comparison of a node with itself. This is not the dead branch
  // it looks like: propagating an equality x = e substitutes e for x on both
  // sides of it, and the reflexive float equality that leaves behind is only
  // recognised as true when the operation is lowered.
  switch (k)
  {
    case EQ:
    case FP_SMT_EQ:
    case BVLT:
    case BVLE:
    case BVGT:
    case BVGE:
    case BVSLT:
    case BVSLE:
    case BVSGT:
    case BVSGE:
      if (b[0] == b[1])
        return 0;
      break;
    default:
      break;
  }

  if (is_FP_kind(k))
    return fpEval(b, k);

  switch (k)
  {
    // Selecting, permuting and inverting bits is wiring: no AND-node is
    // built for any of these.
    case BVNOT:
    case NOT:
    case BVCONCAT:
    case BVEXTRACT:
    case BVSX:
    case BVZX:
    case BOOLEXTRACT:
      return 0;

    case BVAND:
    case BVOR:
    case BVNAND:
    case BVNOR:
    {
      // A constant operand fixes each column, so it costs nothing.
      const unsigned symbolic = degree - constantChildren(b);
      return symbolic < 2 ? 0 : lw * (symbolic - 1);
    }

    case BVXOR:
    case BVXNOR:
    {
      // An AIG spends three nodes on an XOR, but XOR with a constant is a
      // conditional inversion, so it is free.
      const unsigned symbolic = degree - constantChildren(b);
      return symbolic < 2 ? 0 : 3L * lw * (symbolic - 1);
    }

    case BVPLUS:
      return addCost(b, lw, false);

    case BVSUB:
      // Blasted as a + (-b), and the negation folds into the adder.
      return addCost(b, lw, true);

    case BVUMINUS:
      return 4L * (lw - 1);

    case BVMULT:
      if (degree == 2)
        return multiplyCost(b, lw);
      // Wider multiplies are binarised before the bit-blaster sees them.
      return (long)(degree - 1) * multiplyCost(b, lw);

    case BVDIV:
    case BVMOD:
      // Restoring long division: a subtract and a select per quotient bit,
      // over a remainder as wide as the dividend.
      if (b[0].isConstant())
        return constantDivisionCost(true, b[0], lw);
      if (b[1].isConstant())
        return constantDivisionCost(false, b[1], lw);
      return 20L * (lw - 1) * (lw - 1) + 29L * lw;

    case SBVDIV:
    case SBVREM:
    case SBVMOD:
      // The unsigned circuit plus the sign fixups on either side of it.
      if (b[0].isConstant())
        return constantDivisionCost(true, b[0], lw) + 12L * lw;
      if (b[1].isConstant())
        return constantDivisionCost(false, b[1], lw) + 12L * lw;
      return 20L * (lw - 1) * (lw - 1) + 50L * lw;

    case BVLEFTSHIFT:
    case BVRIGHTSHIFT:
    case BVSRSHIFT:
    {
      // A barrel shifter: log2(w) stages of w muxes, plus the sign fill for
      // an arithmetic shift. A constant distance is wiring; shifting a
      // constant leaves each stage with one known input.
      if (b[1].isConstant())
        return 0;
      if (b[0].isConstant())
        return (11L * lw) / 2;
      const long stages = log2ceil(w);
      return ((k == BVSRSHIFT) ? 7L : 6L) * lw * stages / 2;
    }

    case ITE:
    {
      if (w == 0)
        return 3; // a Boolean ITE is one mux.
      const unsigned constantArms =
          (b[1].isConstant() ? 1u : 0u) + (b[2].isConstant() ? 1u : 0u);
      if (constantArms == 2)
        return 0;
      return constantArms == 1 ? lw + 3 : 3L * lw;
    }

    case EQ:
    {
      const unsigned ow = std::max(1u, b[0].GetValueWidth());
      return anyConstantChild(b) ? std::max(1L, (long)ow - 1) : 4L * ow - 1;
    }

    case BVLT:
    case BVLE:
    case BVGT:
    case BVGE:
    case BVSLT:
    case BVSLE:
    case BVSGT:
    case BVSGE:
    {
      const unsigned ow = std::max(1u, b[0].GetValueWidth());
      return anyConstantChild(b) ? (long)ow : 6L * ow - 1;
    }

    case BVUADDO:
    case BVUSUBO:
    {
      // The adder, kept only for its carry out.
      const unsigned ow = std::max(1u, b[0].GetValueWidth());
      return 11L * ow - 7;
    }

    case BVSADDO:
    case BVSSUBO:
    {
      // As above, plus the sign comparison the signed predicate needs.
      const unsigned ow = std::max(1u, b[0].GetValueWidth());
      return 11L * ow + 3;
    }

    case BVUMULO:
    {
      const unsigned ow = std::max(1u, b[0].GetValueWidth());
      return 12L * (ow - 1) * (ow - 1) + 7L * ow;
    }

    case BVSMULO:
    {
      const unsigned ow = std::max(1u, b[0].GetValueWidth());
      return 23L * (ow - 1) * (ow - 1) + 21L * ow;
    }

    // Boolean connectives, one AIG node per binary combination.
    case AND:
    case OR:
    case NAND:
    case NOR:
      return degree - 1;

    case XOR:
    case IFF:
      return 3L * (degree - 1);

    case IMPLIES:
      return 1;

    default:
      // READ and WRITE reach here, as does anything new. Arrays are removed
      // before the bit-blaster runs, so this only has to be a placeholder
      // that grows with the operand.
      return std::max<long>(w, 1) * degree;
  }
}

long DifficultyScore::score(const ASTNode& top, STPMgr* mgr)
{

  {
    const auto it = cache.find(top.GetNodeNum());
    if (it != cache.end())
      return it->second;
  }

  NonAtomIterator ni(top, mgr->ASTUndefined, *mgr);
  ASTNode current;
  long result = 0;
  while ((current = ni.next()) != ni.end())
    {
      evalCount++;
      result += eval(current);
    }

  cache.insert(std::make_pair(top.GetNodeNum(), result));
  return result;
}
}

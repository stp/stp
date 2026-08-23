/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Februrary, 2010
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

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/AST/AST.h"
#include "stp/AST/ASTKind.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/Simplifier/Simplifier.h"
#include <cassert>
#include <cmath>
#include <deque>

using stp::Kind;

using stp::SYMBOL;
using stp::BVNOT;
using stp::BVMOD;
using stp::BVUMINUS;
using stp::BVMULT;
using stp::ITE;
using stp::EQ;
using stp::ARRAY_EQ;
using stp::UF_APPLY;
using stp::BVSRSHIFT;
using stp::SBVREM;
using stp::SBVMOD;
using stp::SBVDIV;
using stp::BVCONCAT;
using stp::BVEXTRACT;
using stp::BVRIGHTSHIFT;
using stp::BVPLUS;
using stp::BVXOR;
using stp::BVDIV;

using std::cout;
using std::endl;

static bool debug_simplifyingNodeFactory = false;

// True if the constant has exactly one bit set.
static bool hasSingleOneBit(const stp::ASTNode& n)
{
  assert(n.GetKind() == stp::BVCONST);
  unsigned found = 0;
  for (unsigned i = 0; i < n.GetValueWidth(); i++)
    if (CONSTANTBV::BitVector_bit_test(n.GetBVConst(), i))
      found++;
  return (found == 1);
}

// Position of the lowest set bit; the constant must not be zero.
static unsigned lowestOneBit(const stp::ASTNode& n)
{
  assert(n.GetKind() == stp::BVCONST);
  unsigned position = 0;
  while (!CONSTANTBV::BitVector_bit_test(n.GetBVConst(), position))
    position++;
  return position;
}

// Recognise the packed floating-point constants +1.0 and -1.0 at any format:
// returns 1 for +1.0, -1 for -1.0, and 0 otherwise. Both have an all-zero
// significand and a biased exponent equal to the bias 2^(eb-1)-1 -- that is,
// the exponent field is 0 1..1, its top bit clear and its remaining eb-1 bits
// set -- and the sign bit selects between them. Read straight from the packed
// representation, so it holds for every width.
static int fpConstPlusMinusOne(const stp::ASTNode& c)
{
  if (c.GetKind() != stp::BVCONST)
    return 0;
  const unsigned eb = c.GetExpWidth();
  const unsigned sb = c.GetSigWidth();
  // A real IEEE format has eb, sb >= 2, and the packed width must be eb + sb
  // for the bit indices below to be in range.
  if (eb < 2 || sb < 2 || c.GetValueWidth() != eb + sb)
    return 0;
  stp::CBV bits = c.GetBVConst();
  // Significand field: bits [0 .. sb-2] all zero.
  for (unsigned i = 0; i + 1 < sb; i++)
    if (CONSTANTBV::BitVector_bit_test(bits, i))
      return 0;
  // Exponent field is [sb-1 .. sb+eb-2]; the bias is 0 1..1, so its top bit
  // (sb+eb-2) is clear and its lower eb-1 bits (sb-1 .. sb+eb-3) are all set.
  if (CONSTANTBV::BitVector_bit_test(bits, sb + eb - 2))
    return 0;
  for (unsigned i = sb - 1; i + 1 < sb + eb - 1; i++)
    if (!CONSTANTBV::BitVector_bit_test(bits, i))
      return 0;
  // Matched ±1.0; the sign bit (the top bit) chooses the sign.
  return CONSTANTBV::BitVector_bit_test(bits, eb + sb - 1) ? -1 : 1;
}

// True for a constant that carries a plausible packed floating-point format:
// the guard every classifier below applies before reading fields. A real IEEE
// format has eb, sb >= 2, and the packed width must be eb + sb for the bit
// indices to be in range. (A rounding-mode constant is also kind BVCONST but
// carries no format, so it fails here.)
static bool fpFormattedConst(const stp::ASTNode& c)
{
  if (c.GetKind() != stp::BVCONST)
    return false;
  const unsigned eb = c.GetExpWidth();
  const unsigned sb = c.GetSigWidth();
  return eb >= 2 && sb >= 2 && c.GetValueWidth() == eb + sb;
}

// True for a packed floating-point constant that is NaN: exponent field
// (bits [sb-1 .. sb+eb-2]) all ones and stored significand (bits
// [0 .. sb-2]) nonzero. Interning canonicalises every NaN literal to one
// pattern, but classify from the bits rather than lean on that.
static bool fpConstIsNaN(const stp::ASTNode& c)
{
  if (!fpFormattedConst(c))
    return false;
  const unsigned eb = c.GetExpWidth();
  const unsigned sb = c.GetSigWidth();
  stp::CBV bits = c.GetBVConst();
  for (unsigned i = sb - 1; i < sb + eb - 1; i++)
    if (!CONSTANTBV::BitVector_bit_test(bits, i))
      return false;
  for (unsigned i = 0; i + 1 < sb; i++)
    if (CONSTANTBV::BitVector_bit_test(bits, i))
      return true;
  return false;
}

// The infinities: exponent field all ones, stored significand zero. Returns
// +1 for +oo, -1 for -oo, and 0 for everything else.
static int fpConstInfSign(const stp::ASTNode& c)
{
  if (!fpFormattedConst(c))
    return 0;
  const unsigned eb = c.GetExpWidth();
  const unsigned sb = c.GetSigWidth();
  stp::CBV bits = c.GetBVConst();
  for (unsigned i = sb - 1; i < sb + eb - 1; i++)
    if (!CONSTANTBV::BitVector_bit_test(bits, i))
      return 0;
  for (unsigned i = 0; i + 1 < sb; i++)
    if (CONSTANTBV::BitVector_bit_test(bits, i))
      return 0;
  return CONSTANTBV::BitVector_bit_test(bits, eb + sb - 1) ? -1 : 1;
}

// True for a packed floating-point constant that is +0 or -0: everything
// below the sign bit is zero.
static bool fpConstIsZero(const stp::ASTNode& c)
{
  assert(c.GetKind() == stp::BVCONST);
  stp::CBV bits = c.GetBVConst();
  for (unsigned i = 0; i + 1 < c.GetValueWidth(); i++)
    if (CONSTANTBV::BitVector_bit_test(bits, i))
      return false;
  return true;
}

// The signed zeros: returns +1 for +0, -1 for -0, and 0 for everything else.
static int fpConstZeroSign(const stp::ASTNode& c)
{
  if (!fpFormattedConst(c) || !fpConstIsZero(c))
    return 0;
  return CONSTANTBV::BitVector_bit_test(c.GetBVConst(), c.GetValueWidth() - 1)
             ? -1
             : 1;
}

// The sign bit of any formatted constant: +1 clear, -1 set, 0 not one.
static int fpConstSign(const stp::ASTNode& c)
{
  if (!fpFormattedConst(c))
    return 0;
  return CONSTANTBV::BitVector_bit_test(c.GetBVConst(), c.GetValueWidth() - 1)
             ? -1
             : 1;
}

// The literal rounding mode in an arithmetic operation's first child, as a
// symbolic_fp::rounding_modes value -- or 0 when the mode is symbolic or not
// a legal one-hot encoding. (Both spellings of a literal mode -- the parser's
// plain 5-bit constant and the API's ASTRMConst -- are kind BVCONST.)
static unsigned fpConstRoundingMode(const stp::ASTNode& rm)
{
  if (rm.GetKind() != stp::BVCONST || rm.GetValueWidth() != 5)
    return 0;
  unsigned v = 0;
  for (unsigned i = 0; i < 5; i++)
    if (CONSTANTBV::BitVector_bit_test(rm.GetBVConst(), i))
      v |= 1u << i;
  return (v != 0 && (v & (v - 1)) == 0) ? v : 0;
}

// Whether adding the signed zero `zeroSign` (+1 for +0, -1 for -0) to any
// float returns that float exactly, under the literal mode `mode` (0 = not
// literal, never an identity). The sum of the two opposite zeros is the one
// input that can see the zero operand: it is +0 under every mode except
// round-toward-negative, where it is -0. So y + (-0) = y unless the mode is
// RTN, and y + (+0) = y only there.
static bool fpZeroIsAdditiveIdentity(int zeroSign, unsigned mode)
{
  if (mode == 0 || zeroSign == 0)
    return false;
  const bool rtn = (mode == stp::symbolic_fp::ROUND_TOWARD_NEGATIVE);
  return (zeroSign < 0) != rtn;
}

// Nonpositive constant: a zero of either sign, or sign bit set -- NaN
// excluded. The strict variant excludes the zeros too.
static bool fpConstIsNonpositive(const stp::ASTNode& c)
{
  if (!fpFormattedConst(c) || fpConstIsNaN(c))
    return false;
  return fpConstSign(c) < 0 || fpConstIsZero(c);
}
static bool fpConstIsNegativeNonzero(const stp::ASTNode& c)
{
  if (!fpFormattedConst(c) || fpConstIsNaN(c))
    return false;
  return fpConstSign(c) < 0 && !fpConstIsZero(c);
}

// A term whose value is never below zero -- at the very least -0, or NaN:
// fp.abs of anything; fp.sqrt of anything (a negative operand gives NaN, and
// sqrt(-0) is -0); and a self-product t*t (the operand's sign cancels with
// itself, and the invalid 0*oo needs distinct operands). The comparison
// rules below only rely on "never strictly below -0".
static bool fpTermNeverNegative(const stp::ASTNode& n)
{
  const stp::Kind k = n.GetKind();
  return (k == stp::FP_ABS && n.Degree() == 1) ||
         (k == stp::FP_SQRT && n.Degree() == 2) ||
         (k == stp::FP_MUL && n.Degree() == 3 && n[1] == n[2]);
}

// The shapes the classification predicates can look through (beyond the
// abs/neg peel): t + t is NaN, zero, negative or positive exactly when t is
// (equal signs cannot cancel, doubling cannot underflow, overflow keeps the
// sign); t * t is NaN exactly when t is and never negative; fp.sqrt keeps
// zeroness and positivity (a negative operand maps to NaN, which no
// classification counts); fp.roundToIntegral keeps NaN, infinity and sign,
// and its result -- integral, zero, infinite or NaN -- is never subnormal.
static bool fpIsSelfSum(const stp::ASTNode& n)
{
  return n.GetKind() == stp::FP_ADD && n.Degree() == 3 && n[1] == n[2];
}
static bool fpIsSelfProduct(const stp::ASTNode& n)
{
  return n.GetKind() == stp::FP_MUL && n.Degree() == 3 && n[1] == n[2];
}
static bool fpIsRoundToIntegral(const stp::ASTNode& n)
{
  return n.GetKind() == stp::FP_ROUNDTOINTEGRAL && n.Degree() == 2;
}

bool SimplifyingNodeFactory::children_all_constants(
    const ASTChildren children) const
{
  for (unsigned i = 0; i < children.size(); i++)
  {
    if (!children[i].isConstant())
    {
      return false;
    }
  }

  return true;
}

ASTNode SimplifyingNodeFactory::get_smallest_number(const unsigned width)
{
  // 1000000000 (most negative number.)
  stp::CBV max = CONSTANTBV::BitVector_Create(width, true);
  CONSTANTBV::BitVector_Bit_On(max, width - 1);
  return bm.CreateBVConst(max, width);
}

ASTNode SimplifyingNodeFactory::get_largest_number(const unsigned width)
{
  // 011111111 (most positive number.)
  stp::CBV max = CONSTANTBV::BitVector_Create(width, false);
  CONSTANTBV::BitVector_Fill(max);
  CONSTANTBV::BitVector_Bit_Off(max, width - 1);
  return bm.CreateBVConst(max, width);
}

ASTNode SimplifyingNodeFactory::foldFPSign(const ASTNode& fpConst, bool flip)
{
  const unsigned width = fpConst.GetValueWidth(); // packed: sign is the top bit
  stp::CBV bits = CONSTANTBV::BitVector_Clone(fpConst.GetBVConst());
  if (!flip) // abs: clear the sign
    CONSTANTBV::BitVector_Bit_Off(bits, width - 1);
  else if (CONSTANTBV::BitVector_bit_test(bits, width - 1)) // neg: flip it
    CONSTANTBV::BitVector_Bit_Off(bits, width - 1);
  else
    CONSTANTBV::BitVector_Bit_On(bits, width - 1);

  return bm.CreateFPConst(bm.CreateBVConst(bits, width),
                          fpConst.GetExpWidth(), fpConst.GetSigWidth());
}

ASTNode SimplifyingNodeFactory::makeFPNaN(unsigned eb, unsigned sb)
{
  const unsigned width = eb + sb;
  stp::CBV bits = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = sb - 1; i < width - 1; i++) // exponent field all ones
    CONSTANTBV::BitVector_Bit_On(bits, i);
  // Any nonzero stored significand: CreateFPConst canonicalises the payload.
  CONSTANTBV::BitVector_Bit_On(bits, 0);
  return bm.CreateFPConst(bm.CreateBVConst(bits, width), eb, sb);
}

ASTNode SimplifyingNodeFactory::makeFPZero(unsigned eb, unsigned sb,
                                           bool negative)
{
  const unsigned width = eb + sb;
  stp::CBV bits = CONSTANTBV::BitVector_Create(width, true);
  if (negative)
    CONSTANTBV::BitVector_Bit_On(bits, width - 1);
  return bm.CreateFPConst(bm.CreateBVConst(bits, width), eb, sb);
}

// The operand of `n` when `n` widens it -- converts into a format both of
// whose dimensions contain the operand's own. A widening is exact and
// order-preserving and fixes the specials, so comparisons look through it.
static stp::ASTNode exactWideningOperand(const stp::ASTNode& n)
{
  if (n.GetKind() != stp::FP_TOFP || n.Degree() != 4)
    return stp::ASTNode();
  if (n[0].GetKind() != stp::BVCONST || n[1].GetKind() != stp::BVCONST)
    return stp::ASTNode();
  const stp::ASTNode& op = n[3];
  if (op.GetType() != stp::FLOATINGPOINT_TYPE)
    return stp::ASTNode();
  const unsigned te = op.GetExpWidth(), ts = op.GetSigWidth();
  if (te < 2 || ts < 2)
    return stp::ASTNode();
  if (n[0].GetUnsignedConst() < te || n[1].GetUnsignedConst() < ts)
    return stp::ASTNode();
  return op;
}

ASTNode SimplifyingNodeFactory::fpConstAdjacent(const ASTNode& fpConst,
                                                bool up)
{
  if (!fpFormattedConst(fpConst) || fpConstIsNaN(fpConst))
    return ASTNode();
  const unsigned eb = fpConst.GetExpWidth();
  const unsigned sb = fpConst.GetSigWidth();
  const unsigned width = eb + sb;

  // The zeros sit together between the smallest subnormals of each sign.
  if (fpConstZeroSign(fpConst) != 0)
  {
    stp::CBV bits = CONSTANTBV::BitVector_Create(width, true);
    CONSTANTBV::BitVector_Bit_On(bits, 0);
    if (!up)
      CONSTANTBV::BitVector_Bit_On(bits, width - 1);
    return bm.CreateFPConst(bm.CreateBVConst(bits, width), eb, sb);
  }

  // Away from the zeros the packed encoding orders each sign's values by
  // magnitude, so stepping the word steps the value: +1 on the
  // non-negative side, -1 on the negative (-smallest-subnormal to -0).
  stp::CBV bits = CONSTANTBV::BitVector_Clone(fpConst.GetBVConst());
  const bool negative = CONSTANTBV::BitVector_bit_test(bits, width - 1);
  if (up != negative)
    CONSTANTBV::BitVector_increment(bits);
  else
    CONSTANTBV::BitVector_decrement(bits);
  return bm.CreateFPConst(bm.CreateBVConst(bits, width), eb, sb);
}

ASTNode SimplifyingNodeFactory::narrowFPConstDirected(const ASTNode& c,
                                                      unsigned te,
                                                      unsigned ts, bool up)
{
  const ASTNode direction = bm.CreateRMConst(
      up ? stp::symbolic_fp::ROUND_TOWARD_POSITIVE
         : stp::symbolic_fp::ROUND_TOWARD_NEGATIVE);
  const ASTNode candidate = NodeFactory::CreateTerm(
      stp::FP_TOFP, te + ts,
      {bm.CreateBVConst(32, te), bm.CreateBVConst(32, ts), direction, c});
  if (!fpFormattedConst(candidate) || fpConstIsNaN(candidate))
    return ASTNode();

  // The narrowing conversion is trusted at runtime; the assertions below
  // and the exhaustive DirectedNarrowing unit test hold it to the defining
  // property of the directed rounding (downward: r <= c < nextUp(r)),
  // stated over exact widenings and constant comparisons -- the
  // conversions a misbehaving narrower (symfpu once mis-rounded into
  // small-exponent formats) cannot affect.
#ifndef NDEBUG
  const unsigned se = c.GetExpWidth(), ss = c.GetSigWidth();
  const ASTNode rne =
      bm.CreateRMConst(stp::symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const auto widen = [&](const ASTNode& v) {
    return NodeFactory::CreateTerm(
        stp::FP_TOFP, se + ss,
        {bm.CreateBVConst(32, se), bm.CreateBVConst(32, ss), rne, v});
  };
  const ASTNode widened = widen(candidate);
  assert(fpFormattedConst(widened));
  // An exactly-representable constant (the infinities included) is its own
  // rounding in both directions and has no neighbour to test against.
  if (widened != c)
  {
    const ASTNode side = up ? NodeFactory::CreateNode(stp::FP_GEQ, widened, c)
                            : NodeFactory::CreateNode(stp::FP_GEQ, c, widened);
    assert(side == ASTTrue);
    (void)side;
    const ASTNode adjacent = fpConstAdjacent(candidate, !up);
    assert(!adjacent.IsNull());
    const ASTNode widenedAdjacent = widen(adjacent);
    assert(fpFormattedConst(widenedAdjacent));
    const ASTNode tight =
        up ? NodeFactory::CreateNode(stp::FP_GT, c, widenedAdjacent)
           : NodeFactory::CreateNode(stp::FP_GT, widenedAdjacent, c);
    assert(tight == ASTTrue);
    (void)tight;
  }
#endif

  return candidate;
}

ASTNode SimplifyingNodeFactory::narrowWidenedFPComparison(Kind kind,
                                                          const ASTNode& a,
                                                          const ASTNode& b)
{
  assert(kind == stp::FP_GT || kind == stp::FP_GEQ);
  const ASTNode xa = exactWideningOperand(a);
  const ASTNode xb = exactWideningOperand(b);

  // Both sides widened from the same format: compare the operands.
  if (!xa.IsNull() && !xb.IsNull() && xa.GetExpWidth() == xb.GetExpWidth() &&
      xa.GetSigWidth() == xb.GetSigWidth())
    return NodeFactory::CreateNode(kind, xa, xb);

  // One side widened, the other a constant of the wide format: round the
  // constant toward the side that keeps the truth value (no narrow value
  // lies strictly between a constant and its directed rounding):
  //
  //   widen(x) >  c   <=>   x >  round_down(c)
  //   widen(x) >= c   <=>   x >= round_up(c)
  //   c >  widen(x)   <=>   round_up(c)   >  x
  //   c >= widen(x)   <=>   round_down(c) >= x
  if (!xa.IsNull() && fpFormattedConst(b) &&
      b.GetExpWidth() == a.GetExpWidth() &&
      b.GetSigWidth() == a.GetSigWidth())
  {
    const ASTNode narrowed = narrowFPConstDirected(
        b, xa.GetExpWidth(), xa.GetSigWidth(), kind == stp::FP_GEQ);
    if (!narrowed.IsNull())
      return NodeFactory::CreateNode(kind, xa, narrowed);
  }
  if (!xb.IsNull() && fpFormattedConst(a) &&
      a.GetExpWidth() == b.GetExpWidth() &&
      a.GetSigWidth() == b.GetSigWidth())
  {
    const ASTNode narrowed = narrowFPConstDirected(
        a, xb.GetExpWidth(), xb.GetSigWidth(), kind == stp::FP_GT);
    if (!narrowed.IsNull())
      return NodeFactory::CreateNode(kind, narrowed, xb);
  }

  return ASTNode();
}

// The narrow-format value that widens exactly to the constant, or Null
// when no such value exists. Decided from the packed bits alone -- no
// conversion is consulted -- so a Null answer is a proof of
// unrepresentability and an equality against the constant may fold to
// false on its strength. The caller establishes that c is a formatted
// constant of a format containing (te, ts), with both exponent widths
// under 63.
ASTNode SimplifyingNodeFactory::fpConstNarrowExact(const ASTNode& c,
                                                   unsigned te, unsigned ts)
{
  const unsigned se = c.GetExpWidth(), ss = c.GetSigWidth();
  assert(fpFormattedConst(c) && se >= te && ss >= ts && se < 63 && te < 63);
  stp::CBV bits = c.GetBVConst();
  const bool negative = CONSTANTBV::BitVector_bit_test(bits, se + ss - 1);

  int64_t expField = 0;
  for (unsigned i = 0; i < se; i++)
    if (CONSTANTBV::BitVector_bit_test(bits, ss - 1 + i))
      expField |= (int64_t)1 << i;

  int sigTop = -1; // highest set stored-significand bit
  for (unsigned i = 0; i + 1 < ss; i++)
    if (CONSTANTBV::BitVector_bit_test(bits, i))
      sigTop = (int)i;

  const int64_t biasS = ((int64_t)1 << (se - 1)) - 1;
  const int64_t biasT = ((int64_t)1 << (te - 1)) - 1;

  if (expField == ((int64_t)1 << se) - 1)
    return (sigTop >= 0)
               ? makeFPNaN(te, ts)
               : bm.CreateFPSpecialConst(negative ? stp::FPSpecial::MinusInfinity
                                                  : stp::FPSpecial::PlusInfinity,
                                         te, ts);
  if (expField == 0 && sigTop < 0)
    return makeFPZero(te, ts, negative);

  // The value as mant * 2^(e - msb), with mant's leading one at msb.
  const bool isNormal = expField != 0;
  const int msb = isNormal ? (int)ss - 1 : sigTop;
  const int64_t e =
      isNormal ? expField - biasS : 1 - biasS - ((int64_t)ss - 1) + sigTop;
  const auto mant = [&](int64_t i) {
    if (i < 0 || i > msb)
      return false;
    if (isNormal && i == msb)
      return true;
    return CONSTANTBV::BitVector_bit_test(bits, (unsigned)i) != 0;
  };

  // Where the leading one lands in the target: bit ts-1 of a normal
  // significand, lower for a subnormal, out of range otherwise.
  int64_t drop; // mantissa bits below this index must all be zero
  int64_t targetExpField;
  if (e > biasT)
    return ASTNode(); // above the largest finite
  if (e >= 1 - biasT)
  {
    drop = msb - ((int64_t)ts - 1);
    targetExpField = e + biasT;
  }
  else if (e >= 2 - biasT - (int64_t)ts)
  {
    drop = msb - (e + biasT + (int64_t)ts - 2);
    targetExpField = 0;
  }
  else
    return ASTNode(); // below the smallest subnormal

  for (int64_t i = 0; i < drop; i++)
    if (mant(i))
      return ASTNode();

  const unsigned tw = te + ts;
  stp::CBV out = CONSTANTBV::BitVector_Create(tw, true);
  if (negative)
    CONSTANTBV::BitVector_Bit_On(out, tw - 1);
  for (unsigned i = 0; i < te; i++)
    if ((targetExpField >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(out, ts - 1 + i);
  for (unsigned k = 0; k + 1 < ts; k++)
    if (mant((int64_t)k + drop))
      CONSTANTBV::BitVector_Bit_On(out, k);
  return bm.CreateFPConst(bm.CreateBVConst(out, tw), te, ts);
}

// Equalities over an exactly-widened operand narrow like the orderings,
// only more simply: nothing rounds. Two widenings from one format compare
// as their operands; against a wide constant, the comparison is with the
// constant's exact narrow preimage when it has one, and false when it
// does not (no narrow value widens onto it, and NaN operands make both
// equality kinds false anyway). The narrowed = form is what
// PropagateEqualities can substitute through, which the widened form
// never allows.
ASTNode SimplifyingNodeFactory::narrowWidenedFPEquality(Kind kind,
                                                        const ASTNode& a,
                                                        const ASTNode& b)
{
  assert(kind == stp::FP_EQ || kind == stp::FP_SMT_EQ);
  const ASTNode xa = exactWideningOperand(a);
  const ASTNode xb = exactWideningOperand(b);

  if (!xa.IsNull() && !xb.IsNull() && xa.GetExpWidth() == xb.GetExpWidth() &&
      xa.GetSigWidth() == xb.GetSigWidth())
    return NodeFactory::CreateNode(kind, xa, xb);

  const ASTNode& x = !xa.IsNull() ? xa : xb;
  const ASTNode& widened = !xa.IsNull() ? a : b;
  const ASTNode& other = !xa.IsNull() ? b : a;
  if (x.IsNull() || !fpFormattedConst(other) ||
      other.GetExpWidth() != widened.GetExpWidth() ||
      other.GetSigWidth() != widened.GetSigWidth() ||
      other.GetExpWidth() >= 63 || x.GetExpWidth() >= 63)
    return ASTNode();

  const ASTNode narrowed =
      fpConstNarrowExact(other, x.GetExpWidth(), x.GetSigWidth());
  if (narrowed.IsNull())
    return ASTFalse;
  return NodeFactory::CreateNode(kind, x, narrowed);
}

ASTNode SimplifyingNodeFactory::create_gt_node(const ASTChildren children)
{
  if (children[0] == children[1])
  {
    return ASTFalse;
  }

  if (children[0].isConstant() &&
      CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
  {
    return ASTFalse;
  }

  if (children[1].isConstant() &&
      CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
  {
    return ASTFalse;
  }

  if (children[0].GetKind() == BVRIGHTSHIFT && children[0][0] == children[1])
  {
    return ASTFalse;
  }

  if (children[0].GetKind() == stp::BVAND && children[0].Degree() > 1 &&
      ((children[0][0] == children[1]) || children[0][1] == children[1]))
  {
    return ASTFalse;
  }

  // (x umod s) > x is false: the remainder never exceeds the dividend,
  // including s == 0, where SMT-LIB defines the result as x itself.
  if (children[0].GetKind() == BVMOD && children[0][0] == children[1])
  {
    return ASTFalse;
  }

  // (x udiv ~x) > x is false: a nonzero divisor keeps the quotient <= x,
  // and ~x == 0 forces x == ones, where dividing by zero gives ones == x.
  if (children[0].GetKind() == BVDIV && children[0][0] == children[1] &&
      children[0][1].GetKind() == BVNOT && children[0][1][0] == children[1])
  {
    return ASTFalse;
  }

  // (t << s) > ~s and (t >> s) > ~s are false: shifting by s >= 1 clears
  // s low (high) bits, capping the result at 2^w - 2^s <= 2^w - 1 - s = ~s,
  // and s == 0 leaves t <= ones = ~s. The same holds with s = ~u, giving
  // the forms (t << ~u) > u and (t >> ~u) > u.
  if (children[0].GetKind() == stp::BVLEFTSHIFT ||
      children[0].GetKind() == BVRIGHTSHIFT)
  {
    const ASTNode& s = children[0][1];
    const ASTNode& u = children[1];
    if ((s.GetKind() == BVNOT && s[0] == u) ||
        (u.GetKind() == BVNOT && u[0] == s))
    {
      return ASTFalse;
    }
  }

  // A 1-bit unsigned comparison has a single satisfying assignment: 1 > 0.
  if (children[0].GetValueWidth() == 1)
  {
    const ASTNode a = NodeFactory::CreateNode(
        EQ, children[0], bm.CreateOneConst(1));
    const ASTNode b = NodeFactory::CreateNode(
        EQ, children[1], bm.CreateZeroConst(1));
    return NodeFactory::CreateNode(stp::AND, a, b);
  }

  // Bitwise complement reverses the unsigned order: ~a > ~b <=> b > a.
  if (children[0].GetKind() == BVNOT && children[1].GetKind() == BVNOT)
  {
    return NodeFactory::CreateNode(stp::BVGT, children[1][0], children[0][0]);
  }

  // x > (x + c) <=> x > ~c, and (x + c) > x <=> NOT(x > ~c): the sum wraps
  // past x exactly when x exceeds ~c.
  for (unsigned side = 0; side < 2; side++)
  {
    const ASTNode& plus = children[side];
    const ASTNode& x = children[1 - side];
    if (plus.GetKind() != BVPLUS || plus.Degree() != 2)
      continue;
    for (unsigned i = 0; i < 2; i++)
      if (plus[i].isConstant() && plus[1 - i] == x)
      {
        const ASTNode notC = NodeFactory::CreateTerm(
            BVNOT, x.GetValueWidth(), plus[i]);
        const ASTNode gt = NodeFactory::CreateNode(stp::BVGT, x, notC);
        return side == 1 ? gt : NodeFactory::CreateNode(stp::NOT, gt);
      }
  }

  //2nd part is the same ->only care about 1st part
  if (children[0].GetKind() == BVCONCAT && children[1].GetKind() == BVCONCAT &&
      children[0][1] == children[1][1])
  {
    return NodeFactory::CreateNode(stp::BVGT, children[0][0], children[1][0]);
  }

  //1st part is the same ->only care about 2nd part
  if (children[0].GetKind() == BVCONCAT && children[1].GetKind() == BVCONCAT &&
      children[0][0] == children[1][0])
  {
    return NodeFactory::CreateNode(stp::BVGT, children[0][1], children[1][1]);
  }

  // 1 > x -> (x ==0)
  if (children[0].isConstant() && CreateOneConst(children[0].GetValueWidth())== children[0])
  {
    return NodeFactory::CreateNode(stp::EQ, NodeFactory::CreateZeroConst(children[0].GetValueWidth()), children[1] );
  }

  //If child 1 is constant, GT == NOT EQ
  if (children[1].isConstant() &&
      CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
  {
    return NodeFactory::CreateNode(
        stp::NOT, NodeFactory::CreateNode(EQ, children[0], children[1]));
  }

  //If child 0 is constant, GT == NOT EQ
  if (children[0].isConstant() &&
      CONSTANTBV::BitVector_is_full(children[0].GetBVConst()))
  {
    return NodeFactory::CreateNode(
        stp::NOT, NodeFactory::CreateNode(EQ, children[0], children[1]));
  }

  // constant > (constant-top ++ y): if the constant's top bits equal the
  // concat's constant top, only the bottom parts matter. e.g.
  //   1352830:(BVGT
  //     1280904:0x00000055
  //     8816:(BVCONCAT
  //       7538:0x000000
  //       1252:x7169))
  if (children[0].GetKind() == stp::BVCONST &&
      children[1].GetKind() == BVCONCAT &&
      children[1][0].GetKind() == stp::BVCONST)
  {
    const ASTNode top = NodeFactory::CreateTerm(
        BVEXTRACT, children[1][0].GetValueWidth(), children[0],
        bm.CreateBVConst(32, children[0].GetValueWidth() - 1),
        bm.CreateBVConst(32, children[1][1].GetValueWidth()));
    if (top == children[1][0])
    {
      const ASTNode bottom = NodeFactory::CreateTerm(
          BVEXTRACT, children[1][1].GetValueWidth(), children[0],
          bm.CreateBVConst(32, children[1][1].GetValueWidth() - 1),
          bm.CreateBVConst(32, 0));
      return NodeFactory::CreateNode(stp::BVGT, bottom, children[1][1]);
    }
  }

  // Issue #381. It's a yucky fix because it only handles a specific instance
  // (not equality or the operands swapped).
  if (children[0].GetKind() == BVMOD && children[0][1] == children[1])
  {
    const auto width = children[0].GetValueWidth();
    const auto zero =NodeFactory::CreateZeroConst(width);

    // Named variables, so that the nodes aren't built in whatever order the
    // compiler picks to evaluate the arguments in.
    const ASTNode isZero = NodeFactory::CreateNode(EQ, children[1], zero);
    const ASTNode isPositive =
        NodeFactory::CreateNode(stp::BVGT, children[0][0], zero);

    return NodeFactory::CreateNode
    (
        stp::AND,
        isZero,
        isPositive
    );
  }

  // No rule applied; the caller falls back to the hashing factory.
  return ASTNode();
}

ASTNode SimplifyingNodeFactory::CreateNode(Kind kind,
                                           const ASTChildren children)
{
  assert(kind != SYMBOL);
  // These are created specially.
  //

  // If all the parameters are constant, return the constant value.
  // The bitblaster calls CreateNode with a boolean vector. We don't try to
  // simplify those.
  // The type kinds (BOOLEAN..ROUNDINGMODE, API-only nodes) are exempt: a
  // childless one has "all children constant" vacuously, and the constant
  // evaluator has no business seeing a type.
  //
  // Floating-point predicates fold here too: the constant evaluator's FP
  // arm evaluates them by lowering over the constant operands and returns
  // TRUE/FALSE, so constant floating-point comparisons and classifications
  // never outlive their creation. (The FP *term* fold, with its
  // format-carrying subtleties, is in CreateTerm.)
  if (kind != stp::UNDEFINED && kind != stp::BOOLEAN &&
      kind != stp::BITVECTOR && kind != stp::ARRAY &&
      kind != stp::FLOATINGPOINT && kind != stp::ROUNDINGMODE &&
      kind != stp::DISTINCT && children_all_constants(children))
  {
    const ASTNode& hash = hashing.CreateNode(kind, children);
    const ASTNode& c = NonMemberBVConstEvaluator(&bm, hash);
    assert(c.isConstant());
    return c;
  }

  ASTNode result;
  switch (kind)
  {
    // convert the Less thans to greater thans.
    case stp::BVLT:
      assert(children.size() == 2);
      result = NodeFactory::CreateNode(stp::BVGT, children[1], children[0]);
      break;

    case stp::BVLE:
      assert(children.size() == 2);
      result = NodeFactory::CreateNode(stp::BVGE, children[1], children[0]);
      break;

    case stp::BVSLT:
      assert(children.size() == 2);
      result = NodeFactory::CreateNode(stp::BVSGT, children[1], children[0]);
      break;

    case stp::BVSLE:
      assert(children.size() == 2);
      result = NodeFactory::CreateNode(stp::BVSGE, children[1], children[0]);
      break;

    case stp::BVSGT:
      assert(children.size() == 2);
      if (children[0] == children[1])
        result = ASTFalse;

      if (children[1].GetKind() == stp::BVCONST)
      {
        const unsigned width = children[0].GetValueWidth();
        if (children[1] == get_largest_number(width))
          result = ASTFalse;
      }

      if (children[0].GetKind() == stp::BVCONST)
      {
        const unsigned width = children[0].GetValueWidth();
        if (children[0] == get_smallest_number(width))
          result = ASTFalse;
      }

      // x >s smallest -> NOT(x == smallest). Nothing is below the most-negative
      // value, so the comparison holds for every x except smallest itself.
      // (Signed dual of the "x > 0 -> NOT(x == 0)" rule in create_gt_node.)
      if (result.IsNull() && children[1].GetKind() == stp::BVCONST &&
          children[1] == get_smallest_number(children[0].GetValueWidth()))
      {
        result = NodeFactory::CreateNode(
            stp::NOT, NodeFactory::CreateNode(EQ, children[0], children[1]));
      }

      // largest >s x -> NOT(largest == x). Nothing is above the most-positive
      // value, so the comparison holds for every x except largest itself.
      // (Signed dual of the "max > x -> NOT(max == x)" rule in create_gt_node.)
      if (result.IsNull() && children[0].GetKind() == stp::BVCONST &&
          children[0] == get_largest_number(children[0].GetValueWidth()))
      {
        result = NodeFactory::CreateNode(
            stp::NOT, NodeFactory::CreateNode(EQ, children[0], children[1]));
      }

      // A 1-bit signed comparison has a single satisfying assignment:
      // 0 is the largest value and -1 (bit set) the smallest, so 0 >s 1.
      if (result.IsNull() && children[0].GetValueWidth() == 1)
      {
        const ASTNode a = NodeFactory::CreateNode(
            EQ, children[0], bm.CreateZeroConst(1));
        const ASTNode b = NodeFactory::CreateNode(
            EQ, children[1], bm.CreateOneConst(1));
        result = NodeFactory::CreateNode(stp::AND, a, b);
      }

      // x >s (x umod ~x) is false: x never signed-exceeds that remainder.
      // The BVMOD rules rewrite (x umod ~x) to (ones umod ~x), so match the
      // dividend as either x or the ones constant.
      if (result.IsNull() && children[1].GetKind() == BVMOD &&
          children[1][1].GetKind() == BVNOT &&
          children[1][1][0] == children[0] &&
          (children[1][0] == children[0] ||
           children[1][0] ==
               bm.CreateMaxConst(children[0].GetValueWidth())))
      {
        result = ASTFalse;
      }

      // x >s (x srem ~x) is false. The SBVREM rules normalise the remainder
      // to -(1 smod ~x), so match both that and the raw form.
      if (result.IsNull() && children[1].GetKind() == BVUMINUS &&
          children[1][0].GetKind() == SBVMOD &&
          children[1][0][1].GetKind() == BVNOT &&
          children[1][0][1][0] == children[0] &&
          children[1][0][0] ==
              bm.CreateOneConst(children[0].GetValueWidth()))
      {
        result = ASTFalse;
      }

      if (result.IsNull() && children[1].GetKind() == SBVREM &&
          children[1][0] == children[0] &&
          children[1][1].GetKind() == BVNOT &&
          children[1][1][0] == children[0])
      {
        result = ASTFalse;
      }

      //2nd part is the same -> only care about 1st part
      if (children[0].GetKind() == BVCONCAT &&
          children[1].GetKind() == BVCONCAT && children[0][1] == children[1][1])
      {
        result =
            NodeFactory::CreateNode(stp::BVSGT, children[0][0], children[1][0]);
      }

      //1st part is the same -> it decides the sign, so the 2nd parts
      // compare unsigned.
      if (result.IsNull() && children[0].GetKind() == BVCONCAT &&
          children[1].GetKind() == BVCONCAT && children[0][0] == children[1][0])
      {
        result =
            NodeFactory::CreateNode(stp::BVGT, children[0][1], children[1][1]);
      }

      // Sign extension keeps the signed value, so the comparison only
      // needs the wider of the two originals' widths: drop the extension
      // of the wider side, and extend the narrower side just up to it.
      // At least one BVSX always goes away.
      if (result.IsNull() && children[0].GetKind() == stp::BVSX &&
          children[1].GetKind() == stp::BVSX)
      {
        const unsigned w0 = children[0][0].GetValueWidth();
        const unsigned w1 = children[1][0].GetValueWidth();
        ASTNode a = children[0][0];
        ASTNode b = children[1][0];
        if (w0 < w1)
          a = NodeFactory::CreateTerm(stp::BVSX, w1, a,
                                      bm.CreateBVConst(32, w1));
        else if (w1 < w0)
          b = NodeFactory::CreateTerm(stp::BVSX, w0, b,
                                      bm.CreateBVConst(32, w0));
        result = NodeFactory::CreateNode(stp::BVSGT, a, b);
      }

      break;

    case stp::BVGT:
      assert(children.size() == 2);
      result = create_gt_node(children);
      break;

    case stp::BVGE:
    {
      assert(children.size() == 2);
      ASTNode a = NodeFactory::CreateNode(stp::BVGT, children[1], children[0]);
      result = NodeFactory::CreateNode(stp::NOT, a);
    }
    break;

    case stp::BVSGE:
    {
      assert(children.size() == 2);
      ASTNode a = NodeFactory::CreateNode(stp::BVSGT, children[1], children[0]);
      result = NodeFactory::CreateNode(stp::NOT, a);
    }
    break;

    case stp::NOT:
      result = CreateSimpleNot(children);
      break;
    case stp::AND:
      result = CreateSimpleAndOr(1, children);
      break;
    case stp::OR:
      result = CreateSimpleAndOr(0, children);
      break;
    case stp::NAND:
      result = CreateSimpleNot(CreateSimpleAndOr(1, children));
      break;
    case stp::NOR:
      result = CreateSimpleNot(CreateSimpleAndOr(0, children));
      break;
    case stp::XOR:
      result = CreateSimpleXor(children);
      break;
    case ITE:
      result = CreateSimpleFormITE(children);
      break;
    case EQ:
      // Whole-array equality is near-opaque until the solve-boundary
      // lowering pass: reflexivity and the structural rules in
      // simplifyArrayEquality apply, but no bit-vector equality rewrite
      // may run over array operands. The hashing factory owns both the
      // conversion to ARRAY_EQ and the rejection when --array-equality is
      // off, so the rules only run once the node is legal to build.
      if (children.size() == 2 && children[0].GetIndexWidth() > 0)
      {
        if (children[0] == children[1])
          result = bm.ASTTrue;
        if (result.IsNull())
          result = selfStoreEquality(children[0], children[1]);
        if (result.IsNull() && bm.UserFlags.enable_array_equality)
          result = simplifyArrayEquality(children[0], children[1]);
        if (result.IsNull())
          result = hashing.CreateNode(EQ, children);
      }
      else
        result = CreateSimpleEQ(children);
      break;
    case ARRAY_EQ:
      assert(children.size() == 2);
      // ARRAY_EQ is deliberately near-opaque to ordinary simplification:
      // reflexivity and the structural rules apply; every other
      // instance must survive until the extensionality lowering pass.
      if (children[0] == children[1])
        result = bm.ASTTrue;
      else
        result = simplifyArrayEquality(children[0], children[1]);
      if (result.IsNull())
        result = hashing.CreateNode(ARRAY_EQ, children);
      break;
    case UF_APPLY:
      // Durable applications are opaque until completed-root lowering.
      result = hashing.CreateNode(UF_APPLY, children);
      break;
    case stp::IFF:
    {
      assert(children.size() == 2);
      result = CreateSimpleXor(children);
      result = CreateSimpleNot(result);
      break;
    }
    case stp::IMPLIES:
    {
      assert(children.size() == 2);
      if (children[0] == children[1])
      {
        result = bm.ASTTrue;
      }
      else
      {
        ASTVec newCh;
        newCh.reserve(2);
        newCh.push_back(CreateSimpleNot(children[0]));
        newCh.push_back(children[1]);
        result = CreateSimpleAndOr(0, newCh);
      }
      break;
    }

    // ----- Cheap floating-point rewrites, applied before bit-blasting. -----
    // These fire on the word-level node, so they shrink the circuit symfpu
    // would otherwise build. Structural only -- constant folding is left to
    // the blaster, which is why the FP kinds bypass the constant-fold path
    // above.

    // Classification ignores the sign, so a wrapping abs or neg is peeled
    // off; past that, each predicate looks through the shapes that preserve
    // what it tests (see the fpIsSelfSum group above). The recursive create
    // re-simplifies, so the rules compose through nested wrappers.
    case stp::FP_ISNORMAL:
    case stp::FP_ISSUBNORMAL:
    case stp::FP_ISZERO:
    case stp::FP_ISINFINITE:
    case stp::FP_ISNAN:
    {
      const ASTNode& t = children[0];
      // A widening fixes NaN, the infinities and the zeros (signs
      // included), so these three classifications commute with it; the
      // normal/subnormal pair does not -- a narrow subnormal widens to a
      // wide normal.
      if ((kind == stp::FP_ISNAN || kind == stp::FP_ISZERO ||
           kind == stp::FP_ISINFINITE) &&
          !exactWideningOperand(t).IsNull())
        result = NodeFactory::CreateNode(kind, exactWideningOperand(t));
      else if (t.GetKind() == stp::FP_ABS || t.GetKind() == stp::FP_NEG)
        result = NodeFactory::CreateNode(kind, t[0]);
      else if (kind == stp::FP_ISNAN &&
               (fpIsRoundToIntegral(t) || fpIsSelfSum(t) || fpIsSelfProduct(t)))
        result = NodeFactory::CreateNode(kind, t[1]);
      else if (kind == stp::FP_ISZERO &&
               ((t.GetKind() == stp::FP_SQRT && t.Degree() == 2) ||
                fpIsSelfSum(t)))
        result = NodeFactory::CreateNode(kind, t[1]);
      else if (kind == stp::FP_ISINFINITE && fpIsRoundToIntegral(t))
        result = NodeFactory::CreateNode(kind, t[1]);
      else if (kind == stp::FP_ISSUBNORMAL && fpIsRoundToIntegral(t))
        result = ASTFalse;
      break;
    }

    // The sign predicates. An abs is never negative, and positive exactly
    // when it is not NaN (both count the zeros: fp.isPositive(+0) holds); a
    // neg swaps the two predicates (NaN stays NaN, failing both); t + t and
    // fp.roundToIntegral keep the sign; sqrt keeps positivity (a negative
    // operand gives NaN, counted by neither); t * t is an abs in disguise.
    case stp::FP_ISNEGATIVE:
    {
      const ASTNode& t = children[0];
      // The sign of a widened value is its operand's (a widening fixes
      // the zeros' signs, and NaN maps to NaN, failing both predicates).
      if (!exactWideningOperand(t).IsNull())
        result = NodeFactory::CreateNode(kind, exactWideningOperand(t));
      else if (t.GetKind() == stp::FP_ABS || fpIsSelfProduct(t))
        result = ASTFalse;
      else if (t.GetKind() == stp::FP_NEG)
        result = NodeFactory::CreateNode(stp::FP_ISPOSITIVE, t[0]);
      else if (fpIsRoundToIntegral(t) || fpIsSelfSum(t))
        result = NodeFactory::CreateNode(kind, t[1]);
      break;
    }
    case stp::FP_ISPOSITIVE:
    {
      const ASTNode& t = children[0];
      // Same commute as FP_ISNEGATIVE: a widening keeps the sign.
      if (!exactWideningOperand(t).IsNull())
        result = NodeFactory::CreateNode(kind, exactWideningOperand(t));
      else if (t.GetKind() == stp::FP_ABS)
        result = NodeFactory::CreateNode(
            stp::NOT, NodeFactory::CreateNode(stp::FP_ISNAN, t[0]));
      else if (fpIsSelfProduct(t))
        result = NodeFactory::CreateNode(
            stp::NOT, NodeFactory::CreateNode(stp::FP_ISNAN, t[1]));
      else if (t.GetKind() == stp::FP_NEG)
        result = NodeFactory::CreateNode(stp::FP_ISNEGATIVE, t[0]);
      else if ((t.GetKind() == stp::FP_SQRT && t.Degree() == 2) ||
               fpIsRoundToIntegral(t) || fpIsSelfSum(t))
        result = NodeFactory::CreateNode(kind, t[1]);
      break;
    }

    // Mirror the less-thans onto the greater-thans, as the bit-vector
    // comparisons are above (BVLT -> BVGT): fp.lt(a, b) is fp.gt(b, a)
    // exactly, NaN included -- both mean "ordered and strictly ordered", so
    // the swap is a pure mirror -- and likewise for the non-strict pair.
    // Downstream simplification then meets only the greater-than forms and
    // needs half the comparison rules. (Unlike the total bit-vector order,
    // this is as far as FP comparisons collapse: not(fp.lt) is geq-or-
    // unordered, so the four kinds reduce to two, not one.)
    case stp::FP_LT:
      if (children.size() == 2)
        result = NodeFactory::CreateNode(stp::FP_GT, children[1], children[0]);
      break;

    case stp::FP_LEQ:
      if (children.size() == 2)
        result =
            NodeFactory::CreateNode(stp::FP_GEQ, children[1], children[0]);
      break;

    // x > x is false, NaN included. So is any comparison against a NaN
    // constant (NaN is unordered against everything), and the two
    // impossible strict comparisons against the extremes: -oo > x and
    // x > +oo hold for no x. (The mirrored fp.lt forms arrive here already
    // swapped, so these rules cover both spellings.) A term that is never
    // below zero (abs, sqrt, a self-product) cannot be under a nonpositive
    // constant, and is over a strictly negative one exactly when it is
    // ordered; and t > |t| never holds, since t <= |t| whenever ordered.
    case stp::FP_GT:
      if (children.size() == 2)
      {
        if (children[0] == children[1] || fpConstIsNaN(children[0]) ||
            fpConstIsNaN(children[1]) || fpConstInfSign(children[0]) == -1 ||
            fpConstInfSign(children[1]) == 1)
          result = ASTFalse;
        else if (children[1].GetKind() == stp::FP_ABS &&
                 children[1][0] == children[0])
          result = ASTFalse;
        else if (fpTermNeverNegative(children[1]) &&
                 fpConstIsNonpositive(children[0]))
          result = ASTFalse;
        else if (fpTermNeverNegative(children[0]) &&
                 fpConstIsNegativeNonzero(children[1]))
          result = NodeFactory::CreateNode(
              stp::NOT, NodeFactory::CreateNode(stp::FP_ISNAN, children[0]));

        if (result.IsNull())
          result =
              narrowWidenedFPComparison(kind, children[0], children[1]);
      }
      break;

    // x >= x holds exactly when x is not NaN -- and so do +oo >= x and
    // x >= -oo, since only a NaN is unordered against an extreme. Against a
    // NaN constant the comparison is simply false. The never-below-zero
    // terms compare against constants as in FP_GT (non-strict, so the zeros
    // change sides: N >= any nonpositive constant whenever ordered, and a
    // zero >= N squeezes N onto the zeros). |t| >= t whenever ordered.
    case stp::FP_GEQ:
      if (children.size() == 2)
      {
        if (fpConstIsNaN(children[0]) || fpConstIsNaN(children[1]))
          result = ASTFalse;
        else if (children[0] == children[1])
          result = NodeFactory::CreateNode(
              stp::NOT, NodeFactory::CreateNode(stp::FP_ISNAN, children[0]));
        else if (fpConstInfSign(children[0]) == 1)
          result = NodeFactory::CreateNode(
              stp::NOT, NodeFactory::CreateNode(stp::FP_ISNAN, children[1]));
        else if (fpConstInfSign(children[1]) == -1)
          result = NodeFactory::CreateNode(
              stp::NOT, NodeFactory::CreateNode(stp::FP_ISNAN, children[0]));
        else if (children[0].GetKind() == stp::FP_ABS &&
                 children[0][0] == children[1])
          result = NodeFactory::CreateNode(
              stp::NOT, NodeFactory::CreateNode(stp::FP_ISNAN, children[1]));
        else if (fpTermNeverNegative(children[0]) &&
                 fpConstIsNonpositive(children[1]))
          result = NodeFactory::CreateNode(
              stp::NOT, NodeFactory::CreateNode(stp::FP_ISNAN, children[0]));
        else if (fpTermNeverNegative(children[1]))
        {
          if (fpConstIsNegativeNonzero(children[0]))
            result = ASTFalse;
          else if (fpConstZeroSign(children[0]) != 0)
            result = NodeFactory::CreateNode(stp::FP_ISZERO, children[1]);
        }

        if (result.IsNull())
          result =
              narrowWidenedFPComparison(kind, children[0], children[1]);
      }
      break;

    case stp::FP_EQ:
    case stp::FP_SMT_EQ:
      if (children.size() == 2)
      {
        // x = x is reflexively true; fp.eq(x, x) fails exactly when x is NaN
        // (the FP_GEQ rule above, restated for the other reflexive predicate).
        //
        // This fold used to be suppressed while incremental solving was on,
        // to hold the equality until bit-blasting and keep the persistent
        // pipeline's encoding order stable. Node construction is meant to be
        // context-free -- the design doc says so -- and the flag it read is
        // set by the first push, so a pushing session got a different
        // word-level DAG even when the driver never engaged, and the
        // batch-versus-incremental differential compared two engines handed
        // different graphs. The evidence for the suppression was a >3x
        // CaDiCaL swing on the Newton family, which this project's own
        // protocol says must never be diagnosed from: it flips between 0.98s
        // and a timeout on identical code. Encoding order, if it needs
        // choosing, belongs where order is chosen.
        if (children[0] == children[1])
        {
          if (kind == stp::FP_SMT_EQ)
            result = bm.ASTTrue;
          else
            result = NodeFactory::CreateNode(
                stp::NOT,
                NodeFactory::CreateNode(stp::FP_ISNAN, children[0]));
          break;
        }

        // An exactly-widened operand: compare at its own format (against
        // the wide constant's exact preimage, or nothing widens onto the
        // constant and the equality is false).
        result =
            narrowWidenedFPEquality(kind, children[0], children[1]);
        if (!result.IsNull())
          break;

        // fp.eq against a constant: fp.eq and = disagree only on pairs
        // holding a NaN or two zeros, and inspecting the constant settles
        // both. Nothing compares fp.eq-equal to NaN; the zeros compare
        // fp.eq-equal to each other and to nothing else; any other value is
        // the sole member of its fp.eq class, where IEEE equality *is*
        // abstract equality. The prize is the = form: PropagateEqualities
        // may substitute through it, which fp.eq must never do.
        // (Both-constant instances folded before the switch.)
        if (kind == stp::FP_EQ)
        {
          const int ci = children[0].GetKind() == stp::BVCONST   ? 0
                         : children[1].GetKind() == stp::BVCONST ? 1
                                                                 : -1;
          // A constant operand of an fp.eq carries its format, but read the
          // fields rather than assume: a packed carrier that has lost the
          // stamp must fall through to the plain symmetric ordering.
          const unsigned eb = ci < 0 ? 0 : children[ci].GetExpWidth();
          const unsigned sb = ci < 0 ? 0 : children[ci].GetSigWidth();
          if (ci >= 0 && eb >= 2 && sb >= 2 &&
              children[ci].GetValueWidth() == eb + sb)
          {
            const ASTNode& c = children[ci];
            const ASTNode& x = children[1 - ci];
            if (fpConstIsNaN(c))
              result = ASTFalse;
            else if (fpConstIsZero(c))
              result = NodeFactory::CreateNode(stp::FP_ISZERO, x);
            else
              result = NodeFactory::CreateNode(stp::FP_SMT_EQ, x, c);
            break;
          }
        }

        // (= t NaN) is exactly (fp.isNaN t): SMT-LIB has a single NaN
        // value. Rewritten only when t is NOT a bare symbol --
        // PropagateEqualities substitutes through a `=` with a symbol on
        // one side and a constant on the other (x := NaN everywhere), which
        // is strictly stronger than holding the smaller predicate; a
        // compound t offers no substitution to lose, and the isNaN may
        // then simplify further (it peels abs/neg and looks through the
        // NaN-transparent shapes).
        if (kind == stp::FP_SMT_EQ)
        {
          for (unsigned k = 0; result.IsNull() && k <= 1; k++)
            if (fpConstIsNaN(children[k]) &&
                children[1 - k].GetKind() != stp::SYMBOL)
              result =
                  NodeFactory::CreateNode(stp::FP_ISNAN, children[1 - k]);
          if (!result.IsNull())
            break;
        }

        // Both float equalities are symmetric. Order the operands so that
        // x ~ y and y ~ x become the same node and share their blasted
        // circuit.
        if (children[0].GetNodeNum() > children[1].GetNodeNum())
        {
          ASTVec swapped;
          swapped.push_back(children[1]);
          swapped.push_back(children[0]);
          result = hashing.CreateNode(kind, swapped);
        }
      }
      break;

    default:
      result = hashing.CreateNode(kind, children);
  }

  if (result.IsNull())
    result = hashing.CreateNode(kind, children);

  return result;
}

ASTNode SimplifyingNodeFactory::CreateSimpleNot(const ASTNode& form)
{
  const Kind k = form.GetKind();
  switch (k)
  {
    case stp::FALSE:
    {
      return ASTTrue;
    }
    case stp::TRUE:
    {
      return ASTFalse;
    }
    case stp::NOT:
    {
      // NOT NOT cancellation
      return form[0];
    }
    default:
    {
      ASTVec children;
      children.push_back(form);
      return hashing.CreateNode(stp::NOT, children);
    }
  }
}

ASTNode SimplifyingNodeFactory::CreateSimpleNot(const ASTChildren children)
{
  assert(children.size() == 1);
  const Kind k = children[0].GetKind();
  switch (k)
  {
    case stp::FALSE:
    {
      return ASTTrue;
    }
    case stp::TRUE:
    {
      return ASTFalse;
    }
    case stp::NOT:
    {
      // NOT NOT cancellation
      return children[0][0];
    }
    default:
    {
      return hashing.CreateNode(stp::NOT, children);
    }
  }
}

ASTNode SimplifyingNodeFactory::CreateSimpleAndOr(bool IsAnd,
                                                  const ASTNode& form1,
                                                  const ASTNode& form2)
{
  ASTVec children;
  children.push_back(form1);
  children.push_back(form2);
  return CreateSimpleAndOr(IsAnd, children);
}

ASTNode SimplifyingNodeFactory::handle_2_children(bool IsAnd,
                                                  const ASTChildren children)
{
  if (children.size() == 2)
  {
    const Kind k = IsAnd ? stp::AND : stp::OR;
    const ASTNode& c0 = children[0];
    const ASTNode& c1 = children[1];

    if (k == stp::OR)
    {
      //case of a || ~a which is constant TRUE

      if (c0.GetKind() == stp::NOT && c0[0] == c1)
        return ASTTrue;
      if (c1.GetKind() == stp::NOT && c1[0] == c0)
        return ASTTrue;

      // A OR NOT(A OR B) == A OR NOT B, for either operand order and either
      // position of A in the inner OR. e.g.
      //   136896:(OR
      //     [127666]
      //     127713:(NOT 127712:(OR
      //       [127666]
      //       ...)))
      for (int i = 0; i < 2; i++)
      {
        const ASTNode& a = children[i];
        const ASTNode& other = children[1 - i];
        if (other.GetKind() == stp::NOT && other[0].GetKind() == stp::OR &&
            other[0].Degree() == 2)
        {
          for (int j = 0; j < 2; j++)
            if (other[0][j] == a)
              return CreateSimpleAndOr(0, a, CreateSimpleNot(other[0][1 - j]));
        }
      }
    }
    else
    {
      assert(k == stp::AND);
      //case of a && ~a which is constant FALSE

      if (c0.GetKind() == stp::NOT && c0[0] == c1)
        return ASTFalse;
      if (c1.GetKind() == stp::NOT && c1[0] == c0)
        return ASTFalse;
    }
  }
  return ASTUndefined;
}

ASTNode SimplifyingNodeFactory::CreateSimpleAndOr(bool IsAnd,
                                                  const ASTChildren c)
{
  ASTNode retval = handle_2_children(IsAnd, c);
  if (retval != ASTUndefined)
    return retval;

  const ASTNode& annihilator = (IsAnd ? ASTFalse : ASTTrue);
  const ASTNode& identity = (IsAnd ? ASTTrue : ASTFalse);

  // Sorting these can be expensive, so we only sort it if it's not already sorted.
  bool isSorted =  std::is_sorted(c.begin(),c.end(),stp::ExprLess{});
  ASTVec sorted_children;
  if (!isSorted)
  {
    sorted_children.assign(c.begin(), c.end());
    SortByExprNum(sorted_children);  
  }
  const ASTChildren children =
      isSorted ? c : ASTChildren(sorted_children);

  // Copy on write. Usually nothing is dropped, so we only build up
  // "new_children" once the first element is actually discarded; until then
  // "children" itself is the answer.
  ASTVec new_children;
  bool materialised = false;

  const Kind node_kind = IsAnd ? stp::AND : stp::OR;
  bool nested_same_kind = false;

  const size_t num_children = children.size();
  for (size_t i = 0; i < num_children; i++)
  {
    const ASTNode& curr = children[i];
    const bool nextexists = (i + 1 < num_children);

    if (nextexists)
    {
      const ASTNode& next = children[i + 1];
      if (next.GetKind() == stp::NOT && next[0] == curr)
        return annihilator;
    }

    if (curr == annihilator)
    {
      return annihilator;
    }
    else if (curr == identity || (nextexists && (children[i + 1] == curr)))
    {
      // just drop it, copying across everything kept so far.
      if (!materialised)
      {
        materialised = true;
        new_children.reserve(num_children);
        new_children.insert(new_children.end(), children.begin(),
                            children.begin() + i);
      }
    }
    else
    {
      if (materialised)
        new_children.push_back(curr);
      if (curr.GetKind() == node_kind)
        nested_same_kind = true;
    }
  }

  const ASTChildren out =
      materialised ? ASTChildren(new_children) : children;

  // A child of the same kind contributes its own children conjunctively
  // (resp. disjunctively), so a literal here and its negation one level
  // down annihilate just as two top-level complements do.
  if (nested_same_kind)
  {
    stp::ASTNodeSet positive, negated;
    for (const ASTNode& n : out)
    {
      if (n.GetKind() == node_kind)
      {
        for (const ASTNode& c : n.GetChildren())
          if (c.GetKind() == stp::NOT)
            negated.insert(c[0]);
          else
            positive.insert(c);
      }
      else if (n.GetKind() == stp::NOT)
        negated.insert(n[0]);
      else
        positive.insert(n);
    }
    for (const ASTNode& n : negated)
      if (positive.find(n) != positive.end())
        return annihilator;
  }

  // If we get here, we saw no annihilators, and children should
  // be only the non-True nodes.
  switch (out.size())
  {
    case 0:
      return identity;
      break;

    case 1:
      return out[0];
      break;

    default:
      // 2 or more children.  Create a new node.
      return hashing.CreateNode(IsAnd ? stp::AND : stp::OR, out);
      break;
  }
  assert(false);
  exit(-1);
}

// Tries to simplify the input to TRUE/FALSE. if it fails, then
// return the constructed equality
ASTNode SimplifyingNodeFactory::CreateSimpleEQ(const ASTChildren children)
{
  assert(children.size() == 2);

  // SYMBOL = something, if not that, then CONSTANT =
  const bool swap = (children[1].GetKind() == stp::SYMBOL ||
                     ((children[0].GetKind() != stp::SYMBOL) &&
                      children[1].GetKind() == stp::BVCONST));
  const ASTNode& in1 = swap ? children[1] : children[0];
  const ASTNode& in2 = swap ? children[0] : children[1];
  const Kind k1 = in1.GetKind();
  const Kind k2 = in2.GetKind();
  const int width = in1.GetValueWidth();

  if (in1 == in2)
    // terms are syntactically the same
    return ASTTrue;

  // Two constant nodes still may be semantically equal: a float constant
  // interns apart from the plain constant with its bits, so compare the
  // bits, not the identities.
  if (stp::BVCONST == k1 && stp::BVCONST == k2)
    return stp::constantsSameBits(in1, in2) ? ASTTrue : ASTFalse;

  if ((k1 == BVNOT && k2 == BVNOT) || (k1 == BVUMINUS && k2 == BVUMINUS))
    return NodeFactory::CreateNode(EQ, in1[0], in2[0]);

  if ((k1 == BVUMINUS && k2 == stp::BVCONST) ||
      (k1 == BVNOT && k2 == stp::BVCONST))
    return NodeFactory::CreateNode(EQ, in1[0],
                                   NodeFactory::CreateTerm(k1, width, in2));

  if ((k2 == BVUMINUS && k1 == stp::BVCONST) ||
      (k2 == BVNOT && k1 == stp::BVCONST))
    return NodeFactory::CreateNode(EQ, in2[0],
                                   NodeFactory::CreateTerm(k2, width, in1));

  if ((k1 == BVNOT && in1[0] == in2) || (k2 == BVNOT && in2[0] == in1))
    return ASTFalse;

  // x = (~x << x) and x = (~x sdiv x) have no solution (checked exhaustively
  // over small widths): for the shift, x == 0 gives ones on the right, and
  // x != 0 has a set bit below position x that the shift has cleared.
  for (int i = 0; i < 2; i++)
  {
    const ASTNode& a = (i == 0) ? in1 : in2;
    const ASTNode& b = (i == 0) ? in2 : in1;
    if ((b.GetKind() == stp::BVLEFTSHIFT || b.GetKind() == SBVDIV) &&
        b[1] == a && b[0].GetKind() == BVNOT && b[0][0] == a)
      return ASTFalse;
  }

  // Normalise 1-bit equalities so both polarities of a test hash to the
  // same node: (x = 1) becomes NOT(x = 0).
  if (width == 1)
  {
    if (in1 == bm.CreateOneConst(1))
      return NodeFactory::CreateNode(
          stp::NOT, NodeFactory::CreateNode(EQ, in2, bm.CreateZeroConst(1)));
    if (in2 == bm.CreateOneConst(1))
      return NodeFactory::CreateNode(
          stp::NOT, NodeFactory::CreateNode(EQ, in1, bm.CreateZeroConst(1)));
  }

  if (k2 == stp::BVDIV && k1 == stp::BVCONST &&
      (in1 == bm.CreateZeroConst(width)))
    return NodeFactory::CreateNode(stp::BVGT, in2[1], in2[0]);

  if (k1 == stp::BVDIV && k2 == stp::BVCONST &&
      (in2 == bm.CreateZeroConst(width)))
    return NodeFactory::CreateNode(stp::BVGT, in1[1], in1[0]);

  // Split the constant to equal each part of the concat. A concat can itself
  // be one of those parts, so the old pair of CreateNode(EQ, ...) calls made
  // this recurse once per concat level.
  if (BVCONCAT == k2 && stp::BVCONST == k1)
    return CreateSimpleEQConstConcat(in1, in2);

  // (a ++ b) = (a ++ c) <=> b = c, and (a ++ c) = (b ++ c) <=> a = b.
  // Sharing a side pins the widths of the other sides to match. Peel an
  // entire run here before re-entering the factory, so a nested concat chain
  // consumes one C++ frame rather than one frame per equality rewrite.
  if (BVCONCAT == k1 && BVCONCAT == k2 &&
      (in1[0] == in2[0] || in1[1] == in2[1]))
  {
    ASTNode lhs = in1;
    ASTNode rhs = in2;
    while (lhs.GetKind() == BVCONCAT && rhs.GetKind() == BVCONCAT)
    {
      if (lhs[0] == rhs[0])
      {
        lhs = lhs[1];
        rhs = rhs[1];
      }
      else if (lhs[1] == rhs[1])
      {
        lhs = lhs[0];
        rhs = rhs[0];
      }
      else
        break;
    }
    return NodeFactory::CreateNode(EQ, lhs, rhs);
  }

  // Sign extension keeps the value, so the equality only needs the wider
  // of the two originals' widths: drop the extension of the wider side,
  // and extend the narrower side just up to it. At least one BVSX always
  // goes away.
  if (stp::BVSX == k1 && stp::BVSX == k2)
  {
    const unsigned w1 = in1[0].GetValueWidth();
    const unsigned w2 = in2[0].GetValueWidth();
    ASTNode a = in1[0];
    ASTNode b = in2[0];
    if (w1 < w2)
      a = NodeFactory::CreateTerm(stp::BVSX, w2, a, bm.CreateBVConst(32, w2));
    else if (w2 < w1)
      b = NodeFactory::CreateTerm(stp::BVSX, w1, b, bm.CreateBVConst(32, w1));
    return NodeFactory::CreateNode(EQ, a, b);
  }

  // This increases the number of nodes. So disable for now.
  if (false && BVCONCAT == k1 && BVCONCAT == k2 &&
      in1[0].GetValueWidth() == in2[0].GetValueWidth())
  {
    ASTNode a = NodeFactory::CreateNode(EQ, in1[0], in2[0]);
    ASTNode b = NodeFactory::CreateNode(EQ, in1[1], in2[1]);
    return NodeFactory::CreateNode(stp::AND, a, b);
  }

  if (k1 == stp::BVCONST && k2 == ITE && in2[1].GetKind() == stp::BVCONST &&
      in2[2].GetKind() == stp::BVCONST)
  {

    const ASTNode thn = NodeFactory::CreateNode(EQ, in1, in2[1]);
    const ASTNode els = NodeFactory::CreateNode(EQ, in1, in2[2]);
    ASTNode result = NodeFactory::CreateNode(ITE, in2[0], thn, els);

    return result;
  }

  // Don't create a PLUS with the same operand on both sides.
  // We don't do big pluses, because 1) this algorithm isn't good enough
  // 2) it might split nodes (a lot).
  if ((k1 == BVPLUS && in1.Degree() <= 2) ||
      (k2 == BVPLUS && in2.Degree() <= 2))
  {
    const ASTVec c1 = (k1 == BVPLUS) ? toASTVec(in1.GetChildren()) : ASTVec(1, in1);
    const ASTVec c2 = (k2 == BVPLUS) ? toASTVec(in2.GetChildren()) : ASTVec(1, in2);

    if (c1.size() <= 2 && c2.size() <= 2)
    {
      int match1 = -1, match2 = -1;

      for (size_t i = 0, c1Size = c1.size(); i < c1Size; ++i)
      {
        for (size_t j = 0, c2Size = c2.size(); j < c2Size; ++j)
        {
          if (c1[i] == c2[j])
          {
            match1 = i;
            match2 = j;
          }
        }
      }

      if (match1 != -1)
      {
        assert(match2 != -1);
        assert(match1 == 0 || match1 == 1);
        assert(match2 == 0 || match2 == 1);
        // If it was 1 element before, it's zero now.
        ASTNode n1 = c1.size() == 1 ? bm.CreateZeroConst(width)
                                    : c1[match1 == 0 ? 1 : 0];
        ASTNode n2 = c2.size() == 1 ? bm.CreateZeroConst(width)
                                    : c2[match2 == 0 ? 1 : 0];
        return NodeFactory::CreateNode(EQ, n1, n2);
      }
    }
  }

  if (k2 == BVPLUS && in2.Degree() == 2 && (in2[1] == in1 || in2[0] == in1))
  {
    return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width),
                                   in2[1] == in1 ? in2[0] : in2[1]);
  }

  if (k1 == BVPLUS && in1.Degree() == 2 && (in1[1] == in2 || in1[0] == in2))
  {
    return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width),
                                   in1[1] == in2 ? in1[0] : in1[1]);
  }

  if (k1 == stp::BVCONST && k2 == stp::BVXOR && in2.Degree() == 2 &&
      in2[0].GetKind() == stp::BVCONST)
  {
    return NodeFactory::CreateNode(
        EQ, NodeFactory::CreateTerm(stp::BVXOR, width, in1, in2[0]), in2[1]);
  }

  if (k2 == stp::BVCONST && k1 == stp::BVXOR && in1.Degree() == 2 &&
      in1[0].GetKind() == stp::BVCONST)
  {
    return NodeFactory::CreateNode(
        EQ, NodeFactory::CreateTerm(stp::BVXOR, width, in2, in1[0]), in1[1]);
  }

  if (k2 == stp::BVXOR && in2.Degree() == 2 && in1 == in2[0])
  {
    return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width), in2[1]);
  }

  if (k1 == stp::BVXOR && in1.Degree() == 2 && in2 == in1[0])
  {
    return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width), in1[1]);
  }

  if (k1 == stp::BVCONST && k2 == stp::BVSX &&
      (in2[0].GetValueWidth() != (unsigned)width))
  {
    // Each of the bits in the extended part, and one into the un-extended part
    // must be the same.
    bool foundZero = false, foundOne = false;
    const int original_width = in2[0].GetValueWidth();
    const int new_width = in2.GetValueWidth();

    for (int i = original_width - 1; i < new_width; i++)
    {
      if (CONSTANTBV::BitVector_bit_test(in1.GetBVConst(), i))
        foundOne = true;
      else
        foundZero = true;
    }

    if (foundZero && foundOne)
      return ASTFalse;

    ASTNode lhs = NodeFactory::CreateTerm(
        BVEXTRACT, original_width, in1,
        bm.CreateBVConst(32, original_width - 1), bm.CreateZeroConst(32));
    ASTNode rhs = NodeFactory::CreateTerm(
        BVEXTRACT, original_width, in2,
        bm.CreateBVConst(32, original_width - 1), bm.CreateZeroConst(32));

    return NodeFactory::CreateNode(EQ, lhs, rhs);
  }

  // Simplifiy (5 = 4/x) to FALSE.
  if (k1 == stp::BVCONST && k2 == stp::BVDIV &&
      in2[0].GetKind() == stp::BVCONST)
  {
    ASTNode maxV = bm.CreateMaxConst(width);
    if (CONSTANTBV::BitVector_Lexicompare(in1.GetBVConst(),
                                          maxV.GetBVConst()) != 0 &&
        CONSTANTBV::BitVector_Lexicompare(in1.GetBVConst(),
                                          in2[0].GetBVConst()) > 0)
    {
      return ASTFalse;
    }
  }

  if (k1 == BVNOT && k2 == BVUMINUS && in1[0] == in2[0])
    return ASTFalse;

  if (k1 == BVUMINUS && k2 == BVNOT && in1[0] == in2[0])
    return ASTFalse;

  // constant = constant + t  -->  (constant - constant) = t.
  if (k1 == stp::BVCONST && k2 == BVPLUS && in2.Degree() == 2 &&
      in2[0].GetKind() == stp::BVCONST)
  {
    ASTNode lhs = NodeFactory::CreateTerm(
        BVPLUS, width, NodeFactory::CreateTerm(BVUMINUS, width, in2[0]), in1);
    assert(lhs.isConstant());
    return NodeFactory::CreateNode(EQ, lhs, in2[1]);
  }

  // last resort is to CreateNode
  return hashing.CreateNode(EQ, children);
}

ASTNode SimplifyingNodeFactory::CreateSimpleEQConstConcat(
    const ASTNode& constant, const ASTNode& concat)
{
  auto splitConstant = [&](const ASTNode& c, const ASTNode& term,
                           ASTNode& low, ASTNode& high) {
    const unsigned lowWidth = term[1].GetValueWidth();
    const unsigned width = term.GetValueWidth();
    low = NodeFactory::CreateTerm(
        BVEXTRACT, lowWidth, c, bm.CreateBVConst(32, lowWidth - 1),
        bm.CreateZeroConst(32));
    high = NodeFactory::CreateTerm(
        BVEXTRACT, term[0].GetValueWidth(), c,
        bm.CreateBVConst(32, width - 1), bm.CreateBVConst(32, lowWidth));
  };

  // Most concat equalities split only once. Keep that case out of the
  // continuation machine so it does not construct a deque for two leaf
  // equalities.
  if (concat[0].GetKind() != BVCONCAT && concat[1].GetKind() != BVCONCAT)
  {
    ASTNode lowConstant, highConstant;
    splitConstant(constant, concat, lowConstant, highConstant);
    const ASTNode lowEquality =
        NodeFactory::CreateNode(EQ, concat[1], lowConstant);
    const ASTNode highEquality =
        NodeFactory::CreateNode(EQ, concat[0], highConstant);
    return NodeFactory::CreateNode(stp::AND, lowEquality, highEquality);
  }

  struct Frame
  {
    enum Phase
    {
      Start,
      LowDone,
      HighDone
    };

    ASTNode constant;
    ASTNode term;
    ASTNode lowConstant;
    ASTNode highConstant;
    ASTNode lowEquality;
    Phase phase = Start;

    Frame(const ASTNode& c, const ASTNode& t) : constant(c), term(t) {}
  };

  std::deque<Frame> stack;
  stack.emplace_back(constant, concat);
  ASTNode result;

  while (true)
  {
    Frame& frame = stack.back();
    if (frame.phase == Frame::Start)
    {
      if (frame.term.GetKind() != BVCONCAT)
      {
        result = NodeFactory::CreateNode(EQ, frame.term, frame.constant);
        stack.pop_back();
        if (stack.empty())
          return result;
        continue;
      }

      splitConstant(frame.constant, frame.term, frame.lowConstant,
                    frame.highConstant);

      frame.phase = Frame::LowDone;
      stack.emplace_back(frame.lowConstant, frame.term[1]);
      continue;
    }

    if (frame.phase == Frame::LowDone)
    {
      frame.lowEquality = result;
      frame.phase = Frame::HighDone;
      stack.emplace_back(frame.highConstant, frame.term[0]);
      continue;
    }

    result = NodeFactory::CreateNode(stp::AND, frame.lowEquality, result);
    stack.pop_back();
    if (stack.empty())
      return result;
  }
}

// Constant children are accumulated in "accumconst".
ASTNode SimplifyingNodeFactory::CreateSimpleXor(const ASTChildren children)
{
  if (debug_simplifyingNodeFactory)
  {
    cout << "========" << endl << "CreateSimpXor ";

    lpvec(toASTVec(children));
    cout << endl;
  }

  // a XOR (NOT a OR b) == (NOT a) OR (NOT b), for either operand order and
  // either position of (NOT a) in the OR. e.g.
  //   2180186:(XOR
  //     363814:var_5736
  //     (OR
  //       363815:(NOT 363814:var_5736)
  //       378221:(NOT 378220:var_8137)))
  if (children.size() == 2)
  {
    for (int i = 0; i < 2; i++)
    {
      const ASTNode& a = children[i];
      const ASTNode& other = children[1 - i];
      if (other.GetKind() == stp::OR && other.Degree() == 2)
      {
        for (int j = 0; j < 2; j++)
        {
          if (other[j].GetKind() == stp::NOT && other[j][0] == a)
            return CreateSimpleAndOr(0, other[j],
                                     CreateSimpleNot(other[1 - j]));
        }
      }
    }
  }

  ASTVec flat_children(children.begin(), children.end());

  // sort so that identical nodes occur in sequential runs, followed by
  // their negations.
  SortByExprNum(flat_children);

  // This is the C Boolean value of all constant args seen.  It is initially
  // 0.  TRUE children cause it to change value.
  bool accumconst = 0;

  ASTVec new_children;
  new_children.reserve(children.size());

  const ASTVec::const_iterator it_end = flat_children.end();
  ASTVec::iterator next_it;
  for (ASTVec::iterator it = flat_children.begin(); it != it_end; it++)
  {
    next_it = it + 1;
    bool nextexists = (next_it < it_end);

    if (ASTTrue == *it)
    {
      accumconst = !accumconst;
    }
    else if (ASTFalse == *it)
    {
      // Ignore it
    }
    else if (nextexists && (*next_it == *it))
    {
      // x XOR x = FALSE.  Skip current, write "false" into next_it
      // so that it gets tossed, too.
      *next_it = ASTFalse;
    }
    else if (nextexists && (next_it->GetKind() == stp::NOT) &&
             ((*next_it)[0] == *it))
    {
      // x XOR NOT x = TRUE.  Skip current, write "true" into next_it
      // so that it gets tossed, too.
      *next_it = ASTTrue;
    }
    else if (stp::NOT == it->GetKind())
    {
      // If child is (NOT alpha), we can flip accumconst and use alpha.
      // This is ok because (NOT alpha) == TRUE XOR alpha
      accumconst = !accumconst;
      // CreateSimpNot just takes child of not.
      new_children.push_back(CreateSimpleNot(*it));
    }
    else
    {
      new_children.push_back(*it);
    }
  }

  ASTNode retval;

  // Children should be non-constant.
  if (new_children.size() < 2)
  {
    if (0 == new_children.size())
    {
      // XOR(TRUE, FALSE) -- accumconst will be 1.
      if (accumconst)
      {
        retval = ASTTrue;
      }
      else
      {
        retval = ASTFalse;
      }
    }
    else
    {
      // there is just one child
      // XOR(x, TRUE) -- accumconst will be 1.
      if (accumconst)
      {
        retval = CreateSimpleNot(new_children[0]);
      }
      else
      {
        retval = new_children[0];
      }
    }
  }
  else
  {
    retval = hashing.CreateNode(stp::XOR, new_children);

    // negate the result if accumulated negation
    if (accumconst)
    {
      retval = CreateSimpleNot(retval);
    }
  }

  if (debug_simplifyingNodeFactory)
  {
    cout << "returns " << retval << endl;
  }
  return retval;
}

ASTNode SimplifyingNodeFactory::CreateSimpleFormITE(
    const ASTChildren children)
{
  const ASTNode& child0 = children[0];
  const ASTNode& child1 = children[1];
  const ASTNode& child2 = children[2];

  ASTNode retval;

  if (debug_simplifyingNodeFactory)
  {
    cout << "========" << endl
         << "CreateSimpleFormITE " << child0 << child1 << child2 << endl;
  }

  if (ASTTrue == child0)
  {
    retval = child1;
  }
  else if (ASTFalse == child0)
  {
    retval = child2;
  }
  else if (child1 == child2)
  {
    retval = child1;
  }
  // ITE(x, TRUE, y ) == x OR y
  else if (ASTTrue == child1)
  {
    retval = CreateSimpleAndOr(0, child0, child2);
  }
  // ITE(x, FALSE, y ) == (!x AND y)
  else if (ASTFalse == child1)
  {
    retval = CreateSimpleAndOr(1, CreateSimpleNot(child0), child2);
  }
  // ITE(x, y, TRUE ) == (!x OR y)
  else if (ASTTrue == child2)
  {
    retval = CreateSimpleAndOr(0, CreateSimpleNot(child0), child1);
  }
  // ITE(x, y, FALSE ) == (x AND y)
  else if (ASTFalse == child2)
  {
    retval = CreateSimpleAndOr(1, child0, child1);
  }
  else if (child0 == child1)
  {
    retval = CreateSimpleAndOr(0, child0, child2);
  }
  else if (child0 == child2)
  {
    retval = CreateSimpleAndOr(1, child0, child1);
  }
  else
  {
    retval = hashing.CreateNode(ITE, children);
  }

  if (debug_simplifyingNodeFactory)
  {
    cout << "returns " << retval << endl;
  }

  return retval;
}

// Move reads down through writes until, either we hit a write to an identical
// (syntactically) index,
// or we hit a write to an index that might be the same. This is intended to
// simplify things like:
// read(write(write(A,1,2),2,3),4) cheaply.
// The "children" that are passed should be the children of a READ.
ASTNode SimplifyingNodeFactory::chaseRead(const ASTChildren children,
                                          unsigned int width)
{
  assert(children[0].GetKind() == stp::WRITE);
  const ASTNode& readIndex = children[1];
  ASTNode write = children[0];

  const bool read_is_const = (stp::BVCONST == readIndex.GetKind());
  ASTVec c(2);

  while (write.GetKind() == stp::WRITE)
  {
    const ASTNode& write_index = write[1];

    if (readIndex == write_index)
    {
      // The are definately the same.
      // cerr << "-";
      return write[2];
    }
    else if (read_is_const && stp::BVCONST == write_index.GetKind() &&
             stp::constantsDenoteDifferentValues(readIndex, write_index))
    {
      // Different bits, so definately different. (Distinct constant
      // nodes alone prove nothing: a float constant interns apart from
      // the plain constant with its bits; skipping a write this read
      // hits reads the wrong cell.)
      // cerr << "+";
    }
    else
    {
      // They may be the same. Exit.
      // We've finished the cheap tests, now do the expensive one.
      // I don't know if the cost of this justifies the benefit.
      // cerr << "#";
      c[0] = write_index;
      c[1] = readIndex;
      ASTNode n = CreateSimpleEQ(c);
      if (n == ASTTrue)
      {
        // cerr << "#";
        return write[2];
      }
      else if (n == ASTFalse)
      {
        // cerr << "!";
      }
      else
      {
        // cerr << "."
        // Perhaps they are the same, perhaps not.
        break;
      }
    }
    write = write[0];
  }
  return hashing.CreateTerm(stp::READ, width, write, readIndex);
}

namespace
{
// The whole-array equality rules only fire over arrays whose cells and
// indexes are plain bitvectors. Floating-point cells are equal modulo the
// NaN quotient and rounding-mode cells only denote through the five one-hot
// patterns, so for those element sorts a bit-level read equality is not
// cell equality; non-bitvector index sorts additionally quotient their
// index patterns. All of that belongs to the extensionality lowering's
// witness machinery, which handles it explicitly.
bool isPlainBitvectorArray(const ASTNode& n)
{
  const stp::SourceSort sort = n.GetSourceSort();
  return sort.kind() == stp::SourceSort::Kind::Array &&
         sort.index().kind() == stp::SourceSort::Kind::BitVector &&
         sort.element().kind() == stp::SourceSort::Kind::BitVector;
}
}

// Structural rules for whole-array equality, applied where the equality
// has a complete quantifier-free meaning over the existing terms and the
// rewrite cannot grow the formula: no rule here creates reads or expands
// write chains. Everything else stays an opaque ARRAY_EQ for the
// extensionality lowering, whose witness abstraction is the general
// decision procedure -- in particular, eagerly reducing write chains to
// read equalities is a decision-procedure choice that belongs at the
// solve boundary, beside the machinery it would be trading against.
// Returns null when no rule applies.
// A write onto an array differs from that array exactly at the written
// index:
//   A = write(A, i, v)  <=>  select(A, i) = v
// Unconditional and O(1) like the rules below, but unlike them it removes
// the whole-array equality entirely -- so, like reflexivity, it runs
// whether or not --array-equality permits one to be built, and it covers
// float-element arrays (the value equality is then the float =).
ASTNode SimplifyingNodeFactory::selfStoreEquality(const ASTNode& a,
                                                  const ASTNode& b)
{
  for (int orientation = 0; orientation < 2; orientation++)
  {
    const ASTNode& w = orientation ? b : a;
    const ASTNode& base = orientation ? a : b;
    if (w.GetKind() != stp::WRITE || w[0] != base)
      continue;
    // Bitvector indexes only, and bitvector or float values: rounding-mode
    // cells and float indexes carry canonicalisation obligations the model
    // machinery meets on the whole-array path, not on a minted read.
    if (w[1].GetSourceSort().kind() != stp::SourceSort::Kind::BitVector)
      continue;
    const stp::SourceSort::Kind valueKind = w[2].GetSourceSort().kind();
    if (valueKind != stp::SourceSort::Kind::BitVector &&
        valueKind != stp::SourceSort::Kind::FloatingPoint)
      continue;
    const ASTNode read =
        NodeFactory::CreateTerm(stp::READ, w[2].GetValueWidth(), base, w[1]);
    const bool fp = valueKind == stp::SourceSort::Kind::FloatingPoint;
    return NodeFactory::CreateNode(fp ? stp::FP_SMT_EQ : stp::EQ, read,
                                   w[2]);
  }
  return ASTNode();
}

ASTNode SimplifyingNodeFactory::simplifyArrayEquality(const ASTNode& a,
                                                      const ASTNode& b)
{
  assert(a != b); // Callers fold reflexivity first.

  if (!isPlainBitvectorArray(a) || !isPlainBitvectorArray(b))
    return ASTNode();

  // Both sides overwrite the same index of the same array: off that
  // index both sides are that array, at it they hold the written
  // values, so the equality is exactly the values' equality.
  //   write(A,i,v) = write(A,i,w)  <=>  v = w
  // Chains sharing a longer prefix are the same shape: hash-consing
  // makes equal sub-chains one node, which appears here as A.
  if (a.GetKind() == stp::WRITE && b.GetKind() == stp::WRITE &&
      a[0] == b[0] && a[1] == b[1])
  {
    ASTVec values;
    values.push_back(a[2]);
    values.push_back(b[2]);
    return CreateSimpleEQ(values);
  }

  // An array ITE equated with one of its own branches: the matching arm
  // holds by reflexivity, leaving the choice of that arm or the other
  // branch's equality.
  //   ite(c,X,Y) = X  <=>  c OR (Y = X)
  //   ite(c,X,Y) = Y  <=>  (NOT c) OR (X = Y)
  for (int orientation = 0; orientation < 2; orientation++)
  {
    const ASTNode& iteNode = (orientation == 0) ? a : b;
    const ASTNode& other = (orientation == 0) ? b : a;
    if (iteNode.GetKind() != ITE)
      continue;
    const bool thenMatches = iteNode[1] == other;
    const bool elseMatches = iteNode[2] == other;
    if (!thenMatches && !elseMatches)
      continue;
    const ASTNode& residualBranch = thenMatches ? iteNode[2] : iteNode[1];
    if (residualBranch.GetSourceSort() != other.GetSourceSort())
      continue; // The hashing factory rejects mismatched-sort equalities.
    ASTVec disjuncts;
    disjuncts.push_back(thenMatches ? iteNode[0]
                                    : CreateSimpleNot(iteNode[0]));
    disjuncts.push_back(
        NodeFactory::CreateNode(ARRAY_EQ, residualBranch, other));
    return CreateSimpleAndOr(0, disjuncts);
  }

  return ASTNode();
}

// A remainder is what a division leaves behind: a == (a / b) * b + (a rem b)
// holds for every a and b, so a + (-b) * (a / b) *is* the remainder. It holds
// for the signed and the unsigned pair alike, and at every operand pair --
// including b = 0 and the most negative dividend -- because SMT-LIB's
// division and remainder are total and satisfy that identity everywhere.
//
// Producers that expand a remainder into a - (a / b) * b, as translation
// validation tools routinely do, otherwise hand the bit-blaster a division
// that nothing recognises as the remainder it is really computing, and it
// gets blasted as a second, independent divider.
//
// Returns the remainder if `a` and `product` have that shape, else null.
ASTNode SimplifyingNodeFactory::remainderFromDivision(const ASTNode& a,
                                                     const ASTNode& product)
{
  // The subtracted form BVSUB(a, b * (a / b)) reaches here as a plus of the
  // dividend and a negated product; otherwise the multiplier carries the
  // negation itself.
  const bool negated = (product.GetKind() == BVUMINUS);
  const ASTNode& mult = negated ? product[0] : product;

  if (mult.GetKind() != stp::BVMULT || mult.Degree() != 2)
    return ASTNode();

  const unsigned width = a.GetValueWidth();

  for (unsigned i = 0; i < 2; i++)
  {
    const ASTNode& quotient = mult[i];
    const ASTNode& multiplier = mult[1 - i];

    const Kind k = quotient.GetKind();
    if ((k != SBVDIV && k != stp::BVDIV) || quotient[0] != a)
      continue;

    const ASTNode& divisor = quotient[1];

    // Only now is it worth building the negated divisor to compare against.
    // Constants fold and a double negation cancels, so this single comparison
    // covers a constant multiplier, a BVUMINUS one, and an already negated
    // divisor alike.
    if (negated ? (multiplier != divisor)
                : (multiplier !=
                   NodeFactory::CreateTerm(BVUMINUS, width, divisor)))
      continue;

    return NodeFactory::CreateTerm(k == SBVDIV ? SBVREM : BVMOD, width, a,
                                   divisor);
  }

  return ASTNode();
}

// True if `n` could be the "- b * (a / b)" half of the pair above, using only
// checks that cost nothing, so that the search over a wide plus gives up
// immediately on almost every operand.
static bool mightBeDivisionProduct(const ASTNode& n)
{
  const ASTNode& mult = (n.GetKind() == BVUMINUS) ? n[0] : n;

  if (mult.GetKind() != stp::BVMULT || mult.Degree() != 2)
    return false;

  for (unsigned i = 0; i < 2; i++)
    if (mult[i].GetKind() == SBVDIV || mult[i].GetKind() == stp::BVDIV)
      return true;

  return false;
}

// One pass of the pairing over a sum's operands: every dividend and its
// product collapse to the remainder they compute, wherever the two sit.
// Returns true if anything folded, so the caller can run it again -- a fold
// can expose another, when the remainder it builds is itself the dividend of
// a product the sum already held.
bool SimplifyingNodeFactory::foldRemainders(ASTVec& children)
{
  std::vector<bool> paired(children.size(), false);
  ASTVec folded;

  for (size_t i = 0; i < children.size(); i++)
  {
    if (paired[i] || !mightBeDivisionProduct(children[i]))
      continue;

    for (size_t j = 0; j < children.size(); j++)
    {
      if (i == j || paired[j])
        continue;

      const ASTNode remainder = remainderFromDivision(children[j], children[i]);
      if (remainder.IsNull())
        continue;

      folded.push_back(remainder);
      paired[i] = true;
      paired[j] = true;
      break;
    }
  }

  if (folded.empty())
    return false;

  for (size_t i = 0; i < children.size(); i++)
    if (!paired[i])
      folded.push_back(children[i]);

  // Each fold takes two operands and gives back one, so a sum of more than
  // two operands keeps at least two.
  assert(folded.size() >= 2);
  children.swap(folded);
  return true;
}

// Push an extract down through the operators it can pass through, narrowing
// the slice as it goes: an extract of a concat reaches only one half, one of
// an extract composes into a single extract, one of a bvnot is the complement
// of the extract underneath, and one of a sign extension either lands inside
// the original term or is a run of copies of its sign bit.
//
// Each of those walks into a term that stays as deep as the input made it --
// nothing collapses a concat chain, or a sign extension over one -- so the
// walk is a loop here rather than a rebuild of the extract one level down
// with the factory taking the next step. Re-entering would spend a stack
// frame per level, and CreateTerm's frame is large enough that a few thousand
// of them exhaust the stack.
//
// Returns null if the extract reaches none of these, so the caller can go on
// to the rules that do not narrow it.
ASTNode SimplifyingNodeFactory::narrowExtract(unsigned width,
                                              ASTChildren children)
{
  ASTNode term = children[0];
  unsigned high = children[1].GetUnsignedConst();
  unsigned low = children[2].GetUnsignedConst();
  // Complements cancel in pairs, so only their parity has to be carried.
  bool complement = false;

  // The sign-extension rebase below moves the slice without changing the
  // term, so "did anything happen" has to watch the offsets too.
  const unsigned firstHigh = high;
  const unsigned firstLow = low;

  for (bool stepped = true; stepped;)
  {
    stepped = true;

    switch (term.GetKind())
    {
      case BVEXTRACT:
      {
        // Slicing a slice is one slice, taken from where the inner one began.
        const unsigned innerLow = term[2].GetUnsignedConst();
        high += innerLow;
        low += innerLow;
        term = term[0];
        break;
      }

      case BVCONCAT:
      {
        // The lower value holds the bottom bits, so it is what the offsets
        // are measured against. An extract that straddles the split needs
        // both halves and stops the walk.
        const unsigned lowerWidth = term[1].GetValueWidth();

        if (high < lowerWidth)
          term = term[1];
        else if (low >= lowerWidth)
        {
          term = term[0];
          high -= lowerWidth;
          low -= lowerWidth;
        }
        else
          stepped = false;
        break;
      }

      case stp::BVNOT:
        complement = !complement;
        term = term[0];
        break;

      case BVUMINUS:
        // Negating cannot change the bottom bit: it is the only one with no
        // borrow below it.
        if (high == 0 && low == 0)
          term = term[0];
        else
          stepped = false;
        break;

      case stp::BVSX:
      {
        const unsigned innerWidth = term[0].GetValueWidth();

        if (low >= innerWidth)
        {
          // Entirely within the extension: every extracted bit is a copy of
          // the sign bit, so rebase the extract to end at the sign bit.
          // Extracts of different slices of the extension then share a node.
          // The rebase leaves `low` at the sign bit, so it does not repeat.
          high = high - low + innerWidth - 1;
          low = innerWidth - 1;
        }
        else if (high < innerWidth)
          term = term[0]; // Entirely within the original term.
        else
          stepped = false;
        break;
      }

      default:
        stepped = false;
        break;
    }
  }

  if (term == children[0] && high == firstHigh && low == firstLow &&
      !complement)
    return ASTNode(); // Nothing here narrows it.

  const ASTNode slice =
      (low == 0 && width == term.GetValueWidth())
          ? term
          : NodeFactory::CreateTerm(BVEXTRACT, width, term,
                                    bm.CreateBVConst(32, high),
                                    bm.CreateBVConst(32, low));

  return complement ? NodeFactory::CreateTerm(stp::BVNOT, width, slice) : slice;
}

// This gets called with the arguments swapped as well. So the rules don't need
// to know about commutivity.
ASTNode SimplifyingNodeFactory::plusRules(const ASTNode& n0, const ASTNode& n1)
{
  ASTNode result;
  const int width = n0.GetValueWidth();

  // a + (-b) * (a / b) is the remainder a rem b. Tried ahead of the chain
  // below so that the negation-pulling rules at its end cannot claim the
  // pair first, and skipped again the moment the shape does not fit.
  if (mightBeDivisionProduct(n1))
    result = remainderFromDivision(n0, n1);

  if (result.IsNull() && n0.isConstant() &&
      CONSTANTBV::BitVector_is_empty(n0.GetBVConst()))
    result = n1;
  else if (width == 1 && n0 == n1)
    result = bm.CreateZeroConst(1);
  else if (n0 == n1)
    result = NodeFactory::CreateTerm(
        stp::BVMULT, width, bm.CreateBVConst(std::string("2"), 10, width), n0);
  else if (n0.GetKind() == BVUMINUS && n1 == n0[0])
    result = bm.CreateZeroConst(width);
  else if (n1.GetKind() == BVPLUS && n1[1].GetKind() == BVUMINUS &&
           n0 == n1[1][0] && n1.Degree() == 2)
    result = n1[0];
  else if (n1.GetKind() == BVPLUS && n1[0].GetKind() == BVUMINUS &&
           n0 == n1[0][0] && n1.Degree() == 2)
    result = n1[1];
  else if (n1.GetKind() == BVUMINUS && n0.GetKind() == BVPLUS &&
           n0.Degree() == 2 && n1[0] == n0[1])
    result = n0[0];
  else if (n1.GetKind() == BVUMINUS && n0.GetKind() == BVPLUS &&
           n0.Degree() == 2 && n1[0] == n0[0])
    result = n0[1];
  else if (n1.GetKind() == BVUMINUS && n1[0].GetKind() == BVPLUS &&
           n1[0].Degree() == 2 && (n1[0][0] == n0 || n1[0][1] == n0))
    // a + -(a + b) = -b. This is BVSUB(a, BVPLUS(a, b)) after the
    // subtraction has been rewritten to plus/uminus form.
    result = NodeFactory::CreateTerm(BVUMINUS, width,
                                     n1[0][(n1[0][0] == n0) ? 1 : 0]);
  else if (n1.GetKind() == BVNOT && n1[0] == n0)
    result = bm.CreateMaxConst(width);
  else if (n0.GetKind() == stp::BVCONST && n1.GetKind() == BVPLUS &&
           n1.Degree() == 2 && n1[0].GetKind() == stp::BVCONST)
  {
    ASTVec ch;
    ch.push_back(n0);
    ch.push_back(n1[0]);
    ASTNode constant = NonMemberBVConstEvaluator(&bm, BVPLUS, ch, width);
    result = NodeFactory::CreateTerm(BVPLUS, width, constant, n1[1]);
  }
// Disabled (kept for reference): guarded out of the build rather than left as
// `else if (false && ...)`, which trips -Wunreachable-code under -Werror.
#if 0
  else if (n1.GetKind() == BVUMINUS &&
           (n0.isConstant() && CONSTANTBV::BitVector_is_full(n0.GetBVConst())))
  {
    result = NodeFactory::CreateTerm(BVNOT, width, n1[0]);
  }
#endif
  else if (n1.GetKind() == BVUMINUS && n0.GetKind() == BVUMINUS)
  {
    ASTNode r = NodeFactory::CreateTerm(BVPLUS, width, n0[0], n1[0]);
    result = NodeFactory::CreateTerm(BVUMINUS, width, r);
  }

  return result;
}

ASTNode SimplifyingNodeFactory::handle_bvxor(
    unsigned int width, const ASTChildren input_children)
{
  // a ^ (a ^ b ^ ...) -> (b ^ ...): cancel an operand shared with a nested
  // xor. Children aren't flattened, so the duplicate-removal below can't see
  // this. Restricted to the binary case to keep the scan cheap.
  if (input_children.size() == 2)
  {
    for (int side = 0; side < 2; side++)
    {
      ASTNode inner = input_children[side];
      const ASTNode& other = input_children[1 - side];
      bool negated = false;
      if (inner.GetKind() == BVNOT)
      {
        negated = true;
        inner = inner[0];
      }
      if (inner.GetKind() != BVXOR)
        continue;
      for (unsigned i = 0; i < inner.Degree(); i++)
      {
        if (inner[i] != other)
          continue;
        ASTVec rest;
        rest.reserve(inner.Degree() - 1);
        for (unsigned j = 0; j < inner.Degree(); j++)
          if (j != i)
            rest.push_back(inner[j]);
        const ASTNode r =
            (rest.size() == 1) ? rest[0]
                               : NodeFactory::CreateTerm(BVXOR, width, rest);
        return negated ? NodeFactory::CreateTerm(BVNOT, width, r) : r;
      }
    }
  }

  bool accum = false;

  const ASTNode zero = bm.CreateZeroConst(width);

  ASTVec flat_children(input_children.begin(), input_children.end());

  // Expression numbers don't place BVNOT(t) next to (t), so strip BVNOTS first..
  for (size_t i = 0; i < flat_children.size();i++)
  {
  
    if (BVNOT == flat_children[i].GetKind())
    {
      accum = !accum;
      flat_children[i] = flat_children[i][0]; // remove the BVNOT
    }
  }

  // sort so that identical nodes occur in sequential runs
  SortByExprNum(flat_children);

  ASTVec new_children;
  new_children.reserve(flat_children.size());

  ASTNode accumulate= bm.CreateZeroConst(width);

  const ASTVec::iterator it_end = flat_children.end();
  ASTVec::iterator next_it;

  for (ASTVec::iterator it = flat_children.begin(); it != it_end; it++)
  {
    next_it = it + 1;
    bool nextexists = (next_it < it_end);

    if (it->isConstant())
    {
        accumulate= bm.CreateTerm(BVXOR, width, accumulate, *it);
    }
    else if (nextexists && (*next_it == *it))
    {
      // x XOR x = FALSE.  Skip current, write "false" into next_it
      // so that it gets tossed, too.
      *next_it = zero;
    } 
    else
    {
      new_children.push_back(*it);
    }
  }

  if (CONSTANTBV::BitVector_bit_test(accumulate.GetBVConst(),0))
  {
    // Aribtrarily we make constants even.
    accumulate= bm.CreateTerm(BVNOT, width, accumulate);
    accum = !accum;
  }

  if (!CONSTANTBV::BitVector_is_empty(accumulate.GetBVConst()))
  {
    new_children.push_back(accumulate);
  }

  ASTNode retval;

  if (0 == new_children.size())
  {
      retval = zero;
  }
  else if (new_children.size() ==1)
  {
      retval = new_children[0];
  }
  else 
  {
      retval = hashing.CreateTerm(BVXOR, width, new_children);
  }

  // negate the result if accumulated negation
  if (accum)
  {
      retval = NodeFactory::CreateTerm(BVNOT,width,retval);
  }

  return retval;
}




// The conjuncts a BVAND constrains, descending through nested BVANDs, since
// (a & (b & c)) constrains exactly a, b and c. A nested BVAND is recorded as
// a conjunct in its own right as well as being descended into: what gets
// negated may be the nested node rather than one of its leaves.
//
// Each conjunct is recorded the way the node numbering already pairs a node
// with its negation: uids step by two, and the odd slot above an operand's
// uid is where boolean NOT sits (see ASTInterior's constructor). BVNOT is
// not numbered that way, so it is recorded that way here instead -- x as its
// uid, ~x as uid(x)+1 -- and sorting brings a literal and its negation next
// to each other. Only boolean NOT nodes occupy odd uids, and none can be a
// BVAND conjunct, so recorded values collide only for equal conjuncts. That
// is the same shape as the adjacency test the duplicate removal below uses.
//
// The buffer is a fixed array rather than a set or a vector. This runs on
// every BVAND that has a BVAND child, 1.9M times over the hard QF_BV
// problems, to hold six conjuncts on average; at that size the allocation
// would cost more than everything else here put together.
//
// Bounded by how many conjuncts have been gathered, not by how deep the walk
// went, and the figure comes from measuring rather than guessing.
// Instrumenting this function over the 4661 hard problems: of those 1.9M
// walks, 65 found a complementary pair, and the shallowest depth at which
// that pair was reachable was
//
//   depth 1: 35   depth 2: 27   depth 3: 1   depth 7: 1   depth 8: 1
//
// So 95% are within two levels, but the tail runs to eight, while the
// nesting itself reaches sixty. A depth limit would have to be set at eight
// to lose nothing, and eight is not a number with any meaning -- it is just
// the deepest pair this corpus happens to contain. Bounding the conjuncts
// bounds the cost directly, and therefore also bounds the fixed traversal
// path below; sixty-four is comfortably past every pair seen.
//
// Stopping early costs a rewrite that does not fire, never a wrong answer.
static const size_t MAX_CONJUNCTS = 64;

static void collectConjuncts(const ASTNode& n, uint64_t* out, size_t& count)
{
  if (count >= MAX_CONJUNCTS)
    return;

  struct Frame
  {
    const ASTNode* node;
    size_t nextChild;
  };

  // A fixed path preserves the recursive depth-first, left-to-right order
  // without allocating on the 1.9M common shallow calls. Every descent first
  // records a conjunct, so count < MAX_CONJUNCTS also proves that the next
  // suspended-parent slot exists.
  Frame path[MAX_CONJUNCTS];
  size_t depth = 0;
  const ASTNode* current = &n;

  while (true)
  {
    out[count++] = (current->GetKind() == BVNOT)
                       ? (*current)[0].GetNodeNum() + 1
                       : current->GetNodeNum();
    if (count >= MAX_CONJUNCTS)
      return;

    if (current->GetKind() == stp::BVAND && current->Degree() != 0)
    {
      assert(depth < MAX_CONJUNCTS);
      path[depth++] = {current, 1};
      current = &(*current)[0];
      continue;
    }

    bool advanced = false;
    while (depth != 0)
    {
      Frame& parent = path[depth - 1];
      if (parent.nextChild < parent.node->Degree())
      {
        current = &(*parent.node)[parent.nextChild++];
        advanced = true;
        break;
      }
      --depth;
    }

    if (!advanced)
      return;
  }
}

ASTNode SimplifyingNodeFactory::handle_bvand(
    unsigned int width, const ASTChildren new_children)
{


  // x & ~x is zero however the two are nested: (~x & (x & y)) and
  // (x & (~x & ~y)) are both zero, and the scan below only ever compares
  // immediate children, so it sees neither. Only worth walking when a nested
  // BVAND is actually present -- and this can only ever return the
  // annihilator, so a node it does not fire on is left exactly as it was.
  {
    bool nested = false;
    for (size_t i = 0; i < new_children.size(); i++)
      if (new_children[i].GetKind() == stp::BVAND)
      {
        nested = true;
        break;
      }

    if (nested)
    {
      uint64_t conjuncts[MAX_CONJUNCTS];
      size_t count = 0;
      for (size_t i = 0; i < new_children.size(); i++)
        collectConjuncts(new_children[i], conjuncts, count);

      std::sort(conjuncts, conjuncts + count);

      // x is recorded as its even uid and ~x as the odd uid above it, so a
      // pair is two consecutive values with the even one first. Equal
      // neighbours are duplicates, not a pair.
      for (size_t i = 1; i < count; i++)
        if (conjuncts[i] == conjuncts[i - 1] + 1 &&
            (conjuncts[i - 1] & 1) == 0)
          return bm.CreateZeroConst(width);
    }
  }

  ASTVec flat_children(new_children.begin(), new_children.end());
  SortByExprNum(flat_children); // We want duplicates to be adjacent.

  const ASTNode annihilator = bm.CreateZeroConst(width);

  // x & (t << x) == 0 for any t: the shift clears the bits below position x,
  // while every set bit of x is below position x (x < 2^x). Only scan when a
  // left shift is actually present.
  for (size_t i = 0; i < flat_children.size(); i++)
  {
    if (flat_children[i].GetKind() != stp::BVLEFTSHIFT)
      continue;
    for (size_t j = 0; j < flat_children.size(); j++)
      if (j != i && flat_children[j] == flat_children[i][1])
        return annihilator;
  }
  const ASTNode identity = bm.CreateMaxConst(width);
  ASTNode accumulator = bm.CreateMaxConst(width);

  ASTVec children;
  children.reserve(flat_children.size());

  stp::ASTNodeSet found;

  for (ASTVec::const_iterator it = flat_children.begin(), it_end = flat_children.end(); it != it_end; it++)
  {
    ASTVec::const_iterator next_it;

    const bool nextexists = (it + 1 < it_end);
    if (nextexists)
      next_it = it + 1;
    else
      next_it = it_end;

    if (it->isConstant())
    {
      accumulator = NodeFactory::CreateTerm(stp::BVAND, width, *it, accumulator);
    }
    else if (nextexists && (*next_it == *it))
    {
      // just drop it
    }
    else if (it->GetKind()== stp::BVNOT && (found.find((*it)[0]) != found.end()))
    {
       return annihilator;
    }
    else
    {
       found.insert(*it);
       children.push_back(*it);
    }
  }

  if (accumulator == identity)
  {
    // discard
  } 
  else  if (accumulator == annihilator)
  {
    return annihilator;
  } 
  else
  {
       children.push_back(accumulator);
  }

  // If we get here, we saw no annihilators, and children should
  // be only the non-True nodes.
  switch(children.size()) {
    case 0:
      return identity;
      break;

    case 1:
      return children[0];
      break;
  }


  // ites with the same condition, where one pair of merged branches folds to a
  // constant.
  if (children.size() ==2 && children[0].GetKind() == stp::ITE && children[1].GetKind() == stp::ITE && children[0][0] == children[1][0])
  {
    const ASTNode thenBranch = NodeFactory::CreateTerm(stp::BVAND, width, children[0][1], children[1][1]);
    const ASTNode elseBranch = NodeFactory::CreateTerm(stp::BVAND, width, children[0][2], children[1][2]);
    if (thenBranch.isConstant() || elseBranch.isConstant())
    {
      return NodeFactory::CreateTerm(stp::ITE, width, children[0][0], thenBranch, elseBranch);
    }
  }


  // If there is just one run of 1 bits, replace by an extract and a concat.
  // i.e. 00011111111000000 & x , will be replaced by an extract of x just
  // where
  // there are one bits.
  // Disabled (kept for reference): guarded out of the build rather than left as
  // `if (false && ...)`, which trips -Wunreachable-code under -Werror.
#if 0
  if (children.size() == 2 &&
      (children[0].isConstant() || children[1].isConstant()))
  {
    ASTNode c0 = children[0];
    ASTNode c1 = children[1];
    if (c1.isConstant())
    {
      ASTNode t = c0;
      c0 = c1;
      c1 = t;
    }

    int start = -1;
    int end = -1;
    stp::CBV c = c0.GetBVConst();
    bool bad = false;
    for (int i = 0; i < (int)width; i++)
    {
      if (CONSTANTBV::BitVector_bit_test(c, i))
      {
        if (start == -1)
          start = i; // first one bit.
        else if (end != -1)
          bad = true;
      }

      if (!CONSTANTBV::BitVector_bit_test(c, i))
      {
        if (start != -1 && end == -1)
          end = i - 1; // end of run.
      }
    }
    if (start != -1 && end == -1)
      end = (int)width - 1;

    if (!bad && start != -1)
    {
      assert(end != -1);

      ASTNode result = NodeFactory::CreateTerm(BVEXTRACT, end - start + 1, c1,
                                       bm.CreateBVConst(32, end),
                                       bm.CreateBVConst(32, start));

      if (start > 0)
      {
        ASTNode z = bm.CreateZeroConst(start);
        result = NodeFactory::CreateTerm(BVCONCAT, end + 1, result, z);
      }
      if (end < (int)width - 1)
      {
        ASTNode z = bm.CreateZeroConst((int)width - end - 1);
        result =  NodeFactory::CreateTerm(BVCONCAT, width, z, result);
      }
      return result;
    }
  }
#endif

  if (children.size() ==2 && children[1].GetKind() == stp::BVAND && children[0] == children[1][0])
  {
    return children[1];
  }

  //(bvand (bvnot |w|) (bvnot (bvand |v| |w|)))) )  
  // -> (bvnot |w|)
  if (children.size() ==2 && 
      children[0].GetKind() == stp::BVNOT && 
      children[1].GetKind() == stp::BVNOT && 
      children[1][0].GetKind() == stp::BVAND &&
      children[1][0].Degree() ==2 &&
      children[1][0][1] == children[0][0] 
    )
  {
    return children[0];
  }

  return hashing.CreateTerm(stp::BVAND,width,children);
}

ASTNode SimplifyingNodeFactory::plusRules(const ASTChildren oldChildren)
{
  assert(oldChildren.size() > 2);
  const unsigned width = oldChildren[0].GetValueWidth();

  // A dividend and its "- b * (a / b)" partner fold back into the remainder
  // they compute, wherever in the sum the two happen to sit.
  //
  // Every pair is taken here, by looping the pass, rather than by rebuilding
  // the sum around one fold and re-entering the factory to find the next:
  // that costs a stack frame per pair, and a sum wide enough -- which is what
  // flattening a long chain of these produces -- overflows the stack. The
  // scan is skipped altogether unless some operand is a product of a
  // division, which almost no sum has.
  bool anyProduct = false;
  for (size_t i = 0; i < oldChildren.size() && !anyProduct; i++)
    anyProduct = mightBeDivisionProduct(oldChildren[i]);

  if (anyProduct)
  {
    ASTVec remaining(oldChildren.begin(), oldChildren.end());

    if (foldRemainders(remaining))
    {
      while (foldRemainders(remaining))
        ;

      return CreateTerm(BVPLUS, width, remaining);
    }
  }

  ASTNode accumulate= bm.CreateZeroConst(width);

  stp::ASTNodeMultiSet bvnot, bvneg, other;

  int constantsFound = 0;
  
  // create multi-sets of relevant kinds.
  for (const auto & n : oldChildren)
  {
      if (n.GetKind() == BVNOT)
        bvnot.insert(n);
      else if (n.GetKind() == BVUMINUS)
        bvneg.insert(n);
      else if (n.GetKind() == stp::BVCONST)
        {
          accumulate = NodeFactory::CreateTerm(BVPLUS, width, accumulate, n);
          constantsFound++;
        }
      else
        other.insert(n);
  }

  bool changed = (constantsFound > 1);

  // negation cancels out.
  for (const auto& n : bvneg)
  {
    if (other.find(n[0]) != other.end())
      {
        other.erase(other.find(n[0]));
        changed = true;
      }
    else
      other.insert(n); 
  }

  // "not" reduces to -1.
  for (const auto& n : bvnot)
  {
    if (other.find(n[0]) != other.end())
    {
      other.erase(other.find(n[0]));
      accumulate = NodeFactory::CreateTerm(BVPLUS, width, accumulate, bm.CreateMaxConst(width));
      changed = true;
    }  
    else
      other.insert(n);   
  }

  // If a zero constant was initially present, it has changed.
  if (constantsFound > 0 && CONSTANTBV::BitVector_is_empty(accumulate.GetBVConst()))
    changed = true;

  if (!changed)
    return hashing.CreateTerm(BVPLUS, width, oldChildren); 

  if (!CONSTANTBV::BitVector_is_empty(accumulate.GetBVConst()))
     other.insert(accumulate);

  ASTVec newChildren(other.begin(), other.end());

  ASTNode result;
  if (newChildren.size() >2)
    result = hashing.CreateTerm(BVPLUS, width, newChildren);
  else if (newChildren.size() ==2)
    result = CreateTerm(BVPLUS, width, newChildren); // has been modified. Call more comprehensive.
  else if (newChildren.size() ==1)
    result = newChildren[0];
  else if (newChildren.size() ==0)
    result = bm.CreateZeroConst(width);

  return result;
}

ASTNode SimplifyingNodeFactory::multRules(const ASTChildren oldChildren)
{
  assert(oldChildren.size() > 2);
  const unsigned width = oldChildren[0].GetValueWidth();

  ASTNode accumulate = bm.CreateOneConst(width);

  stp::ASTNodeMultiSet other;

  int constantsFound = 0;
  unsigned negations = 0;

  for (const auto& n : oldChildren)
  {
    ASTNode m = n;
    if (m.GetKind() == BVUMINUS)
    {
      // Negations commute out of a product; track the parity and put a
      // single one back on top, the canonical form the binary rules make.
      negations++;
      m = m[0];
    }
    if (m.GetKind() == stp::BVCONST)
    {
      accumulate = NodeFactory::CreateTerm(stp::BVMULT, width, accumulate, m);
      constantsFound++;
    }
    else
      other.insert(m);
  }

  // Zero absorbs the whole product.
  if (constantsFound > 0 &&
      CONSTANTBV::BitVector_is_empty(accumulate.GetBVConst()))
    return bm.CreateZeroConst(width);

  // A max constant is -1: fold it into the negation parity.
  if (constantsFound > 0 && !other.empty() &&
      CONSTANTBV::BitVector_is_full(accumulate.GetBVConst()))
  {
    accumulate = bm.CreateOneConst(width);
    negations++;
  }

  const bool accumulateIsOne = (accumulate == bm.CreateOneConst(width));

  bool changed = (constantsFound > 1) || (negations > 0);

  // If a one constant was initially present, it is dropped.
  if (constantsFound > 0 && accumulateIsOne)
    changed = true;

  if (!changed)
    return hashing.CreateTerm(stp::BVMULT, width, oldChildren);

  if (!accumulateIsOne)
    other.insert(accumulate);

  ASTVec newChildren(other.begin(), other.end());

  ASTNode result;
  if (newChildren.size() > 2)
    result = hashing.CreateTerm(stp::BVMULT, width, newChildren);
  else if (newChildren.size() == 2)
    result = CreateTerm(stp::BVMULT, width,
                        newChildren); // has been modified. Call more
                                      // comprehensive.
  else if (newChildren.size() == 1)
    result = newChildren[0];
  else
    result = accumulate; // everything folded into the constant.

  if ((negations & 1) != 0)
    result = CreateTerm(BVUMINUS, width, result);

  return result;
}

// If the shift is bigger than the bitwidth, replace by an extract.
ASTNode convertArithmeticKnownShiftAmount([[maybe_unused]] const Kind k,
                                          const ASTChildren children,
                                          STPMgr& bm, NodeFactory* nf)
{
  const ASTNode a = children[0];
  const ASTNode b = children[1];
  const unsigned width = children[0].GetValueWidth();
  ASTNode output;

  assert(b.isConstant());
  assert(k == BVSRSHIFT);

  if (CONSTANTBV::Set_Max(b.GetBVConst()) > 1 + std::log2(width))
  {
    ASTNode top = bm.CreateBVConst(32, width - 1);
    return nf->CreateTerm(stp::BVSX, width,
                          nf->CreateTerm(stp::BVEXTRACT, 1, children[0], top, top),
                          bm.CreateBVConst(32, width));
  }
  else
  {
    if (b.GetUnsignedConst() >= width)
    {
      ASTNode top = bm.CreateBVConst(32, width - 1);
      return nf->CreateTerm(stp::BVSX, width,
                            nf->CreateTerm(BVEXTRACT, 1, children[0], top, top),
                            bm.CreateBVConst(32, width));
    }
    else
    {
      ASTNode top = bm.CreateBVConst(32, width - 1);
      ASTNode bottom = bm.CreateBVConst(32, b.GetUnsignedConst());

      return nf->CreateTerm(stp::BVSX, width,
                            nf->CreateTerm(stp::BVEXTRACT,
                                           width - b.GetUnsignedConst(),
                                           children[0], top, bottom),
                            bm.CreateBVConst(32, width));
    }
  }

  return ASTNode();
}

// If the rhs of a left or right shift is known.
ASTNode SimplifyingNodeFactory::convertKnownShiftAmount(const Kind k,
                                                        ASTChildren children,
                                                        STPMgr& bm,
                                                        NodeFactory* nf)
{
  const ASTNode a = children[0];
  const ASTNode b = children[1];
  const unsigned width = children[0].GetValueWidth();
  ASTNode output;

  assert(b.isConstant());
  assert(stp::BVLEFTSHIFT== k || BVRIGHTSHIFT == k);

  if (CONSTANTBV::Set_Max(b.GetBVConst()) > 1 + std::log2(width))
  {
    // Intended to remove shifts by very large amounts
    // that don't fit into the unsigned.  at thhe start
    // of the "else" branch.
    output = bm.CreateZeroConst(width);
  }
  else
  {
    const unsigned int shift = b.GetUnsignedConst();
    if (shift >= width)
    {
      output = bm.CreateZeroConst(width);
    }
    else if (shift == 0)
    {
      output = a; // unchanged.
    }
    else
    {
      if (stp::BVLEFTSHIFT == k)
      {
        ASTNode zero = bm.CreateZeroConst(shift);
        ASTNode hi = bm.CreateBVConst(32, width - shift - 1);
        ASTNode low = bm.CreateBVConst(32, 0);
        ASTNode extract = nf->CreateTerm(BVEXTRACT, width - shift, a, hi, low);
        BVTypeCheck(extract);
        output = nf->CreateTerm(BVCONCAT, width, extract, zero);
        BVTypeCheck(output);
      }
      else 
      {
        assert(k == BVRIGHTSHIFT);
        ASTNode zero = bm.CreateZeroConst(shift);
        ASTNode hi = bm.CreateBVConst(32, width - 1);
        ASTNode low = bm.CreateBVConst(32, shift);
        ASTNode extract = nf->CreateTerm(BVEXTRACT, width - shift, a, hi, low);
        BVTypeCheck(extract);
        output = nf->CreateTerm(BVCONCAT, width, zero, extract);
        BVTypeCheck(output);
      }
    }
  }
  return output;
}

ASTNode SimplifyingNodeFactory::CreateTerm(Kind kind, unsigned int width,
                                           const ASTChildren children)
{
  if (!is_Term_kind(kind))
    FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined, kind);

  assert(kind != stp::BVCONST);
  // These are created specially.
  assert(kind != stp::SYMBOL);
  // so are these.

  assert(bm.hashingNodeFactory == &hashing);

  // The partial floating-point operations cannot be constant-folded here:
  // their unspecified cases (fp.min/fp.max on opposite zeros, out-of-range
  // fp.to_ubv/fp.to_sbv) only get an answer when FpTotalise adds its
  // never-constant unspecified-value child, and lowering requires that
  // totalised arity. Every other floating-point term folds through the
  // constant evaluator's FP arm, which re-interns the result with its
  // format via the CreateFPConst funnel -- so both literal spellings,
  // ((_ to_fp e s) bits) and (fp s e m), intern to the same ASTFPConst,
  // and constant arithmetic collapses at creation.
  const bool is_partial_fp_operation =
      kind == stp::FP_MIN || kind == stp::FP_MAX || kind == stp::FP_TO_UBV ||
      kind == stp::FP_TO_SBV;

  if (kind == stp::UF_APPLY)
    return hashing.CreateTerm(kind, width, children);

  // If all the parameters are constant, return the constant value.
  if (children_all_constants(children) && !is_partial_fp_operation)
  {
    const ASTNode& hash = hashing.CreateTerm(kind, width, children);
    const ASTNode& c = NonMemberBVConstEvaluator(&bm, hash);
    assert(c.isConstant());
    return c;
  }

  ASTNode result;
  switch (kind)
  {
    case stp::BVZX:
    {
      if (width - children[0].GetValueWidth() > 0)
      {
        ASTNode zero = bm.CreateZeroConst(width - children[0].GetValueWidth());
        result = NodeFactory::CreateTerm(BVCONCAT, width, zero, children[0]);
      }
      else if (width == children[0].GetValueWidth())
      {
        result = children[0];
      }
      else
      {
        FatalError("Negative zero extend", children[0]);
      }
      break;
    }

    case ITE:
    {
      if (children[0] == ASTTrue)
        result = children[1];
      else if (children[0] == ASTFalse)
        result = children[2];
      else if (children[1] == children[2])
        result = children[1];
      else if (children[2].GetKind() == ITE && (children[2][0] == children[0]))
      {
        if (stp::ARRAY_TYPE == children[2].GetType())
          result = NodeFactory::CreateArrayTerm(
              ITE, children[2].GetIndexWidth(), children[2].GetValueWidth(),
              children[0], children[1], children[2][2]);
        else
          result = NodeFactory::CreateTerm(ITE, width, children[0], children[1],
                                           children[2][2]);
      }
      else if (children[1].GetKind() == ITE && (children[1][0] == children[0]))
      {
        if (stp::ARRAY_TYPE == children[1].GetType())
          result = NodeFactory::CreateArrayTerm(
              ITE, children[1].GetIndexWidth(), children[1].GetValueWidth(),
              children[0], children[1][1], children[2]);
        else
          result = NodeFactory::CreateTerm(ITE, width, children[0],
                                           children[1][1], children[2]);
      }
      else if (children[0].GetKind() == stp::NOT)
      {
        if (stp::ARRAY_TYPE == children[1].GetType())
          result = NodeFactory::CreateArrayTerm(
              ITE, children[1].GetIndexWidth(), children[1].GetValueWidth(),
              children[0][0], children[2], children[1]);
        else
          result = NodeFactory::CreateTerm(ITE, width, children[0][0],
                                           children[2], children[1]);
      }
      else if (children[0].GetKind() == EQ && children[0][1] == children[1] &&
               children[0][0].GetKind() == stp::BVCONST &&
               children[0][1].GetKind() != stp::BVCONST)
        result = NodeFactory::CreateTerm(ITE, width, children[0],
                                         children[0][0], children[2]);
      else if (children[0].GetKind() == EQ && children[0][0] == children[1] &&
               children[0][1].GetKind() == stp::BVCONST &&
               children[0][0].GetKind() != stp::BVCONST)
        result = NodeFactory::CreateTerm(ITE, width, children[0],
                                         children[0][1], children[2]);
      else if (width == 1 && children[0].GetKind() == EQ &&
               children[0][0].GetValueWidth() == 1 &&
               children[1].isConstant() && children[2].isConstant() &&
               children[1] != children[2])
      {
        // A 1-bit ITE choosing between 0 and 1 on a 1-bit equality is the
        // tested term or its complement, e.g. ITE(t = 1, 1, 0) --> t.
        ASTNode t;
        bool condOne = false;
        if (children[0][0].isConstant())
        {
          t = children[0][1];
          condOne = (children[0][0] == bm.CreateOneConst(1));
        }
        else if (children[0][1].isConstant())
        {
          t = children[0][0];
          condOne = (children[0][1] == bm.CreateOneConst(1));
        }
        if (!t.IsNull())
        {
          const bool thenOne = (children[1] == bm.CreateOneConst(1));
          result = (thenOne == condOne) ? t
                                        : NodeFactory::CreateTerm(BVNOT, 1, t);
        }
      }
      break;
    }

    case stp::BVMULT:
    {
      if (children.size() == 2)
      {
        if (children[0].isConstant() &&
            CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
          result = bm.CreateZeroConst(width);

        else if (children[1].isConstant() &&
                 CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
          result = bm.CreateZeroConst(width);

        else if (children[1].isConstant() &&
                 children[1] == bm.CreateOneConst(width))
          result = children[0];

        else if (children[0].isConstant() &&
                 children[0] == bm.CreateOneConst(width))
          result = children[1];

        else if (children[0].isConstant() &&
                 CONSTANTBV::BitVector_is_full(children[0].GetBVConst()))
          result = NodeFactory::CreateTerm(BVUMINUS, width, children[1]);

        else if (width == 1 && children[0] == children[1])
          result = children[0];

        else if (children[0].GetKind() == BVUMINUS &&
                 children[1].GetKind() == BVUMINUS)
          result = NodeFactory::CreateTerm(stp::BVMULT, width, children[0][0],
                                           children[1][0]);
        else if (children[0].GetKind() == BVUMINUS)
        {
          result = NodeFactory::CreateTerm(stp::BVMULT, width, children[0][0],
                                           children[1]);
          result = NodeFactory::CreateTerm(BVUMINUS, width, result);
        }
        else if (children[1].GetKind() == BVUMINUS)
        {
          result = NodeFactory::CreateTerm(stp::BVMULT, width, children[1][0],
                                           children[0]);
          result = NodeFactory::CreateTerm(BVUMINUS, width, result);
        }
        // (t * (u << s)) == ((t * u) << s), for either operand order. A
        // constant shift amount is already lowered to a concat, so this only
        // fires for variable shift amounts.
        else if (children[1].GetKind() == stp::BVLEFTSHIFT)
        {
          result = NodeFactory::CreateTerm(
              stp::BVLEFTSHIFT, width,
              NodeFactory::CreateTerm(stp::BVMULT, width, children[0],
                                      children[1][0]),
              children[1][1]);
        }
        else if (children[0].GetKind() == stp::BVLEFTSHIFT)
        {
          result = NodeFactory::CreateTerm(
              stp::BVLEFTSHIFT, width,
              NodeFactory::CreateTerm(stp::BVMULT, width, children[1],
                                      children[0][0]),
              children[0][1]);
        }
        else
        {
          // (2^p * (k ++ y)) is a left shift by p; when p is the width of k,
          // the shift pushes k out entirely: the result is (y ++ 0^p). e.g.
          //   5254:(BVMULT
          //     1970:0x0100
          //     5242:(BVCONCAT
          //       1402:0x00
          //       1296:T1@2147))
          for (int i = 0; i < 2; i++)
          {
            const ASTNode& constant = children[i];
            const ASTNode& other = children[1 - i];
            if (constant.GetKind() == stp::BVCONST &&
                hasSingleOneBit(constant) && other.GetKind() == BVCONCAT &&
                other[0].GetKind() == stp::BVCONST &&
                lowestOneBit(constant) == other[0].GetValueWidth())
            {
              result = NodeFactory::CreateTerm(
                  BVCONCAT, width, other[1],
                  bm.CreateZeroConst(other[0].GetValueWidth()));
              break;
            }
          }
        }
      }
      else if (children.size() > 2)
      {
        result = multRules(children);
      }
    }
    break;

    case stp::BVLEFTSHIFT:
    {
      if (children[0].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant())
        result = convertKnownShiftAmount(kind, children, bm,
                                                          &hashing);
      else if (width == 1 && children[0] == children[1])
        result = bm.CreateZeroConst(1);
      else if (children[0].GetKind() == BVUMINUS)
        result = NodeFactory::CreateTerm(
            BVUMINUS, width,
            NodeFactory::CreateTerm(stp::BVLEFTSHIFT, width, children[0][0],
                                    children[1]));
      else if (children[0].isConstant() &&
               CONSTANTBV::BitVector_bit_test(children[0].GetBVConst(),
                                              width - 1) &&
               children[0] != get_smallest_number(width))
      {
        // Normalise a negative constant base to positive:
        // (c << s) == -((-c) << s). Excludes the most negative constant,
        // whose negation is itself.
        result = NodeFactory::CreateTerm(
            BVUMINUS, width,
            NodeFactory::CreateTerm(
                stp::BVLEFTSHIFT, width,
                NodeFactory::CreateTerm(BVUMINUS, width, children[0]),
                children[1]));
      }
      else if (children[0].GetKind() == stp::BVSX &&
               children[0][0].GetKind() == BVEXTRACT &&
               children[0][0][0] == children[1] &&
               children[0][0][1] == bm.CreateBVConst(32, width - 1) &&
               children[0][0][2] == bm.CreateBVConst(32, width - 1))
      {
        // (sx(x[msb:msb]) << x) == 0: the base is 0 or ones, and a base of
        // ones means x's top bit is set, so x >= 2^(w-1) >= w and the shift
        // clears everything either way. This is (x ashr x) << x, after the
        // arithmetic shift has been rewritten to the sign-spread form.
        result = bm.CreateZeroConst(width);
      }
    }
    break;

    case BVRIGHTSHIFT:
    {
      if (children[0] == children[1])
        result = bm.CreateZeroConst(width);
      if (children[0].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant())
        result = convertKnownShiftAmount(kind, children, bm,
                                                          &hashing);
      else if (children[0].isConstant() &&
               children[0] == bm.CreateOneConst(width))
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)),
            children[0], bm.CreateZeroConst(width));
      else if (width >= 3 && children[0].GetKind() == BVNOT &&
               children[1] == children[0][0])
        result = NodeFactory::CreateTerm(BVRIGHTSHIFT, width,
                                         bm.CreateMaxConst(width),
                                         children[0][0]); // 320 -> 170
      else if (width >= 3 && children[1].GetKind() == BVNOT &&
               children[1][0] == children[0])
        result = NodeFactory::CreateTerm(BVRIGHTSHIFT, width,
                                         bm.CreateMaxConst(width),
                                         children[1]); // 320 -> 170
      else if (width >= 3 && children[0].GetKind() == BVNOT &&
               children[1].GetKind() == BVUMINUS &&
               children[1][0] == children[0][0])
        result = NodeFactory::CreateTerm(
            BVUMINUS, width,
            NodeFactory::CreateTerm(
                ITE, width, NodeFactory::CreateNode(
                                EQ, bm.CreateZeroConst(width), children[0][0]),
                bm.CreateOneConst(width),
                bm.CreateZeroConst(width))); // 391 -> 70

      if (result.IsNull())
      {
        // (t >> s) == 0 when t <=u s is structurally guaranteed: t <=u s
        // implies t <u 2^s, so every bit of t is shifted out. Generalises
        // the t == s rule above. t <=u s holds when t is an AND containing
        // s, or t umod-by/ushifts-down s. It also holds for (s ashr u):
        // a non-negative s bounds its own arithmetic shift, and a negative
        // s is at least 2^(w-1) >= w as a shift amount.
        const ASTNode& t = children[0];
        const ASTNode& s = children[1];
        bool zero = false;
        if (t.GetKind() == stp::BVAND)
        {
          for (const ASTNode& c : t)
            if (c == s)
              zero = true;
        }
        else if ((t.GetKind() == BVMOD || t.GetKind() == BVRIGHTSHIFT ||
                  t.GetKind() == BVSRSHIFT) &&
                 t[0] == s)
        {
          zero = true;
        }

        // (t >> (t | rest)) == 0: the shift amount is at least t. The OR
        // arrives as ~(~t & ...), so look for ~t among the AND's operands.
        if (!zero && s.GetKind() == BVNOT && s[0].GetKind() == stp::BVAND)
        {
          for (const ASTNode& c : s[0])
            if (c.GetKind() == BVNOT && c[0] == t)
              zero = true;
        }

        if (zero)
          result = bm.CreateZeroConst(width);
      }
    }
    break;

    case stp::BVSRSHIFT:
    {
      if (children[0].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (width > 1 && children[0].isConstant() &&
               children[0] == bm.CreateOneConst(width))
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)),
            children[0], bm.CreateZeroConst(width));
      else if (children[0].isConstant() &&
               CONSTANTBV::BitVector_is_full(children[0].GetBVConst()))
        result = bm.CreateMaxConst(width);
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        result = children[0];
      else if (width == 1 && children[0] == children[1])
        result = children[0];
      else if ((children[0] == children[1]) ||
               (children[0].GetKind() == BVUMINUS &&
                children[0][0] == children[1]))
      {
        assert(width > 1);
        ASTNode extract = NodeFactory::CreateTerm(
            BVEXTRACT, 1, children[0], bm.CreateBVConst(32, width - 1),
            bm.CreateBVConst(32, width - 1));
        result = NodeFactory::CreateTerm(stp::BVSX, width, extract,
                                         bm.CreateBVConst(32, width));
      }
      else if (width == 1 && children[1].isConstant() &&
               children[1] == bm.CreateOneConst(1))
        result = children[0];
      else if (children[1].isConstant())
        result = convertArithmeticKnownShiftAmount(
            kind, children, bm, &hashing);
      else if (children[1].GetKind() == BVUMINUS &&
               children[0] == children[1][0])
        result = NodeFactory::CreateTerm(stp::BVSRSHIFT, width, children[0],
                                         children[1][0]);
      else if (children[0].isConstant() &&
               !CONSTANTBV::BitVector_bit_test(children[0].GetBVConst(),
                                               width - 1))
        result = NodeFactory::CreateTerm(BVRIGHTSHIFT, width, children[0],
                                         children[1]);
      else if (width >= 3 && children[0].GetKind() == BVNOT &&
               children[1].GetKind() == BVUMINUS &&
               children[1][0] == children[0][0])
        result = NodeFactory::CreateTerm(BVSRSHIFT, width, children[0],
                                         children[0][0]); // 414 -> 361
      else if (children[0].GetKind() == BVNOT)
        result = NodeFactory::CreateTerm(
            BVNOT, width, NodeFactory::CreateTerm(BVSRSHIFT, width,
                                                  children[0][0], children[1]));
    }
    break;

    case stp::BVSUB:
      if (children.size() == 2)
      {
        if (children.size() == 2 && children[0] == children[1])
        {
          result = bm.CreateZeroConst(width);
        }
        else if (children.size() == 2 &&
                 children[1] == bm.CreateZeroConst(width))
        {
          result = children[0];
        }
        else
        {
          result = NodeFactory::CreateTerm(
              BVPLUS, width, children[0],
              NodeFactory::CreateTerm(BVUMINUS, width, children[1]));
        }
      }
      break;

    case stp::BVOR:
    {

     ASTVec new_children;
     new_children.reserve(children.size());
     for (size_t i = 0; i < children.size(); i++)
     {
         new_children.push_back(NodeFactory::CreateTerm(BVNOT, width, children[i]));
     }
     result = NodeFactory::CreateTerm(BVNOT, width, NodeFactory::CreateTerm(stp::BVAND,width,new_children));

    }
    break;

    case stp::BVXOR:
    {
      result = handle_bvxor(width, children);
      break;
    }

    case stp::BVAND:
    {
      result = handle_bvand(width, children);
      break;
    }

    case stp::BVSX:
    {
      if (width == children[0].GetValueWidth())
      {
        result = children[0];
      }
      // BVSX(m, BVSX(n, a)) --> BVSX(m, a): the inner sign-extension is
      // subsumed by the outer one.
      else if (children[0].GetKind() == stp::BVSX)
      {
        result = NodeFactory::CreateTerm(stp::BVSX, width, children[0][0],
                                         children[1]);
      }
      break;
    }

    case BVNOT:
      if (children[0].GetKind() == BVNOT)
        result = children[0][0];
      if (children[0].GetKind() == BVPLUS && children[0].Degree() == 2 &&
          children[0][0].GetKind() == stp::BVCONST &&
          children[0][0] == bm.CreateMaxConst(width))
        result = NodeFactory::CreateTerm(BVUMINUS, width, children[0][1]);
      if (children[0].GetKind() == BVUMINUS)
        result = NodeFactory::CreateTerm(BVPLUS, width, children[0][0],
                                         bm.CreateMaxConst(width));
      if (children[0].GetKind() == BVMOD && children[0][0].GetKind() == BVNOT &&
          children[0][1].GetKind() == BVUMINUS &&
          children[0][1][0] == children[0][0][0])
        result = children[0][0][0];

      break;

    case BVUMINUS:
      if (children[0].GetKind() == BVUMINUS)
        result = children[0][0];
      else if (width == 1)
        result = children[0];
      else if (children[0].GetKind() == BVPLUS && children[0].Degree() == 2 &&
               children[0][0].GetKind() == stp::BVCONST &&
               children[0][0] == bm.CreateOneConst(width))
        result = NodeFactory::CreateTerm(BVNOT, width, children[0][1]);
      else if (children[0].GetKind() == BVNOT)
        result = NodeFactory::CreateTerm(BVPLUS, width, children[0][0],
                                         bm.CreateOneConst(width));
      else if (children[0].GetKind() == stp::BVSX &&
               children[0][0].GetValueWidth() == 1)
        result = NodeFactory::CreateTerm(
            BVCONCAT, width, bm.CreateZeroConst(width - 1), children[0][0]);
      else if (children[0].GetKind() == BVMULT && children[0].Degree() == 2 &&
               children[0][0] == bm.CreateMaxConst(width))
        result = children[0][1];
      else if (children[0].GetKind() == stp::BVAND && children[0].Degree() == 2)
      {
        // -(x & -x) == x | -x. (The dual -(x | -x) == x & -x never fires:
        // BVOR is lowered to ~(~x & ~y) at creation, so no BVOR node survives
        // as a BVUMINUS child.)
        const ASTNode& inner = children[0];
        if (inner[1].GetKind() == BVUMINUS && inner[1][0] == inner[0])
          result =
              NodeFactory::CreateTerm(stp::BVOR, width, inner[0], inner[1]);
        else if (inner[0].GetKind() == BVUMINUS && inner[0][0] == inner[1])
          result =
              NodeFactory::CreateTerm(stp::BVOR, width, inner[1], inner[0]);
      }
      break;

    case BVEXTRACT:
      if (width == children[0].GetValueWidth())
        result = children[0];
      else if (ASTNode narrowed = narrowExtract(width, children); !narrowed.IsNull())
        result = narrowed;
      else if (stp::BVMULT == children[0].GetKind() &&
               children[0].Degree() == 2 &&
               (children[0][0].GetKind() == stp::BVCONST ||
                children[0][1].GetKind() == stp::BVCONST))
      {
        // A multiplication by 2^p is a left shift by p; push the extract
        // through it, over a concat with p zeroes.
        const bool constFirst = children[0][0].GetKind() == stp::BVCONST;
        const ASTNode& constant = constFirst ? children[0][0] : children[0][1];
        const ASTNode& other = constFirst ? children[0][1] : children[0][0];
        if (hasSingleOneBit(constant) && lowestOneBit(constant) > 0)
        {
          const unsigned position = lowestOneBit(constant);
          const ASTNode concat = NodeFactory::CreateTerm(
              BVCONCAT, children[0].GetValueWidth() + position, other,
              bm.CreateZeroConst(position));
          result = NodeFactory::CreateTerm(BVEXTRACT, width, concat,
                                           children[1], children[2]);
        }
      }
      break;

    case BVCONCAT:
      // (x[i:j] ++ x[j-1:k]) --> x[i:k]: merge adjacent extracts of the
      // same term.
      if (children[0].GetKind() == BVEXTRACT &&
          children[1].GetKind() == BVEXTRACT &&
          children[0][0] == children[1][0] &&
          children[0][2].GetUnsignedConst() ==
              children[1][1].GetUnsignedConst() + 1)
      {
        result = NodeFactory::CreateTerm(BVEXTRACT, width, children[0][0],
                                         children[0][1], children[1][2]);
      }
      // ((x ++ k1) ++ k2) --> (x ++ (k1 ++ k2)): merge adjacent constants.
      else if (children[0].GetKind() == BVCONCAT &&
          children[1].GetKind() == stp::BVCONST &&
          children[0][1].GetKind() == stp::BVCONST)
      {
        const ASTNode constants = NodeFactory::CreateTerm(
            BVCONCAT,
            children[0][1].GetValueWidth() + children[1].GetValueWidth(),
            children[0][1], children[1]);
        result =
            NodeFactory::CreateTerm(BVCONCAT, width, children[0][0], constants);
      }
      // (k0 ++ (k1 ++ y)) --> ((k0 ++ k1) ++ y): merge adjacent constants.
      else if (children[1].GetKind() == BVCONCAT &&
               children[0].GetKind() == stp::BVCONST &&
               children[1][0].GetKind() == stp::BVCONST)
      {
        const ASTNode constants = NodeFactory::CreateTerm(
            BVCONCAT,
            children[0].GetValueWidth() + children[1][0].GetValueWidth(),
            children[0], children[1][0]);
        result =
            NodeFactory::CreateTerm(BVCONCAT, width, constants, children[1][1]);
      }
      // (t ++ t) with 1-bit t is t sign-extended: the top bit repeats.
      else if (children[0] == children[1] && children[0].GetValueWidth() == 1)
      {
        result = NodeFactory::CreateTerm(stp::BVSX, width, children[0],
                                         bm.CreateBVConst(32, width));
      }
      // (t ++ BVSX(t)) with 1-bit t is one more repetition of t.
      else if (children[0].GetValueWidth() == 1 &&
               children[1].GetKind() == stp::BVSX &&
               children[1][0] == children[0])
      {
        result = NodeFactory::CreateTerm(stp::BVSX, width, children[0],
                                         bm.CreateBVConst(32, width));
      }
      // (BVSX(t) ++ t) with 1-bit t likewise.
      else if (children[1].GetValueWidth() == 1 &&
               children[0].GetKind() == stp::BVSX &&
               children[0][0] == children[1])
      {
        result = NodeFactory::CreateTerm(stp::BVSX, width, children[1],
                                         bm.CreateBVConst(32, width));
      }
      break;

    case BVPLUS:
      if (1 == width)
        result = handle_bvxor(width, children);
      else if (children.size() == 2)
      {
        result = plusRules(children[0], children[1]);
        if (result.IsNull())
          result = plusRules(children[1], children[0]);
      }
     else
          result = plusRules(children);
      break;

    case SBVMOD:
    {
      const ASTNode max = bm.CreateMaxConst(width);

      if (children[1].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        result = children[0];
      else if (children[0] == children[1])
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant() &&
               children[1] == bm.CreateOneConst(width))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant() &&
               children[1] == bm.CreateMaxConst(width))
        result = bm.CreateZeroConst(width);
      else if (children[0].isConstant() &&
               children[0] == bm.CreateZeroConst(width))
        result = bm.CreateZeroConst(width);
      else if (children[0].GetKind() == BVUMINUS &&
               children[0][0] == children[1])
        result = bm.CreateZeroConst(width);
      else if (children[1].GetKind() == BVUMINUS &&
               children[1][0] == children[0])
        result = bm.CreateZeroConst(width);
      else if (children[0].GetKind() == BVNOT && children[1] == children[0][0])
        result = NodeFactory::CreateTerm(SBVMOD, width, max,
                                         children[0][0]); // 9759 -> 542
      else if (children[1].GetKind() == BVNOT && children[1][0] == children[0])
        result = NodeFactory::CreateTerm(SBVMOD, width, max,
                                         children[1]); // 9759 -> 542
      else if (children[0].GetKind() == BVNOT &&
               children[1].GetKind() == BVUMINUS &&
               children[1][0] == children[0][0])
        result = NodeFactory::CreateTerm(SBVMOD, width, max,
                                         children[1]); // 9807 -> 674
      else if (children[1].isConstant() && hasSingleOneBit(children[1]) &&
               lowestOneBit(children[1]) > 0 &&
               lowestOneBit(children[1]) + 1 < width)
      {
        // (bvsmod x 2^n) --> (0^(width-n) ++ x[n-1:0]), for 2^n POSITIVE, i.e.
        // n in [1, width-2] so the divisor's top bit is clear. For a positive
        // modulus SMT-LIB's bvsmod is the mathematical modulo, whose value in
        // [0, 2^n) equals the low n bits of x regardless of x's sign (two's
        // complement preserves value mod 2^n). When n == width-1 the constant
        // 2^n is NEGATIVE, so this rule must not fire and is excluded by the
        // lowestOneBit + 1 < width guard.
        const unsigned n = lowestOneBit(children[1]);
        result = NodeFactory::CreateTerm(
            BVCONCAT, width, bm.CreateZeroConst(width - n),
            NodeFactory::CreateTerm(BVEXTRACT, n, children[0],
                                    bm.CreateBVConst(32, n - 1),
                                    bm.CreateBVConst(32, 0)));
      }
    }

    break;

    case stp::BVDIV:
      if (children[0].GetKind() == BVMOD && children[0][1] == children[1])
      {
        // (x umod y) / y is zero: a remainder is smaller than the divisor it
        // was taken against, so it cannot contain it once. Only y = 0 escapes,
        // where the remainder is x and the total quotient is all ones.
        // Checked before the rules below because the power-of-two divisor is
        // rewritten to an extract, after which nothing sees the remainder.
        if (children[1].isConstant())
          result = CONSTANTBV::BitVector_is_empty(children[1].GetBVConst())
                       ? bm.CreateMaxConst(width)
                       : bm.CreateZeroConst(width);
        else
          result = NodeFactory::CreateTerm(
              ITE, width,
              NodeFactory::CreateNode(EQ, children[1],
                                      bm.CreateZeroConst(width)),
              bm.CreateMaxConst(width), bm.CreateZeroConst(width));
      }
      else if (children[1].isConstant() &&
               children[1] == bm.CreateOneConst(width))
        result = children[0];
      else if (children[1].isConstant() && hasSingleOneBit(children[1]) &&
               lowestOneBit(children[1]) > 0)
      {
        // (x / 2^n) --> (0^n ++ x[width-1:n]): a division by a power of
        // two just discards the low bits.
        const unsigned n = lowestOneBit(children[1]);
        result = NodeFactory::CreateTerm(
            BVCONCAT, width, bm.CreateZeroConst(n),
            NodeFactory::CreateTerm(BVEXTRACT, width - n, children[0],
                                    bm.CreateBVConst(32, width - 1),
                                    bm.CreateBVConst(32, n)));
      }
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_bit_test(children[1].GetBVConst(),
                                              width - 1))
      {
        // We are dividing by something that has a one in the MSB. It's either 1
        // or zero.
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(stp::BVGE, children[0], children[1]),
            bm.CreateOneConst(width), bm.CreateZeroConst(width));
      }
      else if (children[1].isConstant() &&
               children[1] == bm.CreateZeroConst(width))
        result = bm.CreateMaxConst(width);
      else if (children[0].isConstant() &&
               CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)),
            bm.CreateMaxConst(width), bm.CreateZeroConst(width));
      else if (children[0] == children[1])
        // x / x is 1, except at 0 where the SMT-LIB quotient is all ones.
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)),
            bm.CreateMaxConst(width), bm.CreateOneConst(width));

      // ((s & t) mod t) / s  and  (t & (s mod t)) / s  both equal
      // ite(s = 0, max, ite((s & t) = s AND s < t, 1, 0)):
      // each numerator is at most s, so the quotient is 0 or 1, and it is 1
      // exactly when the numerator equals a non-zero s, which for both forms
      // requires s's bits to be a subset of t's and s < t. Replaces a
      // division and a modulus with comparisons.
      if (result.IsNull())
      {
        const ASTNode& s = children[1];
        ASTNode t;
        const ASTNode& n = children[0];
        if (n.GetKind() == BVMOD && n[0].GetKind() == stp::BVAND &&
            n[0].Degree() == 2 &&
            ((n[0][0] == s && n[0][1] == n[1]) ||
             (n[0][1] == s && n[0][0] == n[1])))
        {
          // ((s & t) mod t) / s
          t = n[1];
        }
        else if (n.GetKind() == stp::BVAND && n.Degree() == 2)
        {
          // (t & (s mod t)) / s, with the BVAND's children in either order.
          for (unsigned i = 0; i < 2; i++)
            if (n[i].GetKind() == BVMOD && n[i][0] == s && n[i][1] == n[1 - i])
            {
              t = n[1 - i];
              break;
            }
        }
        if (!t.IsNull())
        {
          const ASTNode subsumes = NodeFactory::CreateNode(
              EQ, NodeFactory::CreateTerm(stp::BVAND, width, s, t), s);
          const ASTNode smaller = NodeFactory::CreateNode(stp::BVLT, s, t);
          const ASTNode cond =
              NodeFactory::CreateNode(stp::AND, subsumes, smaller);
          const ASTNode sIsZero =
              NodeFactory::CreateNode(EQ, s, bm.CreateZeroConst(width));
          const ASTNode oneOrZero = NodeFactory::CreateTerm(
              ITE, width, cond, bm.CreateOneConst(width),
              bm.CreateZeroConst(width));
          result =
              NodeFactory::CreateTerm(ITE, width, sIsZero,
                                      bm.CreateMaxConst(width), oneOrZero);
        }
      }

      break;

    case SBVDIV:
      // NOTE: no power-of-two rewrite here. Signed division rounds toward zero,
      // so (bvsdiv x 2^n) is NOT a plain arithmetic shift right (that would
      // round toward -inf for negative x); it needs a sign correction. Left for
      // the bit-blaster.
      if ((children[0].GetKind() == SBVREM || children[0].GetKind() == SBVMOD) &&
          children[0][1] == children[1])
      {
        // (x srem y) / y and (x smod y) / y are both zero: either remainder is
        // smaller in magnitude than the divisor it was taken against. Only
        // y = 0 escapes, where both remainders are x and the total quotient is
        // one for a negative x and all ones otherwise.
        if (children[1].isConstant() &&
            !CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
          result = bm.CreateZeroConst(width);
        else
        {
          const ASTNode byZero = NodeFactory::CreateTerm(
              ITE, width,
              NodeFactory::CreateNode(stp::BVSLT, children[0][0],
                                      bm.CreateZeroConst(width)),
              bm.CreateOneConst(width), bm.CreateMaxConst(width));

          result = children[1].isConstant()
                       ? byZero
                       : NodeFactory::CreateTerm(
                             ITE, width,
                             NodeFactory::CreateNode(
                                 EQ, children[1], bm.CreateZeroConst(width)),
                             byZero, bm.CreateZeroConst(width));
        }
      }
      else if (children[1].isConstant() &&
               children[1] == bm.CreateOneConst(width))
        result = children[0];
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
        result = NodeFactory::CreateTerm(BVUMINUS, width, children[0]);
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        // x / 0 is 1 for negative x, otherwise all ones.
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(stp::BVSLT, children[0],
                                    bm.CreateZeroConst(width)),
            bm.CreateOneConst(width), bm.CreateMaxConst(width));
      else if (children[0].isConstant() &&
               CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        // 0 / y is 0, except at y = 0 where the quotient is all ones.
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)),
            bm.CreateMaxConst(width), bm.CreateZeroConst(width));
      else if (children[0].isConstant() &&
               CONSTANTBV::BitVector_bit_test(children[0].GetBVConst(),
                                              width - 1) &&
               children[0] != get_smallest_number(width))
        // Truncating division commutes with negation, so normalise a
        // negative constant dividend to positive: c / y == -(-c / y).
        // Excludes the most negative constant, whose negation is itself.
        result = NodeFactory::CreateTerm(
            BVUMINUS, width,
            NodeFactory::CreateTerm(
                SBVDIV, width,
                NodeFactory::CreateTerm(BVUMINUS, width, children[0]),
                children[1]));
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_bit_test(children[1].GetBVConst(),
                                              width - 1) &&
               children[1] != get_smallest_number(width))
        // Likewise for a negative constant divisor: x / c == -(x / -c).
        result = NodeFactory::CreateTerm(
            BVUMINUS, width,
            NodeFactory::CreateTerm(
                SBVDIV, width, children[0],
                NodeFactory::CreateTerm(BVUMINUS, width, children[1])));
      else if (children[0] == children[1])
        // x / x is 1 wherever the division is a real one. The remaining case
        // is 0 / 0, which takes the total-division value the rule above
        // gives: zero is not negative, so all ones. SBVMOD already has the
        // matching x smod x rule; this one was missing, and without it
        // nothing downstream can tell that the quotient is never zero.
        result = NodeFactory::CreateTerm(
            ITE, width,
            NodeFactory::CreateNode(EQ, children[0],
                                    bm.CreateZeroConst(width)),
            bm.CreateMaxConst(width), bm.CreateOneConst(width));
      break;

    case SBVREM:
    {
      // NOTE: no power-of-two rewrite here. The signed remainder takes the sign
      // of the dividend, so (bvsrem x 2^n) is NOT simply the low n bits of x
      // (that is the unsigned/positive-modulus result); it needs a sign
      // correction. Left for the bit-blaster.
      const ASTNode one = bm.CreateOneConst(width);

      if (children[0] == children[1])
        result = bm.CreateZeroConst(width);
      else if (children[0].isConstant() &&
               CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        result = children[0];
      else if (children[1].isConstant() &&
               bm.CreateOneConst(width) == children[1])
        result = bm.CreateZeroConst(width);
      else if (children[1].GetKind() == BVUMINUS)
        result =
            NodeFactory::CreateTerm(SBVREM, width, children[0], children[1][0]);
      else if (children[0].GetKind() == BVUMINUS &&
               children[0][0] == children[1])
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant() &&
               CONSTANTBV::BitVector_bit_test(children[1].GetBVConst(),
                                              width - 1) &&
               children[1] != get_smallest_number(width))
        // The remainder takes the dividend's sign, so a negative constant
        // divisor can be normalised to positive: x rem c == x rem -c.
        // Excludes the most negative constant, whose negation is itself.
        result = NodeFactory::CreateTerm(
            SBVREM, width, children[0],
            NodeFactory::CreateTerm(BVUMINUS, width, children[1]));
      else if (children[0].isConstant() &&
               CONSTANTBV::BitVector_bit_test(children[0].GetBVConst(),
                                              width - 1) &&
               children[0] != get_smallest_number(width))
        // Truncating remainder commutes with negating the dividend:
        // c rem y == -(-c rem y).
        result = NodeFactory::CreateTerm(
            BVUMINUS, width,
            NodeFactory::CreateTerm(
                SBVREM, width,
                NodeFactory::CreateTerm(BVUMINUS, width, children[0]),
                children[1]));
      else if (children[0].GetKind() == BVNOT && children[1] == children[0][0])
        result = NodeFactory::CreateTerm(
            BVUMINUS, width,
            NodeFactory::CreateTerm(SBVMOD, width, one,
                                    children[0][0])); // 9350 -> 624
      else if (children[1].GetKind() == BVNOT && children[1][0] == children[0])
        result = NodeFactory::CreateTerm(
            BVUMINUS, width,
            NodeFactory::CreateTerm(SBVMOD, width, one,
                                    children[1])); // 9350 -> 624
      // ((bvuminus x) srem -1) is subsumed by the srem-by-all-ones rule above.
    }

    break;

    case BVMOD:
    {
      if (children[0] == children[1])
        result = bm.CreateZeroConst(width);

      if (children[0].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);

      if (children[1].isConstant() &&
          CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        result = children[0];

      if (children[0].GetKind() == BVPLUS && children[0].Degree() == 2 &&
          children[0][0] == bm.CreateMaxConst(width) &&
          children[1] == children[0][1])
        result = children[0];

      const ASTNode one = bm.CreateOneConst(width);

      if (children[0].GetKind() == BVNOT && children[1].GetKind() == BVUMINUS &&
          children[1][0] == children[0][0])
        result = children[0];

      if (children[1].isConstant() && children[1] == one)
        result = bm.CreateZeroConst(width);

      if (children[1].isConstant() && hasSingleOneBit(children[1]) &&
          lowestOneBit(children[1]) > 0)
      {
        // (x mod 2^n) --> (0^(width-n) ++ x[n-1:0]): a remainder by a
        // power of two just keeps the low bits.
        const unsigned n = lowestOneBit(children[1]);
        result = NodeFactory::CreateTerm(
            BVCONCAT, width, bm.CreateZeroConst(width - n),
            NodeFactory::CreateTerm(BVEXTRACT, n, children[0],
                                    bm.CreateBVConst(32, n - 1),
                                    bm.CreateBVConst(32, 0)));
      }

      if (children[0].isConstant() && children[0] == one)
        result = NodeFactory::CreateTerm(
            ITE, width, NodeFactory::CreateNode(EQ, children[1], one),
            bm.CreateZeroConst(width), one);
      if (children[0].GetKind() == BVNOT && children[1] == children[0][0])
        result = NodeFactory::CreateTerm(BVMOD, width, bm.CreateMaxConst(width),
                                         children[0][0]); // 3285 -> 3113

      if (children[1].GetKind() == BVNOT && children[1][0] == children[0])
        result = NodeFactory::CreateTerm(BVMOD, width, bm.CreateMaxConst(width),
                                         children[1]); // 3285 -> 3113

      if (children[0].GetKind() == BVUMINUS &&
          children[1].GetKind() == BVNOT &&
          children[1][0] == children[0][0])
        result = NodeFactory::CreateTerm(SBVREM, width, one,
                                         children[1]); // 8883 -> 206
    }

    break;

    case stp::WRITE:
      if (children[0].GetKind() == stp::WRITE && children[1] == children[0][1])
      {
        // If the indexes of two writes are the same, then discard the inner
        // write.
        result = NodeFactory::CreateArrayTerm(
            stp::WRITE, children[0].GetIndexWidth(),
            children[0].GetValueWidth(), children[0][0], children[1],
            children[2]);
      }
      else if (children[2].GetKind() == stp::READ &&
               children[0] == children[2][0] && children[1] == children[2][1])
      {
        // Its writing into the array what's already there. i.e.  a[i] = a[i]
        result = children[0];
      }
      break;

    case stp::READ:
      if (children[0].GetKind() == stp::WRITE)
      {
        result = chaseRead(children, width);
      }
      break;

    // ----- Cheap floating-point rewrites, applied before bit-blasting. -----
    // See the matching block in CreateNode.

    // min(x, x) = max(x, x) = x. A NaN operand is ignored -- fp.min/fp.max
    // return the other operand -- and the matching order extreme absorbs:
    // min(x, -oo) = -oo and max(x, +oo) = +oo for every x, NaN included.
    // All three are sound for either of the totalising pass's zero choices:
    // the choice only matters when the operands are the two opposite zeros,
    // which an equal, NaN or infinite operand precludes. The two float
    // operands are children 0 and 1; the choice child, if the pass has
    // already appended one, is irrelevant to these.
    case stp::FP_MIN:
    case stp::FP_MAX:
      if (children.size() >= 2)
      {
        if (children[0] == children[1])
          result = children[0];
        for (unsigned k = 0; result.IsNull() && k <= 1; k++)
        {
          if (fpConstIsNaN(children[k]))
            result = children[1 - k];
          else if (fpConstInfSign(children[k]) ==
                   (kind == stp::FP_MIN ? -1 : 1))
            result = children[k];
        }
      }
      break;

    // abs(abs x) = abs(neg x) = abs x. On a constant, fold at construction --
    // the cheap floating-point cases (unlike the arithmetic, which the
    // constant evaluator folds by bit-blasting -- and would recurse through
    // here) are pure sign-bit edits, so do them directly and keep the format.
    // abs clears the sign; neg flips it. Both leave a NaN's payload alone,
    // matching IEEE fp.abs/fp.neg (and SMT-LIB, where NaN is a single value).
    case stp::FP_ABS:
      if (children[0].GetKind() == stp::FP_ABS ||
          children[0].GetKind() == stp::FP_NEG)
        result = NodeFactory::CreateTerm(stp::FP_ABS, width, children[0][0]);
      else if (children[0].GetKind() == stp::BVCONST)
        result = foldFPSign(children[0], /*flip=*/false);
      // abs(t * t) = t * t: a self-product is never negative, and -0 (the
      // one nonnegative value abs does change) cannot arise from it.
      else if (fpIsSelfProduct(children[0]))
        result = children[0];
      break;

    // Rounding an already-integral value -- and roundToIntegral yields
    // nothing else: an integral, a zero, an infinity or NaN -- is exact
    // under EVERY mode, so a second roundToIntegral is dropped whatever its
    // own rounding mode.
    case stp::FP_ROUNDTOINTEGRAL:
      if (children.size() == 2 &&
          children[1].GetKind() == stp::FP_ROUNDTOINTEGRAL)
        result = children[1];
      break;

    // neg(neg x) = x.
    case stp::FP_NEG:
      if (children[0].GetKind() == stp::FP_NEG)
        result = children[0][0];
      else if (children[0].GetKind() == stp::BVCONST)
        result = foldFPSign(children[0], /*flip=*/true);
      break;

    // fp.sub(rm, x, y) = fp.add(rm, x, fp.neg y). IEEE-754 defines subtraction
    // as addition of the negation -- exact for every rounding mode and for
    // signed zeros -- so lower it and reuse the add machinery (its constant
    // folding, its commutative ordering, one adder to blast rather than two).
    case stp::FP_SUB:
      if (children.size() == 3)
        result = NodeFactory::CreateTerm(
            stp::FP_ADD, width, children[0], children[1],
            NodeFactory::CreateTerm(stp::FP_NEG, width, children[2]));
      break;

    // fp.add: a NaN operand absorbs -- NaN + x is NaN for every x and mode --
    // and a signed-zero operand whose addition is exact for the literal
    // rounding mode is dropped: x + (-0) = x under every mode except
    // round-toward-negative, x + (+0) = x only there. Otherwise fp.add is
    // commutative in its two float operands (child 0 is the rounding mode):
    // order them so x + y and y + x share a node.
    case stp::FP_ADD:
      if (children.size() == 3)
      {
        for (unsigned k = 1; result.IsNull() && k <= 2; k++)
        {
          if (fpConstIsNaN(children[k]))
            result = children[k];
          else if (fpZeroIsAdditiveIdentity(fpConstZeroSign(children[k]),
                                            fpConstRoundingMode(children[0])))
            result = children[3 - k];
        }
        if (result.IsNull() &&
            children[1].GetNodeNum() > children[2].GetNodeNum())
        {
          ASTVec reordered;
          reordered.push_back(children[0]);
          reordered.push_back(children[2]);
          reordered.push_back(children[1]);
          result = hashing.CreateTerm(stp::FP_ADD, width, reordered);
        }
      }
      break;

    // fp.mul is commutative, and has two exact identity operands: x * 1.0 = x
    // and x * -1.0 = -x, for every value and every rounding mode. 1.0 is the
    // multiplicative identity and -1.0 its negation, so the product is exactly
    // x or -x and no rounding happens (NaN, the infinities and the signed zeros
    // all carry through). A NaN operand absorbs the whole product. Either
    // float operand (child 1 or 2) may be the constant; child 0 is the
    // rounding mode.
    case stp::FP_MUL:
      if (children.size() == 3)
      {
        for (unsigned k = 1; result.IsNull() && k <= 2; k++)
        {
          if (fpConstIsNaN(children[k]))
          {
            result = children[k];
            continue;
          }
          const int pm = fpConstPlusMinusOne(children[k]);
          if (pm == 1)
            result = children[3 - k];
          else if (pm == -1)
            result =
                NodeFactory::CreateTerm(stp::FP_NEG, width, children[3 - k]);
        }
        // Otherwise order the operands so x * y and y * x share a node.
        if (result.IsNull() &&
            children[1].GetNodeNum() > children[2].GetNodeNum())
        {
          ASTVec reordered;
          reordered.push_back(children[0]);
          reordered.push_back(children[2]);
          reordered.push_back(children[1]);
          result = hashing.CreateTerm(stp::FP_MUL, width, reordered);
        }
      }
      break;

    // fp.div: a NaN operand absorbs, and the exact divisors fold -- x / 1.0
    // = x and x / -1.0 = -x for every value and mode. Only the divisor
    // (child 2) has identities: 1.0 / x is not x, so the dividend is
    // otherwise left alone.
    case stp::FP_DIV:
      if (children.size() == 3)
      {
        if (fpConstIsNaN(children[1]))
          result = children[1];
        else if (fpConstIsNaN(children[2]))
          result = children[2];
        else if (fpConstPlusMinusOne(children[2]) == 1)
          result = children[1];
        else if (fpConstPlusMinusOne(children[2]) == -1)
          result = NodeFactory::CreateTerm(stp::FP_NEG, width, children[1]);
      }
      break;

    // fp.fma(rm, x, y, z) computes round(x*y + z), rounding once. A NaN in
    // any float operand absorbs. When the product x*y is exact the single
    // rounding is the addition's, so the fma IS an fp.add of the product:
    // a multiplicand of +-1.0 gives round(+-y + z), and two constant
    // multiplicands with a zero among them give either the invalid 0 * oo
    // (NaN) or the xor-signed zero. The created fp.add re-simplifies, so
    // its own NaN and signed-zero rules finish the job. Otherwise the two
    // multiplicands (children 1 and 2) are symmetric: order them, keeping
    // the rounding mode (child 0) and the addend (child 3) in place.
    case stp::FP_FMA:
      if (children.size() == 4)
      {
        for (unsigned k = 1; result.IsNull() && k <= 3; k++)
          if (fpConstIsNaN(children[k]))
            result = children[k];

        for (unsigned k = 1; result.IsNull() && k <= 2; k++)
        {
          const ASTNode& other = children[3 - k];
          const int pm = fpConstPlusMinusOne(children[k]);
          const int zs = fpConstZeroSign(children[k]);
          if (pm != 0)
            result = NodeFactory::CreateTerm(
                stp::FP_ADD, width, children[0],
                pm == 1 ? other
                        : NodeFactory::CreateTerm(stp::FP_NEG, width, other),
                children[3]);
          else if (zs != 0 && fpFormattedConst(other))
          {
            if (fpConstInfSign(other) != 0)
              result = makeFPNaN(children[k].GetExpWidth(),
                                 children[k].GetSigWidth());
            else
              result = NodeFactory::CreateTerm(
                  stp::FP_ADD, width, children[0],
                  makeFPZero(children[k].GetExpWidth(),
                             children[k].GetSigWidth(),
                             (zs < 0) != (fpConstSign(other) < 0)),
                  children[3]);
          }
        }

        if (result.IsNull() &&
            children[1].GetNodeNum() > children[2].GetNodeNum())
        {
          ASTVec reordered;
          reordered.push_back(children[0]);
          reordered.push_back(children[2]);
          reordered.push_back(children[1]);
          reordered.push_back(children[3]);
          result = hashing.CreateTerm(stp::FP_FMA, width, reordered);
        }
      }
      break;

    // fp.rem(a, b) is exact, so several structural identities hold. Applied
    // one per construction; the recursive calls re-simplify, so nested cases
    // compose. Child 0 is the dividend a, child 1 the divisor b -- there is
    // no rounding mode.
    case stp::FP_REM:
      if (children.size() == 2)
      {
        // rem(rem(a, b), b) = rem(a, b): a second remainder by the same
        // divisor is a no-op.
        if (children[0].GetKind() == stp::FP_REM &&
            children[0][1] == children[1])
          result = children[0];
        // rem(a, -b) = rem(a, |b|) = rem(a, b): the divisor's sign is
        // irrelevant.
        else if (children[1].GetKind() == stp::FP_ABS ||
                 children[1].GetKind() == stp::FP_NEG)
          result = NodeFactory::CreateTerm(stp::FP_REM, width, children[0],
                                           children[1][0]);
        // rem(-a, b) = -rem(a, b): negating the dividend negates the result,
        // so lift the negation out where it can meet another and cancel.
        else if (children[0].GetKind() == stp::FP_NEG)
          result = NodeFactory::CreateTerm(
              stp::FP_NEG, width,
              NodeFactory::CreateTerm(stp::FP_REM, width, children[0][0],
                                      children[1]));
        // The invalid operands: rem is NaN whenever the dividend is NaN or
        // infinite, or the divisor is NaN or zero -- whatever the other
        // operand is.
        else if (fpConstIsNaN(children[0]))
          result = children[0];
        else if (fpConstIsNaN(children[1]))
          result = children[1];
        else if (fpConstInfSign(children[0]) != 0)
          result = makeFPNaN(children[0].GetExpWidth(),
                             children[0].GetSigWidth());
        else if (fpConstZeroSign(children[1]) != 0)
          result = makeFPNaN(children[1].GetExpWidth(),
                             children[1].GetSigWidth());
      }
      break;

    default: // quieten compiler.
      break;
  }

  if (result.IsNull())
    result = hashing.CreateTerm(kind, width, children);

  return result;
}

/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: January 2021
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

#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/Globals/Globals.h"
#include <cassert>
#include <string>

#ifdef STP_ENABLE_FLOATING_POINT
// The symfpu circuits are built behind the blast_* entry points; nothing
// here touches symfpu directly.
#include "stp/FloatBlaster/symbolic_fp.h"
#endif

namespace stp
{

ASTNode FloatBlaster::withFormat(STPMgr* bm, const ASTNode& n,
                                 unsigned int exp_width,
                                 unsigned int sig_width)
{
  if (exp_width == 0 && sig_width == 0)
    return n;

  // Asking for a real format means a float is in the problem, whatever this
  // then does with `n`. Noted before the early returns below, because those
  // are the cases where nothing is stamped and SetExpWidth -- the other place
  // the manager hears about floats -- is never reached. Missing it leaves the
  // floating-point passes switched off and the float reaches the bit-blaster.
  bm->noteFloatingPoint();

  if (n.GetExpWidth() == exp_width && n.GetSigWidth() == sig_width)
    return n;

  // Only a float-shaped value can carry a float's format; a rounding mode or
  // one of to_fp's format arguments must be left alone.
  if (n.GetValueWidth() != exp_width + sig_width)
    return n;

  // ASTBVConst cannot hold a format; ASTFPConst can. The float-stamped
  // constant is a distinct interned node, so this never retypes the shared
  // plain constant.
  if (n.GetKind() == BVCONST)
    return bm->CreateFPConst(n, exp_width, sig_width);

  // A bitvector-kind interior node has nowhere to put a format: nodes are
  // hash-consed and the format is per-node state, so a stamp here would retype
  // every other use of the same bits (see ASTNode::canStoreFPFormat). Leave it
  // the bitvector it is.
  //
  // What reaches this is a caller carrying one node's format over to another
  // -- a rebuild, a fold, a pull-up -- and meeting a node the format was never
  // its to hold. Once the floating-point layer is lowered a float and its
  // packed bits are the same node to everything but the format, and structure
  // that survives lowering goes on deriving a format from the float symbol
  // underneath it: (ite c (fp.abs x) x) over a Float64 x is an ordinary 64-bit
  // if-then-else by then, and still answers 11/53, because its else branch is
  // x and x's format is declared (see deriveFPFormat). Fold the condition, as
  // the simplifier does once it turns out to be a tautology, and what is left
  // is the circuit lowering built for (fp.abs x): bits, needing no format,
  // with the blaster long finished with them.
  if (!n.canStoreFPFormat())
    return n;

  ASTNode out(n);
  out.SetExpWidth(exp_width);
  out.SetSigWidth(sig_width);
  return out;
}

// Defined outside the feature gate: it only reads widths, and the callers
// that thread the format into the blaster are compiled either way.
std::pair<unsigned int, unsigned int>
FloatBlaster::operandFormat(const ASTVec& children)
{
  for (size_t i = 0; i < children.size(); i++)
  {
    const unsigned int exp_width = children[i].GetExpWidth();
    if (exp_width != 0)
      return std::make_pair(exp_width, children[i].GetSigWidth());
  }

  // No float operand: ((_ to_fp e s) bits) and ((_ to_fp_unsigned e s) rm bv)
  // read their source as bits, and name the only format they need in their
  // own e/s children.
  return std::make_pair(0u, 0u);
}

std::pair<unsigned int, unsigned int>
FloatBlaster::operandFormat(const ASTNode& n)
{
  return operandFormat(toASTVec(n.GetChildren()));
}

#ifdef STP_ENABLE_FLOATING_POINT
ASTNode FloatBlaster::canonicalBits(STPMgr* bm, const ASTNode& f)
{
  return canonicalBits(bm, f, f.GetExpWidth(), f.GetSigWidth());
}

// The format-taking form, for callers that know the format but hold a term
// that does not carry it -- a plain bitvector standing where a float-sorted
// value belongs (an array index over a float-indexed array, say).
ASTNode FloatBlaster::canonicalBits(STPMgr* bm, const ASTNode& f,
                                    unsigned int exp_width,
                                    unsigned int sig_width)
{
  // Point symfpu at the manager being blasted (see symbolic_fp::init).
  symbolic_fp::init(bm);
  return symbolic_fp::blast_reinterpret(f, exp_width, sig_width);
}
#endif

// Pure arithmetic, defined outside the feature gate: the parser refers to
// it whenever it builds an fp.rem, including in builds without
// floating-point support (where that path is unreachable but still links).
uint64_t FloatBlaster::remUnrollSteps(unsigned exp_width, unsigned sig_width)
{
  if (exp_width >= 63)
    return UINT64_MAX; // would overflow; certainly over any limit
  return ((uint64_t)1 << exp_width) + sig_width - 4;
}

bool FloatBlaster::remSupported(unsigned exp_width, unsigned sig_width)
{
  return remUnrollSteps(exp_width, sig_width) <= REM_UNROLL_LIMIT;
}

// symfpu's bitsToRepresent (symfpu/core/nondet.h and friends): how many bits
// it takes to write `n`.
static unsigned bitsToRepresent(uint64_t n)
{
  unsigned bits = 0;
  while (n != 0)
  {
    bits++;
    n >>= 1;
  }
  return bits;
}

// Kept line for line with symfpu's unpackedFloat<t>::exponentWidth so the two
// can be diffed; see the header for why it is replicated rather than called.
unsigned FloatBlaster::unpackedExponentWidth(unsigned exp_width,
                                             unsigned sig_width)
{
  if (sig_width <= 3)
  {
    // Subnormals fit into the gap between the minimum normal exponent and
    // what a signed number of this width can hold, so no widening is needed
    // -- and, as formatSupported records, symfpu's own unpack then rejects
    // the format.
    return exp_width;
  }

  if (exp_width >= 63)
    return UINT_MAX; // the shift below would overflow; certainly wide enough

  if (bitsToRepresent(sig_width - 3) < exp_width - 1)
  {
    // Significand is short compared to the exponent range: one extra bit.
    return exp_width + 1;
  }

  // Significand is long compared to the exponent range.
  return bitsToRepresent(((uint64_t)1 << (exp_width - 1)) + sig_width - 3) + 1;
}

bool FloatBlaster::formatSupported(unsigned exp_width, unsigned sig_width)
{
  return unpackedExponentWidth(exp_width, sig_width) > exp_width;
}

bool FloatBlaster::roundToIntegralSupported(unsigned exp_width,
                                            unsigned sig_width)
{
  // unpackedFloat<t>::significandWidth is the format's significand width
  // unchanged, so sig_width is the width convert.h compares against.
  return unpackedExponentWidth(exp_width, sig_width) != sig_width;
}

ASTNode FloatBlaster::unspecifiedValue(STPMgr* bm, const char* tag,
                                       const ASTVec& operands,
                                       const ASTNode& index,
                                       unsigned int value_width)
{
  const unsigned int index_width = index.GetValueWidth();

  // The '@' prefix puts the name in the namespace SMT-LIB 2 reserves for
  // solver use (as CreateFreshVariable does), so it cannot collide with a
  // conforming input's own symbols.
  std::string name("@fp_unspecified_");
  name += tag;

  // Then the operand formats, which the packed widths below cannot stand in
  // for -- see the header. Every caller holds format-carrying operands: the
  // pass runs before lowering, and the model-evaluation route re-stamps its
  // evaluated children through withFormat before totalising them. A caller
  // that lost the format would quietly mint a *different* array from the one
  // the solve constrained, so refuse rather than answer from the wrong one.
  for (size_t i = 0; i < operands.size(); i++)
  {
    const unsigned int exp_width = operands[i].GetExpWidth();
    const unsigned int sig_width = operands[i].GetSigWidth();

    if (exp_width == 0 || sig_width == 0)
      FatalError("unspecifiedValue: a partial floating-point operation's "
                 "operand reached totalisation without its format: ",
                 operands[i]);

    name += "_";
    name += std::to_string(exp_width);
    name += "x";
    name += std::to_string(sig_width);
  }

  name += "_";
  name += std::to_string(index_width);
  name += "_";
  name += std::to_string(value_width);

  const ASTNode array = bm->defaultNodeFactory->CreateSymbol(
      name.c_str(), index_width, value_width);

  return bm->CreateTerm(READ, value_width, array, index);
}

#ifdef STP_ENABLE_FLOATING_POINT
ASTNode FloatBlaster::BlastNode_TopLevel(STPMgr* bm, Kind k, const ASTVec& kids,
                                         unsigned int operand_exp,
                                         unsigned int operand_sig)
{
  // Every operation unpacks its operands, so a format symfpu cannot unpack
  // cannot be blasted at all. Backstop; the parser and the C API refuse
  // earlier, with a line number and the format.
  if (operand_exp != 0 && !formatSupported(operand_exp, operand_sig))
  {
    FatalError("FloatBlaster: this floating-point format is not supported: "
               "symfpu needs an unpacked exponent wider than the format's "
               "own, which does not hold once the significand is 3 bits or "
               "fewer");
  }

  // Point symfpu's backend at the manager being blasted now, rather than
  // whichever manager happened to blast first (see symbolic_fp::init).
  symbolic_fp::init(bm);
  return FloatBlaster::BlastNode(bm, k, kids, operand_exp, operand_sig);
}

// Takes the operation apart rather than as a node, because there is no
// well-formed node to take: its operands are bits by now, and an FP_ADD over
// bitvectors does not type check. Building one anyway, and stamping a format
// on it to make it pass, is what put the format on shared bitvector nodes.
ASTNode FloatBlaster::BlastNode(STPMgr* bm, Kind k, const ASTVec& kids,
                                unsigned int operand_exp,
                                unsigned int operand_sig)
{
  // What format the operands are packed in. They are bits by the time they
  // get here, so they cannot be asked -- see operandFormat.
  const symbolic_fp::floatingPointTypeInfo operands(operand_exp, operand_sig);

  ASTNode output;

  switch (k)
  {
    // The arithmetic operations all carry their rounding mode as child 0,
    // matching their arity in ASTKind.kinds.
    case FP_ADD:
      output = symbolic_fp::blast_fpadd(operands, /* rm */ kids[0], kids[1],
                                        kids[2]);
      break;
    case FP_SUB:
      output = symbolic_fp::blast_fpsub(operands, /* rm */ kids[0], kids[1],
                                        kids[2]);
      break;
    case FP_MUL:
      output = symbolic_fp::blast_fpmul(operands, /* rm */ kids[0], kids[1],
                                        kids[2]);
      break;
    case FP_DIV:
      output = symbolic_fp::blast_fpdiv(operands, /* rm */ kids[0], kids[1],
                                        kids[2]);
      break;
    case FP_FMA:
      output = symbolic_fp::blast_fpfma(operands, /* rm */ kids[0], kids[1],
                                        kids[2], kids[3]);
      break;
    case FP_SQRT:
      output = symbolic_fp::blast_fpsqrt(operands,
                                         /* rm */ kids[0], kids[1]);
      break;
    // fp.rem, fp.min and fp.max take no rounding mode.
    case FP_REM:
      // Backstop; the parser and the C API refuse earlier, with nicer
      // messages.
      if (!remSupported(operand_exp, operand_sig))
      {
        FatalError("FloatBlaster: fp.rem is not supported at this format: "
                   "its circuit unrolls one divide step per representable "
                   "exponent difference, which is exponential in the "
                   "exponent width; use a format no larger than binary64");
      }
      output = symbolic_fp::blast_fprem(operands, kids[0], kids[1]);
      break;
    // The choice of zero for (+0, -0) arrives as a third child, put there by
    // FpTotalise before solving.
    case FP_MIN:
    case FP_MAX:
    {
      assert(kids.size() == 3);

      // Child 2 is a 1-bit bitvector; symfpu wants a proposition.
      const ASTNode zero_case =
          bm->CreateNode(EQ, kids[2], bm->CreateOneConst(1));

      output =
          (k == FP_MIN)
              ? symbolic_fp::blast_fpmin(operands, kids[0], kids[1], zero_case)
              : symbolic_fp::blast_fpmax(operands, kids[0], kids[1], zero_case);
      break;
    }
    case FP_ABS:
      output = symbolic_fp::blast_fpabs(operands, kids[0]);
      break;
    case FP_NEG:
      output = symbolic_fp::blast_fpneg(operands, kids[0]);
      break;
    case FP_ISNORMAL:
      output = symbolic_fp::blast_is_normal(operands, kids[0]);
      break;
    case FP_ISSUBNORMAL:
      output = symbolic_fp::blast_is_subnormal(operands, kids[0]);
      break;
    case FP_ISZERO:
      output = symbolic_fp::blast_is_zero(operands, kids[0]);
      break;
    case FP_ISINFINITE:
      output = symbolic_fp::blast_is_infinite(operands, kids[0]);
      break;
    case FP_ISNAN:
      output = symbolic_fp::blast_is_nan(operands, kids[0]);
      break;
    case FP_ISNEGATIVE:
      output = symbolic_fp::blast_is_negative(operands, kids[0]);
      break;
    case FP_ISPOSITIVE:
      output = symbolic_fp::blast_is_positive(operands, kids[0]);
      break;
    // fp.eq is IEEE equality; FP_SMT_EQ is SMT-LIB's `=` on floats.
    case FP_EQ:
      output = symbolic_fp::blast_fpeq(operands, kids[0], kids[1]);
      break;
    case FP_LT:
      output = symbolic_fp::blast_fplt(operands, kids[0], kids[1]);
      break;
    case FP_LEQ:
      output = symbolic_fp::blast_fpleq(operands, kids[0], kids[1]);
      break;
    // fp.gt/fp.geq are the reversed forms; SMT-LIB defines them that way.
    case FP_GT:
      output = symbolic_fp::blast_fplt(operands, kids[1], kids[0]);
      break;
    case FP_GEQ:
      output = symbolic_fp::blast_fpleq(operands, kids[1], kids[0]);
      break;
    // ((_ to_fp e s) [rm] f). Children are (e, s, bits) for the bitvector
    // reinterpretation, or (e, s, rm, expr) for a float-to-float conversion.
    //
    // Take the target format from the e/s children rather than from the
    // node's own exponent/significand widths. Those are mutable per-node
    // state that a rebuild can drop, and blasting against a format of
    // (0, 0) underflows a width rather than failing; the children always
    // say what the format is.
    case FP_TOFP:
    {
      const unsigned int to_exp = kids[0].GetUnsignedConst();
      const unsigned int to_sig = kids[1].GetUnsignedConst();

      if (kids.size() == 3)
      {
        output =
            symbolic_fp::blast_reinterpret(/* bits */ kids[2], to_exp, to_sig);
      }
      else
      {
        // With a rounding mode this reformats a float. Converting a signed
        // integer is FP_TOFP_SIGNED, a kind of its own -- the two are
        // indistinguishable here, where the source is bits either way.
        assert(kids.size() == 4);
        output = symbolic_fp::blast_convert_float_to_float(
            operands, /* rm */ kids[2], /* expr */ kids[3], to_exp, to_sig);
      }

      return output;
    }
    // ((_ to_fp e s) rm bv) over a *signed* integer.
    case FP_TOFP_SIGNED:
    {
      assert(kids.size() == 4);
      return symbolic_fp::blast_convert_bv_to_float(
          /* rm */ kids[2], /* bits */ kids[3], kids[0].GetUnsignedConst(),
          kids[1].GetUnsignedConst(),
          /* is_signed */ true);
    }
    // ((_ to_fp_unsigned e s) rm bv): the source is always an unsigned
    // integer in a bitvector.
    case FP_TOFP_UNSIGNED:
    {
      const unsigned int to_exp = kids[0].GetUnsignedConst();
      const unsigned int to_sig = kids[1].GetUnsignedConst();
      output = symbolic_fp::blast_convert_bv_to_float(
          /* rm */ kids[2], /* bits */ kids[3], to_exp, to_sig,
          /* is_signed */ false);
      return output;
    }
    // (m, rm, x, unspecified). The result is a bitvector, not a float, so no
    // floating-point format is stamped on it.
    case FP_TO_UBV:
    case FP_TO_SBV:
      assert(kids.size() == 4);
      return symbolic_fp::blast_fp_to_bv(
          operands, /* rm */ kids[1], /* x */ kids[2],
          kids[0].GetUnsignedConst(), /* undef */ kids[3],
          /* is_signed */ k == FP_TO_SBV);
    // A float reinterpreted as its packed IEEE bits (unpack then pack, which
    // canonicalises NaN). Result is a bitvector, not a float.
    case FP_TO_IEEE_BV:
      output =
          symbolic_fp::blast_reinterpret(kids[0], operand_exp, operand_sig);
      break;
    case FP_SMT_EQ:
      output = symbolic_fp::blast_smt_eq(operands, kids[0], kids[1]);
      break;
    case FP_ROUNDTOINTEGRAL:
      // Backstop; the parser and the C API refuse earlier, with nicer
      // messages.
      if (!roundToIntegralSupported(operand_exp, operand_sig))
      {
        FatalError("FloatBlaster: fp.roundToIntegral is not supported at "
                   "this format: symfpu resizes its rounding point with "
                   "matchWidth, which may only widen, on a guard one bit "
                   "short of the width being resized");
      }
      output = symbolic_fp::blast_round_to_integral(operands,
                                                    /* rm */ kids[0],
                                                    /* expr */ kids[1]);
      break;
    default:
      // Fail closed: falling through would return the term unblasted, and
      // the callers would then loop or hand a floating-point node to the
      // bitvector layers.
      std::cerr << _kind_names[k] << std::endl;
      FatalError("FloatBlaster::BlastNode: unhandled kind");
      break;
  };

  // No format is put back on the way out. What comes back is the packed bits
  // the operation computes, and they are a bitvector; a float format on a
  // hash-consed bitvector node is exactly the corruption this avoids.
  assert(!output.IsNull());
  return output;
}

#else

// Fail-closed stubs so the link surface is identical with and without
// floating-point support. The parser and the STPMgr funnels reject
// floating-point input long before these could run (see checkFpSupported
// in smt2.y and SetExpWidth/CreateFPConst), so reaching one means a caller
// bypassed those checks. BlastNode needs no stub: it is only referenced
// from BlastNode_TopLevel's real body.

ASTNode FloatBlaster::canonicalBits(STPMgr*, const ASTNode&)
{
  FatalError("canonicalBits: this STP was built without floating-point "
             "support; reconfigure with -DENABLE_FLOATING_POINT=ON");
}

ASTNode FloatBlaster::canonicalBits(STPMgr*, const ASTNode&, unsigned int,
                                    unsigned int)
{
  FatalError("canonicalBits: this STP was built without floating-point "
             "support; reconfigure with -DENABLE_FLOATING_POINT=ON");
}

ASTNode FloatBlaster::BlastNode_TopLevel(STPMgr*, Kind, const ASTVec&,
                                         unsigned int, unsigned int)
{
  FatalError("BlastNode: this STP was built without floating-point "
             "support; reconfigure with -DENABLE_FLOATING_POINT=ON");
}

#endif

} // namespace stp

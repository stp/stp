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

  // Unpack then pack: the round trip is what collapses the NaN payloads
  // while keeping +0 and -0 apart.
  const symbolic_fp::floatingPointTypeInfo format(exp_width, sig_width);
  return symbolic_fp::unpacked::encode(
      format, symbolic_fp::unpacked::decode(format, f));
}
#else

// Fail-closed stubs so the link surface is identical with and without
// floating-point support. The parser and the STPMgr funnels reject
// floating-point input long before these could run (see checkFpSupported in
// smt2.y and SetExpWidth/CreateFPConst), so reaching one means a caller
// bypassed those checks.

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
// The one deviation is the overflow guard in the last branch, which symfpu
// does not have -- and which has to stay in that branch, since anywhere
// earlier it stops being a guard and starts being a wrong answer.
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

  if (bitsToRepresent(sig_width - 3) < exp_width - 1)
  {
    // Significand is short compared to the exponent range: one extra bit.
    return exp_width + 1;
  }

  // Significand is long compared to the exponent range. Only this branch
  // shifts, so only this branch needs the guard below -- putting it any
  // earlier answers for the branch above as well, and answers it wrong.
  if (exp_width >= 63)
    return UINT_MAX; // the shift would overflow; certainly wide enough

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
  // for -- see the header. Every caller holds format-carrying source operands:
  // the pass runs before lowering, and model evaluation reuses that same pass
  // through the solve's encoding context. A caller that lost the format would
  // quietly mint a *different* array from the one the solve constrained, so
  // refuse rather than answer from the wrong one.
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

  // Not CreateFreshVariable, whose minted names would differ between the
  // solve and the two counterexample re-derivations and so would not be the
  // same array; but introduced all the same, so say so, or the model answers
  // with a symbol the user never declared and in a sort their signature does
  // not have. The solver still gets the array -- only the printers skip it,
  // and CheckCounterExample needs its cell values.
  bm->noteIntroducedSymbol(array);

  return bm->CreateTerm(READ, value_width, array, index);
}

} // namespace stp

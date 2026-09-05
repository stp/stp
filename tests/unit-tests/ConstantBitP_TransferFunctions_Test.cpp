/***********
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
**********************/

// Exhaustive tests of the constant bit propagation transfer functions.
// Every function is checked, at small widths, over every combination of
// fixed/unfixed bits for five properties:
//
// 1) Soundness: propagation must never exclude a concrete assignment of the
//    children and output that was consistent with the bits before
//    propagation ran, and CONFLICT is only reported when no assignment
//    remains.
// 2) The Result contract: NO_CHANGE must mean no bit moved (propagate()
//    trusts it and skips rescheduling), and CHANGED must mean one did.
//    Neither has an exception. NOT_IMPLEMENTED says nothing either way and is
//    rejected unless the call site is marked RESULT_IS_VAGUE - see the note
//    on that constant for who still does it and why it matters.
// 3) The lattice rules: propagation may fix bits, but never unfix them or
//    flip a bit that was already fixed.
// 4) Maximal precision, for the functions the header documents as
//    maximally precise: every bit on which all remaining solutions agree
//    must come out fixed, and CONFLICT must be reported when no solution
//    exists at all. The brute-forced join of the solutions provides the
//    reference, so a propagator that soundly does nothing fails here
//    rather than passing silently.
// 5) Local fixed point: calling the function again on the bits the previous
//    call produced must derive nothing further. ConstantBitPropagation
//    ::propagate() gives each node exactly one call - when a child moves it
//    reschedules that child's other parents, but not the node it just ran -
//    so a function that needs a second call leaves the propagation short of
//    a fixed point and the solver never sees what the later call would have
//    found. A call site that passes a bound above SETTLES_IN_ONE_CALL is
//    recording a measured shortfall, not granting permission; the comment
//    there says what is lost.
//
// The functions checked only for soundness (OVERAPPROXIMATES rather than
// MAX_PRECISE below) are multiplication and the five division operations.
// Everything else is confirmed maximally precise here.
//
// Every operator is checked twice: once with a distinct FixedBits per
// operand, and once ALIASED, with one FixedBits shared between several
// operand slots. Aliasing is not hypothetical - the propagator looks up one
// FixedBits per *node*, so BVCONCAT(x,x) from ((_ repeat 2) x), BVPLUS(x,x)
// and BVAND(x,x) all reach the transfer functions with children[0] ==
// children[1], and a write through one operand is visible through the other.
// Properties 1, 2, 3 and 5 are required in both modes. Property 4 is checked
// only unaliased: an aliased call has no way to know that its two reads must
// take the same value, so the unaliased join is the wrong reference for it.

#include "extlib-constbv/constantbv.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include <gtest/gtest.h>

#include <algorithm>
#include <functional>
#include <memory>
#include <random>
#include <sstream>
#include <string>
#include <vector>

using namespace simplifier::constantBitP;

// File-local helpers from ConstantBitP_Multiplication.cpp that the tests
// exercise directly. They have external linkage but no header.
namespace simplifier
{
namespace constantBitP
{
Result useLeadingZeroesToFix(FixedBits& x, FixedBits& y, FixedBits& output);
Result trailingOneReasoning(FixedBits& x, FixedBits& y, FixedBits& output);
Result multiplyCore(std::vector<FixedBits*>& children, FixedBits& output,
                    MultiplicationStats* ms);
}
}

namespace
{

// Build FixedBits from a string, most significant bit first: '0', '1' or '*'.
FixedBits fromString(const std::string& s)
{
  FixedBits result(s.size(), false);
  for (unsigned i = 0; i < s.size(); i++)
  {
    const char c = s[s.size() - 1 - i]; // character for bit i.
    assert(c == '0' || c == '1' || c == '*');
    if (c != '*')
    {
      result.setFixed(i, true);
      result.setValue(i, c == '1');
    }
  }
  return result;
}

// Build FixedBits from a base-3 code: trit 0 = unfixed, 1 = zero, 2 = one.
FixedBits fromTernary(unsigned width, unsigned code, bool isBoolean = false)
{
  FixedBits result(width, isBoolean);
  for (unsigned i = 0; i < width; i++)
  {
    const unsigned trit = code % 3;
    code /= 3;
    if (trit != 0)
    {
      result.setFixed(i, true);
      result.setValue(i, trit == 2);
    }
  }
  return result;
}

// Whether the concrete value is consistent with the fixed bits.
bool admits(const FixedBits& bits, unsigned value)
{
  for (unsigned i = 0; i < bits.getWidth(); i++)
  {
    const bool bit = ((value >> i) & 1) != 0;
    if (bits.isFixed(i) && bits.getValue(i) != bit)
      return false;
  }
  return true;
}

std::string str(const FixedBits& bits)
{
  std::ostringstream s;
  s << bits;
  return s.str();
}

typedef std::function<Result(std::vector<FixedBits*>&, FixedBits&)> Propagator;
// Concrete semantics: takes one value per child, returns the output value.
typedef std::function<unsigned(const std::vector<unsigned>&)> Semantics;

// The width and boolean-ness of one operand position.
struct Slot
{
  unsigned width;
  bool isBoolean;
};

const bool MAX_PRECISE = true;
const bool OVERAPPROXIMATES = false;

// Which FixedBits object each operand position reads. The identity vector is
// the ordinary case. A repeated entry means one node feeds several operand
// positions, so the propagator sees the same pointer twice - what it gets for
// BVCONCAT(x,x), BVPLUS(x,x) and so on.
typedef std::vector<unsigned> Aliasing;

Aliasing distinctOperands(unsigned arity)
{
  Aliasing a(arity);
  for (unsigned i = 0; i < arity; i++)
    a[i] = i;
  return a;
}

// How many distinct FixedBits objects an aliasing uses.
unsigned objectCount(const Aliasing& readsObject)
{
  unsigned n = 0;
  for (unsigned o : readsObject)
    n = std::max(n, o + 1);
  return n;
}

bool isAliased(const Aliasing& readsObject)
{
  return objectCount(readsObject) != readsObject.size();
}

// How many calls a transfer function is allowed to take before it stops
// deriving anything. propagate() gives it one, so anything above this is a
// known shortfall rather than a licence: the bound is what the function
// measurably needs today, and the call sites that pass more than one name
// what is lost.
const unsigned SETTLES_IN_ONE_CALL = 1;

// Whether the Result a function returns describes what it did. Returning
// CHANGED without moving a bit is never allowed and has no exception. What
// some functions still do is return NOT_IMPLEMENTED unconditionally, which
// says nothing either way; propagate() reads that as "assume it changed" and
// re-derives the truth from countFixed(), so it costs work rather than
// correctness. It is a trap for anything that tries to loop on the Result -
// `while (r == CHANGED)` exits immediately on a shifter that is still
// deriving bits. RESULT_IS_VAGUE marks the functions that do it.
enum class ResultAccuracy
{
  Exact,
  Vague
};
const ResultAccuracy RESULT_IS_EXACT = ResultAccuracy::Exact;
const ResultAccuracy RESULT_IS_VAGUE = ResultAccuracy::Vague;

// Run the propagator on one case and check soundness, the NO_CHANGE
// contract, the lattice rules, that a second call derives nothing further,
// and (for the maximally precise functions) that every bit all the solutions
// agree on gets fixed. Returns a description of the first problem found, or
// the empty string.
//
// obj0 holds one starting value per distinct FixedBits object;
// readsObject[i] says which of them operand i reads.
std::string checkCase(const std::string& opName, const Propagator& propagate,
                      const Semantics& op, const std::vector<FixedBits>& obj0,
                      const Aliasing& readsObject, const FixedBits& out0,
                      bool expectPrecise,
                      unsigned callsAllowed = SETTLES_IN_ONE_CALL,
                      ResultAccuracy resultIsExact = RESULT_IS_EXACT,
                      bool* sawNotImplemented = NULL)
{
  const unsigned objects = obj0.size();
  const unsigned slots = readsObject.size();

  std::vector<FixedBits> obj(obj0);
  FixedBits out(out0);
  std::vector<FixedBits*> children;
  for (unsigned i = 0; i < slots; i++)
    children.push_back(&obj[readsObject[i]]);

  const Result result = propagate(children, out);

  std::ostringstream error;
  error << opName << "(";
  for (unsigned i = 0; i < slots; i++)
    error << (i ? ", " : "") << str(obj0[readsObject[i]]);
  error << ") = " << str(out0) << " became (";
  for (unsigned i = 0; i < slots; i++)
    error << (i ? ", " : "") << str(obj[readsObject[i]]);
  error << ") = " << str(out) << ": ";

  // Enumerate every concrete assignment of the distinct objects. Aliased
  // operands necessarily take the same value as each other.
  std::vector<unsigned> limit(objects);
  unsigned total = 1;
  for (unsigned o = 0; o < objects; o++)
  {
    limit[o] = 1u << obj0[o].getWidth();
    total *= limit[o];
  }

  // The join of the solutions: for each object, which bits are zero in some
  // solution and which are one in some solution. A bit every solution agrees
  // on is the precision target.
  bool anySolution = false;
  std::vector<unsigned> seenZero(objects + 1, 0);
  std::vector<unsigned> seenOne(objects + 1, 0);

  std::vector<unsigned> objVal(objects);
  std::vector<unsigned> val(slots);
  for (unsigned code = 0; code < total; code++)
  {
    unsigned c = code;
    bool consistent = true;
    for (unsigned o = 0; o < objects; o++)
    {
      objVal[o] = c % limit[o];
      c /= limit[o];
      if (!admits(obj0[o], objVal[o]))
      {
        consistent = false;
        break;
      }
    }
    if (!consistent)
      continue;
    for (unsigned i = 0; i < slots; i++)
      val[i] = objVal[readsObject[i]];
    const unsigned ov = op(val);
    if (!admits(out0, ov))
      continue;

    anySolution = true;
    for (unsigned o = 0; o < objects; o++)
    {
      seenZero[o] |= ~objVal[o];
      seenOne[o] |= objVal[o];
    }
    seenZero[objects] |= ~ov;
    seenOne[objects] |= ov;

    // This assignment was consistent before propagation ran.
    if (result == CONFLICT)
    {
      error << "CONFLICT reported, but (";
      for (unsigned i = 0; i < slots; i++)
        error << (i ? ", " : "") << val[i];
      error << ") -> " << ov << " is a solution";
      return error.str();
    }
    bool excluded = !admits(out, ov);
    for (unsigned o = 0; o < objects && !excluded; o++)
      excluded = !admits(obj[o], objVal[o]);
    if (excluded)
    {
      error << "unsoundly excluded the solution (";
      for (unsigned i = 0; i < slots; i++)
        error << (i ? ", " : "") << val[i];
      error << ") -> " << ov;
      return error.str();
    }
  }

  bool movedBits = !FixedBits::equals(out, out0);
  for (unsigned o = 0; o < objects && !movedBits; o++)
    movedBits = !FixedBits::equals(obj[o], obj0[o]);

  if (result == NO_CHANGE && movedBits)
  {
    error << "returned NO_CHANGE but altered bits";
    return error.str();
  }

  if (result == CHANGED && !movedBits)
  {
    error << "returned CHANGED but altered nothing";
    return error.str();
  }

  if (result == NOT_IMPLEMENTED && sawNotImplemented != NULL)
    *sawNotImplemented = true;

  if (resultIsExact == RESULT_IS_EXACT && result == NOT_IMPLEMENTED)
  {
    error << "returned NOT_IMPLEMENTED, which says nothing about whether it "
          << (movedBits ? "changed anything (it did)"
                        : "changed anything (it did not)");
    return error.str();
  }

  bool latticeOK = FixedBits::updateOK(out0, out);
  for (unsigned o = 0; o < objects && latticeOK; o++)
    latticeOK = FixedBits::updateOK(obj0[o], obj[o]);
  if (!latticeOK)
  {
    error << "unfixed or flipped already-fixed bits";
    return error.str();
  }

  // Keep calling until nothing more is derived. propagate() reschedules the
  // other parents of a child that moved, but not the node it just ran, so
  // whatever a later call would have found is simply lost in the solver.
  // Runs on copies so the precision check below still sees what one call
  // produces, which is all the solver gets.
  if (result != CONFLICT)
  {
    std::vector<FixedBits> again(obj);
    FixedBits againOut(out);
    unsigned calls = 1;
    while (true)
    {
      std::vector<FixedBits> before(again);
      const FixedBits beforeOut(againOut);

      std::vector<FixedBits*> againChildren;
      for (unsigned i = 0; i < slots; i++)
        againChildren.push_back(&again[readsObject[i]]);
      const Result r = propagate(againChildren, againOut);

      bool moved = !FixedBits::equals(againOut, beforeOut);
      for (unsigned o = 0; o < objects && !moved; o++)
        moved = !FixedBits::equals(again[o], before[o]);

      if (!moved && r != CONFLICT)
        break; // Settled.

      calls++;
      if (calls > callsAllowed)
      {
        error << "not settled after " << callsAllowed << " call"
              << (callsAllowed == 1 ? "" : "s") << ": call " << calls
              << " gives (";
        for (unsigned i = 0; i < slots; i++)
          error << (i ? ", " : "") << str(again[readsObject[i]]);
        error << ") = " << str(againOut);
        if (r == CONFLICT)
          error << " CONFLICT";
        return error.str();
      }
      if (r == CONFLICT)
        break;
    }
  }

  if (expectPrecise)
  {
    if (!anySolution)
    {
      if (result != CONFLICT)
      {
        error << "no solution exists, but CONFLICT was not reported";
        return error.str();
      }
      return "";
    }

    // Solutions exist, so CONFLICT was ruled out above. Every bit the
    // solutions all agree on must have come out fixed. (A bit fixed to
    // the wrong value is unsoundness, caught above.)
    for (unsigned o = 0; o <= objects; o++)
    {
      const FixedBits& bits = (o == objects) ? out : obj[o];
      for (unsigned j = 0; j < bits.getWidth(); j++)
      {
        const bool zeroSeen = (seenZero[o] >> j) & 1;
        const bool oneSeen = (seenOne[o] >> j) & 1;
        if (zeroSeen && oneSeen)
          continue; // The solutions disagree, so the bit can't be fixed.
        if (!bits.isFixed(j))
        {
          error << "not maximally precise: every solution has "
                << (o == objects ? "the output" : "child ")
                << (o == objects ? std::string() : std::to_string(o))
                << " bit " << j << " as " << (oneSeen ? '1' : '0')
                << ", but it was left unfixed";
          return error.str();
        }
      }
    }
  }

  return "";
}

// Check every combination of fixed/zero/one bits over the given operand
// shape. objs describes the distinct FixedBits the call is given and
// readsObject which of them each operand position reads. Reports at most the
// first five problems.
void exhaustiveCheckAliased(const std::string& opName,
                            const Propagator& propagate, const Semantics& op,
                            const std::vector<Slot>& objs,
                            const Aliasing& readsObject, const Slot& outSlot,
                            bool expectPrecise,
                            unsigned callsAllowed = SETTLES_IN_ONE_CALL,
                            ResultAccuracy resultIsExact = RESULT_IS_EXACT)
{
  bool sawNotImplemented = false;
  const unsigned objects = objs.size();
  std::vector<unsigned> patterns(objects);
  unsigned total = 1;
  for (unsigned o = 0; o < objects; o++)
  {
    patterns[o] = 1;
    for (unsigned j = 0; j < objs[o].width; j++)
      patterns[o] *= 3;
    total *= patterns[o];
  }
  unsigned outPatterns = 1;
  for (unsigned j = 0; j < outSlot.width; j++)
    outPatterns *= 3;
  total *= outPatterns;

  std::vector<std::string> errors;
  for (unsigned code = 0; code < total && errors.size() < 5; code++)
  {
    unsigned c = code;
    std::vector<FixedBits> obj;
    obj.reserve(objects);
    for (unsigned o = 0; o < objects; o++)
    {
      obj.push_back(fromTernary(objs[o].width, c % patterns[o],
                                objs[o].isBoolean));
      c /= patterns[o];
    }
    const FixedBits out = fromTernary(outSlot.width, c, outSlot.isBoolean);

    const std::string e = checkCase(opName, propagate, op, obj, readsObject,
                                    out, expectPrecise, callsAllowed,
                                    resultIsExact, &sawNotImplemented);
    if (!e.empty())
      errors.push_back(e);
  }

  std::ostringstream all;
  for (const auto& e : errors)
    all << e << "\n";
  EXPECT_TRUE(errors.empty())
      << (isAliased(readsObject) ? "aliased operands\n" : "") << all.str();

  // Keep the exception list honest: a function marked RESULT_IS_VAGUE that
  // never actually returns NOT_IMPLEMENTED has been fixed, and the marking
  // should come off rather than sit there hiding a regression.
  EXPECT_TRUE(resultIsExact == RESULT_IS_EXACT || sawNotImplemented ||
              !errors.empty())
      << opName << " is marked RESULT_IS_VAGUE but never returned "
                   "NOT_IMPLEMENTED - drop the marking";
}

// The ordinary case: one distinct FixedBits per operand.
void exhaustiveCheck(const std::string& opName, const Propagator& propagate,
                     const Semantics& op, const std::vector<Slot>& ins,
                     const Slot& outSlot, bool expectPrecise,
                     unsigned callsAllowed = SETTLES_IN_ONE_CALL,
                     ResultAccuracy resultIsExact = RESULT_IS_EXACT)
{
  exhaustiveCheckAliased(opName, propagate, op, ins,
                         distinctOperands(ins.size()), outSlot, expectPrecise,
                         callsAllowed, resultIsExact);
}

// Interpret an unsigned value of the given width as two's complement.
int asSigned(unsigned value, unsigned width)
{
  return value >= (1u << (width - 1)) ? (int)value - (1 << width) : (int)value;
}

// Reference semantics for a two-child operation, tabulated from the
// solver's constant evaluator so conventions like division by zero can't
// drift from STP's.
Semantics evaluatorSemantics(stp::STPMgr* mgr, stp::Kind k, unsigned width)
{
  const unsigned n = 1u << width;
  auto table = std::make_shared<std::vector<unsigned>>(n * n);
  for (unsigned a = 0; a < n; a++)
    for (unsigned b = 0; b < n; b++)
    {
      stp::ASTVec children;
      children.push_back(mgr->CreateBVConst(width, a));
      children.push_back(mgr->CreateBVConst(width, b));
      (*table)[a * n + b] =
          stp::NonMemberBVConstEvaluator(mgr, k, children, width)
              .GetUnsignedConst();
    }
  return [table, n](const std::vector<unsigned>& v) {
    return (*table)[v[0] * n + v[1]];
  };
}

class ConstantBitP_TransferFunctions : public ::testing::Test
{
protected:
  ConstantBitP_TransferFunctions() { CONSTANTBV::BitVector_Boot(); }
  stp::STPMgr mgr;

  // Common shapes: N bitvector children of width 3 and a width-3 output.
  static std::vector<Slot> bv3(unsigned n)
  {
    return std::vector<Slot>(n, Slot{3, false});
  }
  static Slot out3() { return Slot{3, false}; }
  static Slot boolSlot() { return Slot{1, true}; }
};

// The interval reasoning in bvUnsignedDivisionBothWays computes
// maxQuotient * maxBottom + (maxBottom - 1) to tighten the maximum of the
// numerator. At width 4 with maxQuotient = 5 and maxBottom = 3 that is
// 5 * 3 + 2 = 17, which wraps to 1. This is safe only because the strict
// multiply errors once the product reaches bit (width - 1); the test pins
// that invariant. 15 / 3 = 5 must stay admitted.
TEST_F(ConstantBitP_TransferFunctions, divisionIntervalRule3DoesNotWrap)
{
  FixedBits a = fromString("****");
  FixedBits b = fromString("0011");
  FixedBits out = fromString("0*0*");

  std::vector<FixedBits*> children;
  children.push_back(&a);
  children.push_back(&b);

  const Result result = bvUnsignedDivisionBothWays(children, out, &mgr);

  EXPECT_NE(CONFLICT, result);
  EXPECT_TRUE(admits(a, 15)) << "numerator " << str(a)
                             << " no longer admits 15, but 15 / 3 = 5";
  EXPECT_TRUE(admits(out, 5)) << "quotient " << str(out)
                              << " no longer admits 5, but 15 / 3 = 5";
}

TEST_F(ConstantBitP_TransferFunctions, unsignedDivisionExhaustiveWidth3)
{
  const unsigned mask = 7;
  exhaustiveCheck(
      "bvudiv",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvUnsignedDivisionBothWays(children, out, &mgr);
      },
      // SMT-LIB semantics: bvudiv by zero gives all ones.
      [](const std::vector<unsigned>& v) {
        return v[1] == 0 ? mask : v[0] / v[1];
      },
      bv3(2), out3(), OVERAPPROXIMATES);
}

TEST_F(ConstantBitP_TransferFunctions, unsignedModulusExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvurem",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvUnsignedModulusBothWays(children, out, &mgr);
      },
      // SMT-LIB semantics: bvurem by zero gives the numerator.
      [](const std::vector<unsigned>& v) {
        return v[1] == 0 ? v[0] : v[0] % v[1];
      },
      bv3(2), out3(), OVERAPPROXIMATES, SETTLES_IN_ONE_CALL, RESULT_IS_VAGUE);
}

// The three signed division operations were previously untested. None of
// them claims maximal precision.
TEST_F(ConstantBitP_TransferFunctions, signedDivisionExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvsdiv",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvSignedDivisionBothWays(children, out, &mgr);
      },
      evaluatorSemantics(&mgr, stp::SBVDIV, 3), bv3(2), out3(),
      OVERAPPROXIMATES, SETTLES_IN_ONE_CALL, RESULT_IS_VAGUE);
}

TEST_F(ConstantBitP_TransferFunctions, signedRemainderExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvsrem",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvSignedRemainderBothWays(children, out, &mgr);
      },
      evaluatorSemantics(&mgr, stp::SBVREM, 3), bv3(2), out3(),
      OVERAPPROXIMATES, SETTLES_IN_ONE_CALL, RESULT_IS_VAGUE);
}

// bvsmod used to be the only transfer function that failed to settle on a
// single call with *distinct* children: 795 of the 19683 width-3 starting
// states derived more on a later call, 671 of them a CONFLICT the first
// call missed. It now iterates its structural and decompose passes to an
// internal fixed point, so it must settle in one call like everything else.
TEST_F(ConstantBitP_TransferFunctions, signedModulusExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvsmod",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvSignedModulusBothWays(children, out, &mgr);
      },
      evaluatorSemantics(&mgr, stp::SBVMOD, 3), bv3(2), out3(),
      OVERAPPROXIMATES, SETTLES_IN_ONE_CALL);
}

TEST_F(ConstantBitP_TransferFunctions, multiplicationExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvmul",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvMultiplyBothWays(children, out, &mgr, NULL);
      },
      [](const std::vector<unsigned>& v) { return (v[0] * v[1]) & 7; },
      bv3(2), out3(), OVERAPPROXIMATES, SETTLES_IN_ONE_CALL, RESULT_IS_VAGUE);
}

// BVTypeCheck accepts BVMULT with more than two children, and the hashing
// node factory builds such nodes (only the simplifying factory binarises
// them). The multiply transfer function reasons about exactly two operands,
// so on a wider multiply it must do nothing: propagating on the first two
// children fixed the output's low bit to one for <-1> * <-1> * <-->,
// excluding solutions like 1 * 1 * 2 = 2.
TEST_F(ConstantBitP_TransferFunctions, multiplicationThreeChildrenDoesNothing)
{
  FixedBits a = fromString("**1");
  FixedBits b = fromString("**1");
  FixedBits c = fromString("***");
  FixedBits out = fromString("***");

  std::vector<FixedBits*> children;
  children.push_back(&a);
  children.push_back(&b);
  children.push_back(&c);

  EXPECT_EQ(NO_CHANGE, bvMultiplyBothWays(children, out, &mgr, NULL));
  EXPECT_TRUE(FixedBits::equals(out, fromString("***")));
  EXPECT_TRUE(FixedBits::equals(a, fromString("**1")));
}

// The dispatcher must also leave no multiplication-stats entry for a wider
// multiply: bvMultiplyBothWays bails before filling the stats in, and an
// empty entry's NULL column arrays would be read by the bit-blaster's
// getMS() later.
TEST_F(ConstantBitP_TransferFunctions, multiplicationThreeChildrenStoresNoStats)
{
  FixedBits a = fromString("**1");
  FixedBits b = fromString("**1");
  FixedBits c = fromString("***");
  FixedBits out = fromString("***");

  std::vector<FixedBits*> children;
  children.push_back(&a);
  children.push_back(&b);
  children.push_back(&c);

  const stp::ASTNode x = mgr.CreateSymbol("msmX", 0, 3);
  const stp::ASTNode y = mgr.CreateSymbol("msmY", 0, 3);
  const stp::ASTNode z = mgr.CreateSymbol("msmZ", 0, 3);
  const stp::ASTNode n =
      mgr.hashingNodeFactory->CreateTerm(stp::BVMULT, 3, x, y, z);

  MultiplicationStatsMap msm;
  EXPECT_EQ(NO_CHANGE, ConstantBitPropagation::dispatchToTransferFunctions(
                           &mgr, stp::BVMULT, children, out, n, &msm));
  EXPECT_TRUE(msm.map.empty());
}

// An odd operand c is invertible mod 2^k, so c * other == output can also be
// read as inv(c) * output == other, and bvMultiplyBothWays runs the column
// reasoning over that view too. Here 13 * <010*> can only be 0100 or 0001,
// and the inverse view derives output bit 3 from y's bits — the original
// view's column intervals can't see past y's unfixed bit 0, so multiplyCore
// alone fixes only bit 1.
TEST_F(ConstantBitP_TransferFunctions, multiplicationInverseFixesOutputHighBit)
{
  FixedBits x = fromString("1101");
  FixedBits y = fromString("010*");
  FixedBits out = fromString("****");

  std::vector<FixedBits*> children = {&x, &y};
  bvMultiplyBothWays(children, out, &mgr, NULL);

  EXPECT_TRUE(FixedBits::equals(out, fromString("0*0*")));
  EXPECT_TRUE(FixedBits::equals(x, fromString("1101")));
  EXPECT_TRUE(FixedBits::equals(y, fromString("010*")));
}

// The inverse view only needs the *low* bits of an operand fixed (and odd):
// x == <*011> gives x ≡ 3 (mod 8), so y ≡ 3 * output (mod 8), and y's fixed
// zero at bit 2 pins output bit 2 through the inverse.
TEST_F(ConstantBitP_TransferFunctions, multiplicationInverseUsesOddLowPrefix)
{
  FixedBits x = fromString("*011");
  FixedBits y = fromString("*0**");
  FixedBits out = fromString("**0*");

  std::vector<FixedBits*> children = {&x, &y};
  bvMultiplyBothWays(children, out, &mgr, NULL);

  EXPECT_TRUE(FixedBits::equals(out, fromString("*00*")));
  EXPECT_TRUE(FixedBits::equals(x, fromString("*011")));
  EXPECT_TRUE(FixedBits::equals(y, fromString("*0**")));
}

// 13 * 14 = 6 and 13 * 15 = 3 (mod 16): output bit 3 must be zero, which
// only the inverse view derives; asking for a one there is a conflict the
// original view misses.
TEST_F(ConstantBitP_TransferFunctions, multiplicationInverseFindsConflict)
{
  FixedBits x = fromString("1101");
  FixedBits y = fromString("111*");
  FixedBits out = fromString("1***");

  std::vector<FixedBits*> children = {&x, &y};
  EXPECT_EQ(CONFLICT, bvMultiplyBothWays(children, out, &mgr, NULL));
}

// Fully constant odd multiplier with a fully fixed output: the variable
// operand is completely determined (5 * 3 == 15 mod 16).
TEST_F(ConstantBitP_TransferFunctions, multiplicationInverseSolvesOperand)
{
  FixedBits x = fromString("0101");
  FixedBits y = fromString("****");
  FixedBits out = fromString("1111");

  std::vector<FixedBits*> children = {&x, &y};
  bvMultiplyBothWays(children, out, &mgr, NULL);

  EXPECT_TRUE(FixedBits::equals(y, fromString("0011")));
}

// Aliased square with an odd low prefix: t ≡ 3 (mod 8) means t*t ≡ 1
// (mod 8), fixing the output's low bits while t itself stays untouched.
TEST_F(ConstantBitP_TransferFunctions, multiplicationInverseAliasedSquare)
{
  FixedBits t = fromString("*011");
  FixedBits out = fromString("****");

  std::vector<FixedBits*> children = {&t, &t};
  bvMultiplyBothWays(children, out, &mgr, NULL);

  EXPECT_TRUE(FixedBits::equals(out, fromString("*001")));
  EXPECT_TRUE(FixedBits::equals(t, fromString("*011")));
}

// With no odd fixed low prefix on either operand the inverse view doesn't
// apply, and bvMultiplyBothWays must behave exactly like the core column
// reasoning.
TEST_F(ConstantBitP_TransferFunctions, multiplicationEvenPrefixMatchesCore)
{
  FixedBits x = fromString("**10");
  FixedBits y = fromString("***1");
  FixedBits out = fromString("****");

  FixedBits cx(x), cy(y), cout_(out);
  std::vector<FixedBits*> coreChildren = {&cx, &cy};
  multiplyCore(coreChildren, cout_, NULL);

  std::vector<FixedBits*> children = {&x, &y};
  bvMultiplyBothWays(children, out, &mgr, NULL);

  EXPECT_TRUE(FixedBits::equals(x, cx));
  EXPECT_TRUE(FixedBits::equals(y, cy));
  EXPECT_TRUE(FixedBits::equals(out, cout_));
  EXPECT_TRUE(FixedBits::equals(out, fromString("**10")));
}

TEST_F(ConstantBitP_TransferFunctions, additionExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvadd", bvAddBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] + v[1]) & 7; },
      bv3(2), out3(), MAX_PRECISE);
}

TEST_F(ConstantBitP_TransferFunctions, additionThreeChildrenExhaustiveWidth2)
{
  exhaustiveCheck(
      "bvadd3",
      bvAddBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] + v[1] + v[2]) & 3; },
      std::vector<Slot>(3, Slot{2, false}), Slot{2, false}, MAX_PRECISE);
}

TEST_F(ConstantBitP_TransferFunctions, subtractionExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvsub", bvSubtractBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] - v[1]) & 7; },
      bv3(2), out3(), MAX_PRECISE);
}

TEST_F(ConstantBitP_TransferFunctions, unaryMinusExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvneg", bvUnaryMinusBothWays,
      [](const std::vector<unsigned>& v) { return (0u - v[0]) & 7; }, bv3(1),
      out3(), MAX_PRECISE);
}

TEST_F(ConstantBitP_TransferFunctions, shiftsExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvshl", bvLeftShiftBothWays,
      [](const std::vector<unsigned>& v) {
        return v[1] >= 3 ? 0 : (v[0] << v[1]) & 7;
      },
      bv3(2), out3(), MAX_PRECISE, SETTLES_IN_ONE_CALL, RESULT_IS_VAGUE);

  exhaustiveCheck(
      "bvlshr", bvRightShiftBothWays,
      [](const std::vector<unsigned>& v) {
        return v[1] >= 3 ? 0 : v[0] >> v[1];
      },
      bv3(2), out3(), MAX_PRECISE, SETTLES_IN_ONE_CALL, RESULT_IS_VAGUE);

  exhaustiveCheck(
      "bvashr", bvArithmeticRightShiftBothWays,
      [](const std::vector<unsigned>& v) {
        const unsigned sign = (v[0] >> 2) & 1;
        if (v[1] >= 3)
          return sign ? 7u : 0u;
        const unsigned shifted = v[0] >> v[1];
        return sign ? (shifted | (7u & ~(7u >> v[1]))) : shifted;
      },
      bv3(2), out3(), MAX_PRECISE, SETTLES_IN_ONE_CALL, RESULT_IS_VAGUE);
}

TEST_F(ConstantBitP_TransferFunctions, unsignedComparisonsExhaustiveWidth3)
{
  const struct
  {
    const char* name;
    Propagator prop;
    std::function<bool(unsigned, unsigned)> cmp;
  } ops[] = {
      {"bvult",
       [](std::vector<FixedBits*>& c, FixedBits& o) {
         return bvLessThanBothWays(c, o);
       },
       [](unsigned a, unsigned b) { return a < b; }},
      {"bvule", bvLessThanEqualsBothWays,
       [](unsigned a, unsigned b) { return a <= b; }},
      {"bvugt", bvGreaterThanBothWays,
       [](unsigned a, unsigned b) { return a > b; }},
      {"bvuge", bvGreaterThanEqualsBothWays,
       [](unsigned a, unsigned b) { return a >= b; }},
  };
  for (const auto& o : ops)
  {
    const auto cmp = o.cmp;
    exhaustiveCheck(o.name, o.prop,
                    [cmp](const std::vector<unsigned>& v) {
                      return cmp(v[0], v[1]) ? 1u : 0u;
                    },
                    bv3(2), boolSlot(), MAX_PRECISE);
  }
}

TEST_F(ConstantBitP_TransferFunctions, signedComparisonsExhaustiveWidth3)
{
  const struct
  {
    const char* name;
    Propagator prop;
    std::function<bool(int, int)> cmp;
  } ops[] = {
      {"bvslt", bvSignedLessThanBothWays, [](int a, int b) { return a < b; }},
      {"bvsle", bvSignedLessThanEqualsBothWays,
       [](int a, int b) { return a <= b; }},
      {"bvsgt", bvSignedGreaterThanBothWays,
       [](int a, int b) { return a > b; }},
      {"bvsge", bvSignedGreaterThanEqualsBothWays,
       [](int a, int b) { return a >= b; }},
  };
  for (const auto& o : ops)
  {
    const auto cmp = o.cmp;
    exhaustiveCheck(o.name, o.prop,
                    [cmp](const std::vector<unsigned>& v) {
                      return cmp(asSigned(v[0], 3), asSigned(v[1], 3)) ? 1u
                                                                       : 0u;
                    },
                    bv3(2), boolSlot(), MAX_PRECISE);
  }
}

TEST_F(ConstantBitP_TransferFunctions, bitwiseExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvand", bvAndBothWays,
      [](const std::vector<unsigned>& v) { return v[0] & v[1]; }, bv3(2),
      out3(), MAX_PRECISE);
  exhaustiveCheck(
      "bvor", bvOrBothWays,
      [](const std::vector<unsigned>& v) { return v[0] | v[1]; }, bv3(2),
      out3(), MAX_PRECISE);
  exhaustiveCheck(
      "bvxor", bvXorBothWays,
      [](const std::vector<unsigned>& v) { return v[0] ^ v[1]; }, bv3(2),
      out3(), MAX_PRECISE);
  exhaustiveCheck(
      "bvnot",
      [](std::vector<FixedBits*>& c, FixedBits& o) {
        return bvNotBothWays(c, o);
      },
      [](const std::vector<unsigned>& v) { return ~v[0] & 7; }, bv3(1),
      out3(), MAX_PRECISE);
}

TEST_F(ConstantBitP_TransferFunctions, booleanLogicExhaustive)
{
  const std::vector<Slot> two(2, boolSlot());
  const std::vector<Slot> three(3, boolSlot());

  exhaustiveCheck("and", bvAndBothWays,
                  [](const std::vector<unsigned>& v) { return v[0] & v[1]; },
                  two, boolSlot(), MAX_PRECISE);
  exhaustiveCheck(
      "and3", bvAndBothWays,
      [](const std::vector<unsigned>& v) { return v[0] & v[1] & v[2]; }, three,
      boolSlot(), MAX_PRECISE);
  exhaustiveCheck("or", bvOrBothWays,
                  [](const std::vector<unsigned>& v) { return v[0] | v[1]; },
                  two, boolSlot(), MAX_PRECISE);
  exhaustiveCheck(
      "or3", bvOrBothWays,
      [](const std::vector<unsigned>& v) { return v[0] | v[1] | v[2]; }, three,
      boolSlot(), MAX_PRECISE);
  exhaustiveCheck("xor", bvXorBothWays,
                  [](const std::vector<unsigned>& v) { return v[0] ^ v[1]; },
                  two, boolSlot(), MAX_PRECISE);
  exhaustiveCheck(
      "xor3", bvXorBothWays,
      [](const std::vector<unsigned>& v) { return v[0] ^ v[1] ^ v[2]; }, three,
      boolSlot(), MAX_PRECISE);
  exhaustiveCheck(
      "implies", bvImpliesBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] == 0 || v[1]) ? 1u : 0u; },
      two, boolSlot(), MAX_PRECISE);
  exhaustiveCheck(
      "iff", bvEqualsBothWays,
      [](const std::vector<unsigned>& v) { return v[0] == v[1] ? 1u : 0u; },
      two, boolSlot(), MAX_PRECISE);
  exhaustiveCheck("not",
                  [](std::vector<FixedBits*>& c, FixedBits& o) {
                    return bvNotBothWays(c, o);
                  },
                  [](const std::vector<unsigned>& v) { return v[0] ^ 1u; },
                  std::vector<Slot>(1, boolSlot()), boolSlot(), MAX_PRECISE);
}

TEST_F(ConstantBitP_TransferFunctions, equalsExhaustiveWidth3)
{
  exhaustiveCheck(
      "=", bvEqualsBothWays,
      [](const std::vector<unsigned>& v) { return v[0] == v[1] ? 1u : 0u; },
      bv3(2), boolSlot(), MAX_PRECISE);
}

TEST_F(ConstantBitP_TransferFunctions, iteExhaustiveWidth3)
{
  std::vector<Slot> ins;
  ins.push_back(boolSlot());
  ins.push_back(Slot{3, false});
  ins.push_back(Slot{3, false});
  exhaustiveCheck(
      "ite", bvITEBothWays,
      [](const std::vector<unsigned>& v) { return v[0] ? v[1] : v[2]; }, ins,
      out3(), MAX_PRECISE);
}

TEST_F(ConstantBitP_TransferFunctions, concatExhaustive)
{
  // Children are most significant first; widths 2 + 1 = 3.
  std::vector<Slot> ins;
  ins.push_back(Slot{2, false});
  ins.push_back(Slot{1, false});
  exhaustiveCheck(
      "concat", bvConcatBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] << 1) | v[1]; }, ins,
      out3(), MAX_PRECISE);

  exhaustiveCheck(
      "concat3", bvConcatBothWays,
      [](const std::vector<unsigned>& v) {
        return (v[0] << 2) | (v[1] << 1) | v[2];
      },
      std::vector<Slot>(3, Slot{1, false}), out3(), MAX_PRECISE);
}

// Zero and sign extension take a second child (the amount node) that the
// transfer functions ignore; pass a fixed constant for it.
TEST_F(ConstantBitP_TransferFunctions, zeroExtendExhaustiveWidth3To5)
{
  std::vector<std::string> errors;
  for (unsigned ip = 0; ip < 27 && errors.size() < 5; ip++)
    for (unsigned op = 0; op < 243 && errors.size() < 5; op++)
    {
      std::vector<FixedBits> in;
      in.push_back(fromTernary(3, ip));
      in.push_back(FixedBits::fromUnsignedInt(3, 2)); // ignored size argument.
      const std::string e =
          checkCase("zero_extend", bvZeroExtendBothWays,
                    [](const std::vector<unsigned>& v) { return v[0]; }, in,
                    distinctOperands(in.size()), fromTernary(5, op),
                    MAX_PRECISE);
      if (!e.empty())
        errors.push_back(e);
    }
  std::ostringstream all;
  for (const auto& e : errors)
    all << e << "\n";
  EXPECT_TRUE(errors.empty()) << all.str();
}

TEST_F(ConstantBitP_TransferFunctions, signExtendExhaustiveWidth3To5)
{
  std::vector<std::string> errors;
  for (unsigned ip = 0; ip < 27 && errors.size() < 5; ip++)
    for (unsigned op = 0; op < 243 && errors.size() < 5; op++)
    {
      std::vector<FixedBits> in;
      in.push_back(fromTernary(3, ip));
      in.push_back(FixedBits::fromUnsignedInt(3, 2)); // ignored size argument.
      const std::string e = checkCase(
          "sign_extend", bvSignExtendBothWays,
          [](const std::vector<unsigned>& v) {
            return ((v[0] >> 2) & 1) ? (v[0] | 0x18u) : v[0];
          },
          in, distinctOperands(in.size()), fromTernary(5, op), MAX_PRECISE);
      if (!e.empty())
        errors.push_back(e);
    }
  std::ostringstream all;
  for (const auto& e : errors)
    all << e << "\n";
  EXPECT_TRUE(errors.empty()) << all.str();
}

// Extract takes the top and bottom indices as fully-fixed constant children.
TEST_F(ConstantBitP_TransferFunctions, extractExhaustiveWidth3)
{
  std::vector<std::string> errors;
  for (unsigned top = 0; top < 3; top++)
    for (unsigned bottom = 0; bottom <= top; bottom++)
    {
      const unsigned outWidth = top - bottom + 1;
      unsigned outPatterns = 1;
      for (unsigned j = 0; j < outWidth; j++)
        outPatterns *= 3;

      for (unsigned ip = 0; ip < 27 && errors.size() < 5; ip++)
        for (unsigned op = 0; op < outPatterns && errors.size() < 5; op++)
        {
          std::vector<FixedBits> in;
          in.push_back(fromTernary(3, ip));
          in.push_back(FixedBits::fromUnsignedInt(3, top));
          in.push_back(FixedBits::fromUnsignedInt(3, bottom));
          const std::string e = checkCase(
              "extract", bvExtractBothWays,
              [bottom, outWidth](const std::vector<unsigned>& v) {
                return (v[0] >> bottom) & ((1u << outWidth) - 1);
              },
              in, distinctOperands(in.size()), fromTernary(outWidth, op),
              MAX_PRECISE);
          if (!e.empty())
            errors.push_back(e);
        }
    }
  std::ostringstream all;
  for (const auto& e : errors)
    all << e << "\n";
  EXPECT_TRUE(errors.empty()) << all.str();
}

// useLeadingZeroesToFix allocates three bitvectors and, before this was
// fixed, returned CONFLICT without freeing them. The leak is reported when
// the tests are built with a leak-checking sanitizer.
TEST_F(ConstantBitP_TransferFunctions, leadingZeroesConflictDoesNotLeak)
{
  // x * y is at most 1, so output bit 3 must be zero; it is fixed to one.
  FixedBits x = fromString("0001");
  FixedBits y = fromString("0001");
  FixedBits out = fromString("1***");

  EXPECT_EQ(CONFLICT, useLeadingZeroesToFix(x, y, out));
}

// ---------------------------------------------------------------------------
// Superseded multiply propagators, and the proof that the current ones
// subsume them.
//
// These two functions used to live in ConstantBitP_Multiplication.cpp purely
// so that the current implementations could run them on copies inside
// #ifndef NDEBUG and assert that the new result fixed at least as much. That
// put ~150 lines of dead-in-Release code in the shipped translation unit and
// paid an extra propagator run on every invocation of an assertions build.
//
// The property is real and worth keeping, so both the old implementations and
// the subsumption checks moved here. What changed is *which inputs* the
// property is checked against: the in-line assert saw whatever states real
// formulas drove the propagator into, whereas these tests enumerate the
// input space directly - exhaustively at small widths, randomly at larger
// ones. At any width covered exhaustively that is strictly stronger, since
// every reachable state at that width is among the triples enumerated. Above
// that bound it is a sample rather than a sweep.
// ---------------------------------------------------------------------------

// Superseded by useLeadingZeroesToFix. Bounds the product's leading one by
// the sum of the operands' leading-one positions plus one, and zeroes the
// output bits above it. The current version multiplies out the two largest
// admitted values instead, which is never a weaker bound: with x < 2^(xTop+1)
// and y < 2^(yTop+1) the product is below 2^(xTop+yTop+2), so its leading one
// sits at or below xTop+yTop+1.
Result useLeadingZeroesToFix_OLD(FixedBits& x, FixedBits& y, FixedBits& output)
{
  // Count the leading zeroes on x & y.
  // Output should have about that many..
  int xTop = x.topmostPossibleLeadingOne();
  int yTop = y.topmostPossibleLeadingOne();

  int maxOutputOneFromInputs = xTop + yTop + 1;

  for (int i = output.getWidth() - 1; i > maxOutputOneFromInputs; i--)
    if (!output.isFixed(i))
    {
      output.setFixed(i, true);
      output.setValue(i, false);
    }
    else
    {
      if (output.getValue(i))
        return CONFLICT;
    }

  return NOT_IMPLEMENTED;
}

// Superseded by trailingOneReasoning. Same idea - clear a trailing unfixed
// bit of x that has no support in y and the output - but the scan starts at
// x's minimum trailing-one position and stops at the first bit it cannot
// clear. The current version scans from bit zero.
Result trailingOneReasoning_OLD(FixedBits& x, FixedBits& y, FixedBits& output)
{
  Result r = NO_CHANGE;

  const int bitwidth = output.getWidth();

  const int x_min = x.minimum_trailingOne();
  const int x_max = x.maximum_trailingOne();

  const int y_min = y.minimum_trailingOne();
  const int y_max = y.maximum_trailingOne();

  int output_max = output.maximum_trailingOne();

  bool done = false;
  for (int i = x_min; i <= std::min(x_max, bitwidth - 1); i++)
  {
    if (x[i] == '1')
      break;

    if (x[i] == '0')
      continue;

    assert(!done);
    for (int j = y_min; j <= std::min(y_max, output_max); j++)
    {
      if (j + i >= bitwidth || (y[j] != '0' && output[i + j] != '0'))
      {
        done = true;
        break;
      }
    }
    if (!done)
    {
      x.setFixed(i, true);
      x.setValue(i, false);
      r = CHANGED;
    }
    else
      break;
  }
  return r;
}

// A width-`width` FixedBits with each bit independently unfixed, zero or one,
// then - half the time each - a run of leading bits and a run of trailing
// bits forced to zero.
//
// The bias matters. Both propagators reason about runs of zeroes at the ends
// of an operand, and under a uniform trit draw at width 48 the top bit is
// unfixed or one about two thirds of the time, so the leading-zero reasoning
// has nothing to work with on almost every sample. Without the bias the
// random arm of these tests contributes essentially nothing.
FixedBits randomFixedBits(unsigned width, std::mt19937& rng)
{
  FixedBits result(width, false);
  std::uniform_int_distribution<int> trit(0, 2);
  for (unsigned i = 0; i < width; i++)
  {
    const int t = trit(rng);
    if (t != 0)
    {
      result.setFixed(i, true);
      result.setValue(i, t == 2);
    }
  }

  std::uniform_int_distribution<unsigned> coin(0, 1);
  std::uniform_int_distribution<unsigned> runLength(0, width);

  if (coin(rng) == 1)
  {
    const unsigned lead = runLength(rng);
    for (unsigned i = width - lead; i < width; i++)
    {
      result.setFixed(i, true);
      result.setValue(i, false);
    }
  }

  if (coin(rng) == 1)
  {
    const unsigned trail = std::min(runLength(rng), width);
    for (unsigned i = 0; i < trail; i++)
    {
      result.setFixed(i, true);
      result.setValue(i, false);
    }
  }

  return result;
}

// Widths enumerated exhaustively. 3^4 = 81 assignments per operand, so 81^3
// triples at the top width; going one wider is 27x that.
const unsigned EXHAUSTIVE_UPTO = 4;

// Widths sampled, and how many triples at each.
const unsigned RANDOM_FROM = 5;
const unsigned RANDOM_UPTO = 48;
const unsigned RANDOM_TRIPLES = 3000;

// Run `check` over every (x, y, output) triple at widths 1..EXHAUSTIVE_UPTO,
// then over RANDOM_TRIPLES sampled triples at each larger width.
void forEachTriple(
    const std::function<void(FixedBits&, FixedBits&, FixedBits&)>& check)
{
  for (unsigned width = 1; width <= EXHAUSTIVE_UPTO; width++)
  {
    unsigned combinations = 1;
    for (unsigned i = 0; i < width; i++)
      combinations *= 3;

    for (unsigned i = 0; i < combinations; i++)
      for (unsigned j = 0; j < combinations; j++)
        for (unsigned k = 0; k < combinations; k++)
        {
          FixedBits x = fromTernary(width, i);
          FixedBits y = fromTernary(width, j);
          FixedBits out = fromTernary(width, k);
          check(x, y, out);
          if (::testing::Test::HasFatalFailure())
            return;
        }
  }

  std::mt19937 rng(20240607); // fixed seed: a failure must be reproducible.
  for (unsigned width = RANDOM_FROM; width <= RANDOM_UPTO; width++)
    for (unsigned n = 0; n < RANDOM_TRIPLES; n++)
    {
      FixedBits x = randomFixedBits(width, rng);
      FixedBits y = randomFixedBits(width, rng);
      FixedBits out = randomFixedBits(width, rng);
      check(x, y, out);
      if (::testing::Test::HasFatalFailure())
        return;
    }
}

// trailingOneReasoning must leave trailingOneReasoning_OLD nothing to find,
// and the old reasoning must not mutate its arguments once the new one has
// run. This replaces an assert that ran inside trailingOneReasoning itself.
TEST_F(ConstantBitP_TransferFunctions, trailingOneReasoningSubsumesOld)
{
  // Triples on which the old reasoning fixes something when run first. If
  // this stays at zero the subsumption below holds trivially and the test is
  // worthless, so it is checked at the end. It was 129382 when written; the
  // floor is deliberately far below that so retuning the generator does not
  // turn into a spurious failure.
  unsigned oldFiresAlone = 0;

  forEachTriple([&](FixedBits& x, FixedBits& y, FixedBits& out) {
    FixedBits xa(x), ya(y), outa(out);
    if (trailingOneReasoning_OLD(xa, ya, outa) == CHANGED)
      oldFiresAlone++;

    trailingOneReasoning(x, y, out);

    FixedBits x2(x), y2(y), out2(out);
    const Result old = trailingOneReasoning_OLD(x2, y2, out2);

    ASSERT_EQ(NO_CHANGE, old)
        << "old reasoning fired after new on " << str(x) << " * " << str(y)
        << " = " << str(out);
    ASSERT_TRUE(FixedBits::equals(x, x2))
        << "old reasoning mutated " << str(x) << " to " << str(x2);
  });

  EXPECT_GT(oldFiresAlone, 1000u)
      << "the old reasoning almost never fires on these inputs, so the "
         "subsumption check above is close to vacuous";
}

// useLeadingZeroesToFix must fix at least every bit useLeadingZeroesToFix_OLD
// fixes, and must report CONFLICT whenever the old one does. This replaces
// asserts that ran inside useLeadingZeroesToFix itself.
TEST_F(ConstantBitP_TransferFunctions, leadingZeroesSubsumesOld)
{
  // Triples on which the old version fixes an output bit or reports a
  // conflict. Where it does neither, "the new one fixed at least as much" is
  // trivially true, so the count is checked at the end. It was 23986 when
  // written.
  //
  // This is the reason the check is worth more here than it was as an in-line
  // assert. There the old version ran on states the column reasoning had
  // already saturated: over 11504 invocations of useLeadingZeroesToFix across
  // a 2501-file corpus it fixed a bit on exactly none of them, so the
  // assertion it guarded was vacuous every single time.
  unsigned oldFires = 0;

  forEachTriple([&](FixedBits& x, FixedBits& y, FixedBits& out) {
    FixedBits x_p(x), y_p(y), o_p(out);
    const Result old = useLeadingZeroesToFix_OLD(x_p, y_p, o_p);
    if (old == CONFLICT || !FixedBits::equals(o_p, out))
      oldFires++;

    const Result now = useLeadingZeroesToFix(x, y, out);

    if (old == CONFLICT)
    {
      ASSERT_EQ(CONFLICT, now)
          << "old found a conflict the new one missed on " << str(x_p) << " * "
          << str(y_p) << " = " << str(o_p);
      return; // both bailed early, so neither is at its fixed point.
    }

    if (now == CONFLICT)
      return; // the new one stops mid-scan, as it did when this was an assert.

    ASSERT_TRUE(FixedBits::in(x, x_p))
        << "new fixed less of x: " << str(x) << " vs " << str(x_p);
    ASSERT_TRUE(FixedBits::in(y, y_p))
        << "new fixed less of y: " << str(y) << " vs " << str(y_p);
    ASSERT_TRUE(FixedBits::in(out, o_p))
        << "new fixed less of the output: " << str(out) << " vs " << str(o_p);
  });

  EXPECT_GT(oldFires, 1000u)
      << "the old version almost never fixes anything on these inputs, so "
         "the subsumption check above is close to vacuous";
}

// ---------------------------------------------------------------------------
// Aliased operands.
//
// ConstantBitPropagation::propagate() looks up one FixedBits per node, so a
// node whose child list repeats a node hands the transfer function the same
// pointer twice. These runs pass one shared FixedBits into several operand
// slots and require soundness, the NO_CHANGE contract, the lattice rules and
// the local fixed point - everything except maximal precision, which an
// aliased call has no way to reach.
// ---------------------------------------------------------------------------

// n operand positions, all reading object 0.
Aliasing allSame(unsigned arity)
{
  return Aliasing(arity, 0);
}

// Bounds for the functions that do not settle on one call when their
// operands alias. These are measurements, not targets: propagate() calls the
// function once, so every call past the first is reasoning the solver never
// gets. See the aliased tests below for what each one loses.
const unsigned TWO_CALLS = 2;
const unsigned THREE_CALLS = 3;
const unsigned FOUR_CALLS = 4;

const std::vector<Slot> ONE_BV3(1, Slot{3, false});
const std::vector<Slot> ONE_BOOL(1, Slot{1, true});

// Only bvurem falls short here. x % x is 0 for every non-zero x and x for
// x = 0, so an output with a one bit forces x = 0 and then contradicts
// itself - but only on the second call. 6 of the 729 width-3 states are
// UNSAT that the solver does not see.
TEST_F(ConstantBitP_TransferFunctions, aliasedDivisionsWidth3)
{
  const unsigned mask = 7;
  exhaustiveCheckAliased(
      "bvudiv(x,x)",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvUnsignedDivisionBothWays(children, out, &mgr);
      },
      [](const std::vector<unsigned>& v) {
        return v[1] == 0 ? mask : v[0] / v[1];
      },
      ONE_BV3, allSame(2), out3(), OVERAPPROXIMATES);

  exhaustiveCheckAliased(
      "bvurem(x,x)",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvUnsignedModulusBothWays(children, out, &mgr);
      },
      [](const std::vector<unsigned>& v) {
        return v[1] == 0 ? v[0] : v[0] % v[1];
      },
      ONE_BV3, allSame(2), out3(), OVERAPPROXIMATES, TWO_CALLS, RESULT_IS_VAGUE);

  exhaustiveCheckAliased(
      "bvsdiv(x,x)",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvSignedDivisionBothWays(children, out, &mgr);
      },
      evaluatorSemantics(&mgr, stp::SBVDIV, 3), ONE_BV3, allSame(2), out3(),
      OVERAPPROXIMATES);

  exhaustiveCheckAliased(
      "bvsrem(x,x)",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvSignedRemainderBothWays(children, out, &mgr);
      },
      evaluatorSemantics(&mgr, stp::SBVREM, 3), ONE_BV3, allSame(2), out3(),
      OVERAPPROXIMATES);

  exhaustiveCheckAliased(
      "bvsmod(x,x)",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvSignedModulusBothWays(children, out, &mgr);
      },
      evaluatorSemantics(&mgr, stp::SBVMOD, 3), ONE_BV3, allSame(2), out3(),
      OVERAPPROXIMATES);
}

TEST_F(ConstantBitP_TransferFunctions, aliasedMultiplicationWidth3)
{
  exhaustiveCheckAliased(
      "bvmul(x,x)",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvMultiplyBothWays(children, out, &mgr, NULL);
      },
      [](const std::vector<unsigned>& v) { return (v[0] * v[1]) & 7; },
      ONE_BV3, allSame(2), out3(), OVERAPPROXIMATES, SETTLES_IN_ONE_CALL, RESULT_IS_VAGUE);
}

TEST_F(ConstantBitP_TransferFunctions, aliasedArithmeticWidth3)
{
  exhaustiveCheckAliased(
      "bvadd(x,x)", bvAddBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] + v[1]) & 7; },
      ONE_BV3, allSame(2), out3(), OVERAPPROXIMATES);

  exhaustiveCheckAliased(
      "bvadd(x,x,x)", bvAddBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] + v[1] + v[2]) & 3; },
      std::vector<Slot>(1, Slot{2, false}), allSame(3), Slot{2, false},
      OVERAPPROXIMATES);

  exhaustiveCheckAliased(
      "bvsub(x,x)", bvSubtractBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] - v[1]) & 7; },
      ONE_BV3, allSame(2), out3(), OVERAPPROXIMATES);
}

// x shifted by x: narrowing the shift amount from the output narrows the
// value being shifted, which narrows the amount again. bvLeftShiftBothWays
// iterates when its operands alias, so bvshl settles in one call; before that
// it took two here and, because shlCore snapshots the value and the amount
// separately and writes both back to the one object, up to six by width 31 -
// which is why it iterates rather than running a fixed number of times. See
// aliasedSettlesAtWideWidths, since width 3 badly understates this one.
//
// The two right shifts are unfixed. Both are unreachable in the solver: the
// simplifying node factory rewrites bvlshr(x,x) to zero and bvashr(x,x) to a
// sign extension of x's top bit, so neither shape survives node creation.
// Their bounds below are width-3 measurements. Every state needing an extra
// call is an UNSAT that would be missed: 95/729 for bvlshr, 62/729 for
// bvashr.
TEST_F(ConstantBitP_TransferFunctions, aliasedShiftsWidth3)
{
  exhaustiveCheckAliased(
      "bvshl(x,x)", bvLeftShiftBothWays,
      [](const std::vector<unsigned>& v) {
        return v[1] >= 3 ? 0 : (v[0] << v[1]) & 7;
      },
      ONE_BV3, allSame(2), out3(), OVERAPPROXIMATES, SETTLES_IN_ONE_CALL,
      RESULT_IS_VAGUE);

  exhaustiveCheckAliased(
      "bvlshr(x,x)", bvRightShiftBothWays,
      [](const std::vector<unsigned>& v) {
        return v[1] >= 3 ? 0 : v[0] >> v[1];
      },
      ONE_BV3, allSame(2), out3(), OVERAPPROXIMATES, FOUR_CALLS, RESULT_IS_VAGUE);

  exhaustiveCheckAliased(
      "bvashr(x,x)", bvArithmeticRightShiftBothWays,
      [](const std::vector<unsigned>& v) {
        const unsigned sign = (v[0] >> 2) & 1;
        if (v[1] >= 3)
          return sign ? 7u : 0u;
        const unsigned shifted = v[0] >> v[1];
        return sign ? (shifted | (7u & ~(7u >> v[1]))) : shifted;
      },
      ONE_BV3, allSame(2), out3(), OVERAPPROXIMATES, THREE_CALLS, RESULT_IS_VAGUE);
}

// x < x and x <= x are constants, so an output fixed the wrong way is UNSAT.
// The transfer functions get there, but only on the second call: the first
// narrows x against itself until it is fully fixed, and the contradiction is
// visible only once it is. 12 of the 81 width-3 states per operator.
TEST_F(ConstantBitP_TransferFunctions, aliasedComparisonsWidth3)
{
  const struct
  {
    const char* name;
    Propagator prop;
    std::function<bool(unsigned, unsigned)> cmp;
  } unsignedOps[] = {
      {"bvult(x,x)",
       [](std::vector<FixedBits*>& c, FixedBits& o) {
         return bvLessThanBothWays(c, o);
       },
       [](unsigned a, unsigned b) { return a < b; }},
      {"bvule(x,x)", bvLessThanEqualsBothWays,
       [](unsigned a, unsigned b) { return a <= b; }},
      {"bvugt(x,x)", bvGreaterThanBothWays,
       [](unsigned a, unsigned b) { return a > b; }},
      {"bvuge(x,x)", bvGreaterThanEqualsBothWays,
       [](unsigned a, unsigned b) { return a >= b; }},
  };
  for (const auto& o : unsignedOps)
  {
    const auto cmp = o.cmp;
    exhaustiveCheckAliased(o.name, o.prop,
                           [cmp](const std::vector<unsigned>& v) {
                             return cmp(v[0], v[1]) ? 1u : 0u;
                           },
                           ONE_BV3, allSame(2), boolSlot(), OVERAPPROXIMATES,
                           TWO_CALLS);
  }

  const struct
  {
    const char* name;
    Propagator prop;
    std::function<bool(int, int)> cmp;
  } signedOps[] = {
      {"bvslt(x,x)", bvSignedLessThanBothWays,
       [](int a, int b) { return a < b; }},
      {"bvsle(x,x)", bvSignedLessThanEqualsBothWays,
       [](int a, int b) { return a <= b; }},
      {"bvsgt(x,x)", bvSignedGreaterThanBothWays,
       [](int a, int b) { return a > b; }},
      {"bvsge(x,x)", bvSignedGreaterThanEqualsBothWays,
       [](int a, int b) { return a >= b; }},
  };
  for (const auto& o : signedOps)
  {
    const auto cmp = o.cmp;
    exhaustiveCheckAliased(
        o.name, o.prop,
        [cmp](const std::vector<unsigned>& v) {
          return cmp(asSigned(v[0], 3), asSigned(v[1], 3)) ? 1u : 0u;
        },
        ONE_BV3, allSame(2), boolSlot(), OVERAPPROXIMATES, TWO_CALLS);
  }
}

TEST_F(ConstantBitP_TransferFunctions, aliasedBitwiseWidth3)
{
  exhaustiveCheckAliased(
      "bvand(x,x)", bvAndBothWays,
      [](const std::vector<unsigned>& v) { return v[0] & v[1]; }, ONE_BV3,
      allSame(2), out3(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "bvor(x,x)", bvOrBothWays,
      [](const std::vector<unsigned>& v) { return v[0] | v[1]; }, ONE_BV3,
      allSame(2), out3(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "bvxor(x,x)", bvXorBothWays,
      [](const std::vector<unsigned>& v) { return v[0] ^ v[1]; }, ONE_BV3,
      allSame(2), out3(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "=(x,x)", bvEqualsBothWays,
      [](const std::vector<unsigned>& v) { return v[0] == v[1] ? 1u : 0u; },
      ONE_BV3, allSame(2), boolSlot(), OVERAPPROXIMATES);
}

// and/or/xor/iff all settle on one call even aliased. implies(x,x) is the
// exception: it is a tautology, so a false output is UNSAT, and that takes a
// second call to see.
TEST_F(ConstantBitP_TransferFunctions, aliasedBooleanLogic)
{
  exhaustiveCheckAliased(
      "and(x,x)", bvAndBothWays,
      [](const std::vector<unsigned>& v) { return v[0] & v[1]; }, ONE_BOOL,
      allSame(2), boolSlot(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "and(x,x,x)", bvAndBothWays,
      [](const std::vector<unsigned>& v) { return v[0] & v[1] & v[2]; },
      ONE_BOOL, allSame(3), boolSlot(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "or(x,x)", bvOrBothWays,
      [](const std::vector<unsigned>& v) { return v[0] | v[1]; }, ONE_BOOL,
      allSame(2), boolSlot(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "or(x,x,x)", bvOrBothWays,
      [](const std::vector<unsigned>& v) { return v[0] | v[1] | v[2]; },
      ONE_BOOL, allSame(3), boolSlot(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "xor(x,x)", bvXorBothWays,
      [](const std::vector<unsigned>& v) { return v[0] ^ v[1]; }, ONE_BOOL,
      allSame(2), boolSlot(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "xor(x,x,x)", bvXorBothWays,
      [](const std::vector<unsigned>& v) { return v[0] ^ v[1] ^ v[2]; },
      ONE_BOOL, allSame(3), boolSlot(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "implies(x,x)", bvImpliesBothWays,
      [](const std::vector<unsigned>& v) {
        return (v[0] == 0 || v[1]) ? 1u : 0u;
      },
      ONE_BOOL, allSame(2), boolSlot(), OVERAPPROXIMATES, TWO_CALLS);
  exhaustiveCheckAliased(
      "iff(x,x)", bvEqualsBothWays,
      [](const std::vector<unsigned>& v) { return v[0] == v[1] ? 1u : 0u; },
      ONE_BOOL, allSame(2), boolSlot(), OVERAPPROXIMATES);
}

// ((_ repeat n) x) is exactly this shape, and it is what found the problem.
// A single sweep goes least-significant operand first, so a bit written into
// the shared child through a low operand is not read back out through a high
// one until the next sweep - it cost 2 of the 27 two-operand states and 6 of
// the 81 three-operand ones, as lost precision rather than missed conflicts.
// bvConcatBothWays now sweeps twice when its operands alias, which is always
// enough; aliasedSettlesAtWideWidths checks that at wider widths and arities.
TEST_F(ConstantBitP_TransferFunctions, aliasedConcat)
{
  exhaustiveCheckAliased(
      "concat(x,x)", bvConcatBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] << 1) | v[1]; },
      std::vector<Slot>(1, Slot{1, false}), allSame(2), Slot{2, false},
      OVERAPPROXIMATES);

  exhaustiveCheckAliased(
      "concat(x,x,x)", bvConcatBothWays,
      [](const std::vector<unsigned>& v) {
        return (v[0] << 2) | (v[1] << 1) | v[2];
      },
      std::vector<Slot>(1, Slot{1, false}), allSame(3), out3(),
      OVERAPPROXIMATES);
}

// The two value operands of an ITE can be the same node; the guard cannot be
// aliased with them, it has a different type.
TEST_F(ConstantBitP_TransferFunctions, aliasedITEValuesWidth3)
{
  std::vector<Slot> objs;
  objs.push_back(boolSlot());     // object 0: the guard.
  objs.push_back(Slot{3, false}); // object 1: both value operands.

  Aliasing readsObject;
  readsObject.push_back(0);
  readsObject.push_back(1);
  readsObject.push_back(1);

  exhaustiveCheckAliased(
      "ite(c,x,x)", bvITEBothWays,
      [](const std::vector<unsigned>& v) { return v[0] ? v[1] : v[2]; }, objs,
      readsObject, out3(), OVERAPPROXIMATES);
}

// Partial aliasing: an n-ary node where only some operands share a node,
// which is what the corpus actually shows for BVPLUS. allSame() above covers
// the all-operands case; these cover the mixed one.
TEST_F(ConstantBitP_TransferFunctions, partiallyAliasedNary)
{
  // Two width-2 objects: operands 0 and 2 read object 0, operand 1 reads
  // object 1. So bvadd(x, y, x) and concat(x, y, x).
  std::vector<Slot> objs2(2, Slot{2, false});
  Aliasing xyx;
  xyx.push_back(0);
  xyx.push_back(1);
  xyx.push_back(0);

  exhaustiveCheckAliased(
      "bvadd(x,y,x)", bvAddBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] + v[1] + v[2]) & 3; },
      objs2, xyx, Slot{2, false}, OVERAPPROXIMATES);

  exhaustiveCheckAliased(
      "bvadd(x,x,y)", bvAddBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] + v[1] + v[2]) & 3; },
      objs2, {0, 0, 1}, Slot{2, false}, OVERAPPROXIMATES);

  const std::vector<Slot> objs1(2, Slot{1, false});
  exhaustiveCheckAliased(
      "concat(x,y,x)", bvConcatBothWays,
      [](const std::vector<unsigned>& v) {
        return (v[0] << 2) | (v[1] << 1) | v[2];
      },
      objs1, xyx, out3(), OVERAPPROXIMATES);

  exhaustiveCheckAliased(
      "concat(x,x,y)", bvConcatBothWays,
      [](const std::vector<unsigned>& v) {
        return (v[0] << 2) | (v[1] << 1) | v[2];
      },
      objs1, {0, 0, 1}, out3(), OVERAPPROXIMATES);

  const std::vector<Slot> bools2(2, Slot{1, true});
  exhaustiveCheckAliased(
      "and(x,y,x)", bvAndBothWays,
      [](const std::vector<unsigned>& v) { return v[0] & v[1] & v[2]; },
      bools2, xyx, boolSlot(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "or(x,y,x)", bvOrBothWays,
      [](const std::vector<unsigned>& v) { return v[0] | v[1] | v[2]; },
      bools2, xyx, boolSlot(), OVERAPPROXIMATES);
  exhaustiveCheckAliased(
      "xor(x,y,x)", bvXorBothWays,
      [](const std::vector<unsigned>& v) { return v[0] ^ v[1] ^ v[2]; },
      bools2, xyx, boolSlot(), OVERAPPROXIMATES);

  // bvmul is the other n-ary kind the corpus shows aliased. Above two
  // operands its transfer function does nothing, so this is a no-op check
  // that it stays that way.
  const std::vector<Slot> bv3s(2, Slot{3, false});
  exhaustiveCheckAliased(
      "bvmul(x,y,x)",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvMultiplyBothWays(children, out, &mgr, NULL);
      },
      [](const std::vector<unsigned>& v) { return (v[0] * v[1] * v[2]) & 7; },
      bv3s, xyx, out3(), OVERAPPROXIMATES);
}

// The exhaustive checks above only reach width 3, and for the shifts that is
// far too narrow to be representative: before bvLeftShiftBothWays iterated,
// aliased bvshl needed 2 calls at width 3 but 6 at width 31. This is the
// same settling property at widths the exhaustive sweep cannot reach,
// sampled rather than exhaustive.
TEST_F(ConstantBitP_TransferFunctions, aliasedSettlesAtWideWidths)
{
  auto passes = [](const Propagator& prop, std::vector<FixedBits>& obj,
                   FixedBits& out, const Aliasing& reads) {
    unsigned productive = 0, guard = 0;
    while (true)
    {
      std::vector<FixedBits> before(obj);
      const FixedBits beforeOut(out);
      std::vector<FixedBits*> ch;
      for (unsigned i = 0; i < reads.size(); i++) ch.push_back(&obj[reads[i]]);
      const Result r = prop(ch, out);
      if (r == CONFLICT) { productive++; break; }
      bool moved = !FixedBits::equals(out, beforeOut);
      for (unsigned o = 0; o < obj.size() && !moved; o++)
        moved = !FixedBits::equals(obj[o], before[o]);
      if (!moved) break;
      productive++;
      if (++guard > 200) { productive = 9999; break; }
    }
    return productive;
  };
  uint64_t st = 0x9E3779B97F4A7C15ull;
  auto rnd = [&st]() { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st; };
  auto randomBits = [&](unsigned w, unsigned d) {
    FixedBits b(w, false);
    for (unsigned i = 0; i < w; i++)
      if (rnd() % 100 < d) { b.setFixed(i, true); b.setValue(i, rnd() & 1); }
    return b;
  };
  for (unsigned w : {1u,2u,3u,4u,5u,8u,16u,31u,32u,33u,64u})
  {
    unsigned worst = 0;
    for (unsigned d = 5; d <= 95; d += 10)
      for (unsigned t = 0; t < 4000; t++)
      {
        std::vector<FixedBits> obj{randomBits(w, d)};
        FixedBits out = randomBits(w, d);
        worst = std::max(worst, passes(bvLeftShiftBothWays, obj, out, allSame(2)));
      }
    EXPECT_LE(worst, 1u) << "bvshl(x,x) width " << w;
  }
  for (unsigned k : {2u,3u,4u,8u})
    for (unsigned w : {1u,3u,8u,16u})
    {
      unsigned worst = 0;
      for (unsigned d = 5; d <= 95; d += 10)
        for (unsigned t = 0; t < 2000; t++)
        {
          std::vector<FixedBits> obj{randomBits(w, d)};
          FixedBits out = randomBits(k * w, d);
          worst = std::max(worst, passes(bvConcatBothWays, obj, out, allSame(k)));
        }
      EXPECT_LE(worst, 1u) << "concat x" << k << " width " << w;
    }

  // bvConcatBothWays runs a fixed two sweeps rather than iterating, which
  // rests on every operand holding the full join after the first sweep. That
  // argument does not care whether the aliasing is total or partial, so check
  // a mixed pattern too: concat(x, y, x, y, x).
  Aliasing mixed;
  for (unsigned i = 0; i < 5; i++)
    mixed.push_back(i % 2);
  for (unsigned w : {1u, 3u, 8u})
  {
    unsigned worst = 0;
    for (unsigned d = 5; d <= 95; d += 10)
      for (unsigned t = 0; t < 2000; t++)
      {
        std::vector<FixedBits> obj{randomBits(w, d), randomBits(w, d)};
        FixedBits out = randomBits(5 * w, d);
        worst = std::max(worst, passes(bvConcatBothWays, obj, out, mixed));
      }
    EXPECT_LE(worst, 1u) << "concat(x,y,x,y,x) width " << w;
  }
}

} // namespace

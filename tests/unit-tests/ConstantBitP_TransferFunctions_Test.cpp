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

// Tests of the constant bit propagation transfer functions for
// multiplication, division and modulus. These check three properties:
//
// 1) Soundness: propagation must never exclude a concrete (a, b, output)
//    triple that was consistent with the bits before propagation ran.
// 2) The NO_CHANGE contract: ConstantBitPropagation::propagate() trusts a
//    NO_CHANGE result and skips rescheduling, so a transfer function that
//    returns NO_CHANGE must not have altered any bits.
// 3) The lattice rules: propagation may fix bits, but never unfix them or
//    flip a bit that was already fixed.

#include "extlib-constbv/constantbv.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include <gtest/gtest.h>

#include <functional>
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
Result trailingOneReasoning_OLD(FixedBits& x, FixedBits& y, FixedBits& output);
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
FixedBits fromTernary(unsigned width, unsigned code)
{
  FixedBits result(width, false);
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
// Concrete semantics of the operation being propagated.
typedef std::function<unsigned(unsigned, unsigned)> Semantics;

// Run the propagator on one triple and check soundness, the NO_CHANGE
// contract, and the lattice rules. Returns a description of the first
// problem found, or the empty string.
std::string checkTriple(const Propagator& propagate, const Semantics& op,
                        const FixedBits& a0, const FixedBits& b0,
                        const FixedBits& out0)
{
  FixedBits a(a0), b(b0), out(out0);
  std::vector<FixedBits*> children;
  children.push_back(&a);
  children.push_back(&b);

  const Result result = propagate(children, out);

  std::ostringstream error;
  error << str(a0) << " op " << str(b0) << " = " << str(out0) << " became "
        << str(a) << " op " << str(b) << " = " << str(out) << ": ";

  const unsigned width = a0.getWidth();
  for (unsigned av = 0; av < (1u << width); av++)
  {
    if (!admits(a0, av))
      continue;
    for (unsigned bv = 0; bv < (1u << width); bv++)
    {
      if (!admits(b0, bv))
        continue;
      const unsigned ov = op(av, bv);
      if (!admits(out0, ov))
        continue;

      // (av, bv, ov) was consistent before propagation ran.
      if (result == CONFLICT)
      {
        error << "CONFLICT reported, but " << av << " op " << bv << " = " << ov
              << " is a solution";
        return error.str();
      }
      if (!admits(a, av) || !admits(b, bv) || !admits(out, ov))
      {
        error << "unsoundly excluded the solution " << av << " op " << bv
              << " = " << ov;
        return error.str();
      }
    }
  }

  if (result == NO_CHANGE &&
      !(FixedBits::equals(a, a0) && FixedBits::equals(b, b0) &&
        FixedBits::equals(out, out0)))
  {
    error << "returned NO_CHANGE but altered bits";
    return error.str();
  }

  if (!FixedBits::updateOK(a0, a) || !FixedBits::updateOK(b0, b) ||
      !FixedBits::updateOK(out0, out))
  {
    error << "unfixed or flipped already-fixed bits";
    return error.str();
  }

  return "";
}

// Check every combination of fixed/zero/one bits at the given width.
void exhaustiveCheck(const Propagator& propagate, const Semantics& op,
                     unsigned width)
{
  unsigned combinations = 1;
  for (unsigned i = 0; i < width; i++)
    combinations *= 3;

  std::vector<std::string> errors;
  for (unsigned i = 0; i < combinations && errors.size() < 5; i++)
    for (unsigned j = 0; j < combinations && errors.size() < 5; j++)
      for (unsigned k = 0; k < combinations && errors.size() < 5; k++)
      {
        const std::string e =
            checkTriple(propagate, op, fromTernary(width, i),
                        fromTernary(width, j), fromTernary(width, k));
        if (!e.empty())
          errors.push_back(e);
      }

  std::ostringstream all;
  for (const auto& e : errors)
    all << e << "\n";
  EXPECT_TRUE(errors.empty()) << all.str();
}

class ConstantBitP_TransferFunctions : public ::testing::Test
{
protected:
  ConstantBitP_TransferFunctions() { CONSTANTBV::BitVector_Boot(); }
  stp::STPMgr mgr;
};

// The interval reasoning in bvUnsignedDivisionBothWays computes
// maxQuotient * maxBottom + (maxBottom - 1) to tighten the maximum of the
// numerator. At width 4 with maxQuotient = 5 and maxBottom = 3 that is
// 5 * 3 + 2 = 17, which wraps to 1. The wrapped bound used to clamp the
// numerator's maximum to 1, excluding the valid solution 15 / 3 = 5.
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
  const unsigned width = 3;
  const unsigned mask = (1u << width) - 1;
  exhaustiveCheck(
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvUnsignedDivisionBothWays(children, out, &mgr);
      },
      // SMT-LIB semantics: bvudiv by zero gives all ones.
      [mask](unsigned av, unsigned bv) { return bv == 0 ? mask : av / bv; },
      width);
}

TEST_F(ConstantBitP_TransferFunctions, unsignedModulusExhaustiveWidth3)
{
  const unsigned width = 3;
  exhaustiveCheck(
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvUnsignedModulusBothWays(children, out, &mgr);
      },
      // SMT-LIB semantics: bvurem by zero gives the numerator.
      [](unsigned av, unsigned bv) { return bv == 0 ? av : av % bv; }, width);
}

TEST_F(ConstantBitP_TransferFunctions, multiplicationExhaustiveWidth3)
{
  const unsigned width = 3;
  const unsigned mask = (1u << width) - 1;
  exhaustiveCheck(
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvMultiplyBothWays(children, out, &mgr, NULL);
      },
      [mask](unsigned av, unsigned bv) { return (av * bv) & mask; }, width);
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

// trailingOneReasoning asserts that trailingOneReasoning_OLD finds nothing
// further, calling it on the live operands inside assert(). That is only
// safe if the old reasoning is subsumed by the new and never mutates its
// arguments afterwards. Verify both, exhaustively, at width 3.
TEST_F(ConstantBitP_TransferFunctions, trailingOneReasoningSubsumesOld)
{
  const unsigned width = 3;
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
        trailingOneReasoning(x, y, out);

        FixedBits x2(x), y2(y), out2(out);
        const Result old = trailingOneReasoning_OLD(x2, y2, out2);

        ASSERT_EQ(NO_CHANGE, old)
            << "old reasoning fired after new on " << str(x) << " * " << str(y)
            << " = " << str(out);
        ASSERT_TRUE(FixedBits::equals(x, x2))
            << "old reasoning mutated " << str(x) << " to " << str(x2);
      }
}

} // namespace

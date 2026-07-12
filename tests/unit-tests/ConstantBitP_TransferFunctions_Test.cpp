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
// fixed/unfixed bits for three properties:
//
// 1) Soundness: propagation must never exclude a concrete assignment of the
//    children and output that was consistent with the bits before
//    propagation ran, and CONFLICT is only reported when no assignment
//    remains.
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

// Run the propagator on one case and check soundness, the NO_CHANGE
// contract, and the lattice rules. Returns a description of the first
// problem found, or the empty string.
std::string checkCase(const std::string& opName, const Propagator& propagate,
                      const Semantics& op, const std::vector<FixedBits>& in0,
                      const FixedBits& out0)
{
  std::vector<FixedBits> in(in0);
  FixedBits out(out0);
  std::vector<FixedBits*> children;
  for (auto& c : in)
    children.push_back(&c);

  const Result result = propagate(children, out);

  std::ostringstream error;
  error << opName << "(";
  for (unsigned i = 0; i < in0.size(); i++)
    error << (i ? ", " : "") << str(in0[i]);
  error << ") = " << str(out0) << " became (";
  for (unsigned i = 0; i < in.size(); i++)
    error << (i ? ", " : "") << str(in[i]);
  error << ") = " << str(out) << ": ";

  // Enumerate every concrete assignment of the children.
  const unsigned slots = in0.size();
  std::vector<unsigned> limit(slots);
  unsigned total = 1;
  for (unsigned i = 0; i < slots; i++)
  {
    limit[i] = 1u << in0[i].getWidth();
    total *= limit[i];
  }

  std::vector<unsigned> val(slots);
  for (unsigned code = 0; code < total; code++)
  {
    unsigned c = code;
    bool consistent = true;
    for (unsigned i = 0; i < slots; i++)
    {
      val[i] = c % limit[i];
      c /= limit[i];
      if (!admits(in0[i], val[i]))
      {
        consistent = false;
        break;
      }
    }
    if (!consistent)
      continue;
    const unsigned ov = op(val);
    if (!admits(out0, ov))
      continue;

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
    for (unsigned i = 0; i < slots && !excluded; i++)
      excluded = !admits(in[i], val[i]);
    if (excluded)
    {
      error << "unsoundly excluded the solution (";
      for (unsigned i = 0; i < slots; i++)
        error << (i ? ", " : "") << val[i];
      error << ") -> " << ov;
      return error.str();
    }
  }

  if (result == NO_CHANGE)
  {
    bool changed = !FixedBits::equals(out, out0);
    for (unsigned i = 0; i < slots && !changed; i++)
      changed = !FixedBits::equals(in[i], in0[i]);
    if (changed)
    {
      error << "returned NO_CHANGE but altered bits";
      return error.str();
    }
  }

  bool latticeOK = FixedBits::updateOK(out0, out);
  for (unsigned i = 0; i < slots && latticeOK; i++)
    latticeOK = FixedBits::updateOK(in0[i], in[i]);
  if (!latticeOK)
  {
    error << "unfixed or flipped already-fixed bits";
    return error.str();
  }

  return "";
}

// Check every combination of fixed/zero/one bits over the given operand
// shape. Reports at most the first five problems.
void exhaustiveCheck(const std::string& opName, const Propagator& propagate,
                     const Semantics& op, const std::vector<Slot>& ins,
                     const Slot& outSlot)
{
  const unsigned slots = ins.size();
  std::vector<unsigned> patterns(slots);
  unsigned total = 1;
  for (unsigned i = 0; i < slots; i++)
  {
    patterns[i] = 1;
    for (unsigned j = 0; j < ins[i].width; j++)
      patterns[i] *= 3;
    total *= patterns[i];
  }
  unsigned outPatterns = 1;
  for (unsigned j = 0; j < outSlot.width; j++)
    outPatterns *= 3;
  total *= outPatterns;

  std::vector<std::string> errors;
  for (unsigned code = 0; code < total && errors.size() < 5; code++)
  {
    unsigned c = code;
    std::vector<FixedBits> in;
    in.reserve(slots);
    for (unsigned i = 0; i < slots; i++)
    {
      in.push_back(fromTernary(ins[i].width, c % patterns[i], ins[i].isBoolean));
      c /= patterns[i];
    }
    const FixedBits out = fromTernary(outSlot.width, c, outSlot.isBoolean);

    const std::string e = checkCase(opName, propagate, op, in, out);
    if (!e.empty())
      errors.push_back(e);
  }

  std::ostringstream all;
  for (const auto& e : errors)
    all << e << "\n";
  EXPECT_TRUE(errors.empty()) << all.str();
}

// Interpret an unsigned value of the given width as two's complement.
int asSigned(unsigned value, unsigned width)
{
  return value >= (1u << (width - 1)) ? (int)value - (1 << width) : (int)value;
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
      [mask](const std::vector<unsigned>& v) {
        return v[1] == 0 ? mask : v[0] / v[1];
      },
      bv3(2), out3());
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
      bv3(2), out3());
}

TEST_F(ConstantBitP_TransferFunctions, multiplicationExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvmul",
      [this](std::vector<FixedBits*>& children, FixedBits& out) {
        return bvMultiplyBothWays(children, out, &mgr, NULL);
      },
      [](const std::vector<unsigned>& v) { return (v[0] * v[1]) & 7; },
      bv3(2), out3());
}

TEST_F(ConstantBitP_TransferFunctions, additionExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvadd", bvAddBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] + v[1]) & 7; },
      bv3(2), out3());
}

TEST_F(ConstantBitP_TransferFunctions, additionThreeChildrenExhaustiveWidth2)
{
  exhaustiveCheck(
      "bvadd3",
      bvAddBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] + v[1] + v[2]) & 3; },
      std::vector<Slot>(3, Slot{2, false}), Slot{2, false});
}

TEST_F(ConstantBitP_TransferFunctions, subtractionExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvsub", bvSubtractBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] - v[1]) & 7; },
      bv3(2), out3());
}

TEST_F(ConstantBitP_TransferFunctions, unaryMinusExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvneg", bvUnaryMinusBothWays,
      [](const std::vector<unsigned>& v) { return (0u - v[0]) & 7; }, bv3(1),
      out3());
}

TEST_F(ConstantBitP_TransferFunctions, shiftsExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvshl", bvLeftShiftBothWays,
      [](const std::vector<unsigned>& v) {
        return v[1] >= 3 ? 0 : (v[0] << v[1]) & 7;
      },
      bv3(2), out3());

  exhaustiveCheck(
      "bvlshr", bvRightShiftBothWays,
      [](const std::vector<unsigned>& v) {
        return v[1] >= 3 ? 0 : v[0] >> v[1];
      },
      bv3(2), out3());

  exhaustiveCheck(
      "bvashr", bvArithmeticRightShiftBothWays,
      [](const std::vector<unsigned>& v) {
        const unsigned sign = (v[0] >> 2) & 1;
        if (v[1] >= 3)
          return sign ? 7u : 0u;
        const unsigned shifted = v[0] >> v[1];
        return sign ? (shifted | (7u & ~(7u >> v[1]))) : shifted;
      },
      bv3(2), out3());
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
                    bv3(2), boolSlot());
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
                    bv3(2), boolSlot());
  }
}

TEST_F(ConstantBitP_TransferFunctions, bitwiseExhaustiveWidth3)
{
  exhaustiveCheck(
      "bvand", bvAndBothWays,
      [](const std::vector<unsigned>& v) { return v[0] & v[1]; }, bv3(2),
      out3());
  exhaustiveCheck(
      "bvor", bvOrBothWays,
      [](const std::vector<unsigned>& v) { return v[0] | v[1]; }, bv3(2),
      out3());
  exhaustiveCheck(
      "bvxor", bvXorBothWays,
      [](const std::vector<unsigned>& v) { return v[0] ^ v[1]; }, bv3(2),
      out3());
  exhaustiveCheck(
      "bvnot",
      [](std::vector<FixedBits*>& c, FixedBits& o) {
        return bvNotBothWays(c, o);
      },
      [](const std::vector<unsigned>& v) { return ~v[0] & 7; }, bv3(1),
      out3());
}

TEST_F(ConstantBitP_TransferFunctions, booleanLogicExhaustive)
{
  const std::vector<Slot> two(2, boolSlot());
  const std::vector<Slot> three(3, boolSlot());

  exhaustiveCheck("and", bvAndBothWays,
                  [](const std::vector<unsigned>& v) { return v[0] & v[1]; },
                  two, boolSlot());
  exhaustiveCheck(
      "and3", bvAndBothWays,
      [](const std::vector<unsigned>& v) { return v[0] & v[1] & v[2]; }, three,
      boolSlot());
  exhaustiveCheck("or", bvOrBothWays,
                  [](const std::vector<unsigned>& v) { return v[0] | v[1]; },
                  two, boolSlot());
  exhaustiveCheck(
      "or3", bvOrBothWays,
      [](const std::vector<unsigned>& v) { return v[0] | v[1] | v[2]; }, three,
      boolSlot());
  exhaustiveCheck("xor", bvXorBothWays,
                  [](const std::vector<unsigned>& v) { return v[0] ^ v[1]; },
                  two, boolSlot());
  exhaustiveCheck(
      "xor3", bvXorBothWays,
      [](const std::vector<unsigned>& v) { return v[0] ^ v[1] ^ v[2]; }, three,
      boolSlot());
  exhaustiveCheck(
      "implies", bvImpliesBothWays,
      [](const std::vector<unsigned>& v) { return (v[0] == 0 || v[1]) ? 1u : 0u; },
      two, boolSlot());
  exhaustiveCheck(
      "iff", bvEqualsBothWays,
      [](const std::vector<unsigned>& v) { return v[0] == v[1] ? 1u : 0u; },
      two, boolSlot());
  exhaustiveCheck("not",
                  [](std::vector<FixedBits*>& c, FixedBits& o) {
                    return bvNotBothWays(c, o);
                  },
                  [](const std::vector<unsigned>& v) { return v[0] ^ 1u; },
                  std::vector<Slot>(1, boolSlot()), boolSlot());
}

TEST_F(ConstantBitP_TransferFunctions, equalsExhaustiveWidth3)
{
  exhaustiveCheck(
      "=", bvEqualsBothWays,
      [](const std::vector<unsigned>& v) { return v[0] == v[1] ? 1u : 0u; },
      bv3(2), boolSlot());
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
      out3());
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
      out3());

  exhaustiveCheck(
      "concat3", bvConcatBothWays,
      [](const std::vector<unsigned>& v) {
        return (v[0] << 2) | (v[1] << 1) | v[2];
      },
      std::vector<Slot>(3, Slot{1, false}), out3());
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
                    fromTernary(5, op));
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
          in, fromTernary(5, op));
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
              in, fromTernary(outWidth, op));
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

// trailingOneReasoning checks in debug builds that trailingOneReasoning_OLD
// finds nothing further. That is only safe if the old reasoning is subsumed
// by the new and never mutates its arguments afterwards. Verify both,
// exhaustively, at width 3.
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

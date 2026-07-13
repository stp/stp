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

// Checks the constant bit propagation transfer functions at 100 bits,
// where the bitvectors span several machine words. The exhaustive tests
// stop at width 3, so nothing there reaches the multi-word code paths:
// carries across 32-bit words, CBV arithmetic in the multiplication and
// division reasoning, shift amounts that exceed a word, and the bit scans
// used by the shifts.
//
// Each operand is mostly fixed, with a few unfixed bits placed at the
// machine-word boundaries. That keeps the set of concrete values each
// operand admits small enough to enumerate, and STP's constant evaluator
// provides the reference semantics. Every case is checked for the same
// four properties as the exhaustive tests: soundness, the NO_CHANGE
// contract, the lattice rules, and maximal precision for the functions
// the header documents as maximally precise.

#include "extlib-constbv/constantbv.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include <gtest/gtest.h>

#include <functional>
#include <sstream>
#include <string>
#include <vector>

using namespace simplifier::constantBitP;

namespace
{

const bool MAX_PRECISE = true;
const bool OVERAPPROXIMATES = false;

const unsigned WIDTH = 100;

typedef std::function<Result(std::vector<FixedBits*>&, FixedBits&)> Propagator;

std::string str(const FixedBits& bits)
{
  std::ostringstream s;
  s << bits;
  return s.str();
}

// A 100-bit base value: 'z' is zero, 'w' is the 2^64 word boundary, 's' is
// the sign bit, 'm' is all ones, and 'p' is the alternating pattern 01...01.
stp::CBV baseValue(unsigned width, char kind)
{
  stp::CBV r = CONSTANTBV::BitVector_Create(width, true);
  switch (kind)
  {
    case 'z':
      break;
    case 'w':
      assert(width > 64);
      CONSTANTBV::BitVector_Bit_On(r, 64);
      break;
    case 's':
      CONSTANTBV::BitVector_Bit_On(r, width - 1);
      break;
    case 'm':
      CONSTANTBV::BitVector_Fill(r);
      break;
    case 'p':
      for (unsigned i = 0; i < width; i += 2)
        CONSTANTBV::BitVector_Bit_On(r, i);
      break;
    default:
      assert(false);
  }
  return r;
}

// A mostly-fixed operand: the base value with a few bits left unfixed.
struct WideBits
{
  char base;
  std::vector<unsigned> unfixed;
};

// The unfixed positions sit at the word boundaries (bits 31..33 and
// 63..65), at the bottom, at the sign bit, and spread across the words.
const std::vector<WideBits> widePatterns = {
    {'z', {0, 1}},          // small values
    {'z', {31, 32, 33}},    // unknowns across the first word boundary
    {'m', {63, 64, 65}},    // all ones with holes at the second boundary
    {'s', {98, 99}},        // around the sign bit
    {'p', {0, 32, 64, 99}}, // unknowns spread across all the words
    {'w', {}},              // the constant 2^64
};

std::string describe(const WideBits& wb)
{
  std::ostringstream s;
  s << wb.base << "{";
  for (unsigned i = 0; i < wb.unfixed.size(); i++)
    s << (i ? "," : "") << wb.unfixed[i];
  s << "}";
  return s.str();
}

FixedBits makeBits(unsigned width, const WideBits& wb)
{
  FixedBits result(width, false);
  stp::CBV b = baseValue(width, wb.base);
  for (unsigned i = 0; i < width; i++)
  {
    result.setFixed(i, true);
    result.setValue(i, CONSTANTBV::BitVector_bit_test(b, i) != 0);
  }
  CONSTANTBV::BitVector_Destroy(b);
  for (const unsigned pos : wb.unfixed)
  {
    assert(pos < width);
    result.setFixed(pos, false);
  }
  return result;
}

// A fully fixed operand holding the given value.
FixedBits fixedValue(unsigned width, uint64_t value)
{
  FixedBits result(width, false);
  for (unsigned i = 0; i < width; i++)
  {
    result.setFixed(i, true);
    result.setValue(i, i < 64 && ((value >> i) & 1));
  }
  return result;
}

// A boolean operand: unfixed, or fixed to the given value.
FixedBits boolBits(int choice) // 0 unfixed, 1 false, 2 true.
{
  FixedBits result(1, true);
  if (choice != 0)
  {
    result.setFixed(0, true);
    result.setValue(0, choice == 2);
  }
  return result;
}

// Every concrete value the bits admit. The caller destroys them.
std::vector<stp::CBV> enumerateValues(const FixedBits& bits)
{
  std::vector<unsigned> free;
  for (unsigned i = 0; i < bits.getWidth(); i++)
    if (!bits.isFixed(i))
      free.push_back(i);
  assert(free.size() <= 8); // Keeps the brute force enumerable.

  std::vector<stp::CBV> values;
  for (unsigned mask = 0; mask < (1u << free.size()); mask++)
  {
    stp::CBV v = CONSTANTBV::BitVector_Create(bits.getWidth(), true);
    for (unsigned i = 0; i < bits.getWidth(); i++)
      if (bits.isFixed(i) && bits.getValue(i))
        CONSTANTBV::BitVector_Bit_On(v, i);
    for (unsigned j = 0; j < free.size(); j++)
      if ((mask >> j) & 1)
        CONSTANTBV::BitVector_Bit_On(v, free[j]);
    values.push_back(v);
  }
  return values;
}

// Whether the concrete value is consistent with the fixed bits.
bool admits(const FixedBits& bits, const stp::CBV v)
{
  for (unsigned i = 0; i < bits.getWidth(); i++)
    if (bits.isFixed(i) &&
        bits.getValue(i) != (CONSTANTBV::BitVector_bit_test(v, i) != 0))
      return false;
  return true;
}

// Evaluates the operation on one concrete value per child with the
// solver's constant evaluator. Returns an owned bitvector (of width 1 for
// a boolean result).
stp::CBV evalOp(stp::STPMgr* mgr, stp::Kind kind, unsigned outWidth,
                bool outBool, const std::vector<FixedBits>& in,
                const std::vector<stp::CBV>& values)
{
  stp::ASTVec consts;
  for (unsigned i = 0; i < in.size(); i++)
  {
    if (in[i].isBoolean())
      consts.push_back(CONSTANTBV::BitVector_bit_test(values[i], 0)
                           ? mgr->ASTTrue
                           : mgr->ASTFalse);
    else
      consts.push_back(mgr->CreateBVConst(
          CONSTANTBV::BitVector_Clone(values[i]), in[i].getWidth()));
  }

  const stp::ASTNode op =
      outBool ? mgr->hashingNodeFactory->CreateNode(kind, consts)
              : mgr->hashingNodeFactory->CreateTerm(kind, outWidth, consts);
  const stp::ASTNode evaluated = NonMemberBVConstEvaluator(mgr, op);

  if (evaluated.GetKind() == stp::TRUE || evaluated.GetKind() == stp::FALSE)
  {
    stp::CBV r = CONSTANTBV::BitVector_Create(1, true);
    if (evaluated.GetKind() == stp::TRUE)
      CONSTANTBV::BitVector_Bit_On(r, 0);
    return r;
  }
  return CONSTANTBV::BitVector_Clone(evaluated.GetBVConst());
}

// The output for the children's first admitted values, as fixed bits with
// the given positions unfixed again. Anchoring the output on a real
// solution guarantees the case is satisfiable, so it exercises backward
// propagation into the children.
FixedBits anchoredOutput(stp::STPMgr* mgr, stp::Kind kind, unsigned outWidth,
                         bool outBool, const std::vector<FixedBits>& in,
                         const std::vector<unsigned>& unfixed)
{
  std::vector<stp::CBV> firsts;
  for (const FixedBits& c : in)
  {
    std::vector<stp::CBV> values = enumerateValues(c);
    firsts.push_back(values[0]);
    for (unsigned i = 1; i < values.size(); i++)
      CONSTANTBV::BitVector_Destroy(values[i]);
  }
  stp::CBV ov = evalOp(mgr, kind, outWidth, outBool, in, firsts);
  for (stp::CBV v : firsts)
    CONSTANTBV::BitVector_Destroy(v);

  FixedBits result(outWidth, outBool);
  for (unsigned i = 0; i < outWidth; i++)
  {
    result.setFixed(i, true);
    result.setValue(i, CONSTANTBV::BitVector_bit_test(ov, i) != 0);
  }
  CONSTANTBV::BitVector_Destroy(ov);
  for (const unsigned pos : unfixed)
    if (pos < outWidth)
      result.setFixed(pos, false);
  return result;
}

// Runs the propagator on one case and checks soundness, the NO_CHANGE
// contract, the lattice rules, and (for the maximally precise functions)
// that every bit all the solutions agree on gets fixed. Returns a
// description of the first problem found, or the empty string.
std::string checkWideCase(stp::STPMgr* mgr, const std::string& opName,
                          stp::Kind kind, unsigned outWidth, bool outBool,
                          const Propagator& propagate,
                          const std::vector<FixedBits>& in0,
                          const FixedBits& out0, bool expectPrecise)
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

  const unsigned slots = in0.size();
  std::vector<std::vector<stp::CBV>> childValues;
  for (unsigned i = 0; i < slots; i++)
    childValues.push_back(enumerateValues(in0[i]));

  // The join of the solutions: per operand position, whether some solution
  // has the bit as zero and whether some has it as one.
  bool anySolution = false;
  std::vector<std::vector<char>> seenZero(slots + 1), seenOne(slots + 1);
  for (unsigned i = 0; i < slots; i++)
  {
    seenZero[i].assign(in0[i].getWidth(), 0);
    seenOne[i].assign(in0[i].getWidth(), 0);
  }
  seenZero[slots].assign(outWidth, 0);
  seenOne[slots].assign(outWidth, 0);

  std::string problem;

  // Walk the cartesian product of the child values.
  std::vector<size_t> idx(slots, 0);
  while (problem.empty())
  {
    std::vector<stp::CBV> values;
    for (unsigned i = 0; i < slots; i++)
      values.push_back(childValues[i][idx[i]]);

    stp::CBV ov = evalOp(mgr, kind, outWidth, outBool, in0, values);
    if (admits(out0, ov))
    {
      // This assignment was consistent before propagation ran.
      anySolution = true;
      for (unsigned i = 0; i < slots; i++)
        for (unsigned j = 0; j < in0[i].getWidth(); j++)
          (CONSTANTBV::BitVector_bit_test(values[i], j) ? seenOne : seenZero)
              [i][j] = 1;
      for (unsigned j = 0; j < outWidth; j++)
        (CONSTANTBV::BitVector_bit_test(ov, j) ? seenOne : seenZero)
            [slots][j] = 1;

      if (result == CONFLICT)
      {
        error << "CONFLICT reported, but a solution exists";
        problem = error.str();
      }
      else
      {
        bool excluded = !admits(out, ov);
        for (unsigned i = 0; i < slots && !excluded; i++)
          excluded = !admits(in[i], values[i]);
        if (excluded)
        {
          error << "unsoundly excluded a solution";
          problem = error.str();
        }
      }
    }
    CONSTANTBV::BitVector_Destroy(ov);

    unsigned i = 0;
    for (; i < slots; i++)
    {
      if (++idx[i] < childValues[i].size())
        break;
      idx[i] = 0;
    }
    if (i == slots)
      break;
  }

  for (auto& values : childValues)
    for (stp::CBV v : values)
      CONSTANTBV::BitVector_Destroy(v);
  if (!problem.empty())
    return problem;

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
    for (unsigned i = 0; i <= slots; i++)
    {
      const FixedBits& bits = (i == slots) ? out : in[i];
      for (unsigned j = 0; j < bits.getWidth(); j++)
      {
        if (seenZero[i][j] && seenOne[i][j])
          continue; // The solutions disagree, so the bit can't be fixed.
        if (!bits.isFixed(j))
        {
          error << "not maximally precise: every solution has "
                << (i == slots ? "the output" : "child ")
                << (i == slots ? std::string() : std::to_string(i))
                << " bit " << j << " as " << (seenOne[i][j] ? '1' : '0')
                << ", but it was left unfixed";
          return error.str();
        }
      }
    }
  }

  return "";
}

// Bits of the output to unfix when anchoring: at the word boundaries, so
// backward propagation has to reason across words.
const std::vector<unsigned> outputHoles = {31, 32, 63, 64};

class ConstantBitP_Wide : public ::testing::Test
{
protected:
  ConstantBitP_Wide() { CONSTANTBV::BitVector_Boot(); }
  stp::STPMgr mgr;
  std::vector<std::string> errors;

  void record(const std::string& e)
  {
    if (!e.empty() && errors.size() < 3)
      errors.push_back(e);
  }

  void report()
  {
    std::ostringstream all;
    for (const auto& e : errors)
      all << e << "\n";
    EXPECT_TRUE(errors.empty()) << all.str();
  }

  // A two-child operation at width 100: every pair of operand patterns,
  // with an unconstrained output (forward propagation), a fully known
  // output from a real solution (backward propagation), and a known output
  // with holes at the word boundaries (both directions at once).
  void checkBinary(const std::string& opName, stp::Kind kind,
                   const Propagator& propagate, bool expectPrecise)
  {
    for (const WideBits& p0 : widePatterns)
      for (const WideBits& p1 : widePatterns)
      {
        std::vector<FixedBits> in;
        in.push_back(makeBits(WIDTH, p0));
        in.push_back(makeBits(WIDTH, p1));
        const std::string where =
            " [children " + describe(p0) + " " + describe(p1) + "]";

        record(checkWideCase(&mgr, opName + where, kind, WIDTH, false,
                             propagate, in, FixedBits(WIDTH, false),
                             expectPrecise));
        record(checkWideCase(
            &mgr, opName + where, kind, WIDTH, false, propagate, in,
            anchoredOutput(&mgr, kind, WIDTH, false, in, {}), expectPrecise));
        record(checkWideCase(&mgr, opName + where, kind, WIDTH, false,
                             propagate, in,
                             anchoredOutput(&mgr, kind, WIDTH, false, in,
                                            outputHoles),
                             expectPrecise));
        if (!errors.empty())
        {
          report();
          return;
        }
      }
    report();
  }

  // A predicate at width 100: the output is unfixed, false, or true. The
  // fixed outputs drive backward propagation, and often make the case
  // unsatisfiable, which tests CONFLICT detection.
  void checkPredicate(const std::string& opName, stp::Kind kind,
                      const Propagator& propagate, bool expectPrecise)
  {
    for (const WideBits& p0 : widePatterns)
      for (const WideBits& p1 : widePatterns)
        for (int outChoice = 0; outChoice < 3; outChoice++)
        {
          std::vector<FixedBits> in;
          in.push_back(makeBits(WIDTH, p0));
          in.push_back(makeBits(WIDTH, p1));
          const std::string where = " [children " + describe(p0) + " " +
                                    describe(p1) + " output " +
                                    std::to_string(outChoice) + "]";

          record(checkWideCase(&mgr, opName + where, kind, 1, true, propagate,
                               in, boolBits(outChoice), expectPrecise));
          if (!errors.empty())
          {
            report();
            return;
          }
        }
    report();
  }
};

TEST_F(ConstantBitP_Wide, Addition)
{
  checkBinary("bvadd", stp::BVPLUS, bvAddBothWays, MAX_PRECISE);
}

TEST_F(ConstantBitP_Wide, Subtraction)
{
  checkBinary("bvsub", stp::BVSUB, bvSubtractBothWays, MAX_PRECISE);
}

TEST_F(ConstantBitP_Wide, UnaryMinus)
{
  for (const WideBits& p : widePatterns)
  {
    std::vector<FixedBits> in;
    in.push_back(makeBits(WIDTH, p));
    const std::string where = " [child " + describe(p) + "]";

    record(checkWideCase(&mgr, "bvneg" + where, stp::BVUMINUS, WIDTH, false,
                         bvUnaryMinusBothWays, in, FixedBits(WIDTH, false),
                         MAX_PRECISE));
    record(checkWideCase(&mgr, "bvneg" + where, stp::BVUMINUS, WIDTH, false,
                         bvUnaryMinusBothWays, in,
                         anchoredOutput(&mgr, stp::BVUMINUS, WIDTH, false, in,
                                        outputHoles),
                         MAX_PRECISE));
  }
  report();
}

TEST_F(ConstantBitP_Wide, Bitwise)
{
  checkBinary("bvand", stp::BVAND, bvAndBothWays, MAX_PRECISE);
  checkBinary("bvor", stp::BVOR, bvOrBothWays, MAX_PRECISE);
  checkBinary("bvxor", stp::BVXOR, bvXorBothWays, MAX_PRECISE);

  for (const WideBits& p : widePatterns)
  {
    std::vector<FixedBits> in;
    in.push_back(makeBits(WIDTH, p));
    const std::string where = " [child " + describe(p) + "]";
    const Propagator prop = [](std::vector<FixedBits*>& c, FixedBits& o) {
      return bvNotBothWays(c, o);
    };
    record(checkWideCase(&mgr, "bvnot" + where, stp::BVNOT, WIDTH, false,
                         prop, in, FixedBits(WIDTH, false), MAX_PRECISE));
    record(checkWideCase(&mgr, "bvnot" + where, stp::BVNOT, WIDTH, false,
                         prop, in,
                         anchoredOutput(&mgr, stp::BVNOT, WIDTH, false, in,
                                        outputHoles),
                         MAX_PRECISE));
  }
  report();
}

TEST_F(ConstantBitP_Wide, Multiplication)
{
  const Propagator prop = [this](std::vector<FixedBits*>& c, FixedBits& o) {
    return bvMultiplyBothWays(c, o, &mgr, NULL);
  };
  checkBinary("bvmul", stp::BVMULT, prop, OVERAPPROXIMATES);
}

TEST_F(ConstantBitP_Wide, UnsignedDivision)
{
  const Propagator div = [this](std::vector<FixedBits*>& c, FixedBits& o) {
    return bvUnsignedDivisionBothWays(c, o, &mgr);
  };
  checkBinary("bvudiv", stp::BVDIV, div, OVERAPPROXIMATES);
}

TEST_F(ConstantBitP_Wide, UnsignedModulus)
{
  const Propagator rem = [this](std::vector<FixedBits*>& c, FixedBits& o) {
    return bvUnsignedModulusBothWays(c, o, &mgr);
  };
  checkBinary("bvurem", stp::BVMOD, rem, OVERAPPROXIMATES);
}

TEST_F(ConstantBitP_Wide, SignedDivision)
{
  const Propagator div = [this](std::vector<FixedBits*>& c, FixedBits& o) {
    return bvSignedDivisionBothWays(c, o, &mgr);
  };
  checkBinary("bvsdiv", stp::SBVDIV, div, OVERAPPROXIMATES);
}

TEST_F(ConstantBitP_Wide, SignedRemainder)
{
  const Propagator rem = [this](std::vector<FixedBits*>& c, FixedBits& o) {
    return bvSignedRemainderBothWays(c, o, &mgr);
  };
  checkBinary("bvsrem", stp::SBVREM, rem, OVERAPPROXIMATES);
}

TEST_F(ConstantBitP_Wide, SignedModulus)
{
  const Propagator mod = [this](std::vector<FixedBits*>& c, FixedBits& o) {
    return bvSignedModulusBothWays(c, o, &mgr);
  };
  checkBinary("bvsmod", stp::SBVMOD, mod, OVERAPPROXIMATES);
}

// The shift amount operands cover in-range amounts, the word boundaries,
// out-of-range amounts, and partially unfixed amounts, including one whose
// unfixed bit 90 allows astronomically large shifts.
TEST_F(ConstantBitP_Wide, Shifts)
{
  std::vector<FixedBits> amounts;
  for (const uint64_t v : {0ull, 1ull, 31ull, 32ull, 63ull, 64ull, 99ull,
                           100ull, 1ull << 40})
    amounts.push_back(fixedValue(WIDTH, v));
  amounts.push_back(makeBits(WIDTH, {'z', {0, 1}}));       // 0..3
  amounts.push_back(makeBits(WIDTH, {'z', {5, 6, 90}}));   // maybe huge

  const struct
  {
    const char* name;
    stp::Kind kind;
    Propagator prop;
  } ops[] = {
      {"bvshl", stp::BVLEFTSHIFT, bvLeftShiftBothWays},
      {"bvlshr", stp::BVRIGHTSHIFT, bvRightShiftBothWays},
      {"bvashr", stp::BVSRSHIFT, bvArithmeticRightShiftBothWays},
  };

  for (const auto& op : ops)
  {
    for (const WideBits& p : widePatterns)
      for (unsigned a = 0; a < amounts.size(); a++)
      {
        std::vector<FixedBits> in;
        in.push_back(makeBits(WIDTH, p));
        in.push_back(amounts[a]);
        const std::string where = " [child " + describe(p) + " amount " +
                                  std::to_string(a) + "]";

        record(checkWideCase(&mgr, op.name + where, op.kind, WIDTH, false,
                             op.prop, in, FixedBits(WIDTH, false),
                             MAX_PRECISE));
        record(checkWideCase(&mgr, op.name + where, op.kind, WIDTH, false,
                             op.prop, in,
                             anchoredOutput(&mgr, op.kind, WIDTH, false, in,
                                            outputHoles),
                             MAX_PRECISE));
        if (!errors.empty())
        {
          report();
          return;
        }
      }
  }
  report();
}

TEST_F(ConstantBitP_Wide, Comparisons)
{
  const struct
  {
    const char* name;
    stp::Kind kind;
    Propagator prop;
  } ops[] = {
      {"bvult", stp::BVLT,
       [](std::vector<FixedBits*>& c, FixedBits& o) {
         return bvLessThanBothWays(c, o);
       }},
      {"bvule", stp::BVLE, bvLessThanEqualsBothWays},
      {"bvugt", stp::BVGT, bvGreaterThanBothWays},
      {"bvuge", stp::BVGE, bvGreaterThanEqualsBothWays},
      {"bvslt", stp::BVSLT, bvSignedLessThanBothWays},
      {"bvsle", stp::BVSLE, bvSignedLessThanEqualsBothWays},
      {"bvsgt", stp::BVSGT, bvSignedGreaterThanBothWays},
      {"bvsge", stp::BVSGE, bvSignedGreaterThanEqualsBothWays},
      {"=", stp::EQ, bvEqualsBothWays},
  };
  for (const auto& op : ops)
  {
    checkPredicate(op.name, op.kind, op.prop, MAX_PRECISE);
    if (!errors.empty())
      return;
  }
}

TEST_F(ConstantBitP_Wide, Ite)
{
  for (int condChoice = 0; condChoice < 3; condChoice++)
    for (const WideBits& p0 : widePatterns)
      for (const WideBits& p1 : widePatterns)
      {
        std::vector<FixedBits> in;
        in.push_back(boolBits(condChoice));
        in.push_back(makeBits(WIDTH, p0));
        in.push_back(makeBits(WIDTH, p1));
        const std::string where = " [cond " + std::to_string(condChoice) +
                                  " children " + describe(p0) + " " +
                                  describe(p1) + "]";

        record(checkWideCase(&mgr, "ite" + where, stp::ITE, WIDTH, false,
                             bvITEBothWays, in, FixedBits(WIDTH, false),
                             MAX_PRECISE));
        record(checkWideCase(&mgr, "ite" + where, stp::ITE, WIDTH, false,
                             bvITEBothWays, in,
                             anchoredOutput(&mgr, stp::ITE, WIDTH, false, in,
                                            outputHoles),
                             MAX_PRECISE));
        if (!errors.empty())
        {
          report();
          return;
        }
      }
  report();
}

// Concatenation of 60 and 40 bit children: the join lands away from the
// machine-word boundaries, so the copies inside the propagator straddle
// them.
TEST_F(ConstantBitP_Wide, Concat)
{
  const std::vector<WideBits> highPatterns = {
      {'z', {0, 1}}, {'p', {31, 32, 33}}, {'m', {58, 59}}};
  const std::vector<WideBits> lowPatterns = {
      {'z', {0, 1}}, {'p', {31, 32, 33}}, {'m', {38, 39}}};

  for (const WideBits& p0 : highPatterns)
    for (const WideBits& p1 : lowPatterns)
    {
      std::vector<FixedBits> in;
      in.push_back(makeBits(60, p0));
      in.push_back(makeBits(40, p1));
      const std::string where =
          " [children " + describe(p0) + " " + describe(p1) + "]";

      record(checkWideCase(&mgr, "concat" + where, stp::BVCONCAT, WIDTH,
                           false, bvConcatBothWays, in,
                           FixedBits(WIDTH, false), MAX_PRECISE));
      record(checkWideCase(&mgr, "concat" + where, stp::BVCONCAT, WIDTH,
                           false, bvConcatBothWays, in,
                           anchoredOutput(&mgr, stp::BVCONCAT, WIDTH, false,
                                          in, outputHoles),
                           MAX_PRECISE));
    }
  report();
}

// Extracts whose ranges land on and straddle the word boundaries.
TEST_F(ConstantBitP_Wide, Extract)
{
  const std::vector<std::pair<unsigned, unsigned>> ranges = {
      {70, 30}, {99, 64}, {31, 0}, {64, 63}};

  for (const auto& range : ranges)
    for (const WideBits& p : widePatterns)
    {
      const unsigned outWidth = range.first - range.second + 1;
      std::vector<FixedBits> in;
      in.push_back(makeBits(WIDTH, p));
      in.push_back(fixedValue(32, range.first));
      in.push_back(fixedValue(32, range.second));
      const std::string where = " [child " + describe(p) + " range " +
                                std::to_string(range.first) + ":" +
                                std::to_string(range.second) + "]";

      record(checkWideCase(&mgr, "extract" + where, stp::BVEXTRACT, outWidth,
                           false, bvExtractBothWays, in,
                           FixedBits(outWidth, false), MAX_PRECISE));
      record(checkWideCase(&mgr, "extract" + where, stp::BVEXTRACT, outWidth,
                           false, bvExtractBothWays, in,
                           anchoredOutput(&mgr, stp::BVEXTRACT, outWidth,
                                          false, in, {0, 31}),
                           MAX_PRECISE));
      if (!errors.empty())
      {
        report();
        return;
      }
    }
  report();
}

// Extension from 100 to 128 bits. The second child (the size) is ignored
// by the transfer functions but needed to build the reference node.
TEST_F(ConstantBitP_Wide, Extends)
{
  const unsigned outWidth = 128;
  const struct
  {
    const char* name;
    stp::Kind kind;
    Propagator prop;
  } ops[] = {
      {"sign_extend", stp::BVSX, bvSignExtendBothWays},
      {"zero_extend", stp::BVZX, bvZeroExtendBothWays},
  };

  for (const auto& op : ops)
    for (const WideBits& p : widePatterns)
    {
      std::vector<FixedBits> in;
      in.push_back(makeBits(WIDTH, p));
      in.push_back(fixedValue(32, outWidth));
      const std::string where = " [child " + describe(p) + "]";

      record(checkWideCase(&mgr, op.name + where, op.kind, outWidth, false,
                           op.prop, in, FixedBits(outWidth, false),
                           MAX_PRECISE));
      record(checkWideCase(&mgr, op.name + where, op.kind, outWidth, false,
                           op.prop, in,
                           anchoredOutput(&mgr, op.kind, outWidth, false, in,
                                          {99, 100, 127}),
                           MAX_PRECISE));
      if (!errors.empty())
      {
        report();
        return;
      }
    }
  report();
}

} // namespace

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

// Checks the interval transfer functions at 100 bits, where the bitvectors
// span several machine words. The exhaustive tests cover widths 1 to 4;
// this covers the multi-word code paths (word boundaries, capped shift
// amounts, carries across words) that narrow widths can't reach.
//
// Each child interval is narrow -- at most four values -- and sits at a
// boundary: near zero, across the 2^64 word boundary, across the sign bit,
// or at the top. Narrow intervals keep the brute-force hull computable:
// every concrete value is enumerated and run through STP's constant
// evaluator. The transfer functions classified as perfect must return
// exactly the hull; the over-approximating ones (BVMOD, BVMULT) must
// contain it.

#include "stp/STPManager/STPManager.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include <gtest/gtest.h>
#include <sstream>
#include <string>
#include <vector>

namespace
{

const bool EXACT = true;
const bool OVERAPPROXIMATES = false;

const unsigned WIDTH = 100;

// BitVector_Boot must run before anything allocates constant bitvectors.
struct Boot
{
  Boot() { CONSTANTBV::BitVector_Boot(); }
};

struct Context
{
  Boot boot;
  stp::STPMgr mgr;
  SimplifyingNodeFactory snf;
  stp::UnsignedIntervalAnalysis analysis;

  Context() : snf(*(mgr.hashingNodeFactory), mgr), analysis(mgr)
  {
    mgr.defaultNodeFactory = &snf;
  }
};

// A value near a boundary of the width: 'z' is zero + delta, 'w' is the
// 2^64 word boundary + delta, 's' is the sign bit 2^(width-1) + delta, and
// 'm' is the all-ones maximum + delta (delta <= 0).
stp::CBV boundaryValue(unsigned width, char kind, long delta)
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
    default:
      assert(false);
  }
  for (; delta > 0; delta--)
    CONSTANTBV::BitVector_increment(r);
  for (; delta < 0; delta++)
    CONSTANTBV::BitVector_decrement(r);
  return r;
}

// A narrow interval at a boundary: [kind + lo, kind + hi].
struct WideInterval
{
  char kind;
  long lo, hi;
};

std::string describe(const WideInterval& wi)
{
  std::ostringstream s;
  s << wi.kind << "[" << wi.lo << ".." << wi.hi << "]";
  return s.str();
}

const std::vector<WideInterval> wideIntervals = {
    {'z', 0, 3},  // at the bottom, includes zero
    {'z', 7, 7},  // a small constant
    {'z', 5, 7},  // small, no zero, not constant
    {'w', -2, 1}, // crosses the 2^64 word boundary
    {'s', -2, 1}, // crosses the sign bit
    {'m', -3, 0}, // at the top
};

std::vector<stp::CBV> enumerateValues(unsigned width, const WideInterval& wi)
{
  std::vector<stp::CBV> values;
  for (long d = wi.lo; d <= wi.hi; d++)
    values.push_back(boundaryValue(width, wi.kind, d));
  return values;
}

stp::UnsignedInterval* makeInterval(unsigned width, const WideInterval& wi)
{
  return new stp::UnsignedInterval(boundaryValue(width, wi.kind, wi.lo),
                                   boundaryValue(width, wi.kind, wi.hi));
}

void destroyValues(std::vector<std::vector<stp::CBV>>& childValues)
{
  for (auto& values : childValues)
    for (stp::CBV v : values)
      CONSTANTBV::BitVector_Destroy(v);
}

// Runs the transfer function for n on the given child intervals, computes
// the brute-force hull over the enumerated child values with the constant
// evaluator, and compares. childValues[i] must list every value that
// children[i] allows (a null child is fine as long as its values are
// listed, e.g. an unknown boolean).
void checkHull(Context& c, const stp::ASTNode& n,
               const std::vector<std::vector<stp::CBV>>& childValues,
               std::vector<const stp::UnsignedInterval*>& children,
               bool exact, const std::string& label)
{
  stp::UnsignedInterval* result =
      c.analysis.dispatchToTransferFunctions(n, children);

  const bool isPredicate = (n.GetType() == stp::BOOLEAN_TYPE);

  stp::CBV bruteMin = nullptr;
  stp::CBV bruteMax = nullptr;

  // Walk the cartesian product of the child values.
  std::vector<size_t> idx(childValues.size(), 0);
  while (true)
  {
    stp::ASTVec consts;
    for (unsigned i = 0; i < childValues.size(); i++)
    {
      const stp::CBV v = childValues[i][idx[i]];
      if (n[i].GetType() == stp::BOOLEAN_TYPE)
        consts.push_back(CONSTANTBV::BitVector_bit_test(v, 0) ? c.mgr.ASTTrue
                                                              : c.mgr.ASTFalse);
      else
        consts.push_back(c.mgr.CreateBVConst(CONSTANTBV::BitVector_Clone(v),
                                             n[i].GetValueWidth()));
    }

    const stp::ASTNode op =
        isPredicate
            ? c.mgr.hashingNodeFactory->CreateNode(n.GetKind(), consts)
            : c.mgr.hashingNodeFactory->CreateTerm(n.GetKind(),
                                                   n.GetValueWidth(), consts);
    const stp::ASTNode evaluated = NonMemberBVConstEvaluator(&c.mgr, op);

    stp::CBV value;
    if (evaluated.GetKind() == stp::TRUE ||
        evaluated.GetKind() == stp::FALSE)
    {
      value = CONSTANTBV::BitVector_Create(1, true);
      if (evaluated.GetKind() == stp::TRUE)
        CONSTANTBV::BitVector_Bit_On(value, 0);
    }
    else
      value = CONSTANTBV::BitVector_Clone(evaluated.GetBVConst());

    if (bruteMin == nullptr)
    {
      bruteMin = CONSTANTBV::BitVector_Clone(value);
      bruteMax = CONSTANTBV::BitVector_Clone(value);
    }
    else
    {
      if (CONSTANTBV::BitVector_Lexicompare(value, bruteMin) < 0)
        CONSTANTBV::BitVector_Copy(bruteMin, value);
      if (CONSTANTBV::BitVector_Lexicompare(value, bruteMax) > 0)
        CONSTANTBV::BitVector_Copy(bruteMax, value);
    }
    CONSTANTBV::BitVector_Destroy(value);

    unsigned i = 0;
    for (; i < idx.size(); i++)
    {
      if (++idx[i] < childValues[i].size())
        break;
      idx[i] = 0;
    }
    if (i == idx.size())
      break;
  }

  if (result == nullptr)
  {
    const bool hullComplete = CONSTANTBV::BitVector_is_empty(bruteMin) &&
                              CONSTANTBV::BitVector_is_full(bruteMax);
    EXPECT_TRUE(!exact || hullComplete)
        << label << ": nothing was computed, but the hull isn't complete";
  }
  else
  {
    EXPECT_LE(CONSTANTBV::BitVector_Lexicompare(result->minV, bruteMin), 0)
        << label << ": UNSOUND minimum";
    EXPECT_GE(CONSTANTBV::BitVector_Lexicompare(result->maxV, bruteMax), 0)
        << label << ": UNSOUND maximum";

    if (exact)
    {
      EXPECT_EQ(CONSTANTBV::BitVector_Lexicompare(result->minV, bruteMin), 0)
          << label << ": imprecise minimum";
      EXPECT_EQ(CONSTANTBV::BitVector_Lexicompare(result->maxV, bruteMax), 0)
          << label << ": imprecise maximum";
    }
  }

  CONSTANTBV::BitVector_Destroy(bruteMin);
  CONSTANTBV::BitVector_Destroy(bruteMax);
  delete result;
}

void checkWideBinary(stp::Kind k, bool isPredicate, bool exact)
{
  Context c;

  stp::ASTVec symbols;
  symbols.push_back(c.mgr.CreateSymbol("x", 0, WIDTH));
  symbols.push_back(c.mgr.CreateSymbol("y", 0, WIDTH));
  const stp::ASTNode n =
      isPredicate ? c.mgr.hashingNodeFactory->CreateNode(k, symbols)
                  : c.mgr.hashingNodeFactory->CreateTerm(k, WIDTH, symbols);

  for (const WideInterval& i0 : wideIntervals)
    for (const WideInterval& i1 : wideIntervals)
    {
      std::vector<std::vector<stp::CBV>> childValues = {
          enumerateValues(WIDTH, i0), enumerateValues(WIDTH, i1)};
      std::vector<const stp::UnsignedInterval*> children = {
          makeInterval(WIDTH, i0), makeInterval(WIDTH, i1)};

      checkHull(c, n, childValues, children, exact,
                describe(i0) + " op " + describe(i1));

      destroyValues(childValues);
      for (const auto* ch : children)
        delete ch;
    }
}

void checkWideUnary(stp::Kind k, bool exact)
{
  Context c;

  stp::ASTVec symbols;
  symbols.push_back(c.mgr.CreateSymbol("x", 0, WIDTH));
  const stp::ASTNode n =
      c.mgr.hashingNodeFactory->CreateTerm(k, WIDTH, symbols);

  for (const WideInterval& i0 : wideIntervals)
  {
    std::vector<std::vector<stp::CBV>> childValues = {
        enumerateValues(WIDTH, i0)};
    std::vector<const stp::UnsignedInterval*> children = {
        makeInterval(WIDTH, i0)};

    checkHull(c, n, childValues, children, exact, describe(i0));

    destroyValues(childValues);
    for (const auto* ch : children)
      delete ch;
  }
}

TEST(UnsignedIntervalWide, Udiv)
{
  checkWideBinary(stp::BVDIV, false, EXACT);
}

TEST(UnsignedIntervalWide, Urem)
{
  checkWideBinary(stp::BVMOD, false, OVERAPPROXIMATES);
}

TEST(UnsignedIntervalWide, Plus)
{
  checkWideBinary(stp::BVPLUS, false, EXACT);
}

TEST(UnsignedIntervalWide, Mult)
{
  checkWideBinary(stp::BVMULT, false, OVERAPPROXIMATES);
}

TEST(UnsignedIntervalWide, Bvand)
{
  checkWideBinary(stp::BVAND, false, EXACT);
}

TEST(UnsignedIntervalWide, Bvor)
{
  checkWideBinary(stp::BVOR, false, EXACT);
}

TEST(UnsignedIntervalWide, Bvxor)
{
  checkWideBinary(stp::BVXOR, false, EXACT);
}

TEST(UnsignedIntervalWide, RightShift)
{
  checkWideBinary(stp::BVRIGHTSHIFT, false, EXACT);
}

TEST(UnsignedIntervalWide, LeftShift)
{
  checkWideBinary(stp::BVLEFTSHIFT, false, EXACT);
}

TEST(UnsignedIntervalWide, SignedRightShift)
{
  checkWideBinary(stp::BVSRSHIFT, false, EXACT);
}

TEST(UnsignedIntervalWide, Bvgt)
{
  checkWideBinary(stp::BVGT, true, EXACT);
}

TEST(UnsignedIntervalWide, Bvsgt)
{
  checkWideBinary(stp::BVSGT, true, EXACT);
}

TEST(UnsignedIntervalWide, Eq)
{
  checkWideBinary(stp::EQ, true, EXACT);
}

TEST(UnsignedIntervalWide, Bvnot)
{
  checkWideUnary(stp::BVNOT, EXACT);
}

TEST(UnsignedIntervalWide, Bvuminus)
{
  checkWideUnary(stp::BVUMINUS, EXACT);
}

TEST(UnsignedIntervalWide, Extract)
{
  // Positions chosen to land on and straddle the 32-bit word boundaries.
  const std::vector<std::pair<unsigned, unsigned>> positions = {
      {99, 68}, {95, 32}, {67, 60}, {63, 32}, {31, 0}, {99, 0}};

  for (const auto& position : positions)
  {
    const unsigned hi = position.first;
    const unsigned lo = position.second;
    const unsigned wOut = hi - lo + 1;

    Context c;
    stp::ASTVec symbols;
    symbols.push_back(c.mgr.CreateSymbol("x", 0, WIDTH));
    symbols.push_back(c.mgr.CreateBVConst(32, hi));
    symbols.push_back(c.mgr.CreateBVConst(32, lo));
    const stp::ASTNode n =
        c.mgr.hashingNodeFactory->CreateTerm(stp::BVEXTRACT, wOut, symbols);

    for (const WideInterval& i0 : wideIntervals)
    {
      std::vector<std::vector<stp::CBV>> childValues = {
          enumerateValues(WIDTH, i0),
          {boundaryValue(32, 'z', hi)},
          {boundaryValue(32, 'z', lo)}};
      std::vector<const stp::UnsignedInterval*> children = {
          makeInterval(WIDTH, i0),
          new stp::UnsignedInterval(boundaryValue(32, 'z', hi),
                                    boundaryValue(32, 'z', hi)),
          new stp::UnsignedInterval(boundaryValue(32, 'z', lo),
                                    boundaryValue(32, 'z', lo))};

      std::ostringstream label;
      label << describe(i0) << "[" << hi << ":" << lo << "]";
      checkHull(c, n, childValues, children, EXACT, label.str());

      destroyValues(childValues);
      for (const auto* ch : children)
        delete ch;
    }
  }
}

TEST(UnsignedIntervalWide, Bvsx)
{
  const unsigned wOut = 128;

  Context c;
  stp::ASTVec symbols;
  symbols.push_back(c.mgr.CreateSymbol("x", 0, WIDTH));
  symbols.push_back(c.mgr.CreateBVConst(32, wOut));
  const stp::ASTNode n =
      c.mgr.hashingNodeFactory->CreateTerm(stp::BVSX, wOut, symbols);

  for (const WideInterval& i0 : wideIntervals)
  {
    std::vector<std::vector<stp::CBV>> childValues = {
        enumerateValues(WIDTH, i0), {boundaryValue(32, 'z', wOut)}};
    std::vector<const stp::UnsignedInterval*> children = {
        makeInterval(WIDTH, i0),
        new stp::UnsignedInterval(boundaryValue(32, 'z', wOut),
                                  boundaryValue(32, 'z', wOut))};

    checkHull(c, n, childValues, children, EXACT, describe(i0) + " sx");

    destroyValues(childValues);
    for (const auto* ch : children)
      delete ch;
  }
}

TEST(UnsignedIntervalWide, Concat)
{
  const unsigned lowWidth = 28;

  Context c;
  stp::ASTVec symbols;
  symbols.push_back(c.mgr.CreateSymbol("x", 0, WIDTH));
  symbols.push_back(c.mgr.CreateSymbol("y", 0, lowWidth));
  const stp::ASTNode n = c.mgr.hashingNodeFactory->CreateTerm(
      stp::BVCONCAT, WIDTH + lowWidth, symbols);

  // The 'w' kind needs more than 64 bits, so the low child uses the others.
  const std::vector<WideInterval> lowIntervals = {
      {'z', 0, 3}, {'s', -1, 1}, {'m', -2, 0}};

  for (const WideInterval& i0 : wideIntervals)
    for (const WideInterval& i1 : lowIntervals)
    {
      std::vector<std::vector<stp::CBV>> childValues = {
          enumerateValues(WIDTH, i0), enumerateValues(lowWidth, i1)};
      std::vector<const stp::UnsignedInterval*> children = {
          makeInterval(WIDTH, i0), makeInterval(lowWidth, i1)};

      checkHull(c, n, childValues, children, EXACT,
                describe(i0) + " concat " + describe(i1));

      destroyValues(childValues);
      for (const auto* ch : children)
        delete ch;
    }
}

TEST(UnsignedIntervalWide, Ite)
{
  Context c;
  stp::ASTVec symbols;
  symbols.push_back(c.mgr.CreateSymbol("c", 0, 0));
  symbols.push_back(c.mgr.CreateSymbol("x", 0, WIDTH));
  symbols.push_back(c.mgr.CreateSymbol("y", 0, WIDTH));
  const stp::ASTNode n =
      c.mgr.hashingNodeFactory->CreateTerm(stp::ITE, WIDTH, symbols);

  // Condition alternatives: unknown (null interval, both values), false,
  // true.
  for (unsigned condChoice = 0; condChoice < 3; condChoice++)
    for (const WideInterval& i1 : wideIntervals)
      for (const WideInterval& i2 : wideIntervals)
      {
        std::vector<stp::CBV> condValues;
        if (condChoice == 0 || condChoice == 1)
          condValues.push_back(CONSTANTBV::BitVector_Create(1, true));
        if (condChoice == 0 || condChoice == 2)
        {
          stp::CBV one = CONSTANTBV::BitVector_Create(1, true);
          CONSTANTBV::BitVector_Bit_On(one, 0);
          condValues.push_back(one);
        }

        const stp::UnsignedInterval* cond = nullptr;
        if (condChoice == 1)
          cond = new stp::UnsignedInterval(
              CONSTANTBV::BitVector_Create(1, true),
              CONSTANTBV::BitVector_Create(1, true));
        else if (condChoice == 2)
        {
          stp::CBV lo = CONSTANTBV::BitVector_Create(1, true);
          stp::CBV hi = CONSTANTBV::BitVector_Create(1, true);
          CONSTANTBV::BitVector_Bit_On(lo, 0);
          CONSTANTBV::BitVector_Bit_On(hi, 0);
          cond = new stp::UnsignedInterval(lo, hi);
        }

        std::vector<std::vector<stp::CBV>> childValues = {
            condValues, enumerateValues(WIDTH, i1),
            enumerateValues(WIDTH, i2)};
        std::vector<const stp::UnsignedInterval*> children = {
            cond, makeInterval(WIDTH, i1), makeInterval(WIDTH, i2)};

        std::ostringstream label;
        label << "ite cond" << condChoice << " " << describe(i1) << " "
              << describe(i2);
        checkHull(c, n, childValues, children, EXACT, label.str());

        destroyValues(childValues);
        for (const auto* ch : children)
          delete ch;
      }
}

} // namespace

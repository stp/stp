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

/*
 * Tests of the ValueSet domain:
 *
 * 1) The ValueSet container itself.
 * 2) The transfer functions, on hand-built child sets.
 * 3) The three-way harmonise: enumeration from the bits/interval,
 *    filtering of the set, and (exhaustively at small widths) that the
 *    triple's shared values are preserved exactly and a second call
 *    changes nothing.
 * 4) End to end: equalities of ITE trees over constants are proven
 *    false when the sets are disjoint, and rewritten to selection
 *    conditions when exactly one value is shared.
 */

#include "stp/Simplifier/NodeDomainAnalysis.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/StrengthReduction.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/ValueSet.h"
#include "stp/Simplifier/ValueSetAnalysis.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include <gtest/gtest.h>

using simplifier::constantBitP::FixedBits;

static void boot()
{
  static bool booted = false;
  if (!booted)
  {
    CONSTANTBV::BitVector_Boot();
    booted = true;
  }
}

static stp::CBV makeCBV(unsigned width, unsigned value)
{
  stp::CBV result = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width; i++)
    if ((value >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(result, i);
  return result;
}

static unsigned fromCBV(const stp::CBV v, unsigned width)
{
  unsigned result = 0;
  for (unsigned i = 0; i < width; i++)
    if (CONSTANTBV::BitVector_bit_test(v, i))
      result |= 1u << i;
  return result;
}

// A set holding the given values.
static stp::ValueSet* makeSet(unsigned width, bool isBoolean,
                              const std::vector<unsigned>& values)
{
  stp::ValueSet* result = new stp::ValueSet(width, isBoolean);
  for (unsigned v : values)
    EXPECT_TRUE(result->insert(makeCBV(width, v)));
  return result;
}

// The members as unsigned values, in the stored (ascending) order.
static std::vector<unsigned> members(const stp::ValueSet* set)
{
  std::vector<unsigned> result;
  if (set != nullptr)
    for (const stp::CBV m : set->values)
      result.push_back(fromCBV(m, set->getWidth()));
  return result;
}

struct Context
{
  stp::STPMgr mgr;
  SimplifyingNodeFactory snf;

  Context() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    mgr.defaultNodeFactory = &snf;
  }

  NodeFactory* hashing() { return mgr.hashingNodeFactory; }

  ASTNode symbol(const char* name, unsigned width)
  {
    return mgr.CreateSymbol(name, 0, width);
  }

  ASTNode boolSymbol(const char* name) { return mgr.CreateSymbol(name, 0, 0); }

  ASTNode constant(unsigned width, unsigned value)
  {
    return mgr.CreateBVConst(width, value);
  }

  // Evaluate "n" with the symbols replaced by the constants in "assignment".
  ASTNode eval(const ASTNode& n, stp::ASTNodeMap assignment)
  {
    stp::ASTNodeMap cache;
    ASTNode substituted =
        stp::SubstitutionMap::replace(n, assignment, cache, &snf);
    if (substituted.isConstant())
      return substituted;
    return stp::NonMemberBVConstEvaluator(&mgr, substituted);
  }
};

/////////////////////////////////////////////////////////////////////////////
// The container.
/////////////////////////////////////////////////////////////////////////////

TEST(ValueSet_Test, container_basics)
{
  boot();

  stp::ValueSet set(8, false);

  // Inserted out of order, stored sorted, duplicates coalesce.
  ASSERT_TRUE(set.insert(makeCBV(8, 200)));
  ASSERT_TRUE(set.insert(makeCBV(8, 3)));
  ASSERT_TRUE(set.insert(makeCBV(8, 90)));
  ASSERT_TRUE(set.insert(makeCBV(8, 3)));

  ASSERT_EQ(set.size(), 3u);
  ASSERT_EQ(fromCBV(set.smallest(), 8), 3u);
  ASSERT_EQ(fromCBV(set.largest(), 8), 200u);

  stp::CBV probe = makeCBV(8, 90);
  ASSERT_TRUE(set.in(probe));
  CONSTANTBV::BitVector_Destroy(probe);

  probe = makeCBV(8, 91);
  ASSERT_FALSE(set.in(probe));
  CONSTANTBV::BitVector_Destroy(probe);

  // A 13th distinct value doesn't fit.
  for (unsigned v = 10; v < 19; v++)
    ASSERT_TRUE(set.insert(makeCBV(8, v)));
  ASSERT_EQ(set.size(), stp::ValueSet::MAX_ELEMENTS);
  ASSERT_FALSE(set.insert(makeCBV(8, 19)));
  ASSERT_EQ(set.size(), stp::ValueSet::MAX_ELEMENTS);

  // Re-inserting an existing value still succeeds at capacity.
  ASSERT_TRUE(set.insert(makeCBV(8, 200)));
}

/////////////////////////////////////////////////////////////////////////////
// Transfer functions.
/////////////////////////////////////////////////////////////////////////////

TEST(ValueSet_Test, transfer_pointwise_add)
{
  boot();
  Context c;
  stp::ValueSetAnalysis analysis(c.mgr);

  ASTNode n = c.hashing()->CreateTerm(stp::BVPLUS, 8, c.symbol("x", 8),
                                      c.symbol("y", 8));

  stp::ValueSet* left = makeSet(8, false, {1, 2, 3});
  stp::ValueSet* right = makeSet(8, false, {10, 20});

  stp::ValueSet* result = analysis.dispatchToTransferFunctions(n, {left, right});

  ASSERT_NE(result, nullptr);
  ASSERT_EQ(members(result), std::vector<unsigned>({11, 12, 13, 21, 22, 23}));

  delete left;
  delete right;
  delete result;
}

TEST(ValueSet_Test, transfer_ite)
{
  boot();
  Context c;
  stp::ValueSetAnalysis analysis(c.mgr);

  ASTNode n = c.hashing()->CreateTerm(stp::ITE, 8, c.boolSymbol("p"),
                                      c.symbol("x", 8), c.symbol("y", 8));

  stp::ValueSet* thenSet = makeSet(8, false, {1, 2});
  stp::ValueSet* elseSet = makeSet(8, false, {2, 7});

  // Unknown condition: the union of the branches.
  stp::ValueSet* result =
      analysis.dispatchToTransferFunctions(n, {nullptr, thenSet, elseSet});
  ASSERT_EQ(members(result), std::vector<unsigned>({1, 2, 7}));
  delete result;

  // A condition fixed to true selects the then-branch, even when
  // nothing is known about the other branch.
  stp::ValueSet* trueSet = makeSet(1, true, {1});
  result = analysis.dispatchToTransferFunctions(n, {trueSet, thenSet, nullptr});
  ASSERT_EQ(members(result), std::vector<unsigned>({1, 2}));
  delete result;

  // Unknown condition with an unknown branch: nothing known.
  result = analysis.dispatchToTransferFunctions(n, {nullptr, thenSet, nullptr});
  ASSERT_EQ(result, nullptr);

  delete trueSet;
  delete thenSet;
  delete elseSet;
}

TEST(ValueSet_Test, transfer_widens_past_max_elements)
{
  boot();
  Context c;
  stp::ValueSetAnalysis analysis(c.mgr);

  ASTNode n = c.hashing()->CreateTerm(stp::BVCONCAT, 8, c.symbol("x", 4),
                                      c.symbol("y", 4));

  // 16 distinct results is more than a set can hold.
  stp::ValueSet* left = makeSet(4, false, {0, 1, 2, 3});
  stp::ValueSet* right = makeSet(4, false, {0, 1, 2, 3});

  stp::ValueSet* result = analysis.dispatchToTransferFunctions(n, {left, right});
  ASSERT_EQ(result, nullptr);

  delete left;
  delete right;
}

TEST(ValueSet_Test, transfer_respects_product_cap)
{
  boot();
  Context c;
  stp::ValueSetAnalysis analysis(c.mgr);

  ASTVec children = {c.symbol("x", 8), c.symbol("y", 8), c.symbol("z", 8)};
  ASTNode n = c.hashing()->CreateTerm(stp::BVPLUS, 8, children);

  // 6*6*6 = 216 combinations exceeds the evaluation cap, even though
  // the result would collapse to few values.
  stp::ValueSet* a = makeSet(8, false, {0, 1, 2, 3, 4, 5});
  stp::ValueSet* b = makeSet(8, false, {0, 1, 2, 3, 4, 5});
  stp::ValueSet* d = makeSet(8, false, {0, 1, 2, 3, 4, 5});

  stp::ValueSet* result = analysis.dispatchToTransferFunctions(n, {a, b, d});
  ASSERT_EQ(result, nullptr);

  delete a;
  delete b;
  delete d;
}

TEST(ValueSet_Test, transfer_skips_kinds_without_an_evaluator)
{
  boot();
  Context c;
  stp::ValueSetAnalysis analysis(c.mgr);

  ASSERT_FALSE(stp::ValueSetAnalysis::constEvaluable(stp::BVXNOR));

  ASTNode n = c.hashing()->CreateTerm(stp::BVXNOR, 8, c.symbol("x", 8),
                                      c.symbol("y", 8));

  stp::ValueSet* left = makeSet(8, false, {1});
  stp::ValueSet* right = makeSet(8, false, {2});

  stp::ValueSet* result = analysis.dispatchToTransferFunctions(n, {left, right});
  ASSERT_EQ(result, nullptr);

  delete left;
  delete right;
}

TEST(ValueSet_Test, transfer_division_by_zero)
{
  boot();
  Context c;
  stp::ValueSetAnalysis analysis(c.mgr);

  stp::ValueSet* left = makeSet(4, false, {5});
  stp::ValueSet* right = makeSet(4, false, {0, 2});

  // 5 bvudiv 0 is all ones; 5 bvurem 0 is 5.
  ASTNode div = c.hashing()->CreateTerm(stp::BVDIV, 4, c.symbol("x", 4),
                                        c.symbol("y", 4));
  stp::ValueSet* result = analysis.dispatchToTransferFunctions(div, {left, right});
  ASSERT_EQ(members(result), std::vector<unsigned>({2, 15}));
  delete result;

  ASTNode mod = c.hashing()->CreateTerm(stp::BVMOD, 4, c.symbol("x", 4),
                                        c.symbol("y", 4));
  result = analysis.dispatchToTransferFunctions(mod, {left, right});
  ASSERT_EQ(members(result), std::vector<unsigned>({1, 5}));
  delete result;

  delete left;
  delete right;
}

TEST(ValueSet_Test, transfer_comparison_of_disjoint_sets)
{
  boot();
  Context c;
  stp::ValueSetAnalysis analysis(c.mgr);

  ASTNode n = c.hashing()->CreateNode(stp::EQ, c.symbol("x", 8),
                                      c.symbol("y", 8));

  stp::ValueSet* left = makeSet(8, false, {8, 9});
  stp::ValueSet* right = makeSet(8, false, {7, 10});

  stp::ValueSet* result = analysis.dispatchToTransferFunctions(n, {left, right});
  ASSERT_NE(result, nullptr);
  ASSERT_TRUE(result->isBoolean());
  ASSERT_EQ(members(result), std::vector<unsigned>({0}));

  delete left;
  delete right;
  delete result;
}

/////////////////////////////////////////////////////////////////////////////
// Three-way harmonise.
/////////////////////////////////////////////////////////////////////////////

TEST(ValueSet_Test, harmonise_enumerates_small_intervals)
{
  boot();
  Context c;
  stp::NodeDomainAnalysis domain(&c.mgr);

  // [3,5] has three values: they become the set.
  {
    FixedBits* bits = nullptr;
    stp::UnsignedInterval* interval =
        new stp::UnsignedInterval(makeCBV(8, 3), makeCBV(8, 5));
    stp::ValueSet* set = nullptr;

    domain.harmonise(bits, interval, set, 8, false);
    ASSERT_EQ(members(set), std::vector<unsigned>({3, 4, 5}));

    // Idempotent.
    domain.harmonise(bits, interval, set, 8, false);
    ASSERT_EQ(members(set), std::vector<unsigned>({3, 4, 5}));

    delete bits;
    delete interval;
    delete set;
  }

  // The full interval has far too many values.
  {
    FixedBits* bits = nullptr;
    stp::UnsignedInterval* interval =
        new stp::UnsignedInterval(makeCBV(8, 0), makeCBV(8, 255));
    stp::ValueSet* set = nullptr;

    domain.harmonise(bits, interval, set, 8, false);
    ASSERT_EQ(set, nullptr);

    delete bits;
    delete interval;
  }

  // An interval ending at the maximum value doesn't wrap around.
  {
    FixedBits* bits = nullptr;
    stp::UnsignedInterval* interval =
        new stp::UnsignedInterval(makeCBV(8, 252), makeCBV(8, 255));
    stp::ValueSet* set = nullptr;

    domain.harmonise(bits, interval, set, 8, false);
    ASSERT_EQ(members(set), std::vector<unsigned>({252, 253, 254, 255}));

    delete bits;
    delete interval;
    delete set;
  }

  // Fixed bits cut a wide interval down to few enough values.
  {
    FixedBits* bits = new FixedBits(8, false);
    for (unsigned i = 3; i < 8; i++)
    {
      bits->setFixed(i, true);
      bits->setValue(i, false);
    }
    stp::UnsignedInterval* interval =
        new stp::UnsignedInterval(makeCBV(8, 0), makeCBV(8, 255));
    stp::ValueSet* set = nullptr;

    domain.harmonise(bits, interval, set, 8, false);
    ASSERT_EQ(members(set),
              std::vector<unsigned>({0, 1, 2, 3, 4, 5, 6, 7}));

    delete bits;
    delete interval;
    delete set;
  }
}

TEST(ValueSet_Test, harmonise_filters_and_tightens)
{
  boot();
  Context c;
  stp::NodeDomainAnalysis domain(&c.mgr);

  FixedBits* bits = nullptr;
  stp::UnsignedInterval* interval =
      new stp::UnsignedInterval(makeCBV(8, 4), makeCBV(8, 10));
  stp::ValueSet* set = makeSet(8, false, {1, 5, 9});

  domain.harmonise(bits, interval, set, 8, false);

  // 1 is outside the interval; the survivors are {5, 9}.
  ASSERT_EQ(members(set), std::vector<unsigned>({5, 9}));

  // The interval becomes the set's hull.
  ASSERT_EQ(fromCBV(interval->minV, 8), 5u);
  ASSERT_EQ(fromCBV(interval->maxV, 8), 9u);

  // 5 is 0101 and 9 is 1001: bits 0 and 1 agree.
  ASSERT_NE(bits, nullptr);
  ASSERT_TRUE(bits->isFixed(0) && bits->getValue(0));
  ASSERT_TRUE(bits->isFixed(1) && !bits->getValue(1));

  delete bits;
  delete interval;
  delete set;
}

// Base-3 encoding: digit 0=unfixed, 1=fixed-to-zero, 2=fixed-to-one.
static FixedBits bitsFromTernary(unsigned width, unsigned config)
{
  FixedBits b(width, false);
  for (unsigned i = 0; i < width; i++)
  {
    const unsigned digit = config % 3;
    config /= 3;
    if (digit == 0)
      b.setFixed(i, false);
    else
    {
      b.setFixed(i, true);
      b.setValue(i, digit == 2);
    }
  }
  return b;
}

static bool bitsContain(const FixedBits& b, unsigned v)
{
  for (unsigned i = 0; i < b.getWidth(); i++)
    if (b.isFixed(i) && b.getValue(i) != (((v >> i) & 1) != 0))
      return false;
  return true;
}

// All three domains trimmed to exactly their shared values, and a
// second call changes nothing. Exhaustive over every combination of
// fixed bits, interval and set at small widths.
TEST(ValueSet_Test, harmonise_threeway_exhaustive)
{
  boot();
  Context c;
  stp::NodeDomainAnalysis domain(&c.mgr);

  for (unsigned width = 1; width <= 3; width++)
  {
    unsigned configs = 1;
    for (unsigned i = 0; i < width; i++)
      configs *= 3;
    const unsigned values = 1u << width;

    for (unsigned config = 0; config < configs; config++)
    {
      const FixedBits pattern = bitsFromTernary(width, config);

      for (unsigned lo = 0; lo < values; lo++)
        for (unsigned hi = lo; hi < values; hi++)
          for (unsigned mask = 1; mask < (1u << values); mask++)
          {
            // The values every domain admits. Sound domains always
            // share the node's real values, so harmonise requires a
            // non-empty intersection; skip the impossible inputs.
            // (The pairwise bits/interval intersection can't be empty
            // when the triple's isn't.)
            std::vector<bool> shared(values);
            bool anyShared = false;
            for (unsigned v = 0; v < values; v++)
            {
              shared[v] = bitsContain(pattern, v) && v >= lo && v <= hi &&
                          ((mask >> v) & 1);
              anyShared |= shared[v];
            }
            bool pairShared = false;
            for (unsigned v = 0; v < values; v++)
              pairShared |= bitsContain(pattern, v) && v >= lo && v <= hi;
            if (!anyShared || !pairShared)
              continue;

            FixedBits* bits = new FixedBits(pattern);
            stp::UnsignedInterval* interval = new stp::UnsignedInterval(
                makeCBV(width, lo), makeCBV(width, hi));
            std::vector<unsigned> setValues;
            for (unsigned v = 0; v < values; v++)
              if ((mask >> v) & 1)
                setValues.push_back(v);
            stp::ValueSet* set = makeSet(width, false, setValues);

            domain.harmonise(bits, interval, set, width, false);

            // The set is exactly the shared values (they always fit at
            // these widths), except that a set holding every value
            // carries no information and becomes null.
            std::vector<unsigned> expected;
            for (unsigned v = 0; v < values; v++)
              if (shared[v])
                expected.push_back(v);

            if (expected.size() == values)
              ASSERT_EQ(set, nullptr)
                  << "width " << width << " config " << config << " [" << lo
                  << "," << hi << "] mask " << mask;
            else
              ASSERT_EQ(members(set), expected)
                  << "width " << width << " config " << config << " [" << lo
                  << "," << hi << "] mask " << mask;

            // The interval is the shared values' hull, or null when
            // that spans everything.
            if (expected.front() == 0 && expected.back() == values - 1)
              ASSERT_EQ(interval, nullptr);
            else
            {
              ASSERT_NE(interval, nullptr);
              ASSERT_EQ(fromCBV(interval->minV, width), expected.front());
              ASSERT_EQ(fromCBV(interval->maxV, width), expected.back());
            }

            // A bit is fixed exactly when every shared value agrees.
            for (unsigned i = 0; i < width; i++)
            {
              bool anyZero = false, anyOne = false;
              for (unsigned v : expected)
                (((v >> i) & 1) ? anyOne : anyZero) = true;

              const bool fixed =
                  bits != nullptr && bits->isFixed(i);
              ASSERT_EQ(fixed, !(anyZero && anyOne));
              if (fixed)
              {
                ASSERT_EQ(bits->getValue(i), anyOne);
              }
            }

            // Idempotent: a second call changes nothing.
            const std::vector<unsigned> setBefore = members(set);
            const bool setWasNull = set == nullptr;
            FixedBits bitsBefore =
                (bits != nullptr) ? *bits : FixedBits(width, false);
            const bool bitsWereNull = bits == nullptr;
            const bool intervalWasNull = interval == nullptr;
            const unsigned minBefore =
                intervalWasNull ? 0 : fromCBV(interval->minV, width);
            const unsigned maxBefore =
                intervalWasNull ? 0 : fromCBV(interval->maxV, width);

            domain.harmonise(bits, interval, set, width, false);

            ASSERT_EQ(set == nullptr, setWasNull);
            ASSERT_EQ(members(set), setBefore);
            ASSERT_EQ(bits == nullptr, bitsWereNull);
            if (bits != nullptr)
            {
              ASSERT_TRUE(FixedBits::equals(*bits, bitsBefore));
            }
            ASSERT_EQ(interval == nullptr, intervalWasNull);
            if (interval != nullptr)
            {
              ASSERT_EQ(fromCBV(interval->minV, width), minBefore);
              ASSERT_EQ(fromCBV(interval->maxV, width), maxBefore);
            }

            delete bits;
            delete interval;
            delete set;
          }
    }
  }
}

/////////////////////////////////////////////////////////////////////////////
// End to end.
/////////////////////////////////////////////////////////////////////////////

// The requested example: (ite p 8 9) = (ite q 7 10). The sets {8,9} and
// {7,10} are disjoint, so the equality is false.
TEST(ValueSet_Test, disjoint_ite_equality_is_false)
{
  boot();
  Context c;
  stp::NodeDomainAnalysis domain(&c.mgr);

  const unsigned width = 20;
  ASTNode left = c.hashing()->CreateTerm(stp::ITE, width, c.boolSymbol("p"),
                                         c.constant(width, 8),
                                         c.constant(width, 9));
  ASTNode right = c.hashing()->CreateTerm(stp::ITE, width, c.boolSymbol("q"),
                                          c.constant(width, 7),
                                          c.constant(width, 10));
  ASTNode eq = c.hashing()->CreateNode(stp::EQ, left, right);

  domain.buildMap(eq);

  const stp::ValueSet* eqSet = (*domain.getValueSetMap())[eq];
  ASSERT_EQ(members(eqSet), std::vector<unsigned>({0}));

  FixedBits* eqBits = (*domain.getCbitMap())[eq];
  ASSERT_NE(eqBits, nullptr);
  ASSERT_TRUE(eqBits->isFixed(0) && !eqBits->getValue(0));

  stp::StrengthReduction sr(&c.snf, &c.mgr.UserFlags);
  ASSERT_EQ(sr.topLevel(eq, domain), c.mgr.ASTFalse);
}

// A disjoint pair that neither the fixed bits nor the interval can
// prove apart: {1,6} vs {2,5} fix no bits and the hulls overlap. Only
// the sets show the equality is false.
TEST(ValueSet_Test, disjoint_equality_only_the_sets_prove)
{
  boot();
  Context c;
  stp::NodeDomainAnalysis domain(&c.mgr);

  const unsigned width = 8;
  ASTNode left = c.hashing()->CreateTerm(stp::ITE, width, c.boolSymbol("p"),
                                         c.constant(width, 1),
                                         c.constant(width, 6));
  ASTNode right = c.hashing()->CreateTerm(stp::ITE, width, c.boolSymbol("q"),
                                          c.constant(width, 2),
                                          c.constant(width, 5));
  ASTNode eq = c.hashing()->CreateNode(stp::EQ, left, right);

  domain.buildMap(eq);

  // The low bits carry no information: 1/6 and 2/5 disagree on all of
  // them (the sets do fix the high bits to zero, identically on both
  // sides, which cannot separate the terms either).
  for (unsigned i = 0; i < 3; i++)
  {
    ASSERT_FALSE((*domain.getCbitMap())[left]->isFixed(i));
    ASSERT_FALSE((*domain.getCbitMap())[right]->isFixed(i));
  }

  ASSERT_EQ(members((*domain.getValueSetMap())[eq]),
            std::vector<unsigned>({0}));

  stp::StrengthReduction sr(&c.snf, &c.mgr.UserFlags);
  ASSERT_EQ(sr.topLevel(eq, domain), c.mgr.ASTFalse);
}

// Exactly one value shared: the equality becomes the conjunction of
// "each side selects the shared value", checked equivalent on every
// assignment.
TEST(ValueSet_Test, single_common_value_rewrites_to_selection)
{
  boot();
  Context c;
  stp::NodeDomainAnalysis domain(&c.mgr);

  const unsigned width = 8;
  ASTNode p = c.boolSymbol("p");
  ASTNode q = c.boolSymbol("q");
  ASTNode left = c.hashing()->CreateTerm(stp::ITE, width, p,
                                         c.constant(width, 8),
                                         c.constant(width, 9));
  ASTNode right = c.hashing()->CreateTerm(stp::ITE, width, q,
                                          c.constant(width, 9),
                                          c.constant(width, 10));
  ASTNode eq = c.hashing()->CreateNode(stp::EQ, left, right);

  stp::StrengthReduction sr(&c.snf, &c.mgr.UserFlags);
  ASTNode result = sr.topLevel(eq, domain);

  // Rewritten away from an equality of ITE trees.
  ASSERT_NE(result, eq);
  ASSERT_NE(result.GetKind(), stp::EQ);

  // Equivalent under all four assignments.
  for (unsigned pv = 0; pv <= 1; pv++)
    for (unsigned qv = 0; qv <= 1; qv++)
    {
      stp::ASTNodeMap assignment;
      assignment.insert({p, pv ? c.mgr.ASTTrue : c.mgr.ASTFalse});
      assignment.insert({q, qv ? c.mgr.ASTTrue : c.mgr.ASTFalse});
      ASSERT_EQ(c.eval(eq, assignment), c.eval(result, assignment))
          << "differ on p=" << pv << " q=" << qv;
    }
}

// The split doesn't need the sides to be ITE trees over constants: any
// term with a known value set qualifies. Here the right side is an
// addition, which only the sets pin down to two values.
TEST(ValueSet_Test, single_common_value_splits_non_ite_terms)
{
  boot();
  Context c;
  stp::NodeDomainAnalysis domain(&c.mgr);

  const unsigned width = 8;
  ASTNode p = c.boolSymbol("p");
  ASTNode q = c.boolSymbol("q");
  ASTNode left = c.hashing()->CreateTerm(stp::ITE, width, p,
                                         c.constant(width, 8),
                                         c.constant(width, 9));
  // ite(q, 8, 9) + 1, so {9, 10}: shares just 9 with the left side.
  ASTNode right = c.hashing()->CreateTerm(
      stp::BVPLUS, width,
      c.hashing()->CreateTerm(stp::ITE, width, q, c.constant(width, 8),
                              c.constant(width, 9)),
      c.constant(width, 1));
  ASTNode eq = c.hashing()->CreateNode(stp::EQ, left, right);

  stp::StrengthReduction sr(&c.snf, &c.mgr.UserFlags);
  ASTNode result = sr.topLevel(eq, domain);

  ASSERT_NE(result, eq);
  ASSERT_NE(result.GetKind(), stp::EQ);

  // Equivalent under all four assignments.
  for (unsigned pv = 0; pv <= 1; pv++)
    for (unsigned qv = 0; qv <= 1; qv++)
    {
      stp::ASTNodeMap assignment;
      assignment.insert({p, pv ? c.mgr.ASTTrue : c.mgr.ASTFalse});
      assignment.insert({q, qv ? c.mgr.ASTTrue : c.mgr.ASTFalse});
      ASSERT_EQ(c.eval(eq, assignment), c.eval(result, assignment))
          << "differ on p=" << pv << " q=" << qv;
    }
}

// A node whose interval spans more values than a set can hold gets no
// set, while the interval information is kept.
TEST(ValueSet_Test, widens_when_the_interval_is_too_big)
{
  boot();
  Context c;
  stp::NodeDomainAnalysis domain(&c.mgr);

  const unsigned width = 8;
  // x bvurem 21 is within [0, 20]: 21 values, too many for a set.
  ASTNode n = c.hashing()->CreateTerm(stp::BVMOD, width, c.symbol("x", width),
                                      c.constant(width, 21));

  domain.buildMap(n);

  ASSERT_EQ((*domain.getValueSetMap())[n], nullptr);

  const stp::UnsignedInterval* interval = (*domain.getIntervalMap())[n];
  ASSERT_NE(interval, nullptr);
  ASSERT_EQ(fromCBV(interval->maxV, width), 20u);
}

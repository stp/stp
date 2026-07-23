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

// Unit tests for the UnsignedIntervalSet container: the sorted/disjoint
// invariant, union of overlapping and adjacent intervals, collapse to the
// cap by joining the smallest gap first, and (exhaustively at small width)
// soundness -- the set always contains every value ever inserted.

#include "stp/Simplifier/UnsignedIntervalSet.h"
#include "stp/Simplifier/constantBitP/MersenneTwister.h"
#include <gtest/gtest.h>
#include <set>
#include <vector>

namespace
{

struct Boot
{
  Boot() { CONSTANTBV::BitVector_Boot(); }
};
Boot boot;

stp::CBV makeCBV(unsigned width, uint64_t value)
{
  stp::CBV r = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width && i < 64; i++)
    if ((value >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(r, i);
  return r;
}

uint64_t cbvValue(const stp::CBV c, unsigned width)
{
  return *c & (width >= 64 ? ~0ull : ((1ull << width) - 1));
}

// Adds [lo, hi] and keeps ownership tidy.
void add(stp::UnsignedIntervalSet& s, unsigned width, uint64_t lo, uint64_t hi)
{
  stp::CBV a = makeCBV(width, lo);
  stp::CBV b = makeCBV(width, hi);
  s.addInterval(a, b);
  CONSTANTBV::BitVector_Destroy(a);
  CONSTANTBV::BitVector_Destroy(b);
}

bool contains(const stp::UnsignedIntervalSet& s, unsigned width, uint64_t v)
{
  stp::CBV c = makeCBV(width, v);
  bool r = s.in(c);
  CONSTANTBV::BitVector_Destroy(c);
  return r;
}

// The concrete membership implied by the current parts, as a value set.
std::set<uint64_t> concretise(const stp::UnsignedIntervalSet& s, unsigned width)
{
  std::set<uint64_t> out;
  for (const auto* p : s.parts)
  {
    uint64_t lo = cbvValue(p->minV, width);
    uint64_t hi = cbvValue(p->maxV, width);
    for (uint64_t v = lo; v <= hi; v++)
      out.insert(v);
  }
  return out;
}

TEST(UnsignedIntervalSet, single)
{
  stp::UnsignedIntervalSet s(6, 4);
  add(s, 6, 3, 7);
  EXPECT_EQ(1u, s.size());
  EXPECT_FALSE(contains(s, 6, 2));
  EXPECT_TRUE(contains(s, 6, 3));
  EXPECT_TRUE(contains(s, 6, 7));
  EXPECT_FALSE(contains(s, 6, 8));
  s.checkInvariant();
}

TEST(UnsignedIntervalSet, disjointStaySeparate)
{
  stp::UnsignedIntervalSet s(6, 4);
  add(s, 6, 0, 1);
  add(s, 6, 10, 12);
  add(s, 6, 20, 20);
  EXPECT_EQ(3u, s.size());
  EXPECT_FALSE(contains(s, 6, 5));
  EXPECT_FALSE(contains(s, 6, 15));
  s.checkInvariant();
}

TEST(UnsignedIntervalSet, overlappingMerge)
{
  stp::UnsignedIntervalSet s(6, 4);
  add(s, 6, 3, 7);
  add(s, 6, 6, 10);
  EXPECT_EQ(1u, s.size());
  EXPECT_TRUE(contains(s, 6, 3));
  EXPECT_TRUE(contains(s, 6, 10));
  s.checkInvariant();
}

TEST(UnsignedIntervalSet, adjacentMerge)
{
  stp::UnsignedIntervalSet s(6, 4);
  add(s, 6, 3, 5);
  add(s, 6, 6, 8); // abuts: 5 and 6 are consecutive
  EXPECT_EQ(1u, s.size());
  EXPECT_TRUE(contains(s, 6, 5));
  EXPECT_TRUE(contains(s, 6, 6));
  s.checkInvariant();
}

TEST(UnsignedIntervalSet, collapseSmallestGapFirst)
{
  stp::UnsignedIntervalSet s(6, 2);
  add(s, 6, 0, 0);
  add(s, 6, 2, 2); // gap to previous = 2
  add(s, 6, 5, 5); // gap to previous = 3
  // Cap is 2, so the closest pair {0,2} merges, filling value 1.
  EXPECT_EQ(2u, s.size());
  EXPECT_TRUE(contains(s, 6, 0));
  EXPECT_TRUE(contains(s, 6, 1)); // gap filled by the join
  EXPECT_TRUE(contains(s, 6, 2));
  EXPECT_FALSE(contains(s, 6, 3));
  EXPECT_FALSE(contains(s, 6, 4));
  EXPECT_TRUE(contains(s, 6, 5));
  s.checkInvariant();
}

TEST(UnsignedIntervalSet, capOneIsHull)
{
  stp::UnsignedIntervalSet s(6, 1);
  add(s, 6, 1, 2);
  add(s, 6, 30, 31);
  ASSERT_EQ(1u, s.size());
  // Hull of the two: [1, 31].
  EXPECT_TRUE(contains(s, 6, 1));
  EXPECT_TRUE(contains(s, 6, 15));
  EXPECT_TRUE(contains(s, 6, 31));
  EXPECT_FALSE(contains(s, 6, 0));
  stp::UnsignedInterval* h = s.hull();
  ASSERT_NE(nullptr, h);
  EXPECT_EQ(1u, cbvValue(h->minV, 6));
  EXPECT_EQ(31u, cbvValue(h->maxV, 6));
  delete h;
}

TEST(UnsignedIntervalSet, completeAndConstant)
{
  stp::UnsignedIntervalSet s(5, 4);
  add(s, 5, 7, 7);
  EXPECT_TRUE(s.isConstant());
  EXPECT_FALSE(s.isComplete());
  stp::UnsignedInterval* h = s.hull(); // a constant hulls to itself
  ASSERT_NE(nullptr, h);
  EXPECT_TRUE(h->isConstant());
  delete h;

  s.resetToComplete();
  EXPECT_TRUE(s.isComplete());
  EXPECT_EQ(nullptr, s.hull()); // complete hull reported as null
  EXPECT_TRUE(contains(s, 5, 0));
  EXPECT_TRUE(contains(s, 5, 31));
}

// Random soundness: whatever values were inserted must remain members,
// the invariant must hold, and the cap must be respected -- at every step.
TEST(UnsignedIntervalSet, randomSoundness)
{
  const unsigned width = 6;
  const uint64_t N = 1ull << width;
  MTRand rand(1u);

  for (unsigned cap = 1; cap <= 5; cap++)
  {
    for (unsigned trial = 0; trial < 300; trial++)
    {
      stp::UnsignedIntervalSet s(width, cap);
      std::set<uint64_t> inserted;

      const unsigned inserts = 1 + (rand.randInt() % 8);
      for (unsigned k = 0; k < inserts; k++)
      {
        uint64_t lo = rand.randInt() % N;
        uint64_t hi = rand.randInt() % N;
        if (lo > hi)
          std::swap(lo, hi);
        add(s, width, lo, hi);
        for (uint64_t v = lo; v <= hi; v++)
          inserted.insert(v);

        // Soundness: everything inserted so far is still a member.
        for (uint64_t v : inserted)
          ASSERT_TRUE(contains(s, width, v))
              << "cap=" << cap << " lost value " << v;

        // Structure: cap respected and invariant intact.
        ASSERT_LE(s.size(), cap);
        s.checkInvariant();

        // The concretisation is a superset of the true set (over-approx).
        std::set<uint64_t> conc = concretise(s, width);
        for (uint64_t v : inserted)
          ASSERT_TRUE(conc.count(v));
      }
    }
  }
}

} // namespace

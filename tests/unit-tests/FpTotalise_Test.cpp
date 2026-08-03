/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August 2026
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

// The shape of the arrays that make the partial operations total.
//
// fp.min/fp.max are unspecified only on (+0, -0) and (-0, +0), so their
// choice map needs four cells; fp.to_ubv/fp.to_sbv are unspecified on NaN,
// the infinities and anything out of range, which depends on the whole
// value, so theirs is indexed on the rounding mode and the whole float.
// The end-to-end consequences are in tests/query-files/fp-tests; these pin
// the encoding itself, which the answers cannot show.

#include "stp/AST/AST.h"
#include "stp/FloatBlaster/FpTotalise.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

struct Fixture
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;

  Fixture() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    mgr.defaultNodeFactory = &snf;
  }

  ASTNode rne()
  {
    return mgr.CreateRMConst(symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  }
};

// The extra child FpTotalise appends is the array read supplying the
// unspecified value.
const ASTNode& unspecifiedRead(const ASTNode& totalised, size_t child)
{
  return totalised[child];
}

} // namespace

TEST(FpTotalise, min_indexes_the_choice_on_two_sign_bits)
{
  Fixture f;
  const SourceSort fp32 = SourceSort::floatingPoint(8, 24);
  const ASTNode x = f.mgr.CreateSourceSymbol("x", fp32);
  const ASTNode y = f.mgr.CreateSourceSymbol("y", fp32);
  const ASTNode min = f.mgr.CreateTerm(FP_MIN, 32, ASTVec{x, y});
  ASSERT_EQ(2u, min.Degree());

  FpTotalise totalise(&f.mgr);
  const ASTNode out = totalise.topLevel(min);

  ASSERT_EQ(FP_MIN, out.GetKind());
  ASSERT_EQ(3u, out.Degree()); // the choice is now a child

  const ASTNode& read = unspecifiedRead(out, 2);
  ASSERT_EQ(READ, read.GetKind());
  EXPECT_EQ(1u, read.GetValueWidth());   // one bit of choice
  EXPECT_EQ(2u, read[1].GetValueWidth()); // ... at a two-bit index
  EXPECT_EQ(2u, read[0].GetIndexWidth()); // ... into a four-cell array
}

TEST(FpTotalise, max_uses_a_different_array_from_min)
{
  Fixture f;
  const SourceSort fp32 = SourceSort::floatingPoint(8, 24);
  const ASTNode x = f.mgr.CreateSourceSymbol("x", fp32);
  const ASTNode y = f.mgr.CreateSourceSymbol("y", fp32);

  FpTotalise totalise(&f.mgr);
  const ASTNode min =
      totalise.topLevel(f.mgr.CreateTerm(FP_MIN, 32, ASTVec{x, y}));
  const ASTNode max =
      totalise.topLevel(f.mgr.CreateTerm(FP_MAX, 32, ASTVec{x, y}));

  // Same shape, different array: fp.min and fp.max choose independently.
  EXPECT_NE(unspecifiedRead(min, 2)[0], unspecifiedRead(max, 2)[0]);
}

TEST(FpTotalise, each_format_gets_its_own_choice_array)
{
  Fixture f;
  const ASTNode x =
      f.mgr.CreateSourceSymbol("x", SourceSort::floatingPoint(8, 24));
  const ASTNode y =
      f.mgr.CreateSourceSymbol("y", SourceSort::floatingPoint(8, 24));
  const ASTNode p =
      f.mgr.CreateSourceSymbol("p", SourceSort::floatingPoint(11, 53));
  const ASTNode q =
      f.mgr.CreateSourceSymbol("q", SourceSort::floatingPoint(11, 53));

  FpTotalise totalise(&f.mgr);
  const ASTNode single =
      totalise.topLevel(f.mgr.CreateTerm(FP_MIN, 32, ASTVec{x, y}));
  const ASTNode dbl =
      totalise.topLevel(f.mgr.CreateTerm(FP_MIN, 64, ASTVec{p, q}));

  // Both are four-cell maps now, so only the name keeps them apart -- and it
  // must, because fp.min at two formats is two unspecified functions.
  EXPECT_EQ(2u, unspecifiedRead(single, 2)[1].GetValueWidth());
  EXPECT_EQ(2u, unspecifiedRead(dbl, 2)[1].GetValueWidth());
  EXPECT_NE(unspecifiedRead(single, 2)[0], unspecifiedRead(dbl, 2)[0]);
}

// The same operands must read the same cell, or the array is not a function
// and fp.min stops being congruent.
TEST(FpTotalise, the_same_operands_read_the_same_cell)
{
  Fixture f;
  const SourceSort fp32 = SourceSort::floatingPoint(8, 24);
  const ASTNode x = f.mgr.CreateSourceSymbol("x", fp32);
  const ASTNode y = f.mgr.CreateSourceSymbol("y", fp32);

  FpTotalise totalise(&f.mgr);
  const ASTNode a =
      totalise.topLevel(f.mgr.CreateTerm(FP_MIN, 32, ASTVec{x, y}));
  const ASTNode b =
      totalise.topLevel(f.mgr.CreateTerm(FP_MIN, 32, ASTVec{x, y}));
  EXPECT_EQ(a, b);

  // ... and swapping them reads a different cell, because (+0,-0) and
  // (-0,+0) are separately unspecified.
  const ASTNode swapped =
      totalise.topLevel(f.mgr.CreateTerm(FP_MIN, 32, ASTVec{y, x}));
  EXPECT_NE(unspecifiedRead(a, 2)[1], unspecifiedRead(swapped, 2)[1]);
}

// fp.to_ubv is unspecified on NaN, the infinities and out-of-range values,
// which is not a function of the sign, so its index keeps the whole float
// and the rounding mode.
TEST(FpTotalise, to_ubv_indexes_on_the_rounding_mode_and_the_whole_value)
{
  Fixture f;
  const ASTNode x =
      f.mgr.CreateSourceSymbol("x", SourceSort::floatingPoint(8, 24));
  const ASTNode to_ubv = f.mgr.CreateTerm(
      FP_TO_UBV, 16,
      ASTVec{f.mgr.CreateBVConst(32, 16), f.rne(), x});

  FpTotalise totalise(&f.mgr);
  const ASTNode out = totalise.topLevel(to_ubv);

  ASSERT_EQ(FP_TO_UBV, out.GetKind());
  ASSERT_EQ(4u, out.Degree());

  const ASTNode& read = unspecifiedRead(out, 3);
  ASSERT_EQ(READ, read.GetKind());
  EXPECT_EQ(16u, read.GetValueWidth());     // the target width
  EXPECT_EQ(5u + 32u, read[1].GetValueWidth()); // rounding mode ++ float
}

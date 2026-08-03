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

// The shape of the maps that make the partial operations total.
//
// fp.min/fp.max are unspecified only on (+0, -0) and (-0, +0), so their
// choice map is four free bits selected between by the two sign bits and
// introduces no array at all; fp.to_ubv/fp.to_sbv are unspecified on NaN,
// the infinities and anything out of range, which depends on the whole
// value, so theirs is an array indexed on the rounding mode and the whole
// float. The end-to-end consequences are in tests/query-files/fp-tests;
// these pin the encoding itself, which the answers cannot show -- and which
// arrays a query acquires is not observable from its answer at all, though
// it decides how the user's own arrays get solved.

#include "stp/AST/AST.h"
#include "stp/FloatBlaster/FpTotalise.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>

#include <string>

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

// The extra child FpTotalise appends is whatever supplies the unspecified
// value: an array read for the conversions, a mux over free bits for
// fp.min/fp.max.
const ASTNode& unspecified(const ASTNode& totalised, size_t child)
{
  return totalised[child];
}

// The introduced symbol underneath an unspecified value -- the array for a
// conversion, the cells for a choice. Identity lives in the name, so that is
// what this looks for.
ASTNode unspecifiedSymbol(const ASTNode& n)
{
  if (n.GetKind() == SYMBOL &&
      std::string(n.GetName()).rfind("@fp_unspecified_", 0) == 0)
    return n;

  for (size_t i = 0; i < n.Degree(); i++)
  {
    const ASTNode found = unspecifiedSymbol(n[i]);
    if (!found.IsNull())
      return found;
  }
  return ASTNode();
}

bool containsRead(const ASTNode& n)
{
  if (n.GetKind() == READ)
    return true;
  for (size_t i = 0; i < n.Degree(); i++)
    if (containsRead(n[i]))
      return true;
  return false;
}

} // namespace

TEST(FpTotalise, min_selects_four_free_bits_on_two_sign_bits)
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

  const ASTNode& choice = unspecified(out, 2);
  EXPECT_EQ(1u, choice.GetValueWidth()); // one bit of choice

  const ASTNode cells = unspecifiedSymbol(choice);
  ASSERT_FALSE(cells.IsNull());
  EXPECT_EQ(4u, cells.GetValueWidth()); // ... one of four cells
  EXPECT_EQ(0u, cells.GetIndexWidth()); // ... held in a scalar, not an array
}

// The whole point of the four-cell encoding: a query whose only "arrays"
// would have been the ones totalisation invented has none. FpTotalise runs
// before containsArrayOps and numberOfReadsLessThan, so a read introduced
// here is indistinguishable from the user's and changes how the user's own
// arrays are solved.
TEST(FpTotalise, min_introduces_no_array)
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

  EXPECT_FALSE(containsRead(min));
  EXPECT_FALSE(containsRead(max));

  // ... whereas a conversion, whose domain really is unbounded, still does.
  const ASTNode to_ubv = totalise.topLevel(f.mgr.CreateTerm(
      FP_TO_UBV, 16, ASTVec{f.mgr.CreateBVConst(32, 16), f.rne(), x}));
  EXPECT_TRUE(containsRead(to_ubv));
}

TEST(FpTotalise, max_uses_different_cells_from_min)
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

  // Same shape, different cells: fp.min and fp.max choose independently.
  EXPECT_NE(unspecifiedSymbol(unspecified(min, 2)),
            unspecifiedSymbol(unspecified(max, 2)));
}

TEST(FpTotalise, each_format_gets_its_own_choice_cells)
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

  // Both are four-cell maps, so only the name keeps them apart -- and it
  // must, because fp.min at two formats is two unspecified functions.
  const ASTNode single_cells = unspecifiedSymbol(unspecified(single, 2));
  const ASTNode dbl_cells = unspecifiedSymbol(unspecified(dbl, 2));
  ASSERT_FALSE(single_cells.IsNull());
  ASSERT_FALSE(dbl_cells.IsNull());
  EXPECT_EQ(4u, single_cells.GetValueWidth());
  EXPECT_EQ(4u, dbl_cells.GetValueWidth());
  EXPECT_NE(single_cells, dbl_cells);
}

// The same operands must select the same cell, or the map is not a function
// and fp.min stops being congruent. Hash-consing is what supplies this now
// that there are no index equalities to do it.
TEST(FpTotalise, the_same_operands_select_the_same_cell)
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

  // ... and swapping them selects a different cell, because (+0,-0) and
  // (-0,+0) are separately unspecified. Same cells, different mux.
  const ASTNode swapped =
      totalise.topLevel(f.mgr.CreateTerm(FP_MIN, 32, ASTVec{y, x}));
  EXPECT_EQ(unspecifiedSymbol(unspecified(a, 2)),
            unspecifiedSymbol(unspecified(swapped, 2)));
  EXPECT_NE(unspecified(a, 2), unspecified(swapped, 2));
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

  const ASTNode& read = unspecified(out, 3);
  ASSERT_EQ(READ, read.GetKind());
  EXPECT_EQ(16u, read.GetValueWidth());     // the target width
  EXPECT_EQ(5u + 32u, read[1].GetValueWidth()); // rounding mode ++ float
}

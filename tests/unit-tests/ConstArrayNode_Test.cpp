/***********
AUTHORS: Andrew Teylu

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

// A constant array is a CONST_ARRAY node: its default is child 0 and a
// parameter naming its sort is child 1. These pin what that buys -- the
// default is visible to every walk, the node is hash-consed by sort and
// default, and a rebuild that knows nothing about constant arrays keeps the
// sort -- and the fold of a read to the default.

#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include <gtest/gtest.h>

using namespace stp;

namespace
{

const SourceSort bv8 = SourceSort::bitVector(8);

TEST(ConstArrayNode, DefaultIsChildZeroAndTheParameterNamesTheSort)
{
  STPMgr mgr;
  const SourceSort sort = SourceSort::array(bv8, bv8);
  const ASTNode x = mgr.CreateSourceSymbol("x", bv8);
  const ASTNode k = mgr.CreateConstArray(sort, x);

  ASSERT_EQ(CONST_ARRAY, k.GetKind());
  ASSERT_EQ(2u, k.Degree());
  EXPECT_EQ(x, k[0]);
  EXPECT_EQ(BVCONST, k[1].GetKind());
  EXPECT_EQ(sort, mgr.constArraySort(k[1]));
  EXPECT_EQ(sort, k.GetSourceSort());
  EXPECT_EQ(ARRAY_TYPE, k.GetType());
  EXPECT_EQ(8u, k.GetIndexWidth());
  EXPECT_EQ(8u, k.GetValueWidth());
  EXPECT_TRUE(BVTypeCheck(k));
  EXPECT_TRUE(mgr.hasConstArrays());
}

TEST(ConstArrayNode, ReadFoldsToTheDefault)
{
  STPMgr mgr;
  const ASTNode x = mgr.CreateSourceSymbol("x", bv8);
  const ASTNode i = mgr.CreateSourceSymbol("i", bv8);
  const ASTNode k = mgr.CreateConstArray(SourceSort::array(bv8, bv8), x);
  EXPECT_EQ(x, mgr.hashingNodeFactory->CreateTerm(READ, 8, k, i));
  EXPECT_EQ(x, mgr.defaultNodeFactory->CreateTerm(READ, 8, k, i));
}

// The same default at two sorts with one carrier is two arrays. Neither the
// default nor the widths tell them apart; the parameter does.
TEST(ConstArrayNode, InternedBySortAndDefault)
{
  STPMgr mgr;
  const ASTNode bit = mgr.CreateOneConst(1);

  // A rounding mode is carried in five bits, one per mode.
  const SourceSort byBv = SourceSort::array(SourceSort::bitVector(5), bv8);
  const SourceSort byMode = SourceSort::array(SourceSort::roundingMode(), bv8);
  const ASTNode zero8 = mgr.CreateZeroConst(8);
  const ASTNode kBv = mgr.CreateConstArray(byBv, zero8);
  const ASTNode kMode = mgr.CreateConstArray(byMode, zero8);
  ASSERT_EQ(kBv.GetIndexWidth(), kMode.GetIndexWidth());
  EXPECT_NE(kBv, kMode);
  EXPECT_EQ(byBv, kBv.GetSourceSort());
  EXPECT_EQ(byMode, kMode.GetSourceSort());
  EXPECT_EQ(kBv, mgr.CreateConstArray(byBv, zero8));

  // A Boolean element is stored packed, as a one-bit read yields it.
  const SourceSort ofBool = SourceSort::array(bv8, SourceSort::boolean());
  const SourceSort ofBit = SourceSort::array(bv8, SourceSort::bitVector(1));
  const ASTNode kBool = mgr.CreateConstArray(ofBool, mgr.ASTTrue);
  const ASTNode kBit = mgr.CreateConstArray(ofBit, bit);
  EXPECT_EQ(kBool[0], kBit[0]);
  EXPECT_EQ(1u, kBool.GetValueWidth());
  EXPECT_NE(kBool, kBit);
  EXPECT_EQ(ofBool, kBool.GetSourceSort());
  EXPECT_EQ(ofBit, kBit.GetSourceSort());
}

// The default is an ordinary child, so a walk that has never heard of
// constant arrays still finds what the default depends on.
TEST(ConstArrayNode, PlainWalksReachTheDefault)
{
  STPMgr mgr;
  const ASTNode x = mgr.CreateSourceSymbol("x", bv8);
  const ASTNode y = mgr.CreateSourceSymbol("y", bv8);
  const ASTNode sum = mgr.hashingNodeFactory->CreateTerm(BVPLUS, 8, x, y);
  const ASTNode k = mgr.CreateConstArray(SourceSort::array(bv8, bv8), sum);
  const ASTNode i = mgr.CreateSourceSymbol("i", bv8);
  const ASTNode store = mgr.hashingNodeFactory->CreateArrayTerm(
      WRITE, 8, 8, {k, i, mgr.CreateZeroConst(8)});

  EXPECT_TRUE(containsKind(store, BVPLUS));
  const ASTNode first = mgr.firstFreeSymbol(k);
  EXPECT_TRUE(first == x || first == y);
}

// A rebuild through the factory, as every pass makes one, keeps the sort the
// default cannot carry: here a rounding-mode index of a float array.
TEST(ConstArrayNode, GenericRebuildKeepsTheSort)
{
  STPMgr mgr;
  const SourceSort f32 = SourceSort::floatingPoint(8, 24);
  const SourceSort sort = SourceSort::array(SourceSort::roundingMode(), f32);
  const ASTNode x = mgr.CreateSourceSymbol("fx", f32);
  const ASTNode y = mgr.CreateSourceSymbol("fy", f32);
  const ASTNode k = mgr.CreateConstArray(sort, x);
  EXPECT_EQ(8u, k.GetExpWidth());
  EXPECT_EQ(24u, k.GetSigWidth());

  ASTNodeMap fromTo, cache;
  fromTo[x] = y;
  const ASTNode replaced =
      SubstitutionMap::replace(k, fromTo, cache, mgr.hashingNodeFactory);
  ASSERT_EQ(CONST_ARRAY, replaced.GetKind());
  EXPECT_EQ(y, replaced[0]);
  EXPECT_EQ(sort, replaced.GetSourceSort());
  EXPECT_EQ(mgr.CreateConstArray(sort, y), replaced);
  EXPECT_EQ(8u, replaced.GetExpWidth());
  EXPECT_EQ(24u, replaced.GetSigWidth());
  EXPECT_TRUE(BVTypeCheck(replaced));

  // The original is untouched: rebuilding never mutates a node.
  EXPECT_EQ(x, k[0]);
}

} // namespace

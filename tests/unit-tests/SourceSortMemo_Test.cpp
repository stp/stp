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

// A node's source sort is derived from its children -- through both branches
// of an ITE -- so without a memo the derivation costs one walk per *path*
// rather than one per node. The result is correct either way, which is why
// these tests count derivations rather than compare sorts: the count is the
// only place the difference shows.

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

// A spine of `depth` stores over one array, as a memory model or a lookup
// table produces. Each WRITE derives its sort from the array beneath it.
ASTNode storeChain(STPMgr& mgr, unsigned depth)
{
  const SourceSort array =
      SourceSort::array(SourceSort::bitVector(16), SourceSort::bitVector(8));
  ASTNode current = mgr.CreateSourceSymbol("a", array);

  for (unsigned i = 0; i < depth; i++)
  {
    const ASTNode index = mgr.CreateBVConst(16, i);
    const ASTNode value = mgr.CreateBVConst(8, i % 256);
    current = mgr.CreateArrayTerm(WRITE, 16, 8, {current, index, value});
  }
  return current;
}

// Two interleaved ITE spines: every level's branches are the previous
// level's two nodes, so the node count is linear in the depth while the
// number of root-to-leaf paths is 2^depth.
ASTNode iteDiamond(STPMgr& mgr, unsigned depth)
{
  ASTNode left = mgr.CreateSourceSymbol("x", SourceSort::bitVector(8));
  ASTNode right = mgr.CreateSourceSymbol("y", SourceSort::bitVector(8));

  for (unsigned i = 0; i < depth; i++)
  {
    const std::string cname = "c" + std::to_string(i);
    const std::string ename = "e" + std::to_string(i);
    const ASTNode c = mgr.CreateSourceSymbol(cname.c_str(),
                                             SourceSort::boolean());
    const ASTNode e = mgr.CreateSourceSymbol(ename.c_str(),
                                             SourceSort::boolean());

    const ASTNode next_left = mgr.CreateTerm(ITE, 8, c, left, right);
    const ASTNode next_right = mgr.CreateTerm(ITE, 8, e, right, left);
    left = next_left;
    right = next_right;
  }
  return left;
}

} // namespace

TEST(SourceSortMemo, ite_diamond_derives_once_per_node_not_once_per_path)
{
  STPMgr mgr;
  const unsigned depth = 40; // 2^40 paths; a per-path walk cannot finish.
  const ASTNode root = iteDiamond(mgr, depth);

  mgr.source_sort_derivations = 0;
  const SourceSort sort = root.GetSourceSort();

  EXPECT_EQ(SourceSort::bitVector(8), sort);
  // Two ITEs per level plus the leaves beneath them; the bound is deliberately
  // loose, because the point is that it is linear in the depth at all.
  EXPECT_LE(mgr.source_sort_derivations, 4 * depth + 16);
}

TEST(SourceSortMemo, store_chain_derives_once_per_node)
{
  STPMgr mgr;
  const unsigned depth = 2000;
  const ASTNode root = storeChain(mgr, depth);

  mgr.source_sort_derivations = 0;
  const SourceSort sort = root.GetSourceSort();

  EXPECT_EQ(SourceSort::Kind::Array, sort.kind());
  EXPECT_EQ(SourceSort::bitVector(8), sort.element());
  EXPECT_LE(mgr.source_sort_derivations, depth + 16);
}

TEST(SourceSortMemo, asking_again_costs_no_derivation)
{
  STPMgr mgr;
  const ASTNode root = storeChain(mgr, 64);
  root.GetSourceSort();

  mgr.source_sort_derivations = 0;
  EXPECT_EQ(root.GetSourceSort(), root.GetSourceSort());
  EXPECT_EQ(0u, mgr.source_sort_derivations);
}

// The node factories re-assert a node's widths on every hash-cons hit, so a
// memo dropped on every width *assignment* rather than on every width
// *change* is no memo at all -- it would be discarded once per incoming edge.
TEST(SourceSortMemo, reasserting_the_same_width_keeps_the_memo)
{
  STPMgr mgr;
  const ASTNode x = mgr.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode y = mgr.CreateSourceSymbol("y", SourceSort::bitVector(8));
  const ASTNode sum = mgr.CreateTerm(BVPLUS, 8, x, y);

  EXPECT_EQ(SourceSort::bitVector(8), sum.GetSourceSort());

  mgr.source_sort_derivations = 0;
  sum.SetValueWidth(8); // what the node factory does on every lookup
  EXPECT_EQ(SourceSort::bitVector(8), sum.GetSourceSort());
  EXPECT_EQ(0u, mgr.source_sort_derivations);
}

TEST(SourceSortMemo, changing_a_width_drops_the_memo)
{
  STPMgr mgr;
  const ASTNode x = mgr.CreateSourceSymbol("x", SourceSort::bitVector(8));
  const ASTNode y = mgr.CreateSourceSymbol("y", SourceSort::bitVector(8));
  const ASTNode sum = mgr.CreateTerm(BVPLUS, 8, x, y);

  EXPECT_EQ(SourceSort::bitVector(8), sum.GetSourceSort());

  sum.SetValueWidth(16);
  EXPECT_EQ(SourceSort::bitVector(16), sum.GetSourceSort());

  sum.SetValueWidth(8); // put it back, so the node is left as it was found
  EXPECT_EQ(SourceSort::bitVector(8), sum.GetSourceSort());
}

// A symbol's sort is part of its identity, so a name-only probe cannot be
// built for the unique table. These cover the name index that answers the
// name-only lookups instead -- which is what keeps creating a symbol from
// being linear in the number of symbols already made.
TEST(SymbolNameIndex, finds_a_typed_declaration_by_name_alone)
{
  STPMgr mgr;
  const ASTNode declared =
      mgr.CreateSourceSymbol("v", SourceSort::bitVector(32));

  EXPECT_TRUE(mgr.LookupSymbol("v"));
  ASTNode found;
  EXPECT_TRUE(mgr.LookupSymbol("v", found));
  EXPECT_EQ(declared, found);

  EXPECT_FALSE(mgr.LookupSymbol("not_declared"));
  ASTNode missing;
  EXPECT_FALSE(mgr.LookupSymbol("not_declared", missing));
}

// The legacy untyped entry point resolves a name to whatever was declared
// under it, rather than minting a second, sort-less symbol beside it.
TEST(SymbolNameIndex, untyped_lookup_reuses_the_typed_declaration)
{
  STPMgr mgr;
  const ASTNode declared =
      mgr.CreateSourceSymbol("w", SourceSort::bitVector(16));
  const ASTNode again = mgr.LookupOrCreateSymbol("w");

  EXPECT_EQ(declared, again);
  EXPECT_EQ(SourceSort::bitVector(16), again.GetSourceSort());
}

// One name at two sorts is what the sorted key admits and the old name-keyed
// one could not; the index has to keep both, and answer deterministically.
TEST(SymbolNameIndex, keeps_every_sort_declared_under_one_name)
{
  STPMgr mgr;
  const ASTNode first = mgr.CreateSourceSymbol("s", SourceSort::bitVector(8));
  const ASTNode second =
      mgr.CreateSourceSymbol("s", SourceSort::bitVector(16));

  EXPECT_NE(first, second);
  EXPECT_TRUE(mgr.LookupSymbol("s"));

  ASTNode found;
  EXPECT_TRUE(mgr.LookupSymbol("s", found));
  EXPECT_EQ(first, found); // the first declared, not an arbitrary one

  ASTNode again;
  EXPECT_TRUE(mgr.LookupSymbol("s", again));
  EXPECT_EQ(found, again);
}

// CreateFreshVariable asserts the name it mints is unused, so the index has
// to see every symbol the manager holds, however it was made.
TEST(SymbolNameIndex, sees_internally_minted_symbols)
{
  STPMgr mgr;
  const ASTNode fresh = mgr.CreateFreshVariable(0, 8, "unconstrained");

  EXPECT_TRUE(mgr.LookupSymbol(fresh.GetName()));
  ASTNode found;
  EXPECT_TRUE(mgr.LookupSymbol(fresh.GetName(), found));
  EXPECT_EQ(fresh, found);
}

// A float-indexed array of rounding modes: none of it is expressible in the
// index/value/exp/sig widths, so it exercises the derivation rather than the
// GetType() fallback beneath it.
TEST(SourceSortMemo, memo_preserves_sorts_the_widths_cannot_express)
{
  STPMgr mgr;
  const SourceSort array = SourceSort::array(SourceSort::floatingPoint(8, 24),
                                             SourceSort::roundingMode());
  const ASTNode a = mgr.CreateSourceSymbol("a", array);
  const ASTNode i =
      mgr.CreateSourceSymbol("i", SourceSort::floatingPoint(8, 24));
  const ASTNode r = mgr.CreateSourceSymbol("r", SourceSort::roundingMode());
  const ASTNode write = mgr.CreateArrayTerm(WRITE, 32, 5, {a, i, r});
  const ASTNode read = mgr.CreateTerm(READ, 5, write, i);

  EXPECT_EQ(array, write.GetSourceSort());
  EXPECT_EQ(SourceSort::roundingMode(), read.GetSourceSort());

  // Asked twice, answered the same -- the memo is not a different answer.
  EXPECT_EQ(array, write.GetSourceSort());
  EXPECT_EQ(SourceSort::roundingMode(), read.GetSourceSort());
}

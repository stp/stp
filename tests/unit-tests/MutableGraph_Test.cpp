/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: October, 2026
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

// MutableGraph: an editable view over a hash-consed formula. Import copies
// nothing, edits touch only private copies, export returns hash-consed
// nodes, and parent counts stay exact throughout.

#include "stp/AST/AST.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/MutableGraph.h"
#include <gtest/gtest.h>

using namespace stp;

namespace
{
struct Fixture : public ::testing::Test
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory& hashing;

  Fixture() : snf(*mgr.hashingNodeFactory, mgr), hashing(*mgr.hashingNodeFactory)
  {
    mgr.defaultNodeFactory = &snf;
  }

  ASTNode bv(const char* name, unsigned width = 8)
  {
    return hashing.CreateSymbol(name, 0, width);
  }
  ASTNode boolean(const char* name) { return hashing.CreateSymbol(name, 0, 0); }
  ASTNode eq(const ASTNode& a, const ASTNode& b)
  {
    return hashing.CreateNode(EQ, {a, b});
  }
};

TEST_F(Fixture, ImportThenExportIsIdentity)
{
  const ASTNode x = bv("x"), y = bv("y");
  const ASTNode a = boolean("a"), b = boolean("b");
  const ASTNode f = hashing.CreateNode(AND, {eq(x, y), hashing.CreateNode(OR, {a, b})});

  MutableGraph g(mgr);
  g.import(f);
  EXPECT_TRUE(g.checkInvariant());
  EXPECT_EQ(g.exportRoot(), f);
  EXPECT_EQ(g.parentCount(x), 1u);
  EXPECT_EQ(g.parentCount(y), 1u);
  EXPECT_EQ(g.parentCount(f[0]), 1u);
  EXPECT_EQ(g.parentCount(f), 1u); // the query's hold
}

TEST_F(Fixture, ParentsAreAMultiset)
{
  const ASTNode t = bv("t");
  const ASTNode f = hashing.CreateTerm(BVMULT, 8, {t, t});
  MutableGraph g(mgr);
  g.import(f);
  EXPECT_EQ(g.parentCount(t), 2u);
  std::vector<ASTNode> ps;
  g.parents(t, ps);
  EXPECT_EQ(ps.size(), 2u);
}

TEST_F(Fixture, PatchOneSlotAndExport)
{
  const ASTNode x = bv("x"), y = bv("y"), z = bv("z");
  const ASTNode a = boolean("a"), b = boolean("b");
  const ASTNode orAB = hashing.CreateNode(OR, {a, b});
  const ASTNode f = hashing.CreateNode(AND, {eq(x, y), orAB});

  MutableGraph g(mgr);
  g.import(f);
  // The and's children are in the hashing factory's order, not ours.
  const ASTNode theEq = f[0].GetKind() == EQ ? f[0] : f[1];
  MutableInterior* m = g.materialise(theEq);
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(g.checkInvariant());
  EXPECT_EQ(g.parentCount(m->handle()), 1u);
  EXPECT_EQ(g.parentCount(y), 1u);

  // y -> z in the equality. The or is untouched and must come back as the
  // same node.
  size_t slot = (m->GetChildren()[0] == y) ? 0 : 1;
  g.replaceChild(m, slot, z);
  EXPECT_TRUE(g.checkInvariant());
  EXPECT_EQ(g.parentCount(y), 0u);
  EXPECT_EQ(g.parentCount(z), 1u);
  EXPECT_EQ(g.parentCount(x), 1u);

  const ASTNode out = g.exportRoot();
  EXPECT_EQ(out, hashing.CreateNode(AND, {eq(x, z), orAB}));
  EXPECT_TRUE(out[0] == orAB || out[1] == orAB); // the same node, not a rebuild
  EXPECT_FALSE(out.isMutableInterior());
  EXPECT_FALSE(out[0].isMutableInterior());
}

TEST_F(Fixture, PatchThatEqualsAnExistingNodeMerges)
{
  const ASTNode x = bv("x"), y = bv("y"), z = bv("z");
  const ASTNode exy = eq(x, y), exz = eq(x, z);
  const ASTNode f = hashing.CreateNode(AND, {exy, exz});

  MutableGraph g(mgr);
  g.import(f);
  EXPECT_EQ(g.parentCount(x), 2u);
  MutableInterior* m = g.materialise(exy);
  const size_t slot = (m->GetChildren()[0] == y) ? 0 : 1;
  g.replaceChild(m, slot, z);
  EXPECT_TRUE(g.checkInvariant());

  // The copy now has exz's structure: it merged into exz and died. The
  // and above, converted because a node below it was replaced, became
  // (and e e), which the rules fold to e: the formula is exz.
  EXPECT_TRUE(m->isDead());
  EXPECT_EQ(g.current(exy), exz);
  EXPECT_EQ(g.parentCount(exz), 1u); // the query's hold: it is the root
  EXPECT_EQ(g.parentCount(x), 1u);   // read in one place now
  EXPECT_EQ(g.parentCount(y), 0u);

  const ASTNode out = g.exportRoot();
  EXPECT_EQ(out, exz);
}

TEST_F(Fixture, ReplacingTheRoot)
{
  const ASTNode x = bv("x"), y = bv("y"), z = bv("z");
  const ASTNode f = eq(x, y);
  MutableGraph g(mgr);
  g.import(f);
  MutableInterior* m = g.materialise(f);
  EXPECT_TRUE(g.root().isMutableInterior());
  const size_t slot = (m->GetChildren()[0] == x) ? 0 : 1;
  g.replaceChild(m, slot, z);
  EXPECT_TRUE(g.checkInvariant());
  EXPECT_EQ(g.parentCount(x), 0u);
  EXPECT_EQ(g.parentCount(z), 1u);
  EXPECT_EQ(g.exportRoot(), eq(z, y));
}

TEST_F(Fixture, SimplifyingRulesRunOnGraphNodes)
{
  const ASTNode a = boolean("a"), b = boolean("b"), c = boolean("c");
  const ASTNode orBC = hashing.CreateNode(OR, {b, c});
  const ASTNode f = hashing.CreateNode(AND, {a, orBC});

  MutableGraph g(mgr);
  g.import(f);
  MutableInterior* m = g.materialise(orBC);
  const ASTNode mh = m->handle();

  // Annihilator: the rule fires on a mutable operand and returns a leaf.
  EXPECT_EQ(g.factory().CreateNode(AND, {mh, mgr.ASTFalse}), mgr.ASTFalse);
  // Identity: x or x is x, mutable or not.
  EXPECT_EQ(g.factory().CreateNode(OR, {mh, mh}), mh);
  // A new combination over a mutable child is a mutable node in this graph,
  // hash-consed there: asking twice gives the same node.
  const ASTNode n1 = g.factory().CreateNode(AND, {mh, a});
  const ASTNode n2 = g.factory().CreateNode(AND, {a, mh});
  EXPECT_TRUE(n1.isMutableInterior());
  EXPECT_EQ(n1, n2);
  // A combination over immutable children only stays in the manager.
  EXPECT_FALSE(g.factory().CreateNode(AND, {a, b}).isMutableInterior());
  // Double negation is not built.
  const ASTNode notM = g.factory().CreateNode(NOT, {mh});
  EXPECT_TRUE(notM.isMutableInterior());
  EXPECT_EQ(notM.GetNodeNum(), mh.GetNodeNum() + 1);
  EXPECT_EQ(g.factory().CreateNode(NOT, {notM}), mh);
}

TEST_F(Fixture, SplicingARuleResultIn)
{
  // (and a (or b c)): patch the or's first slot to (not b) through the
  // graph's own factory, then export. The result is what the hashing
  // factory builds for the same formula.
  const ASTNode a = boolean("a"), b = boolean("b"), c = boolean("c");
  const ASTNode orBC = hashing.CreateNode(OR, {b, c});
  const ASTNode f = hashing.CreateNode(AND, {a, orBC});

  MutableGraph g(mgr);
  g.import(f);
  MutableInterior* m = g.materialise(orBC);
  const ASTNode notB = g.factory().CreateNode(NOT, {b});
  const size_t slot = (m->GetChildren()[0] == b) ? 0 : 1;
  g.replaceChild(m, slot, notB);
  EXPECT_TRUE(g.checkInvariant());
  EXPECT_EQ(g.parentCount(b), 1u); // under the not
  EXPECT_EQ(g.parentCount(notB), 1u);

  const ASTNode out = g.exportRoot();
  EXPECT_EQ(out, hashing.CreateNode(
                     AND, {a, hashing.CreateNode(OR, {hashing.CreateNode(NOT, {b}), c})}));
}

TEST_F(Fixture, DetachingASubtreeWithdrawsItsCounts)
{
  // (and (= x (bvadd y z)) (= y w)): replace the bvadd by w. y keeps the
  // equality's use, z drops to zero, w gains one.
  const ASTNode x = bv("x"), y = bv("y"), z = bv("z"), w = bv("w");
  const ASTNode add = hashing.CreateTerm(BVPLUS, 8, {y, z});
  const ASTNode f = hashing.CreateNode(AND, {eq(x, add), eq(y, w)});

  MutableGraph g(mgr);
  g.import(f);
  EXPECT_EQ(g.parentCount(y), 2u);
  EXPECT_EQ(g.parentCount(w), 1u);
  const ASTNode eqAdd = (f[0][0] == add || f[0][1] == add) ? f[0] : f[1];
  MutableInterior* m = g.materialise(eqAdd);
  const size_t slot = (m->GetChildren()[0] == add) ? 0 : 1;
  g.replaceChild(m, slot, w);
  EXPECT_TRUE(g.checkInvariant());
  EXPECT_EQ(g.parentCount(add), 0u);
  EXPECT_EQ(g.parentCount(z), 0u);
  EXPECT_EQ(g.parentCount(y), 1u);
  EXPECT_EQ(g.parentCount(w), 2u);
  EXPECT_EQ(g.exportRoot(), hashing.CreateNode(AND, {eq(x, w), eq(y, w)}));
}

TEST_F(Fixture, DeepChainIsWalkedOnTheHeap)
{
  // 20,000 nested ands, patched at the very bottom so export has to rebuild
  // the whole chain.
  const ASTNode a = boolean("a"), b = boolean("b"), c = boolean("c");
  ASTNode chain = hashing.CreateNode(OR, {a, b});
  const ASTNode bottom = chain;
  for (int i = 0; i < 20000; i++)
    chain = hashing.CreateNode(AND, {chain, boolean(("v" + std::to_string(i)).c_str())});

  MutableGraph g(mgr);
  g.import(chain);
  EXPECT_EQ(g.exportRoot(), chain);
  MutableInterior* m = g.materialise(bottom);
  const size_t slot = (m->GetChildren()[0] == a) ? 0 : 1;
  g.replaceChild(m, slot, c);
  EXPECT_EQ(g.parentCount(a), 0u);
  EXPECT_EQ(g.parentCount(c), 1u);
  const ASTNode out = g.exportRoot();
  EXPECT_NE(out, chain);
  EXPECT_FALSE(out.isMutableInterior());
  // Walk down the exported chain to its bottom.
  ASTNode cur = out;
  while (cur.GetKind() == AND)
  {
    // The nested and, or at the bottom the or; the other child is a symbol.
    cur = cur[0].GetKind() == SYMBOL ? cur[1] : cur[0];
  }
  EXPECT_EQ(cur, hashing.CreateNode(OR, {c, b}));
}
} // namespace

// A node with more than 64 children is kept out of the table and never
// re-sorted; its slots are indexed so repointing one child of a 200-way
// conjunction does not scan it. Every conjunct shares y: replacing y
// patches 200 equalities, each of which patches the root.
TEST_F(Fixture, WideConjunctionIsRepointedBySlot)
{
  const ASTNode y = bv("y"), z = bv("z");
  ASTVec conj;
  for (int i = 0; i < 200; i++)
    conj.push_back(eq(bv(("x" + std::to_string(i)).c_str()), y));
  const ASTNode f = hashing.CreateNode(AND, conj);

  MutableGraph g(mgr);
  g.import(f);
  MutableInterior* root = g.materialise(f);
  ASSERT_NE(root, nullptr);
  EXPECT_EQ(root->GetChildren().size(), 200u);
  EXPECT_TRUE(g.checkInvariant());

  // A leaf is not replaced as a node; each equality's slot is patched,
  // as the pass patches around a symbol.
  for (int i = 0; i < 200; i++)
  {
    const ASTNode c = g.current(root->handle())[i];
    MutableInterior* m = g.materialise(c);
    ASSERT_NE(m, nullptr);
    const size_t slot = (m->GetChildren()[0] == y) ? 0 : 1;
    g.replaceChild(m, slot, z);
  }
  std::string why;
  EXPECT_TRUE(g.checkInvariant(&why)) << why;
  EXPECT_EQ(g.parentCount(y), 0u);
  EXPECT_EQ(g.parentCount(z), 200u);

  // Then drop one conjunct to TRUE: the root is patched again in place.
  const ASTNode first = g.current(root->handle())[0];
  g.replace(first, mgr.ASTTrue);
  EXPECT_TRUE(g.checkInvariant(&why)) << why;

  // The rules never run on a wide node and the export is through the
  // hashing factory, so the TRUE stays as a conjunct for the pipeline's
  // next rebuild to drop; the other 199 all hold z now.
  const ASTNode out = g.exportRoot();
  EXPECT_EQ(out.GetKind(), AND);
  EXPECT_EQ(out.Degree(), 200u);
  size_t trues = 0;
  for (const ASTNode& c : out)
  {
    if (c == mgr.ASTTrue)
      trues++;
    else
      EXPECT_TRUE(c[0] == z || c[1] == z); // the factory orders the pair
  }
  EXPECT_EQ(trues, 1u);
}

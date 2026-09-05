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

// Replacing an assertion where it occurs inside another assertion.
//
// The way this goes wrong is the mirror of most simplifications: it does not
// invent a fact, it *loses* one. Every assertion maps to true, so a walk that
// substituted an assertion's own top node would rewrite it to `true` and drop
// it -- and the query would come back satisfiable on models the dropped
// constraint forbids. A negated assertion is the sharper version of the same
// trap: `not p` maps p to false, so rebuilding it from its own child yields
// `not false`, which is `true`, which is the constraint gone.
//
// Both are checked here directly, by counting what survives. The rest is the
// substitution itself doing what it claims on shapes where the answer is
// obvious by inspection.
#include "stp/Simplifier/EmbeddedConstraints.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

class EmbeddedTest : public ::testing::Test
{
protected:
  STPMgr mgr;
  NodeFactory* nf = nullptr;
  ASTNode p, q, r;

  void SetUp() override
  {
    nf = mgr.defaultNodeFactory;
    p = nf->CreateNode(EQ, mgr.CreateSymbol("p0", 0, 8),
                       mgr.CreateSymbol("p1", 0, 8));
    q = nf->CreateNode(EQ, mgr.CreateSymbol("q0", 0, 8),
                       mgr.CreateSymbol("q1", 0, 8));
    r = nf->CreateNode(EQ, mgr.CreateSymbol("r0", 0, 8),
                       mgr.CreateSymbol("r1", 0, 8));
  }

  ASTNode run(const ASTNode& n) { return EmbeddedConstraints(&mgr).topLevel(n); }

  // Does `needle` occur anywhere in `hay`?
  bool contains(const ASTNode& hay, const ASTNode& needle)
  {
    if (hay == needle)
      return true;
    for (const ASTNode& c : hay.GetChildren())
      if (contains(c, needle))
        return true;
    return false;
  }
};

} // namespace

// The point of the pass: p is asserted, so the copy of it inside the other
// assertion is true and whatever was built over it collapses.
TEST_F(EmbeddedTest, an_embedded_assertion_becomes_true)
{
  const ASTNode other = nf->CreateNode(OR, p, q);
  const ASTNode out = run(nf->CreateNode(AND, p, other));

  ASSERT_EQ(out.GetKind(), AND);
  // p survives as an assertion in its own right...
  EXPECT_TRUE(contains(out, p));
  // ... and the disjunction that contained it is gone, because `p or q` with
  // p true is true.
  EXPECT_FALSE(contains(out, other))
      << "the assertion containing p should have collapsed";
}

// The trap. p maps to true, and p is itself an assertion: if the walk touched
// the assertion's own node it would become `true` and the constraint would be
// lost.
TEST_F(EmbeddedTest, an_assertion_does_not_substitute_into_itself)
{
  const ASTNode out = run(nf->CreateNode(AND, p, q));
  ASSERT_EQ(out.GetKind(), AND);
  EXPECT_TRUE(contains(out, p)) << "p was dropped";
  EXPECT_TRUE(contains(out, q)) << "q was dropped";
}

// The sharper version: `not p` says p is false, and p is its own child.
TEST_F(EmbeddedTest, a_negated_assertion_does_not_erase_itself)
{
  const ASTNode notP = nf->CreateNode(NOT, p);
  const ASTNode out = run(nf->CreateNode(AND, notP, q));

  ASSERT_EQ(out.GetKind(), AND);
  EXPECT_TRUE(contains(out, notP))
      << "the negated assertion rebuilt itself into `true` and was lost";
  EXPECT_TRUE(contains(out, q));
}

// ... while still substituting p elsewhere, with the negated reading.
TEST_F(EmbeddedTest, a_negated_assertion_substitutes_as_false)
{
  const ASTNode notP = nf->CreateNode(NOT, p);
  const ASTNode other = nf->CreateNode(AND, p, q); // false, since p is false
  const ASTNode out = run(nf->CreateNode(AND, notP, other));

  ASSERT_TRUE(contains(out, notP)) << "the negated assertion was lost";
  EXPECT_FALSE(contains(out, other))
      << "`p and q` with p false should have collapsed";
}

// Nothing to do where there are no siblings, and nothing to do where no
// assertion occurs inside another.
TEST_F(EmbeddedTest, unrelated_assertions_are_left_alone)
{
  const ASTNode conj = nf->CreateNode(AND, p, q, r);
  EXPECT_EQ(run(conj), conj);
}

TEST_F(EmbeddedTest, a_lone_assertion_is_left_alone)
{
  EXPECT_EQ(run(p), p);
}

// A deeper occurrence, to show the walk is not just looking at the immediate
// children of each assertion.
TEST_F(EmbeddedTest, a_deeply_embedded_assertion_is_found)
{
  const ASTNode deep =
      nf->CreateNode(OR, r, nf->CreateNode(AND, q, nf->CreateNode(OR, p, r)));
  const ASTNode out = run(nf->CreateNode(AND, p, deep));
  EXPECT_TRUE(contains(out, p));
  EXPECT_FALSE(contains(out, deep)) << "the nested occurrence was not replaced";
}

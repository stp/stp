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

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/UninterpretedFunctions/UFPreLowering.h"
#include "stp/Util/DagWalk.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

// Every distinct application node reachable from `root`.
ASTNodeSet applicationsIn(const ASTNode& root)
{
  ASTNodeSet visited;
  ASTNodeSet applications;
  walkPreOrder(root, [&](const ASTNode& n) -> bool {
    if (!visited.insert(n).second)
      return false;
    if (n.GetKind() == UF_APPLY)
      applications.insert(n);
    return true;
  });
  return applications;
}

// The top-level conjuncts of `root`, nested conjunctions opened.
ASTNodeSet conjunctsOf(const ASTNode& root)
{
  ASTNodeSet out;
  std::vector<ASTNode> pending;
  pending.push_back(root);
  while (!pending.empty())
  {
    const ASTNode n = pending.back();
    pending.pop_back();
    if (n.GetKind() == AND)
    {
      for (size_t i = 0; i < n.Degree(); ++i)
        pending.push_back(n[i]);
      continue;
    }
    out.insert(n);
  }
  return out;
}

// The simplifying factory is the one every front end installs, and the pass
// relies on it to fold what a rewrite exposes: (= #x03 #x03) to true, and a
// conjunction with a false conjunct to false.
struct Fixture
{
  STPMgr manager;
  SimplifyingNodeFactory simplifying;
  UFContext* context = NULL;
  NodeFactory* factory = NULL;
  const SourceSort bv8 = SourceSort::bitVector(8);
  const UFDecl* f = NULL;
  std::string diagnostic;

  Fixture() : simplifying(*(manager.hashingNodeFactory), manager)
  {
    manager.defaultNodeFactory = &simplifying;
    manager.UserFlags.enable_uninterpreted_functions = true;
    context = manager.getUFContext();
    factory = manager.defaultNodeFactory;
    f = context->declareFunction("f", {bv8}, bv8, &diagnostic);
  }

  ASTNode symbol(const char* name) { return manager.CreateSourceSymbol(name, bv8); }
  ASTNode constant(unsigned value) { return manager.CreateBVConst(8, value); }
  ASTNode apply(const ASTNode& actual)
  {
    return context->apply(f, {actual}, &diagnostic);
  }
  ASTNode eq(const ASTNode& a, const ASTNode& b)
  {
    return factory->CreateNode(EQ, a, b);
  }
};

} // namespace

TEST(UFPreLowering, EqualArgumentsMergeTheirApplications)
{
  Fixture fx;
  ASSERT_NE(nullptr, fx.f) << fx.diagnostic;
  const ASTNode x = fx.symbol("x");
  const ASTNode y = fx.symbol("y");
  const ASTNode z = fx.symbol("z");
  // Two applications the query can only relate through a chain of
  // equalities, with a third symbol so that the chain has a middle.
  const ASTNode root = fx.factory->CreateNode(
      AND, {fx.eq(x, y), fx.eq(y, z),
            fx.factory->CreateNode(NOT, fx.eq(fx.apply(x), fx.apply(z)))});
  ASSERT_EQ(2u, applicationsIn(root).size());

  UFPreLowering pass(&fx.manager);
  UFPreLoweringStats stats;
  const ASTNode rewritten = pass.propagate(root, &stats);

  EXPECT_EQ(2u, stats.symbolSubstitutions);
  EXPECT_EQ(0u, stats.applicationSubstitutions);
  // (f x) and (f z) are one application, so the disequality between them
  // folded to false and took the root with it.
  EXPECT_EQ(fx.manager.ASTFalse, rewritten);
  EXPECT_EQ(0u, stats.applicationsRemaining);
}

TEST(UFPreLowering, DefiningEqualitiesAreKept)
{
  Fixture fx;
  ASSERT_NE(nullptr, fx.f) << fx.diagnostic;
  const ASTNode x = fx.symbol("x");
  const ASTNode y = fx.symbol("y");
  const ASTNode a = fx.symbol("a");
  const ASTNode root = fx.factory->CreateNode(
      AND, {fx.eq(x, y), fx.eq(a, fx.apply(y)), fx.eq(fx.apply(x), fx.constant(7))});

  UFPreLowering pass(&fx.manager);
  UFPreLoweringStats stats;
  const ASTNode rewritten = pass.propagate(root, &stats);

  // One application survives and it is pinned to 7. The definition of a is
  // resolved through everything else the pass read -- (f y) is (f x) is 7 --
  // so a is defined as 7, and the symbol equality itself is still there.
  const ASTNodeSet applications = applicationsIn(rewritten);
  ASSERT_EQ(1u, applications.size());
  const ASTNode application = *applications.begin();
  const ASTNodeSet conjuncts = conjunctsOf(rewritten);
  EXPECT_NE(conjuncts.end(), conjuncts.find(fx.eq(application, fx.constant(7))));
  EXPECT_NE(conjuncts.end(), conjuncts.find(fx.eq(a, fx.constant(7))));
  EXPECT_NE(conjuncts.end(), conjuncts.find(fx.eq(x, y)));
  EXPECT_EQ(1u, stats.applicationsRemaining);
}

TEST(UFPreLowering, ApplicationPinnedToAConstantFoldsElsewhere)
{
  Fixture fx;
  ASSERT_NE(nullptr, fx.f) << fx.diagnostic;
  const ASTNode w = fx.symbol("w");
  const ASTNode z = fx.symbol("z");
  const ASTNode application = fx.apply(fx.constant(3));
  // z = w / ((f 3) + 1) with (f 3) = 0 pins z to w.
  const ASTNode quotient = fx.factory->CreateTerm(
      BVDIV, 8, w,
      fx.factory->CreateTerm(BVPLUS, 8, application, fx.constant(1)));
  const ASTNode root = fx.factory->CreateNode(
      AND, {fx.eq(application, fx.constant(0)), fx.eq(z, quotient)});

  UFPreLowering pass(&fx.manager);
  UFPreLoweringStats stats;
  const ASTNode rewritten = pass.propagate(root, &stats);

  EXPECT_EQ(1u, stats.applicationSubstitutions);
  const ASTNodeSet conjuncts = conjunctsOf(rewritten);
  // The application is still defined, and it occurs nowhere else: the
  // divisor folded to a constant, taking the application out of z's
  // definition.
  EXPECT_NE(conjuncts.end(),
            conjuncts.find(fx.eq(application, fx.constant(0))));
  for (const ASTNode& conjunct : conjuncts)
  {
    if (conjunct != fx.eq(application, fx.constant(0)))
    {
      EXPECT_TRUE(applicationsIn(conjunct).empty());
    }
  }
  EXPECT_EQ(1u, stats.applicationsRemaining);
}

TEST(UFPreLowering, ASymbolIsNeverReplacedByATermMentioningIt)
{
  Fixture fx;
  ASSERT_NE(nullptr, fx.f) << fx.diagnostic;
  const ASTNode x = fx.symbol("x");
  const ASTNode y = fx.symbol("y");
  const ASTNode z = fx.symbol("z");
  // x = (f x) is a fact about x, not a definition of it, however well an
  // application ranks as a value; y = x and (f y) = z are definitions.
  const ASTNode root = fx.factory->CreateNode(
      AND, {fx.eq(x, fx.apply(x)), fx.eq(y, x), fx.eq(fx.apply(y), z)});

  UFPreLowering pass(&fx.manager);
  UFPreLoweringStats stats;
  const ASTNode rewritten = pass.propagate(root, &stats);

  EXPECT_EQ(2u, stats.symbolSubstitutions);
  const ASTNodeSet conjuncts = conjunctsOf(rewritten);
  // x was left alone, and (f y) became (f x): one application, still the
  // one x is equated with.
  EXPECT_NE(conjuncts.end(), conjuncts.find(fx.eq(x, fx.apply(x))));
  EXPECT_NE(conjuncts.end(), conjuncts.find(fx.eq(z, fx.apply(x))));
  EXPECT_EQ(1u, stats.applicationsRemaining);
}

TEST(UFPreLowering, ARootWithNoFactIsReturnedUnchanged)
{
  Fixture fx;
  ASSERT_NE(nullptr, fx.f) << fx.diagnostic;
  const ASTNode x = fx.symbol("x");
  const ASTNode y = fx.symbol("y");
  const ASTNode root = fx.factory->CreateNode(
      AND, {fx.factory->CreateNode(BVLT, x, y),
            fx.factory->CreateNode(NOT, fx.eq(fx.apply(x), fx.apply(y)))});

  UFPreLowering pass(&fx.manager);
  UFPreLoweringStats stats;
  EXPECT_EQ(root, pass.propagate(root, &stats));
  EXPECT_EQ(0u, stats.symbolSubstitutions);
  EXPECT_EQ(0u, stats.rounds);
  EXPECT_EQ(2u, stats.applicationsRemaining);
}

TEST(UFPreLowering, AnAssertedAtomIsTrueWhereverElseItOccurs)
{
  Fixture fx;
  ASSERT_NE(nullptr, fx.f) << fx.diagnostic;
  const ASTNode x = fx.symbol("x");
  const ASTNode y = fx.symbol("y");
  const ASTNode guard = fx.factory->CreateNode(BVLE, y, fx.constant(16));
  // The guard is asserted, and it guards the fact that pins x. Nothing
  // equates a symbol at the top level, so only the atom rewrite can expose
  // x = 5 to the application.
  const ASTNode root = fx.factory->CreateNode(
      AND, {guard,
            fx.factory->CreateNode(IMPLIES, guard, fx.eq(x, fx.constant(5))),
            fx.eq(fx.apply(x), fx.constant(9)),
            fx.eq(fx.apply(fx.constant(5)), fx.constant(3))});
  ASSERT_EQ(2u, applicationsIn(root).size());

  UFPreLowering pass(&fx.manager);
  UFPreLoweringStats stats;
  const ASTNode rewritten = pass.propagate(root, &stats);

  EXPECT_GE(stats.atomSubstitutions, 1u);
  // The implication collapsed to x = 5, the second round read it, and
  // (f x) became (f 5): pinned to both 9 and 3, the root is false.
  EXPECT_EQ(fx.manager.ASTFalse, rewritten);
}

TEST(UFPreLowering, ANegatedAssertionIsFalseWhereverElseItOccurs)
{
  Fixture fx;
  ASSERT_NE(nullptr, fx.f) << fx.diagnostic;
  const ASTNode x = fx.symbol("x");
  const ASTNode y = fx.symbol("y");
  const ASTNode guard = fx.factory->CreateNode(BVLE, y, fx.constant(16));
  const ASTNode root = fx.factory->CreateNode(
      AND, {fx.factory->CreateNode(NOT, guard),
            fx.factory->CreateNode(OR, guard, fx.eq(x, fx.constant(5))),
            fx.eq(fx.apply(x), fx.constant(9)),
            fx.eq(fx.apply(fx.constant(5)), fx.constant(3))});

  UFPreLowering pass(&fx.manager);
  UFPreLoweringStats stats;
  const ASTNode rewritten = pass.propagate(root, &stats);

  EXPECT_GE(stats.atomSubstitutions, 1u);
  EXPECT_EQ(fx.manager.ASTFalse, rewritten);
}

TEST(UFPreLowering, ASymbolEquatedWithAnArithmeticTermStaysItsName)
{
  Fixture fx;
  ASSERT_NE(nullptr, fx.f) << fx.diagnostic;
  const ASTNode a = fx.symbol("a");
  const ASTNode b = fx.symbol("b");
  const ASTNode x = fx.symbol("x");
  const ASTNode quotient = fx.factory->CreateTerm(BVDIV, 8, a, b);
  // x names a quotient and is an argument of f. The quotient is not pushed
  // into the application: x keeps naming it, and the conjunct is used as an
  // asserted atom instead.
  const ASTNode root = fx.factory->CreateNode(
      AND, {fx.eq(x, quotient),
            fx.factory->CreateNode(
                IMPLIES, fx.eq(x, quotient),
                fx.eq(fx.apply(x), fx.constant(9)))});

  UFPreLowering pass(&fx.manager);
  UFPreLoweringStats stats;
  const ASTNode rewritten = pass.propagate(root, &stats);

  EXPECT_EQ(0u, stats.symbolSubstitutions);
  EXPECT_GE(stats.atomSubstitutions, 1u);
  const ASTNodeSet conjuncts = conjunctsOf(rewritten);
  EXPECT_NE(conjuncts.end(), conjuncts.find(fx.eq(x, quotient)));
  EXPECT_NE(conjuncts.end(),
            conjuncts.find(fx.eq(fx.apply(x), fx.constant(9))));
}


/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

// Whether PrimeAudit catches a pass and its priming walk disagreeing.
//
// Six memoised computations fill their tables from the bottom up so their
// own recursion stops one level down, which is sound only where the walk
// reaches the nodes the pass would have reached anyway. Comparing the
// generated CNF catches a violation only when the violation changes the
// output, and a walk that stops short of a subtree does not: the pass goes
// down its own call stack for that subtree and answers exactly as before.
//
// So the walk and the pass are compared directly (stp/Util/DagWalk.h),
// and this is the test of the comparison rather than of any pass: a walk and
// a pass are played against each other by hand, agreeing and then failing to,
// so that the check is known to report what it exists to report. A check
// nobody has seen fail is a check nobody has.
//
// The audit is debug-only, so all of this compiles away under NDEBUG.

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/DagWalk.h"
#include <gtest/gtest.h>
#include <string>
#include <type_traits>
#include <utility>


using namespace stp;

namespace
{

using WalkOperandResult = decltype(std::declval<const WalkOperands&>().at(
    std::declval<const ASTNode&>(), size_t{0}));
static_assert(std::is_same<WalkOperandResult, const ASTNode&>::value,
              "operand views must not increment AST reference counts");

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* hf; // hashing factory: builds the input without folding it.

  Context() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;

    mgr.defaultNodeFactory = &snf;
    hf = mgr.hashingNodeFactory;
  }

  // BVXOR(BVXOR(x0, x1), x2): two interior nodes, three leaves, and no rule
  // in any factory that rewrites it.
  ASTNode chain() { return chain(3); }

  // The same nested `levels` deep.
  ASTNode chain(unsigned levels)
  {
    ASTNode n = mgr.CreateSymbol(("x" + std::to_string(counter++)).c_str(), 0, 8);
    for (unsigned i = 1; i < levels; i++)
      n = hf->CreateTerm(
          BVXOR, 8, n,
          mgr.CreateSymbol(("x" + std::to_string(counter++)).c_str(), 0, 8));
    return n;
  }

  unsigned counter = 0;

  // The factory orders a commutative node's children, so which index holds
  // the nested one is not fixed.
  static ASTNode interiorChild(const ASTNode& n)
  {
    for (const ASTNode& c : n.GetChildren())
      if (c.Degree() > 0)
        return c;
    return n;
  }

  static ASTNode leafChild(const ASTNode& n)
  {
    for (const ASTNode& c : n.GetChildren())
      if (c.Degree() == 0)
        return c;
    return n;
  }
};

// The manager is deliberately not destroyed, as in DeepDag_Test.cpp: what
// tearing one down does while its nodes are still held is not what these
// cases are about, and the process is about to exit anyway.
Context& fresh()
{
  return *(new Context());
}

TEST(DagWalk, preorder_is_left_to_right_and_honours_pruning)
{
  Context& c = fresh();
  const ASTNode a = c.mgr.CreateSymbol("preorder-a", 0, 4);
  const ASTNode b = c.mgr.CreateSymbol("preorder-b", 0, 4);
  const ASTNode d = c.mgr.CreateSymbol("preorder-d", 0, 4);
  const ASTNode e = c.mgr.CreateSymbol("preorder-e", 0, 4);
  const ASTNode left = c.hf->CreateTerm(BVCONCAT, 8, a, b);
  const ASTNode pruned = c.hf->CreateTerm(BVCONCAT, 8, d, e);
  const ASTNode top = c.hf->CreateTerm(BVCONCAT, 16, left, pruned);

  ASTVec visited;
  walkPreOrder(top, [&](const ASTNode& n) {
    visited.push_back(n);
    return n != pruned;
  });

  EXPECT_EQ((ASTVec{top, left, a, b, pruned}), visited);
}

TEST(DagWalk, postorder_rebuild_preserves_child_ranges_and_sharing)
{
  Context& c = fresh();
  const ASTNode a = c.mgr.CreateSymbol("rebuild-a", 0, 4);
  const ASTNode b = c.mgr.CreateSymbol("rebuild-b", 0, 4);
  const ASTNode d = c.mgr.CreateSymbol("rebuild-d", 0, 4);
  const ASTNode shared = c.hf->CreateTerm(BVXOR, 4, a, b);
  const ASTNode left = c.hf->CreateTerm(BVPLUS, 4, shared, d);
  const ASTNode top = c.hf->CreateTerm(BVAND, 4, left, shared);

  ASTNodeMap cache;
  std::vector<std::pair<ASTNode, ASTVec>> combined;
  const ASTNode result = postOrderRebuild(
      top, cache, [&](const ASTNode& n, const ASTVec& children) {
        combined.push_back({n, children});
        return n;
      });

  ASSERT_EQ(top, result);
  ASSERT_EQ(3U, combined.size());
  EXPECT_EQ(shared, combined[0].first);
  EXPECT_EQ(toASTVec(shared.GetChildren()), combined[0].second);
  EXPECT_EQ(left, combined[1].first);
  EXPECT_EQ(toASTVec(left.GetChildren()), combined[1].second);
  EXPECT_EQ(top, combined[2].first);
  EXPECT_EQ(toASTVec(top.GetChildren()), combined[2].second);
  EXPECT_EQ(3U, cache.size());
}

TEST(PrimeMemo, non_owning_operand_views_preserve_postorder)
{
  Context& c = fresh();
  const ASTNode a = c.mgr.CreateSymbol("view-a", 0, 0);
  const ASTNode b = c.mgr.CreateSymbol("view-b", 0, 0);
  const ASTNode d = c.mgr.CreateSymbol("view-d", 0, 0);
  const ASTNode e = c.mgr.CreateSymbol("view-e", 0, 0);
  const ASTNode inner = c.hf->CreateNode(OR, ASTVec{a, b, d});
  const ASTNode top = c.hf->CreateNode(AND, ASTVec{inner, e});

  ASTVec visited;
  primeMemo(
      top, [](const ASTNode& n)
      { return n.Degree() == 0 ? Walk::Visit : Walk::Descend; },
      [&](const ASTNode& n)
      {
        if (n == top)
          return WalkOperands::reversed(n);
        if (n == inner)
          return WalkOperands::range(1, n.Degree());
        return WalkOperands::all(n);
      },
      [&](const ASTNode& n, PrimeMemoReady) { visited.push_back(n); });

  ASTVec expected;
  for (size_t i = top.Degree(); i != 0; --i)
  {
    const ASTNode child = top[i - 1];
    if (child == inner)
    {
      for (size_t j = 1; j < inner.Degree(); ++j)
        expected.push_back(inner[j]);
      expected.push_back(inner);
    }
    else
      expected.push_back(child);
  }
  expected.push_back(top);

  EXPECT_EQ(expected, visited);
}

#ifndef NDEBUG

// A pass, played by hand: it runs a node, asks for the nodes the test says it
// asks for, and reports both to the audit exactly as a real pass does.
void run(PrimeAudit& audit, const ASTNode& n, const ASTVec& asks)
{
  PrimeAudit::Running running(audit, n);
  for (const ASTNode& child : asks)
  {
    PrimeAudit::Running below(audit, child);
  }
}

// A pass that was not primed: it runs a node and, from inside it, the node
// below -- one level of its own call stack per level of the input, which is
// what priming exists to stop and what the depth claim is about.
void runUnprimed(PrimeAudit& audit, const ASTNode& n)
{
  PrimeAudit::Running running(audit, n);

  const ASTNode below = Context::interiorChild(n);
  if (below != n) // the bottom of the chain answers with itself.
    runUnprimed(audit, below);
}

// Holds the audit open while a case reads its verdict. The check runs when
// the pass's outermost call returns, and where the pass is past its claim it
// stops the process -- which is what it is for, and is checked below by a case
// that lets it happen, but is not a thing to read a string out of.
struct Held
{
  PrimeAudit& audit;
  PrimeAudit::Running running;

  Held(PrimeAudit& audit_, const ASTNode& sentinel)
      : audit(audit_), running(audit_, sentinel)
  {
  }

  // Cleared before the sentinel is dropped, so the comparison it triggers
  // has nothing left to disagree about.
  ~Held() { audit.clear(); }
};

// A primed pass: it runs a node, its operands answer from the memo, and its
// own calls go one level. Whatever the input nests to.
TEST(PrimeAudit, a_pass_within_its_claim_is_silent)
{
  Context& c = fresh();
  const ASTNode top = c.chain(12);
  const ASTNode inner = Context::interiorChild(top);
  const ASTNode leaf = Context::leafChild(top);

  PrimeAudit audit("test", 8);

  {
    PrimeAudit::Running running(audit, top);
    run(audit, inner, ASTVec{inner[0], inner[1]});
    PrimeAudit::Running below(audit, leaf);
  }

  EXPECT_EQ(audit.disagreement(), "");
}

// What priming getting it wrong looks like from here: the walk misses a
// subtree, the pass reaches it anyway -- down its own call stack, one frame
// per level, which is the crash priming exists to prevent. Nothing in the
// output moves, so the CNF comparison cannot see it; the depth can.
TEST(PrimeAudit, a_pass_that_nests_past_its_claim_is_reported)
{
  Context& c = fresh();
  const ASTNode top = c.chain(12);

  PrimeAudit audit("test", 4);

  std::string bad;
  {
    Held held(audit, c.mgr.CreateSymbol("sentinel", 0, 8));
    runUnprimed(audit, top); // nothing was primed, so it goes all the way.
    bad = audit.disagreement();
  }

  EXPECT_NE(bad.find("nested 12 deep"), std::string::npos)
      << "audit said: " << bad;
  EXPECT_NE(bad.find("over its claim of 4"), std::string::npos)
      << "audit said: " << bad;
}

// ... and it stops the process rather than reporting quietly, which is the
// only way an assertions build has of insisting.
TEST(PrimeAuditDeath, nesting_past_the_claim_stops_the_process)
{
  EXPECT_DEATH(
      {
        Context& c = fresh();
        PrimeAudit audit("test", 4);
        runUnprimed(audit, c.chain(12));
      },
      "nested 11 deep");
}


// Re-entering on a node the pass has just built is allowed, and is why the
// claim is a small number rather than one or two: the operands of such a node
// are already primed, so the nesting is a property of the rewriting and not
// of the input.
TEST(PrimeAudit, re_entering_on_a_built_node_is_within_the_claim)
{
  Context& c = fresh();
  const ASTNode top = c.chain();
  const ASTNode inner = Context::interiorChild(top);
  const ASTNode leaf = Context::leafChild(top);

  PrimeAudit audit("test", 8);

  const ASTNode built = c.hf->CreateTerm(BVNOT, 8, top);

  {
    PrimeAudit::Running running(audit, top);
    run(audit, inner, ASTVec{inner[0], inner[1]});
    PrimeAudit::Running below(audit, leaf);
    PrimeAudit::Running newer(audit, built); // asked for, never primed.
  }

  EXPECT_EQ(audit.disagreement(), "");
}


#endif // NDEBUG

} // namespace

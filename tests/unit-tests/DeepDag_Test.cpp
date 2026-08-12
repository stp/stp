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

// AST-depth-recursive traversals: no pass may consume call stack in
// proportion to the depth of the input DAG.
//
// Deeply nested formulas (CPAchecker k-induction traces, ~9,300 nested
// nodes) deterministically segfault STP: Rewriting::rewrite and
// Dependencies::build recurse once per level of the input, so an input
// deep enough to exhaust the stack kills the process. The depth is chosen
// by whoever wrote the input, so no fixed stack size is a fix -- these
// traversals have to keep their working state on the heap.
//
// Each property below is checked twice: once on a shallow chain, which
// says the property itself holds, and once on a chain far deeper than the
// recursive frames fit in, which is what fails today. Two things make the
// deep result a property of STP rather than of the machine it runs on:
//
//   * it runs under a stack rlimit the test sets itself, so the ambient
//     `ulimit -s` (8 MiB here, unlimited on some CI runners) cannot
//     decide the outcome; and
//   * it runs in a forked child, so a stack overflow is one failing test
//     rather than a segfault that takes the rest of the binary with it.
//
// The chains are built with the hashing factory: the simplifying factory
// would fold or reassociate them, and the DAG under test would no longer
// be the deep one the test means to build.

#include "stp/AST/MutableASTNode.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Flatten.h"
#include "stp/Simplifier/Rewriting.h"
#include "stp/Simplifier/NodeDomainAnalysis.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/FloatBlaster/FpEncodingContext.h"
#include "stp/FloatBlaster/FpTotalise.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/Printer/printers.h"
#include "stp/Simplifier/CommonSubSum.h"
#include "stp/Simplifier/PropagateEqualities.h"
#include "stp/Simplifier/RemoveUnconstrained.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/UseITEContext.h"
#include "stp/Simplifier/VariablesInExpression.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BitBlaster.h"
#include "stp/Util/NodeIterator.h"
#include "stp/Simplifier/StrengthReduction.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Simplifier/constantBitP/Dependencies.h"
#include "stp/Simplifier/constantBitP/WorkList.h"
#include <algorithm>
#include <cstdlib>
#include <gtest/gtest.h>
#include <sstream>
#include <string>
#include <unordered_map>

#ifndef _WIN32
#include <sys/resource.h>
#endif

using namespace stp;

namespace
{

// Small enough that a per-level call frame cannot fit these depths, large
// enough for anything a stack-safe traversal legitimately does.
const size_t STACK_BYTES = 1024 * 1024;

// Exit codes of the forked child. Anything else -- in particular a signal
// -- is the failure this file exists to catch.
const int EXIT_OK = 0;
const int EXIT_BAD_RESULT = 2;

// Shallow enough to recurse safely: what the control cases run on.
const unsigned SHALLOW = 50;

// Cap how far this process's stack may grow. Linux applies a lowered
// RLIMIT_STACK to further growth of the main stack, so the check runs
// against a stack of exactly this size whatever the ambient `ulimit -s`
// is -- 8 MiB on a developer box, sometimes unlimited on a CI runner.
// Bounding it is what makes a passing deep case mean "the traversal does
// not use the stack for depth" rather than "this machine had room".
void capStack()
{
#ifndef _WIN32
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) == 0)
  {
    rl.rlim_cur = STACK_BYTES;
    setrlimit(RLIMIT_STACK, &rl);
  }
#else
  // No setrlimit; MSVC's default main-thread stack is 1 MiB already, which
  // is the size this wants.
#endif
}

// Runs one of the checks below in a child process on a bounded stack.
// `check` returning false -- the pass ran but got the wrong answer -- is
// reported as an exit code distinct from a crash.
//
// The manager is deliberately not destroyed. Releasing a deep DAG used to
// be depth-recursive itself (~ASTInterior -> CleanUp -> ~ASTInterior, one
// level per node), so tearing these chains down would overflow the stack
// after the traversal under test had already returned, and every case here
// would report the destructor's limit instead of the pass's. CleanUp drains
// a queue now and deep_teardown below covers it, but keeping the roots alive
// still isolates each case from the others: the child exits immediately, so
// leaving the DAG alive costs nothing.
#define EXPECT_STACK_SAFE(check, depth)                                     \
  EXPECT_EXIT(                                                              \
      {                                                                     \
        capStack();                                                         \
        Context* c = new Context();                                         \
        std::exit(check(*c, depth) ? EXIT_OK : EXIT_BAD_RESULT);            \
      },                                                                    \
      ::testing::ExitedWithCode(EXIT_OK), "")

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* nf; // simplifying factory: what the passes themselves use.
  NodeFactory* hf; // hashing factory: builds the input without folding it.

  // Roots each check hands over, so that returning from it does not drop
  // the last handle on a deep DAG and start the recursive teardown
  // described at EXPECT_STACK_SAFE.
  ASTVec roots;

  Context() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;

    mgr.defaultNodeFactory = &snf;
    nf = &snf;
    hf = mgr.hashingNodeFactory;
  }

  // A chain `depth` symbols long, so `depth`-1 operator nodes nested one
  // inside the next. No rewrite or flattening rule matches a chain of
  // BVXORs or BVMULTs over symbols, so what the passes do here is exactly
  // the traversal.
  ASTNode chain(Kind k, unsigned depth, unsigned width = 8)
  {
    ASTNode n = mgr.CreateSymbol("x0", 0, width);
    for (unsigned i = 1; i < depth; i++)
    {
      const std::string name = "x" + std::to_string(i);
      n = hf->CreateTerm(k, width, n,
                         mgr.CreateSymbol(name.c_str(), 0, width));
    }
    return n;
  }

  // The passes take a formula, and rewrite rules fire on the children of a
  // visited node rather than on the root, so put the chain under one.
  ASTNode formula(const ASTNode& term)
  {
    return hf->CreateNode(EQ, term, mgr.CreateZeroConst(term.GetValueWidth()));
  }

  // The factories order commutative children (constants first, then
  // symbols), so which index holds the chain is not fixed.
  static ASTNode childOfKind(const ASTNode& n, Kind k)
  {
    for (const auto& c : n.GetChildren())
      if (c.GetKind() == k)
        return c;
    return n;
  }
};

// Rewriting::rewrite (19 of the 21 known corpus crashes, ~9,300 nested
// frames deep) and, ahead of it in the same pass, the equally unbounded
// Rewriting::buildShareCount.
bool rewritingIdentityOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(top);

  Rewriting r(&c.mgr, c.nf);
  ASTNode f = top;
  // No rule matches a BVXOR chain, so the pass is an identity here; any
  // other answer means the traversal lost part of the DAG.
  return r.topLevel(f) == top;
}

// The second recursion point: when a rule rewrites a child, the result is
// fed back through rewrite(). The rule is `0 = (a + b)` -->
// `(bvuminus a) = b`, placed beside a deep chain so the re-entry happens
// in a traversal that is already deep.
bool rewritingRuleFiresOk(Context& c, unsigned depth)
{
  const unsigned width = 8;
  // The hashing factory orders a node's children by node number, and the
  // rule matches EQ(const, plus): the constant has to exist before the
  // operands do, or the equality comes out as EQ(plus, const) and nothing
  // fires.
  const ASTNode zero = c.mgr.CreateZeroConst(width);
  const ASTNode a = c.mgr.CreateSymbol("a", 0, width);
  const ASTNode b = c.mgr.CreateSymbol("b", 0, width);
  const ASTNode plus = c.hf->CreateTerm(BVPLUS, width, a, b);
  const ASTNode fires = c.hf->CreateNode(EQ, zero, plus);
  if (fires[0].GetKind() != BVCONST || fires[1].GetKind() != BVPLUS)
    return false; // not the shape the rule matches: prove nothing quietly.

  const ASTNode top =
      c.hf->CreateNode(AND, fires, c.formula(c.chain(BVXOR, depth, width)));
  c.roots.push_back(top);

  Rewriting r(&c.mgr, c.nf);
  ASTNode f = top;
  // The equality is rewritten, so the pass must not be an identity.
  return r.topLevel(f) != top;
}

// Flatten::buildShareCount on its own. A chain of same-kind flattenable
// nodes is the one shape flatten() does not recurse on: it appends the
// grandchildren to its own worklist and keeps looping, so the only
// depth-recursive walk this input reaches is the share count built ahead
// of it.
bool flattenShareCountOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVPLUS, depth));
  c.roots.push_back(top);

  Flatten flattener(&c.mgr, c.nf);
  ASTNode f = top;
  const ASTNode result = flattener.topLevel(f);
  c.roots.push_back(result);

  // The whole chain collapses into one BVPLUS over every symbol in it.
  const ASTNode plus = Context::childOfKind(result, BVPLUS);
  return plus.GetKind() == BVPLUS && plus.Degree() == depth;
}

// Flatten carries its own copy of both traversals: an identical
// buildShareCount, and flatten() with the same recursive shape as
// rewrite(). Flattening is off by default since #786, so it is not on the
// observed crash path -- but --flatten puts it back. BVMULT is not a
// flattenable kind, which keeps this a test of the traversal rather than
// of flattening.
bool flattenIdentityOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVMULT, depth));
  c.roots.push_back(top);

  Flatten flattener(&c.mgr, c.nf);
  ASTNode f = top;
  return flattener.topLevel(f) == top;
}

// SubstitutionMap::replace, which rebuilds a DAG with some nodes swapped
// out. Reached from every pass that applies a substitution, and the walk
// is over the whole input.
bool substitutionOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(top);

  // The symbol at the far end of the chain maps to a constant, so the walk
  // has to reach the bottom and every node above it is rebuilt on the way
  // back up.
  ASTNodeMap fromTo, cache;
  fromTo[c.mgr.CreateSymbol("x0", 0, 8)] = c.mgr.CreateBVConst(8, 1);

  const ASTNode result =
      SubstitutionMap::replace(top, fromTo, cache, c.nf);
  c.roots.push_back(result);
  return result != top;
}

// StrengthReduction::visit, which rebuilds the DAG applying whatever the
// domain analyses prove about each node.
bool strengthReductionOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(top);

  StrengthReduction sr(c.nf, &c.mgr.UserFlags);
  NodeDomainAnalysis nda(&c.mgr);
  const ASTNode result = sr.topLevel(top, nda);
  c.roots.push_back(result);

  // Nothing about a chain of unconstrained symbols is reducible, so the
  // pass has to hand back what it was given.
  return result == top;
}

// NodeIterator historically visits children right-to-left. Put the deep
// child last so a pending-node implementation retains one unvisited sibling
// at every level; a continuation iterator retains just the active path.
bool nodeIteratorOk(Context& c, unsigned depth)
{
  ASTNode n = c.mgr.CreateSymbol("iterator-x0", 0, 8);
  for (unsigned i = 1; i < depth; ++i)
  {
    const std::string name = "iterator-x" + std::to_string(i);
    n = c.hf->CreateTerm(BVXOR, 8,
                         c.mgr.CreateSymbol(name.c_str(), 0, 8), n);
  }
  c.roots.push_back(n);
  return c.mgr.NodeSize(n) == 2 * depth - 1;
}

bool nodeIteratorOrderOk(Context& c)
{
  const ASTNode condition =
      c.mgr.CreateSymbol("iterator-order-condition", 0, 0);
  const ASTNode a = c.mgr.CreateSymbol("iterator-order-a", 0, 8);
  const ASTNode b = c.mgr.CreateSymbol("iterator-order-b", 0, 8);
  const ASTNode d = c.mgr.CreateSymbol("iterator-order-d", 0, 8);
  const ASTNode left = c.hf->CreateTerm(BVCONCAT, 16, a, b);
  const ASTNode right = c.hf->CreateTerm(BVCONCAT, 16, b, d);
  const ASTNode top =
      c.hf->CreateTerm(ITE, 16, condition, left, right);
  c.roots.push_back(top);

  const ASTVec expected{top, right, d, b, left, a, condition};
  ASTVec actual;
  NodeIterator nodes(top, c.mgr.ASTUndefined, c.mgr);
  for (ASTNode n = nodes.next(); n != nodes.end(); n = nodes.next())
    actual.push_back(n);
  return actual == expected;
}

bool nonAtomIteratorOrderOk(Context& c)
{
  const ASTNode condition =
      c.mgr.CreateSymbol("non-atom-order-condition", 0, 0);
  const ASTNode a = c.mgr.CreateSymbol("non-atom-order-a", 0, 8);
  const ASTNode b = c.mgr.CreateSymbol("non-atom-order-b", 0, 8);
  const ASTNode d = c.mgr.CreateSymbol("non-atom-order-d", 0, 8);
  const ASTNode left = c.hf->CreateTerm(BVCONCAT, 16, a, b);
  const ASTNode right = c.hf->CreateTerm(BVCONCAT, 16, b, d);
  const ASTNode top = c.hf->CreateTerm(ITE, 16, condition, left, right);
  c.roots.push_back(top);

  const ASTVec expected{top, right, left};
  ASTVec actual;
  NonAtomIterator nodes(top, c.mgr.ASTUndefined, c.mgr);
  for (ASTNode n = nodes.next(); n != nodes.end(); n = nodes.next())
    actual.push_back(n);
  return actual == expected;
}

// PropagateEqualities::buildCandidateList -- a void pre-order walk with a
// visited set, so a worklist is enough.
bool propagateEqualitiesOk(Context& c, unsigned depth)
{
  ASTNode f = c.hf->CreateNode(EQ, c.mgr.CreateSymbol("q0", 0, 8),
                               c.mgr.CreateZeroConst(8));
  for (unsigned i = 1; i < depth; i++)
  {
    const std::string nm = "q" + std::to_string(i);
    f = c.hf->CreateNode(AND, c.hf->CreateNode(EQ, c.mgr.CreateSymbol(nm.c_str(), 0, 8),
                                               c.mgr.CreateZeroConst(8)), f);
  }
  c.roots.push_back(f);
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  PropagateEqualities pe(&simp, c.nf, &c.mgr);
  return pe.topLevel(f).GetKind() != UNDEFINED;
}

// CommonSubSum::topLevel. Already stack-safe; here to keep it that way.
bool commonSubSumOk(Context& c, unsigned depth)
{
  const ASTNode f = c.formula(c.chain(BVPLUS, depth));
  c.roots.push_back(f);
  CommonSubSum css(&c.mgr, c.nf);
  ASTNode g = f;
  return css.topLevel(g).GetKind() != UNDEFINED;
}

TEST(DeepDag, shallow_rewriting)
{
  Context c;
  EXPECT_TRUE(rewritingIdentityOk(c, SHALLOW));
}

TEST(DeepDag, shallow_rewriting_rule_fires)
{
  Context c;
  EXPECT_TRUE(rewritingRuleFiresOk(c, SHALLOW));
}

TEST(DeepDag, shallow_flatten)
{
  Context c;
  EXPECT_TRUE(flattenIdentityOk(c, SHALLOW));
}

TEST(DeepDag, shallow_flatten_share_count)
{
  Context c;
  EXPECT_TRUE(flattenShareCountOk(c, SHALLOW));
}

TEST(DeepDag, flatten_lazy_scratch_preserves_rebuild_and_dedup)
{
  Context c;
  const ASTNode a = c.mgr.CreateSymbol("flatten-scratch-a", 0, 8);
  const ASTNode b = c.mgr.CreateSymbol("flatten-scratch-b", 0, 8);
  const ASTNode d = c.mgr.CreateSymbol("flatten-scratch-d", 0, 8);
  const ASTNode other = c.mgr.CreateSymbol("flatten-scratch-other", 0, 8);
  const ASTNode left = c.hf->CreateTerm(BVAND, 8, a, b);
  const ASTNode right = c.hf->CreateTerm(BVAND, 8, b, d);
  const ASTNode nested = c.hf->CreateTerm(BVAND, 8, left, right);
  ASTNode input = c.hf->CreateNode(EQ, nested, other);
  c.roots.push_back(input);

  Flatten flattener(&c.mgr, c.nf);
  const ASTNode result = flattener.topLevel(input);
  c.roots.push_back(result);
  const ASTNode flat = Context::childOfKind(result, BVAND);

  ASSERT_EQ(EQ, result.GetKind());
  ASSERT_EQ(BVAND, flat.GetKind());
  EXPECT_EQ(3U, flat.Degree());
  ASTNodeSet children(flat.begin(), flat.end());
  EXPECT_EQ(3U, children.size());
  EXPECT_EQ(1U, children.count(a));
  EXPECT_EQ(1U, children.count(b));
  EXPECT_EQ(1U, children.count(d));
}

TEST(DeepDag, wide_share_count_walks_preserve_shared_rewrite_guards)
{
  Context c;
  const ASTNode three = c.mgr.CreateBVConst(3, 3);
  const ASTNode two = c.mgr.CreateBVConst(3, 2);
  const ASTNode x = c.mgr.CreateSymbol("wide-share-x", 0, 3);
  const ASTNode y = c.mgr.CreateSymbol("wide-share-y", 0, 3);
  const ASTNode plus = c.hf->CreateTerm(BVPLUS, 3, three, x);
  const ASTNode guarded = c.hf->CreateNode(
      NOT, c.hf->CreateNode(BVGT, two, plus));
  const ASTNode otherUse = c.hf->CreateNode(EQ, y, plus);

  ASTVec children{guarded, otherUse};
  children.reserve(4098);
  for (unsigned i = 0; i < 4096; ++i)
  {
    const std::string name = "wide-share-b" + std::to_string(i);
    children.push_back(c.mgr.CreateSymbol(name.c_str(), 0, 0));
  }
  ASTNode input = c.hf->CreateNode(AND, children);
  c.roots.push_back(input);

  Rewriting rewriting(&c.mgr, c.nf);
  ASTNode rewriteInput = input;
  EXPECT_EQ(input, rewriting.topLevel(rewriteInput));

  Flatten flattening(&c.mgr, c.nf);
  ASTNode flattenInput = input;
  EXPECT_EQ(input, flattening.topLevel(flattenInput));
}

TEST(DeepDag, wide_propagate_equalities_visits_every_conjunct)
{
  Context c;
  c.mgr.UserFlags.propagate_equalities = true;
  ASTVec symbols;
  symbols.reserve(2048);
  for (unsigned i = 0; i < 2048; ++i)
  {
    const std::string name = "wide-propagate-b" + std::to_string(i);
    symbols.push_back(c.mgr.CreateSymbol(name.c_str(), 0, 0));
  }
  const ASTNode input = c.hf->CreateNode(AND, symbols);
  c.roots.push_back(input);

  SubstitutionMap substitutions(&c.mgr);
  Simplifier simplifier(&c.mgr, &substitutions);
  PropagateEqualities propagate(&simplifier, c.nf, &c.mgr);
  EXPECT_EQ(c.mgr.ASTTrue, propagate.topLevel(input));
}

TEST(DeepDag, shallow_substitution)
{
  Context c;
  EXPECT_TRUE(substitutionOk(c, SHALLOW));
}

TEST(DeepDag, substitution_root_fast_paths_preserve_results)
{
  Context c;
  const ASTNode x = c.mgr.CreateSymbol("subst-x", 0, 8);
  const ASTNode y = c.mgr.CreateSymbol("subst-y", 0, 8);
  const ASTNode free = c.mgr.CreateSymbol("subst-free", 0, 8);
  const ASTNode cached = c.mgr.CreateSymbol("subst-cached", 0, 8);
  const ASTNode one = c.mgr.CreateOneConst(8);
  const ASTNode zero = c.mgr.CreateZeroConst(8);

  ASTNodeMap fromTo, cache;
  fromTo[x] = y;
  fromTo[y] = one;
  cache[cached] = zero;

  EXPECT_EQ(zero, SubstitutionMap::replace(zero, fromTo, cache, c.nf));
  EXPECT_EQ(free, SubstitutionMap::replace(free, fromTo, cache, c.nf));
  EXPECT_EQ(zero, SubstitutionMap::replace(cached, fromTo, cache, c.nf));
  EXPECT_EQ(one, SubstitutionMap::replace(x, fromTo, cache, c.nf));
  EXPECT_EQ(one, fromTo.at(x));

  const ASTNode array = c.mgr.CreateSymbol("subst-array", 8, 8);
  const ASTNode write = c.hf->CreateArrayTerm(
      WRITE, 8, 8, array, c.mgr.CreateZeroConst(8), one);
  EXPECT_EQ(write, SubstitutionMap::replace(write, fromTo, cache, c.nf,
                                            true, false));
}

TEST(DeepDag, shallow_strength_reduction)
{
  Context c;
  EXPECT_TRUE(strengthReductionOk(c, SHALLOW));
}

TEST(DeepDag, node_iterator_preserves_lifo_dag_order)
{
  Context c;
  EXPECT_TRUE(nodeIteratorOrderOk(c));
}

TEST(DeepDag, non_atom_iterator_preserves_filtered_lifo_order)
{
  Context c;
  EXPECT_TRUE(nonAtomIteratorOrderOk(c));
}

TEST(DeepDag, shallow_node_iterator)
{
  Context c;
  EXPECT_TRUE(nodeIteratorOk(c, SHALLOW));
}

TEST(DeepDag, deep_rewriting_share_count)
{
  EXPECT_STACK_SAFE(rewritingIdentityOk, 200000);
}

TEST(DeepDag, deep_rewriting_rewrite)
{
  EXPECT_STACK_SAFE(rewritingIdentityOk, 10000);
}

TEST(DeepDag, deep_rewriting_rule_fires)
{
  EXPECT_STACK_SAFE(rewritingRuleFiresOk, 10000);
}

TEST(DeepDag, deep_flatten_share_count)
{
  EXPECT_STACK_SAFE(flattenShareCountOk, 100000);
}

TEST(DeepDag, deep_flatten)
{
  EXPECT_STACK_SAFE(flattenIdentityOk, 10000);
}

TEST(DeepDag, deep_substitution)
{
  EXPECT_STACK_SAFE(substitutionOk, 20000);
}

TEST(DeepDag, deep_strength_reduction)
{
  EXPECT_STACK_SAFE(strengthReductionOk, 20000);
}

TEST(DeepDag, deep_common_sub_sum)              { EXPECT_STACK_SAFE(commonSubSumOk, 20000); }
TEST(DeepDag, deep_node_iterator)      { EXPECT_STACK_SAFE(nodeIteratorOk, 20000); }
TEST(DeepDag, deep_propagate_equalities) { EXPECT_STACK_SAFE(propagateEqualitiesOk, 20000); }
} // namespace

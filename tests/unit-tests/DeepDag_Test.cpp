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
#ifdef STP_ENABLE_FLOATING_POINT

// A chain of if-then-else terms, nested in the else-branch: a boolean symbol
// the model says nothing about takes false, so evaluating one descends the
// chain rather than stopping at the first level.
ASTNode iteChain(Context& c, unsigned depth)
{
  const ASTNode cond = c.mgr.CreateSymbol("p", 0, 0);
  const ASTNode zero = c.mgr.CreateZeroConst(8);
  ASTNode t = c.mgr.CreateSymbol("x", 0, 8);
  for (unsigned i = 0; i < depth; i++)
    t = c.hf->CreateTerm(ITE, 8, cond, zero, t);
  return t;
}

// A chain of stores over one array symbol, whose elements are `width` bits.
ASTNode storeChain(Context& c, unsigned depth, const ASTNode& base,
                   unsigned width = 8)
{
  ASTNode a = base;
  for (unsigned i = 0; i < depth; i++)
  {
    const std::string nm = "w" + std::to_string(i);
    a = c.hf->CreateArrayTerm(WRITE, 8, width, a,
                              c.mgr.CreateSymbol(nm.c_str(), 0, 8),
                              c.mgr.CreateZeroConst(width));
  }
  return a;
}

ASTNode storeChain(Context& c, unsigned depth)
{
  return storeChain(c, depth, c.mgr.CreateSymbol("A", 8, 8));
}
#endif // STP_ENABLE_FLOATING_POINT


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

// Releasing a DAG. A node that loses its last reference releases its
// children, which can lose theirs: the teardown is as deep as the input,
// and it runs wherever the last handle happens to be dropped.
bool teardownOk(Context& c, unsigned depth)
{
  {
    const ASTNode top = c.formula(c.chain(BVXOR, depth));
    (void)top;
  } // the only handle goes here, and the whole chain follows it.
  return true;
}

// Two independently owned chains die under the same root. Both reach the
// direct-deletion cap while that root is still being destroyed, so the
// outermost cleanup has more than one spill frontier to drain.
bool teardownSpillFrontiersOk(Context& c, unsigned depth)
{
  auto chain = [&](const char* side) {
    const std::string first = std::string(side) + "0";
    ASTNode n = c.mgr.CreateSymbol(first.c_str(), 0, 8);
    for (unsigned i = 1; i < depth; ++i)
    {
      const std::string name = std::string(side) + std::to_string(i);
      n = c.hf->CreateTerm(BVXOR, 8, n,
                           c.mgr.CreateSymbol(name.c_str(), 0, 8));
    }
    return n;
  };

  {
    const ASTNode top =
        c.hf->CreateTerm(BVPLUS, 8, chain("delete-left-"),
                         chain("delete-right-"));
    (void)top;
  }
  return true;
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

// BitBlaster::BBTerm, which reaches its operands by calling itself from 24
// places across its kind switch. The blaster uses ordinary recursion for a
// bounded prefix, then fills the remaining suffix of its memo from the bottom
// first. This depth is well beyond that boundary.
bool bitBlastTermOk(Context& c, unsigned depth)
{
  const ASTNode f = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(f);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  BBNodeManagerAIG nm;
  BitBlaster bb(&nm, &simp, c.nf, &c.mgr.UserFlags);
  bb.BBForm(f);

  // Every xor in the chain is 8 bits of AIG, so this cannot pass without
  // the whole chain having been blasted.
  return nm.totalNumberOfNodes() >= static_cast<int>(depth);
}

// A deep term that is only reachable through a formula that is only
// reachable through a term: the chain is an equality's operand, the equality
// is an ITE's condition, and the ITE is a term. Priming each memo on its own
// left this to the recursion -- the walk over terms handed the condition to
// BBForm and stopped, and the walk over formulas was suppressed while the
// first was running, so nothing primed the chain and BBTerm descended it a
// frame at a time.
ASTNode termUnderFormulaUnderTerm(Context& c, unsigned depth)
{
  const ASTNode chain = c.chain(BVXOR, depth);
  const ASTNode cond = c.hf->CreateNode(EQ, chain, c.mgr.CreateZeroConst(8));
  const ASTNode y0 = c.mgr.CreateSymbol("y0", 0, 8);
  const ASTNode y1 = c.mgr.CreateSymbol("y1", 0, 8);
  const ASTNode ite = c.hf->CreateTerm(ITE, 8, cond, y0, y1);
  return c.hf->CreateTerm(BVMULT, 8, ite, y0);
}

bool bitBlastNestedOk(Context& c, unsigned depth)
{
  const ASTNode f = c.formula(termUnderFormulaUnderTerm(c, depth));
  c.roots.push_back(f);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  BBNodeManagerAIG nm;
  BitBlaster bb(&nm, &simp, c.nf, &c.mgr.UserFlags);
  bb.BBForm(f);

  // The chain is under the condition, so it cannot have been blasted
  // without the walk having crossed into it.
  return nm.totalNumberOfNodes() >= static_cast<int>(depth);
}

// BitBlaster::BBForm, which blasts a formula's operands by calling itself.
bool bitBlastOk(Context& c, unsigned depth)
{
  ASTNode f = c.hf->CreateNode(EQ, c.mgr.CreateSymbol("b0", 0, 8),
                               c.mgr.CreateZeroConst(8));
  for (unsigned i = 1; i < depth; i++)
  {
    const std::string name = "b" + std::to_string(i);
    const ASTNode leaf = c.hf->CreateNode(
        EQ, c.mgr.CreateSymbol(name.c_str(), 0, 8), c.mgr.CreateZeroConst(8));
    f = c.hf->CreateNode(AND, leaf, f);
  }
  c.roots.push_back(f);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  BBNodeManagerAIG nm;
  BitBlaster bb(&nm, &simp, c.nf, &c.mgr.UserFlags);
  bb.BBForm(f);

  // One AIG node per conjunct at the very least.
  return nm.totalNumberOfNodes() >= static_cast<int>(depth);
}

// NodeDomainAnalysis::buildMap.
bool nodeDomainOk(Context& c, unsigned depth)
{
  const ASTNode f = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(f);
  NodeDomainAnalysis nda(&c.mgr);
  nda.buildMap(f);
  return true;
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

// VariablesInExpression::getSymbol.
bool varsInExpressionOk(Context& c, unsigned depth)
{
  const ASTNode f = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(f);
  VariablesInExpression vie;
  bool destruct = false;
  ASTNodeSet* v = vie.SetofVarsSeenInTerm(f, destruct);
  const bool ok = v != nullptr;
  if (destruct) delete v;
  return ok;
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

// FlattenKind, which every pass that wants an n-ary view of a nested
// same-kind chain goes through: the simplifier, the BV solver,
// PropagateEqualities, MergeSame and UseITEContext. Its two forms differ in
// whether they dedup or take a depth limit, and a chain of the kind being
// flattened reaches each of them one level at a time.
//
// The deduplicating form is the one AND, OR, BVAND and BVOR take, and it
// ignores the depth limit entirely.
bool flattenKindNoDuplicatesOk(Context& c, unsigned depth)
{
  const ASTNode top = c.chain(BVAND, depth);
  c.roots.push_back(top);

  // The chain is left-nested, so flattening the top node yields every symbol
  // in it -- which is also how we know the walk reached the bottom.
  const ASTVec flat = FlattenKind(BVAND, top.GetChildren(), 15);
  return flat.size() == depth;
}

// The depth-limited form, which the arithmetic kinds take -- with no limit at
// all from two of the simplifier's arms, which is where its own recursion is
// as deep as the chain.
bool flattenKindDepthOk(Context& c, unsigned depth)
{
  const ASTNode top = c.chain(BVPLUS, depth);
  c.roots.push_back(top);

  const ASTVec flat = FlattenKind(BVPLUS, top.GetChildren());
  return flat.size() == depth;
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

// The read-count heuristic must traverse a read-free deep term without C++
// recursion. Once its strict limit is reached, it must also stop the whole
// traversal rather than continuing into a later deep sibling.
bool numberOfReadsWalkOk(Context& c, unsigned depth)
{
  const ASTNode deep = c.chain(BVXOR, depth);
  c.roots.push_back(deep);
  if (!numberOfReadsLessThan(deep, 1))
    return false;

  const ASTNode array = c.mgr.CreateSymbol("read-count-array", 8, 8);
  const ASTNode index = c.mgr.CreateSymbol("read-count-index", 0, 8);
  const ASTNode read = c.hf->CreateTerm(READ, 8, array, index);
  const ASTNode earlyStop = c.hf->CreateTerm(BVCONCAT, 16, read, deep);
  c.roots.push_back(earlyStop);
  return !numberOfReadsLessThan(earlyStop, 1);
}
#ifdef STP_ENABLE_FLOATING_POINT

/* A node's floating-point format and its source sort are both derived from
   its children and memoised on it, and both derivations read a child's answer
   by asking for it -- which derives the child the same way. So each ran one
   call frame per level of whatever it walked: a store chain for both of them,
   an if-then-else spine for both of them.

   Neither is a pass, so neither has an input of its own: they are reached by
   asking an ordinary question about a node. GetType() asks for the format,
   and everything asks GetType(). That is what makes these worth converting --
   a query deep enough cannot be asked its type at all, from anywhere. */

// deriveFPFormat's if-then-else arm, which takes a branch's format and so
// walks the spine. Reached here through GetType, the way almost everything
// reaches it.
bool fpFormatIteChainOk(Context& c, unsigned depth)
{
  const ASTNode t = iteChain(c, depth);
  c.roots.push_back(t);
  return t.GetType() == BITVECTOR_TYPE;
}

// deriveFPFormat's read and store arms: an array of floats keeps its element
// format on the array node, so a read over a store chain derives through
// every store in it.
//
// The one case here that answers with a format rather than with "not a
// float", so it checks that the walk carried an answer up rather than only
// that it finished: the format found at the top is the one declared at the
// bottom, 20,000 stores below.
bool fpFormatStoreChainOk(Context& c, unsigned depth)
{
  const ASTNode a = c.mgr.CreateSymbol("A", 8, 16);
  a.SetExpWidth(5);
  a.SetSigWidth(11);

  const ASTNode chain = storeChain(c, depth, a, 16);
  const ASTNode r =
      c.hf->CreateTerm(READ, 16, chain, c.mgr.CreateSymbol("j", 0, 8));
  c.roots.push_back(r);
  return r.GetExpWidth() == 5 && r.GetSigWidth() == 11;
}

// deriveSourceSort's if-then-else arm, which asks both branches and walks the
// same spine.
bool sourceSortIteChainOk(Context& c, unsigned depth)
{
  const ASTNode t = iteChain(c, depth);
  c.roots.push_back(t);
  return t.GetSourceSort().kind() == SourceSort::Kind::BitVector;
}

// deriveSourceSort's store arm: a store has the sort of the array under it.
bool sourceSortStoreChainOk(Context& c, unsigned depth)
{
  const ASTNode a = storeChain(c, depth);
  c.roots.push_back(a);
  return a.GetSourceSort().kind() == SourceSort::Kind::Array;
}

// FpTotalise, which replaces every partial floating-point operation with its
// total form before the blaster sees it. How deeply a float expression nests
// is the input's choice, and both of this pass's walks -- the totalising one
// and the rounding-mode collector that runs over its output -- went down it a
// frame at a time. A query built from 30,000 nested fp.add operations found
// it, once the simplifier stopped dying in front of it.
//
// The chain is fp.add over one float symbol, which is what that query is.
// Constructing it needs the format on the leaf: a symbol's is declared, and
// every operation above derives its own from it.
bool fpTotaliseChainOk(Context& c, unsigned depth)
{
  const unsigned eb = 8, sb = 24;
  const ASTNode x = c.mgr.CreateSymbol("x", 0, eb + sb);
  x.SetExpWidth(eb);
  x.SetSigWidth(sb);
  const ASTNode rm = c.mgr.CreateBVConst(5, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);

  ASTNode t = x;
  for (unsigned i = 0; i < depth; i++)
    t = c.hf->CreateTerm(FP_ADD, eb + sb, rm, t, x);

  const ASTNode f = c.hf->CreateNode(FP_ISNAN, t);
  c.roots.push_back(f);

  FpTotalise fpt(&c.mgr);
  const ASTNode result = fpt.topLevel(f);
  c.roots.push_back(result);
  return result.GetKind() != UNDEFINED;
}
#endif // STP_ENABLE_FLOATING_POINT


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

TEST(DeepDag, shallow_node_domain)
{
  Context c;
  EXPECT_TRUE(nodeDomainOk(c, SHALLOW));
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
#ifdef STP_ENABLE_FLOATING_POINT

TEST(DeepDag, wide_fp_rounding_mode_walk_adds_every_constraint)
{
  Context c;
  const ASTNode rne = c.mgr.CreateRMConst(
      symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  ASTVec clauses;
  clauses.reserve(256);
  for (unsigned i = 0; i < 256; ++i)
  {
    const std::string name = "wide-rounding-mode" + std::to_string(i);
    const ASTNode rm =
        c.mgr.CreateSourceSymbol(name.c_str(), SourceSort::roundingMode());
    clauses.push_back(c.hf->CreateNode(EQ, rm, rne));
  }
  const ASTNode input = c.hf->CreateNode(AND, clauses);
  c.roots.push_back(input);

  FpTotalise totalise(&c.mgr);
  const ASTNode result = totalise.topLevel(input);
  c.roots.push_back(result);

  size_t validityConstraints = 0;
  ASTNodeSet seen;
  walkPreOrder(result, [&](const ASTNode& n) {
    if (!seen.insert(n).second)
      return false;
    validityConstraints += n.GetKind() == OR && n.Degree() == 5;
    return true;
  });
  EXPECT_EQ(clauses.size(), validityConstraints);
}
#endif // STP_ENABLE_FLOATING_POINT


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

TEST(DeepDag, shallow_teardown)
{
  Context c;
  EXPECT_TRUE(teardownOk(c, SHALLOW));
}

TEST(DeepDag, teardown_drains_multiple_spill_frontiers)
{
  Context c;
  EXPECT_TRUE(teardownSpillFrontiersOk(c, SHALLOW));
}

TEST(DeepDag, shallow_flatten_kind_no_duplicates)
{
  Context c;
  EXPECT_TRUE(flattenKindNoDuplicatesOk(c, SHALLOW));
}

TEST(DeepDag, shallow_flatten_kind_depth)
{
  Context c;
  EXPECT_TRUE(flattenKindDepthOk(c, SHALLOW));
}

TEST(DeepDag, flat_flatten_kind_preserves_children)
{
  Context c;
  ASTVec children;
  for (unsigned i = 0; i < 4; ++i)
  {
    const std::string name = "flat" + std::to_string(i);
    children.push_back(c.mgr.CreateSymbol(name.c_str(), 0, 8));
  }
  const ASTNode holder = c.hf->CreateTerm(BVXOR, 8, children);
  const ASTVec expected = toASTVec(holder.GetChildren());

  EXPECT_EQ(expected, FlattenKind(BVAND, holder.GetChildren()));
  EXPECT_EQ(expected, FlattenKind(BVPLUS, holder.GetChildren()));
}

TEST(DeepDag, duplicate_flatten_kind_does_not_reserve_discarded_edges)
{
  Context c;
  const ASTNode a = c.mgr.CreateSymbol("flat-shared-a", 0, 8);
  const ASTNode b = c.mgr.CreateSymbol("flat-shared-b", 0, 8);
  const ASTNode shared = c.hf->CreateTerm(BVAND, 8, a, b);
  const ASTNode holder = c.hf->CreateTerm(BVXOR, 8, ASTVec(4096, shared));

  const ASTVec flat = FlattenKind(BVAND, holder.GetChildren());
  EXPECT_EQ(toASTVec(shared.GetChildren()), flat);
  EXPECT_LT(flat.capacity(), holder.Degree());
}

TEST(DeepDag, shallow_strength_reduction)
{
  Context c;
  EXPECT_TRUE(strengthReductionOk(c, SHALLOW));
}

TEST(DeepDag, shallow_bit_blast)
{
  Context c;
  EXPECT_TRUE(bitBlastOk(c, SHALLOW));
}

TEST(DeepDag, shallow_bit_blast_term)
{
  Context c;
  EXPECT_TRUE(bitBlastTermOk(c, SHALLOW));
}

TEST(DeepDag, shallow_bit_blast_nested)
{
  Context c;
  EXPECT_TRUE(bitBlastNestedOk(c, SHALLOW));
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
#ifdef STP_ENABLE_FLOATING_POINT

TEST(DeepDag, shallow_fp_format_ite)
{
  Context c;
  EXPECT_TRUE(fpFormatIteChainOk(c, SHALLOW));
}

TEST(DeepDag, shallow_fp_format_store)
{
  Context c;
  EXPECT_TRUE(fpFormatStoreChainOk(c, SHALLOW));
}

TEST(DeepDag, shallow_source_sort_ite)
{
  Context c;
  EXPECT_TRUE(sourceSortIteChainOk(c, SHALLOW));
}

TEST(DeepDag, shallow_source_sort_store)
{
  Context c;
  EXPECT_TRUE(sourceSortStoreChainOk(c, SHALLOW));
}
#endif // STP_ENABLE_FLOATING_POINT


TEST(DeepDag, array_read_count_is_strict_and_deduplicates_the_dag)
{
  Context c;
  const ASTNode array = c.mgr.CreateSymbol("read-count-shared-array", 8, 8);
  const ASTNode i = c.mgr.CreateSymbol("read-count-shared-i", 0, 8);
  const ASTNode j = c.mgr.CreateSymbol("read-count-shared-j", 0, 8);
  const ASTNode first = c.hf->CreateTerm(READ, 8, array, i);
  const ASTNode second = c.hf->CreateTerm(READ, 8, array, j);
  const ASTNode top =
      c.hf->CreateTerm(BVXOR, 8, ASTVec{first, first, second});
  c.roots.push_back(top);

  EXPECT_TRUE(numberOfReadsLessThan(top, 3));
  EXPECT_FALSE(numberOfReadsLessThan(top, 2));
  EXPECT_FALSE(numberOfReadsLessThan(first, 1));
  EXPECT_TRUE(numberOfReadsLessThan(first, 2));
  EXPECT_FALSE(numberOfReadsLessThan(top, 0));
}

TEST(DeepDag, shallow_array_read_count_walk)
{
  Context c;
  EXPECT_TRUE(numberOfReadsWalkOk(c, SHALLOW));
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

TEST(DeepDag, deep_teardown)
{
  EXPECT_STACK_SAFE(teardownOk, 50000);
}

TEST(DeepDag, deep_flatten_kind_no_duplicates)
{
  EXPECT_STACK_SAFE(flattenKindNoDuplicatesOk, 20000);
}

TEST(DeepDag, deep_flatten_kind_depth)
{
  EXPECT_STACK_SAFE(flattenKindDepthOk, 20000);
}

TEST(DeepDag, deep_strength_reduction)
{
  EXPECT_STACK_SAFE(strengthReductionOk, 20000);
}

TEST(DeepDag, deep_bit_blast)
{
  EXPECT_STACK_SAFE(bitBlastOk, 20000);
}

TEST(DeepDag, deep_bit_blast_term)
{
  EXPECT_STACK_SAFE(bitBlastTermOk, 20000);
}

TEST(DeepDag, deep_bit_blast_nested)
{
  EXPECT_STACK_SAFE(bitBlastNestedOk, 20000);
}

TEST(DeepDag, deep_common_sub_sum)              { EXPECT_STACK_SAFE(commonSubSumOk, 20000); }
TEST(DeepDag, deep_node_domain)        { EXPECT_STACK_SAFE(nodeDomainOk, 20000); }
TEST(DeepDag, deep_node_iterator)      { EXPECT_STACK_SAFE(nodeIteratorOk, 20000); }
TEST(DeepDag, deep_vars_in_expression) { EXPECT_STACK_SAFE(varsInExpressionOk, 20000); }
TEST(DeepDag, deep_propagate_equalities) { EXPECT_STACK_SAFE(propagateEqualitiesOk, 20000); }
TEST(DeepDag, deep_array_read_count_walk)
{
  EXPECT_STACK_SAFE(numberOfReadsWalkOk, 20000);
}
#ifdef STP_ENABLE_FLOATING_POINT
TEST(DeepDag, deep_fp_totalise)        { EXPECT_STACK_SAFE(fpTotaliseChainOk, 20000); }
TEST(DeepDag, deep_fp_format_ite)      { EXPECT_STACK_SAFE(fpFormatIteChainOk, 20000); }
TEST(DeepDag, deep_fp_format_store)    { EXPECT_STACK_SAFE(fpFormatStoreChainOk, 20000); }
TEST(DeepDag, deep_source_sort_ite)    { EXPECT_STACK_SAFE(sourceSortIteChainOk, 20000); }
TEST(DeepDag, deep_source_sort_store)  { EXPECT_STACK_SAFE(sourceSortStoreChainOk, 20000); }
#endif // STP_ENABLE_FLOATING_POINT

} // namespace

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
#include "stp/Simplifier/SplitExtracts.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Simplifier/SubstitutionMap.h"
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

// Structural depth without putting the measurement itself on the call
// stack. Memoisation matters for the generated FP circuits, which are DAGs
// with extensive sharing rather than trees.
size_t dagDepth(const ASTNode& top)
{
  struct Frame
  {
    ASTNode node;
    size_t nextChild = 0;
    size_t deepestChild = 0;

    explicit Frame(const ASTNode& n) : node(n) {}
  };

  std::unordered_map<uint64_t, size_t> known;
  std::vector<Frame> stack;
  stack.emplace_back(top);
  size_t result = 0;

  while (!stack.empty())
  {
    Frame& frame = stack.back();
    if (frame.nextChild < frame.node.Degree())
    {
      const ASTNode child = frame.node[frame.nextChild++];
      const auto found = known.find(child.GetNodeNum());
      if (found != known.end())
        frame.deepestChild = std::max(frame.deepestChild, found->second);
      else
        stack.emplace_back(child);
      continue;
    }

    result = frame.deepestChild + 1;
    known[frame.node.GetNodeNum()] = result;
    stack.pop_back();
    if (!stack.empty())
      stack.back().deepestChild =
          std::max(stack.back().deepestChild, result);
  }

  return result;
}

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

// Dependencies::build, the parent map constant-bit propagation runs on.
// Two of the 21 known corpus crashes land here.
bool dependenciesChainOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(top);

  simplifier::constantBitP::Dependencies deps(top);

  // Every link of the chain is read by exactly one parent, the link above
  // it -- and the traversal has to have reached the bottom to know that.
  ASTNode n = Context::childOfKind(top, BVXOR);
  unsigned levels = 0;
  while (n.GetKind() == BVXOR)
  {
    const ASTNode child = n[0].GetKind() == BVXOR ? n[0] : n[1];
    if (deps.getDependents(child).size() != 1)
      return false;
    if (!deps.nodeDependsOn(n, child))
      return false;
    n = child;
    levels++;
  }
  return levels == depth - 1;
}

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
// The extract-over-concat rule in the simplifying factory, which drops the
// halves of a concat the extract does not reach into. A concat chain is a
// normal form, so it stays as deep as the input made it, and an extract of
// the far end has to walk the whole thing.
//
// Built with the simplifying factory rather than the hashing one: the rule
// under test is the factory's, and it fires as the extract is created. The
// chain itself is hash-consed either way -- no rule rewrites a concat of
// distinct symbols -- so `nf` still produces the deep chain this needs.
bool extractOverConcatOk(Context& c, unsigned links)
{
  const unsigned piece = 8;

  // Symbols rather than constants: a concat of constants is folded on
  // creation, so a chain built from them would collapse as it was built and
  // there would be no depth here to walk.
  const ASTNode chainTail = c.mgr.CreateSymbol("extract-concat-tail", 0, piece);
  ASTNode chain = chainTail;

  // One symbol serves every link. What makes each concat a distinct node is
  // its right operand, which is a longer chain at each turn, so the left
  // operands do not have to differ -- unlike the xor and multiply chains
  // above, where a repeated symbol would cancel the depth away.
  const ASTNode link = c.mgr.CreateSymbol("extract-concat-link", 0, piece);

  for (unsigned i = 0; i < links; i++)
    chain = c.nf->CreateTerm(BVCONCAT, chain.GetValueWidth() + piece, link,
                             chain);
  c.roots.push_back(chain);

  // Every link still contributes its bits, so the walk below really is over
  // that many of them. Without this the test goes on passing if some later
  // rule flattens the chain, while no longer testing anything.
  if (chain.GetValueWidth() != piece * (links + 1))
    return false;

  // The bottom byte is the tail, at the far end of the chain, so the walk
  // has to have descended through every link to reach it. The tail is a
  // different symbol from the links precisely so that this can say which
  // one the extract landed on rather than merely that it landed on some
  // symbol.
  const ASTNode extract =
      c.nf->CreateTerm(BVEXTRACT, piece, chain, c.mgr.CreateBVConst(32, 7),
                       c.mgr.CreateBVConst(32, 0));
  c.roots.push_back(extract);

  return extract == chainTail;
}

// The remainder reconstruction in the simplifying factory, which pairs a
// dividend with the "- b * (a / b)" product beside it in a sum. The pairs are
// independent of each other, so the number of them is chosen by the input,
// not by its depth: folding one and re-entering the factory to find the next
// would spend a frame per pair. Flattening a chain of these additions is what
// hands the factory one sum this wide.
bool remainderFoldingOk(Context& c, unsigned pairs)
{
  const unsigned width = 32;
  const ASTNode divisor = c.mgr.CreateBVConst(width, 101);
  // The negated divisor as the constant it reaches the factory as: every
  // node in a real query has been through the simplifying factory, which
  // folds a negated constant on creation.
  const ASTNode negDivisor = c.mgr.CreateBVConst(width, (1ULL << width) - 101);

  ASTVec children;
  children.reserve(2 * pairs);
  for (unsigned i = 0; i < pairs; i++)
  {
    const std::string name = "rem-fold-a" + std::to_string(i);
    const ASTNode a = c.mgr.CreateSymbol(name.c_str(), 0, width);
    children.push_back(a);
    children.push_back(c.hf->CreateTerm(
        BVMULT, width, negDivisor,
        c.hf->CreateTerm(SBVDIV, width, a, divisor)));
  }

  const ASTNode sum = c.nf->CreateTerm(BVPLUS, width, children);
  c.roots.push_back(sum);

  // Every pair became a remainder, so the sum has one operand per pair.
  return sum.GetKind() == BVPLUS && sum.Degree() == pairs &&
         sum[0].GetKind() == SBVREM;
}

bool flattenIdentityOk(Context& c, unsigned depth)
{
  // A kind the pass traverses but never merges (BVMULT flattens now, like
  // BVPLUS), so this stays a pure walk of the whole chain: stack safety
  // with no rewriting.
  const ASTNode top = c.formula(c.chain(BVSUB, depth));
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

// SplitExtracts::buildMap, which records every extract-of-a-symbol in the
// input so that overlapping uses of one symbol can be split into pieces.
// On the default path -- enable_split_extracts is on, and TopLevelSTPAux
// runs the pass on every query -- and the walk is over the whole input.
//
// No extract matches a chain of BVXORs over symbols, so what the pass does
// here is exactly the traversal, and finding nothing to split means the
// formula comes back unchanged.
// The incremental driver's check-sat. It used to run its body on a worker
// thread with a 256 MiB stack, because the passes it drives -- the
// per-conjunct simplifier, substitution replace(), the bit-blaster -- were
// depth-recursive. They are not any more, and this is what says so: the
// driver now runs on whatever stack it is called on, so it has to clear the
// same 1 MiB bound as every other pass here.
bool incrementalDriverOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(top);

  // The minimal core: no fitted preparation, promotion or backend policy, so
  // what this measures is the encode/solve path itself.
  c.mgr.UserFlags.incremental_core_only = true;

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer at(&c.mgr, &simp);
  AbsRefine_CounterExample ce(&c.mgr, &simp, &at);
  IncrementalSolver inc(&c.mgr, &ce, &simp, &at);

  const ASTVec stack{top};
  return inc.checkSat(stack) == SOLVER_SATISFIABLE;
}

bool splitExtractsOk(Context& c, unsigned depth)
{
  const ASTNode top = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(top);

  c.mgr.UserFlags.enable_split_extracts = true;

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  SplitExtracts split(c.mgr);

  const ASTNode result = split.topLevel(top, &simp);
  c.roots.push_back(result);
  return result == top && split.getIntroduced() == 0;
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

// Simplifier::SimplifyFormula. The AND/OR spine it nests through is walked
// on the heap; the other boolean kinds still recurse into each other.
bool simplifyOk(Context& c, unsigned depth)
{
  // A chain of ANDs: each operand of each one is simplified by coming back
  // through SimplifyFormula.
  ASTNode f = c.hf->CreateNode(EQ, c.mgr.CreateSymbol("s0", 0, 8),
                               c.mgr.CreateZeroConst(8));
  for (unsigned i = 1; i < depth; i++)
  {
    const std::string name = "s" + std::to_string(i);
    const ASTNode leaf = c.hf->CreateNode(
        EQ, c.mgr.CreateSymbol(name.c_str(), 0, 8), c.mgr.CreateZeroConst(8));
    f = c.hf->CreateNode(AND, leaf, f);
  }
  c.roots.push_back(f);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  const ASTNode result = simp.SimplifyFormula_TopLevel(f, false);
  c.roots.push_back(result);
  return result.GetKind() == AND || result.GetKind() == EQ;
}

// The formula arms that are not AND or OR. Those two were walked on the heap
// first, on the argument that the rest "nest through each other rather than
// through a spine, and nothing has been seen to reach a depth that matters".
// A float chain's lowering nests NOT and if-then-else exactly that way: a
// query built from 8,000 nested fp.add operations died in these two arms, at
// a depth below the deepest input we have.
bool simplifyFormulaSpineOk(Context& c, unsigned depth)
{
  const ASTNode p = c.mgr.CreateSymbol("p", 0, 0);
  ASTNode f = c.hf->CreateNode(EQ, c.mgr.CreateSymbol("s0", 0, 8),
                               c.mgr.CreateZeroConst(8));
  for (unsigned i = 1; i < depth; i++)
  {
    const std::string name = "s" + std::to_string(i);
    const ASTNode leaf = c.hf->CreateNode(
        EQ, c.mgr.CreateSymbol(name.c_str(), 0, 8), c.mgr.CreateZeroConst(8));
    f = c.hf->CreateNode(NOT, c.hf->CreateNode(ITE, p, leaf, f));
  }
  c.roots.push_back(f);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  const ASTNode result = simp.SimplifyFormula_TopLevel(f, false);
  c.roots.push_back(result);
  return result.GetKind() != UNDEFINED;
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

// Simplifier's term side. The job machine must use the same flattened operand
// policy as the old recursive code; simplifying intermediate BVAND/BVOR/
// BVPLUS nodes would change which nodes the pass constructs.
bool simplifyTermOk(Context& c, unsigned depth)
{
  const ASTNode t = c.chain(BVXOR, depth);
  c.roots.push_back(t);
  c.mgr.UserFlags.optimize_flag = true;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  return simp.SimplifyTerm(t).GetValueWidth() == 8;
}

// SimplifyTerm again, for the deep term it reaches through the substitution
// map rather than through a child. The term handed to the pass is shallow;
// everything below it arrives from the map, which is not somewhere a walk
// over children would look.
bool simplifyTermSubstitutedOk(Context& c, unsigned depth)
{
  const ASTNode deep = c.chain(BVXOR, depth);
  c.roots.push_back(deep);

  c.mgr.UserFlags.optimize_flag = true;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);

  const ASTNode s = c.mgr.CreateSymbol("substituted", 0, 8);
  if (!simp.UpdateSolverMap(s, deep))
    return false; // the map refused it: prove nothing quietly.

  const ASTNode t =
      c.hf->CreateTerm(BVMULT, 8, s, c.mgr.CreateSymbol("y0", 0, 8));
  c.roots.push_back(t);
  return simp.SimplifyTerm(t).GetValueWidth() == 8;
}

// The term work frame uses one operand buffer for both the inputs and their
// answers. Exercise every way an entry can be handled: a boolean operand is a
// formula job, a bit-vector operand is a term job, and an array operand stays
// in place until READ schedules its separate array job.
bool simplifyMixedTermOperandsOk(Context& c)
{
  const ASTNode zero = c.mgr.CreateZeroConst(8);
  const ASTNode one = c.mgr.CreateOneConst(8);
  const ASTNode index = c.mgr.CreateBVConst(8, 3);
  const ASTNode stored = c.mgr.CreateBVConst(8, 0x2a);
  const ASTNode array = c.mgr.CreateSymbol("operand-array", 8, 8);

  const ASTNode write =
      c.hf->CreateArrayTerm(WRITE, 8, 8, array, index, stored);
  const ASTNode read = c.hf->CreateTerm(READ, 8, write, index);
  const ASTNode condition = c.hf->CreateNode(EQ, zero, one);
  const ASTNode selected = c.hf->CreateTerm(ITE, 8, condition, one, zero);
  const ASTNode input = c.hf->CreateTerm(BVXOR, 8, selected, read);
  c.roots.push_back(input);

  c.mgr.UserFlags.optimize_flag = true;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  const ASTNode output = simp.SimplifyTerm(input);
  c.roots.push_back(output);
  return output == stored;
}

// A descendant term is prechecked before its frame is pushed. Preserve a
// substitution image found by that check so the frame neither probes the map
// again nor accidentally simplifies the original symbol instead.
bool simplifyPrecheckedSubstitutionOk(Context& c)
{
  const ASTNode one = c.mgr.CreateOneConst(8);
  const ASTNode two = c.mgr.CreateBVConst(8, 2);
  const ASTNode three = c.mgr.CreateBVConst(8, 3);
  const ASTNode substituted = c.mgr.CreateSymbol("prechecked", 0, 8);
  const ASTNode image = c.hf->CreateTerm(BVPLUS, 8, one, two);
  const ASTNode input = c.hf->CreateTerm(BVXOR, 8, substituted,
                                         c.mgr.CreateZeroConst(8));
  c.roots.push_back(image);
  c.roots.push_back(input);

  c.mgr.UserFlags.optimize_flag = true;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  if (!simp.UpdateSolverMap(substituted, image))
    return false;

  const ASTNode output = simp.SimplifyTerm(input);
  c.roots.push_back(output);
  return output == three;
}

// The NOT frame delegates an atomic child to AtomicJob. The child job owns
// the pushed-negation memo entry, while the returning NOT frame owns its
// outer entry; removing duplicate probes and writes must preserve both keys.
bool simplifyNotAtomicMemoOk(Context& c)
{
  const ASTNode zero = c.mgr.CreateZeroConst(8);
  const ASTNode x = c.mgr.CreateSymbol("memo-not-atomic", 0, 8);
  const ASTNode term = c.hf->CreateTerm(BVXOR, 8, x, zero);
  const ASTNode atomic = c.hf->CreateNode(EQ, term, zero);
  const ASTNode input = c.hf->CreateNode(NOT, atomic);
  c.roots.push_back(input);

  c.mgr.UserFlags.optimize_flag = true;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  const ASTNode output = simp.SimplifyFormula(input, false);
  c.roots.push_back(output);

  ASTNode atomicCached;
  ASTNode inputCached;
  return simp.CheckSimplifyMap(atomic, atomicCached, true) &&
         simp.CheckSimplifyMap(input, inputCached, false) &&
         atomicCached == output && inputCached == output &&
         simp.SimplifyFormula(input, false) == output;
}

// Leaves, cached roots and transparent root substitutions are all answered
// before the unified simplifier needs a continuation frame. Exercise each
// shortcut and then a nontrivial substituted image, which must still enter
// the job machine and produce the same result.
bool simplifyRootFastPathsOk(Context& c)
{
  const ASTNode zero = c.mgr.CreateZeroConst(8);
  const ASTNode one = c.mgr.CreateOneConst(8);
  const ASTNode two = c.mgr.CreateBVConst(8, 2);
  const ASTNode x = c.mgr.CreateSymbol("root-fast-x", 0, 8);
  const ASTNode cachedTerm = c.hf->CreateTerm(BVXOR, 8, x, zero);
  const ASTNode cachedFormula = c.hf->CreateNode(EQ, cachedTerm, zero);
  const ASTNode substituted = c.mgr.CreateSymbol("root-fast-sub", 0, 8);
  const ASTNode image = c.hf->CreateTerm(BVPLUS, 8, one, two);
  c.roots.push_back(cachedFormula);
  c.roots.push_back(image);

  c.mgr.UserFlags.optimize_flag = true;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);

  if (simp.SimplifyTerm(zero) != zero ||
      simp.SimplifyFormula(c.mgr.ASTTrue, false) != c.mgr.ASTTrue)
    return false;

  const ASTNode termOutput = simp.SimplifyTerm(cachedTerm);
  const ASTNode formulaOutput = simp.SimplifyFormula(cachedFormula, false);
  if (simp.SimplifyTerm(cachedTerm) != termOutput ||
      simp.SimplifyFormula(cachedFormula, false) != formulaOutput)
    return false;

  if (!simp.UpdateSolverMap(substituted, image))
    return false;
  const ASTNode substitutedOutput = simp.SimplifyTerm(substituted);
  c.roots.push_back(termOutput);
  c.roots.push_back(formulaOutput);
  c.roots.push_back(substitutedOutput);
  return termOutput.GetType() == BITVECTOR_TYPE &&
         formulaOutput.GetType() == BOOLEAN_TYPE &&
         substitutedOutput == c.mgr.CreateBVConst(8, 3);
}

// A descendant request normally answers from the simplification map rather
// than by pushing another work frame. The parent must consume those ready
// term and formula answers in place: yielding and re-dispatching is wasted
// work, while treating a ready answer as a completed parent drops the rest of
// the parent entirely.
bool simplifyReadyDescendantsOk(Context& c)
{
  const ASTNode zero = c.mgr.CreateZeroConst(8);
  const ASTNode x = c.mgr.CreateSymbol("ready-descendant-x", 0, 8);
  const ASTNode y = c.mgr.CreateSymbol("ready-descendant-y", 0, 8);
  const ASTNode z = c.mgr.CreateSymbol("ready-descendant-z", 0, 8);
  const ASTNode left = c.hf->CreateTerm(BVXOR, 8, x, zero);
  const ASTNode right = c.hf->CreateTerm(BVXOR, 8, y, zero);
  const ASTNode third = c.hf->CreateTerm(BVXOR, 8, z, zero);
  const ASTNode equality = c.hf->CreateNode(EQ, left, right);
  const ASTNode top = c.hf->CreateNode(AND, equality, c.mgr.ASTTrue);
  c.roots.push_back(top);

  c.mgr.UserFlags.optimize_flag = true;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);

  // Prime both term continuations and then the formula continuation. Every
  // child request made while simplifying `top` can now answer immediately.
  const ASTNode simplifiedLeft = simp.SimplifyTerm(left);
  const ASTNode simplifiedRight = simp.SimplifyTerm(right);
  const ASTNode simplifiedThird = simp.SimplifyTerm(third);
  const ASTNode simplifiedEquality = simp.SimplifyFormula(equality, false);
  const ASTNode output = simp.SimplifyFormula(top, false);

  // Pin the n-ary loops too: each answer is ready, but every position still
  // has to be consumed exactly once before the parent is rebuilt.
  const ASTNode wideTerm =
      c.hf->CreateTerm(BVXOR, 8, ASTVec{left, right, third});
  const ASTNode expectedTerm = c.nf->CreateTerm(
      BVXOR, 8, ASTVec{simplifiedLeft, simplifiedRight, simplifiedThird});
  const ASTNode termOutput = simp.SimplifyTerm(wideTerm);

  const ASTNode p = c.mgr.CreateSymbol("ready-descendant-p", 0, 0);
  const ASTNode q = c.mgr.CreateSymbol("ready-descendant-q", 0, 0);
  const ASTNode r = c.mgr.CreateSymbol("ready-descendant-r", 0, 0);
  const ASTNode wideAnd =
      c.hf->CreateNode(AND, ASTVec{p, q, r, c.mgr.ASTTrue});
  const ASTNode expectedAnd = c.nf->CreateNode(AND, ASTVec{p, q, r});
  const ASTNode andOutput = simp.SimplifyFormula(wideAnd, false);

  const ASTNode wideXor = c.hf->CreateNode(XOR, ASTVec{p, q, r});
  const ASTNode expectedXor = c.nf->CreateNode(XOR, ASTVec{p, q, r});
  const ASTNode xorOutput = simp.SimplifyFormula(wideXor, false);

  // Unary floating-point predicates collect their term operands through the
  // same ready-answer loop rather than the binary atomic-formula path.
  const ASTNode fp = c.mgr.CreateSymbol("ready-descendant-fp", 0, 16);
  fp.SetExpWidth(5);
  fp.SetSigWidth(11);
  simp.SimplifyTerm(fp);
  const ASTNode fpPredicate = c.hf->CreateNode(FP_ISNAN, fp);
  const ASTNode expectedFpPredicate = c.nf->CreateNode(FP_ISNAN, fp);
  const ASTNode fpOutput = simp.SimplifyFormula(fpPredicate, false);

  c.roots.push_back(simplifiedEquality);
  c.roots.push_back(output);
  c.roots.push_back(termOutput);
  c.roots.push_back(andOutput);
  c.roots.push_back(xorOutput);
  c.roots.push_back(fpOutput);
  return output == simplifiedEquality && termOutput == expectedTerm &&
         andOutput == expectedAnd && xorOutput == expectedXor &&
         fpOutput == expectedFpPredicate;
}

// A term contains a formula which contains the preceding term, at every
// level. Separate iterative formula and term drivers are insufficient for
// this shape: calling from one driver into the other still makes one C++
// frame per alternation.
bool simplifyAlternatingTermFormulaOk(Context& c, unsigned depth)
{
  const ASTNode zero = c.mgr.CreateZeroConst(8);
  const ASTNode one = c.mgr.CreateOneConst(8);
  ASTNode term = c.mgr.CreateSymbol("alternating", 0, 8);
  for (unsigned i = 0; i < depth; ++i)
  {
    const ASTNode condition = c.hf->CreateNode(EQ, term, zero);
    term = c.hf->CreateTerm(ITE, 8, condition, one, zero);
  }
  c.roots.push_back(term);

  c.mgr.UserFlags.optimize_flag = true;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  const ASTNode output = simp.SimplifyTerm(term);
  c.roots.push_back(output);
  return output.GetValueWidth() == 8;
}

// A source expression only three operations deep can lower to a bit-vector
// circuit thousands of terms deep. This is the shape that made term priming
// an incomplete fix: the generated nodes did not exist when the input was
// primed, so SimplifyTerm still descended them recursively. Exponent width
// 11 is the supported boundary for fp.rem and generates the 8,000-level case
// from rem-exponent-width-boundary.smt2; width 5 is the shallow control.
bool simplifyInternallyGeneratedFpTermOk(Context& c, unsigned exponentWidth)
{
  const unsigned significandWidth = 8;
  const unsigned width = exponentWidth + significandWidth;
  const ASTNode x = c.mgr.CreateSymbol("generated-fp", 0, width);
  x.SetExpWidth(exponentWidth);
  x.SetSigWidth(significandWidth);
  const ASTNode rm = c.mgr.CreateBVConst(
      5, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  const ASTNode rounded =
      c.hf->CreateTerm(FP_ROUNDTOINTEGRAL, width, rm, x);
  const ASTNode remainder = c.hf->CreateTerm(FP_REM, width, rounded, x);
  const ASTNode source = c.hf->CreateNode(FP_ISNAN, remainder);
  c.roots.push_back(source);

  FpEncodingContext encoding(&c.mgr);
  const ASTNode prepared = encoding.prepare(source);
  const ASTNode lowered = encoding.lowerPrepared(prepared);
  c.roots.push_back(prepared);
  c.roots.push_back(lowered);
  if (lowered == prepared)
    return false; // no generated circuit means the intended path was missed.
  if (exponentWidth == 11 && dagDepth(lowered) < 4000)
    return false; // keep the low-stack case deep even if lowering changes.

  c.mgr.UserFlags.optimize_flag = true;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  const ASTNode output = simp.SimplifyFormula_TopLevel(lowered, false);
  c.roots.push_back(output);
  return output.GetType() == BOOLEAN_TYPE && output.GetKind() != UNDEFINED;
}

// CreateSimpleEQ peels equal sides from two concat chains. Each peel used to
// re-enter the simplifying node factory and consume another C++ frame.
bool concatEqualityOk(Context& c, unsigned depth)
{
  ASTNode lhsBase = c.mgr.CreateSymbol("concat-lhs", 0, 1);
  ASTNode rhsBase = c.mgr.CreateSymbol("concat-rhs", 0, 1);
  ASTNode lhs = lhsBase;
  ASTNode rhs = rhsBase;
  for (unsigned i = 1; i < depth; ++i)
  {
    const std::string name = "concat-common-" + std::to_string(i);
    const ASTNode common = c.mgr.CreateSymbol(name.c_str(), 0, 1);
    lhs = c.hf->CreateTerm(BVCONCAT, i + 1, lhs, common);
    rhs = c.hf->CreateTerm(BVCONCAT, i + 1, rhs, common);
  }
  c.roots.push_back(lhs);
  c.roots.push_back(rhs);

  const ASTNode expected = c.hf->CreateNode(EQ, lhsBase, rhsBase);
  const ASTNode result = c.nf->CreateNode(EQ, lhs, rhs);
  c.roots.push_back(result);
  return result == expected;
}

// Constant equality takes both concat branches and rebuilds their two
// equalities under AND, so it needs a real continuation frame rather than the
// tail-peeling loop used by the shared-side case above.
bool concatConstantEqualityOk(Context& c, unsigned depth)
{
  ASTNode concat = c.mgr.CreateSymbol("concat-constant-0", 0, 1);
  for (unsigned i = 1; i < depth; ++i)
  {
    const std::string name = "concat-constant-" + std::to_string(i);
    concat = c.hf->CreateTerm(
        BVCONCAT, i + 1, concat,
        c.mgr.CreateSymbol(name.c_str(), 0, 1));
  }
  c.roots.push_back(concat);

  const ASTNode result =
      c.nf->CreateNode(EQ, c.mgr.CreateZeroConst(depth), concat);
  c.roots.push_back(result);
  return result.GetType() == BOOLEAN_TYPE;
}

// Simplifier::CreateSimplifiedEQ compares every bit of the leading constant
// prefixes. Make the only difference their least-significant bit, so it must
// inspect the whole prefix; each lookup must reuse the constant found by one
// descent through these deep concat chains.
bool leadingConcatConstantScanOk(Context& c, unsigned depth)
{
  ASTNode lhs = c.mgr.CreateZeroConst(depth);
  ASTNode rhs = c.mgr.CreateOneConst(depth);
  const ASTNode tail = c.mgr.CreateSymbol("leading-constant-tail", 0, 1);
  for (unsigned i = 0; i < depth; ++i)
  {
    const unsigned width = depth + i + 1;
    lhs = c.hf->CreateTerm(BVCONCAT, width, lhs, tail);
    rhs = c.hf->CreateTerm(BVCONCAT, width, rhs, tail);
  }
  c.roots.push_back(lhs);
  c.roots.push_back(rhs);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  return simp.CreateSimplifiedEQ(lhs, rhs) == c.mgr.ASTFalse;
}

// UseITEContext::visit. Carries a context set down, so neither the walker
// nor priming fits: the same node under two contexts has two answers.
bool useITEContextOk(Context& c, unsigned depth)
{
  const ASTNode f = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(f);
  UseITEContext u(&c.mgr);
  return u.topLevel(f).GetKind() != UNDEFINED;
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

// MutableASTNode::build, the up-and-down graph unconstrained-variable
// elimination runs on. Not an AST walk by signature -- it hands back a
// MutableASTNode, so the recursion checker's ASTNode test never saw it --
// but it descends the input DAG all the same, and this is the shape that
// found it: a formula that alternates NOT and AND has no flat spine for the
// simplifier to collapse, so it reaches RemoveUnconstrained as deep as it
// was written.
bool removeUnconstrainedOk(Context& c, unsigned depth)
{
  ASTNode f = c.hf->CreateNode(EQ, c.mgr.CreateSymbol("u0", 0, 8),
                               c.mgr.CreateZeroConst(8));
  for (unsigned i = 1; i < depth; i++)
  {
    const std::string nm = "u" + std::to_string(i);
    f = c.hf->CreateNode(
        NOT, c.hf->CreateNode(
                 AND, c.hf->CreateNode(EQ, c.mgr.CreateSymbol(nm.c_str(), 0, 8),
                                       c.mgr.CreateZeroConst(8)),
                 f));
  }
  c.roots.push_back(f);

  c.mgr.UserFlags.optimize_flag = true;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  RemoveUnconstrained ru(c.mgr);
  const ASTNode result = ru.topLevel(f, &simp);
  c.roots.push_back(result);
  return result.GetKind() != UNDEFINED;
}

// The mutable graph has walks in both directions: invariant/variable scans
// and dirty rebuilding go down, dirty propagation goes up, and detaching an
// orphaned subtree tears it down in post-order. Exercise all of them on the
// same chain so none can hide behind MutableASTNode::build's iterative walk.
bool mutableDagWalksOk(Context& c, unsigned depth)
{
  const ASTNode input = c.chain(BVXOR, depth);
  c.roots.push_back(input);
  MutableASTNode* root = MutableASTNode::build(input);

  bool ok = root->checkInvariant();
  vector<MutableASTNode*> symbols;
  std::unordered_set<MutableASTNode*> visited;
  root->getAllVariablesRecursively(symbols, visited);
  ok = ok && symbols.size() == depth;

  MutableASTNode* leaf = root;
  unsigned pathDepth = 0;
  while (!leaf->isSymbol())
  {
    MutableASTNode* next = NULL;
    for (MutableASTNode* child : leaf->children)
      if (!child->isSymbol())
      {
        next = child;
        break;
      }
    leaf = next == NULL ? leaf->children[0] : next;
    pathDepth++;
  }
  ok = ok && pathDepth == depth - 1;

  vector<MutableASTNode*> variables;
  leaf->replaceWithVar(c.mgr.CreateSymbol("mutable-leaf", 0, 8), variables);
  const ASTNode rebuilt = root->toASTNode(&c.mgr);
  c.roots.push_back(rebuilt);
  ok = ok && rebuilt != input && !variables.empty();

  // Replacing the root orphans the whole rebuilt chain. removeChildren must
  // finish that teardown without using one call frame per level.
  root->replaceWithVar(c.mgr.CreateSymbol("mutable-root", 0, 8), variables);
  ok = ok && root->toASTNode(&c.mgr) == root->n && root->checkInvariant();
  MutableASTNode::cleanup();
  return ok;
}

// Root-level no-ops should not need a traversal worklist: a repeated variable
// scan is already visited, a symbol has no children to remove, and propagating
// from an already-dirty replacement has nowhere new to go.
bool mutableDagRootFastPathsOk(Context& c)
{
  const ASTNode original = c.mgr.CreateSymbol("mutable-fast-original", 0, 8);
  MutableASTNode* root = MutableASTNode::build(original);

  vector<MutableASTNode*> symbols;
  std::unordered_set<MutableASTNode*> visited;
  root->getAllVariablesRecursively(symbols, visited);
  root->getAllVariablesRecursively(symbols, visited);

  vector<MutableASTNode*> variables;
  root->removeChildren(variables);
  const ASTNode replacement =
      c.mgr.CreateSymbol("mutable-fast-replacement", 0, 8);
  root->replaceWithVar(replacement, variables);
  root->propagateUpDirty();

  const bool ok = symbols.size() == 1 && symbols[0] == root &&
                  variables.empty() && root->toASTNode(&c.mgr) == replacement;
  MutableASTNode::cleanup();
  return ok;
}

// A parent consumes a newly built child directly when its child frame
// returns; it must not need to find that child in `visited` a second time.
// Mix misses and a shared hit so the continuation is pinned to the right
// child position as well as to the right mutable node.
bool mutableDagBuildResumeOrderOk(Context& c)
{
  const ASTNode a = c.mgr.CreateSymbol("mutable-build-a", 0, 8);
  const ASTNode b = c.mgr.CreateSymbol("mutable-build-b", 0, 8);
  const ASTNode d = c.mgr.CreateSymbol("mutable-build-d", 0, 8);
  const ASTNode left = c.hf->CreateTerm(BVXOR, 8, a, b);
  const ASTNode right = c.hf->CreateTerm(BVAND, 8, b, d);
  const ASTNode top = c.hf->CreateTerm(BVPLUS, 8, left, right, left);
  c.roots.push_back(top);

  std::unordered_map<uint64_t, MutableASTNode*> nodes;
  MutableASTNode* root = MutableASTNode::build(top, nodes);
  bool ok = root->children.size() == top.Degree() && nodes.size() == 6;
  for (size_t i = 0; ok && i < top.Degree(); ++i)
  {
    const auto child = nodes.find(top[i].GetNodeNum());
    ok = child != nodes.end() && root->children[i] == child->second;
  }

  const auto leftNode = nodes.find(left.GetNodeNum());
  size_t leftEdges = 0;
  if (leftNode != nodes.end())
  {
    for (MutableASTNode* child : root->children)
      leftEdges += child == leftNode->second;
  }
  ok = ok && leftNode != nodes.end() && leftEdges == 2 &&
       leftNode->second->parents.count(root) == 1;
  MutableASTNode::cleanup();
  return ok;
}

// Dirty rebuilding can reach the same mutable child through more than one
// parent. The first route rebuilds it and later routes reuse the stored AST;
// the parent must gather both answers in operand order even though rebuild
// frames no longer retain their own child vectors.
bool mutableDagSharedRebuildOk(Context& c)
{
  const ASTNode x = c.mgr.CreateSymbol("mutable-rebuild-x", 0, 8);
  const ASTNode y = c.mgr.CreateSymbol("mutable-rebuild-y", 0, 8);
  const ASTNode z = c.mgr.CreateSymbol("mutable-rebuild-z", 0, 8);
  const ASTNode shared = c.hf->CreateTerm(BVXOR, 8, x, y);
  const ASTNode left = c.hf->CreateTerm(BVPLUS, 8, shared, z);
  const ASTNode right = c.hf->CreateTerm(BVAND, 8, z, shared);
  const ASTNode top = c.hf->CreateTerm(BVPLUS, 8, left, right, z);
  c.roots.push_back(top);

  std::unordered_map<uint64_t, MutableASTNode*> nodes;
  MutableASTNode* root = MutableASTNode::build(top, nodes);
  vector<MutableASTNode*> variables;
  const ASTNode replacement =
      c.mgr.CreateSymbol("mutable-rebuild-replacement", 0, 8);
  nodes.at(x.GetNodeNum())->replaceWithVar(replacement, variables);

  const ASTNode expectedShared =
      c.hf->CreateTerm(BVXOR, 8, replacement, y);
  const ASTNode expectedLeft =
      c.hf->CreateTerm(BVPLUS, 8, expectedShared, z);
  const ASTNode expectedRight =
      c.hf->CreateTerm(BVAND, 8, z, expectedShared);
  const ASTNode expected =
      c.hf->CreateTerm(BVPLUS, 8, expectedLeft, expectedRight, z);
  const ASTNode rebuilt = root->toASTNode(&c.mgr);
  c.roots.push_back(rebuilt);

  const bool ok = rebuilt == expected && root->toASTNode(&c.mgr) == rebuilt &&
                  variables.size() == 1 && root->checkInvariant();
  MutableASTNode::cleanup();
  return ok;
}

// Mutable parents are a set, so two edges from one parent represent one
// parent relationship. Detaching such a DAG must likewise process that
// relationship once. Otherwise every duplicate edge revisits an already
// orphaned child: n[i] = xor(n[i-1], n[i-1]) takes 2^i work, and a symbol
// retained by another parent is reported once per path.
bool mutableDagRepeatedEdgesOk(Context& c)
{
  const ASTNode shared = c.mgr.CreateSymbol("mutable-shared", 0, 8);
  ASTNode repeated = shared;
  for (unsigned i = 0; i < 12; ++i)
    repeated = c.hf->CreateTerm(BVXOR, 8, repeated, repeated);

  const ASTNode keeper = c.hf->CreateTerm(
      BVXOR, 8, shared,
      c.mgr.CreateSymbol("mutable-keeper-child", 0, 8));
  const ASTNode top = c.hf->CreateTerm(BVPLUS, 8, repeated, keeper);
  c.roots.push_back(top);

  std::unordered_map<uint64_t, MutableASTNode*> nodes;
  MutableASTNode::build(top, nodes);
  MutableASTNode* repeatedMutable = nodes.at(repeated.GetNodeNum());

  vector<MutableASTNode*> variables;
  repeatedMutable->removeChildren(variables);
  const bool ok = variables.size() == 1 && variables[0]->n == shared &&
                  variables[0]->parents.size() == 1;
  MutableASTNode::cleanup();
  return ok;
}

// WorkList::addToWorklist, which seeds constant-bit propagation by walking
// the whole input. A constant somewhere in the chain is what puts nodes on
// the worklist at all, so the chain is built with one.
bool workListOk(Context& c, unsigned depth)
{
  ASTNode t = c.mgr.CreateSymbol("k0", 0, 8);
  for (unsigned i = 1; i < depth; i++)
  {
    const std::string nm = "k" + std::to_string(i);
    t = c.hf->CreateTerm(BVXOR, 8, t, c.mgr.CreateSymbol(nm.c_str(), 0, 8));
    t = c.hf->CreateTerm(BVPLUS, 8, t, c.mgr.CreateOneConst(8));
  }
  const ASTNode f = c.formula(t);
  c.roots.push_back(f);

  simplifier::constantBitP::WorkList wl(f);
  return wl.size() > 0;
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
  CommonSubSum css(&c.mgr, c.nf, BVPLUS);
  ASTNode g = f;
  return css.topLevel(g).GetKind() != UNDEFINED;
}

// ArrayTransformer, whose three functions -- TransformFormula,
// TransformTerm and TransformArrayRead -- reach each other once per level of
// the input, and are one walk on the heap.
//
// Priming would not have done here, which is why this one is a state
// machine: the ITE arms transform the condition and then only the branch
// that survives it, telling the extensionality context which branch they
// dropped, and which that is cannot be known until the condition has been
// transformed. Nor does the operands hook rescue it, as SimplifyTerm's
// flattening was rescued: the hook would have to run the pass to answer.
bool arrayTransformerOk(Context& c, unsigned depth)
{
  const ASTNode f = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(f);
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer at(&c.mgr, &simp);
  return at.TransformFormula_TopLevel(f).GetKind() != UNDEFINED;
}

// A chain of reads, each indexing the array with the last one's result.
// TransformArrayRead transforms a read's index by handing it back to
// TransformTerm, so this is the input's nesting and not the pass's.
bool arrayReadChainOk(Context& c, unsigned depth)
{
  const ASTNode a = c.mgr.CreateSymbol("A", 8, 8);
  ASTNode t = c.mgr.CreateSymbol("i", 0, 8);
  for (unsigned i = 0; i < depth; i++)
    t = c.hf->CreateTerm(READ, 8, a, t);

  const ASTNode f = c.formula(t);
  c.roots.push_back(f);
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer at(&c.mgr, &simp);
  const ASTNode result = at.TransformFormula_TopLevel(f);
  c.roots.push_back(result);
  // Every read is abstracted to a fresh variable, so nothing of the chain
  // may be left.
  return result.GetKind() != UNDEFINED;
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

// Complete-DAG kind queries are used at solve boundaries, where the formula
// may be supplied by the caller and therefore arbitrarily deep.
bool containsKindWalkOk(Context& c, unsigned depth)
{
  const ASTNode deep = c.chain(BVXOR, depth);
  const ASTNode formula = c.formula(deep);
  c.roots.push_back(formula);
  return containsKind(formula, BVXOR) && !containsKind(formula, ARRAY_EQ);
}

// A chain of writes under one read. The read is pushed under the writes one
// at a time, each step building a new read over the array below it and
// transforming that -- so the walk descends the write chain, which is again
// the input's nesting.
bool arrayWriteChainOk(Context& c, unsigned depth)
{
  ASTNode a = c.mgr.CreateSymbol("A", 8, 8);
  for (unsigned i = 0; i < depth; i++)
  {
    const std::string nm = "w" + std::to_string(i);
    a = c.hf->CreateArrayTerm(WRITE, 8, 8, a,
                              c.mgr.CreateSymbol(nm.c_str(), 0, 8),
                              c.mgr.CreateZeroConst(8));
  }
  const ASTNode f =
      c.formula(c.hf->CreateTerm(READ, 8, a, c.mgr.CreateSymbol("j", 0, 8)));
  c.roots.push_back(f);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer at(&c.mgr, &simp);
  const ASTNode result = at.TransformFormula_TopLevel(f);
  c.roots.push_back(result);
  return result.GetKind() != UNDEFINED;
}

// Solve-boundary array equality lowering used a recursive std::function for
// this post-order rebuild. A write chain is unchanged below the equality but
// still drove that function one native frame per write; at 5,000 writes it
// dies under a 512 KiB stack before any ordinary preprocessing runs.
bool arrayEqualityLoweringOk(Context& c, unsigned depth)
{
  c.mgr.UserFlags.enable_array_equality = true;
  ASTNode chain = c.mgr.CreateSymbol("lower-array-a", 16, 8);
  const ASTNode other = c.mgr.CreateSymbol("lower-array-b", 16, 8);
  const ASTNode index = c.mgr.CreateSymbol("lower-array-i", 0, 16);
  const ASTNode value = c.mgr.CreateSymbol("lower-array-v", 0, 8);
  for (unsigned i = 0; i < depth; ++i)
    chain = c.hf->CreateArrayTerm(WRITE, 16, 8, chain, index, value);

  const ASTNode opaque = c.hf->CreateNode(EQ, chain, other);
  c.roots.push_back(opaque);

  ExtensionalityContext ext(&c.mgr);
  ext.beginSolve();
  const ASTNode lowered = ext.lowerArrayEqualities(opaque);
  c.roots.push_back(lowered);
  return lowered.GetKind() == SYMBOL && ext.getRecords().size() == 1 &&
         ext.getActiveRecordCount() == 1;
}

// TransformFormula's own spine. A conjunction reaches this pass flat in
// ordinary use, because the simplifier collapses it first -- but that is the
// simplifier's doing, not a property of this pass, and the pass is reachable
// without it.
bool transformFormulaSpineOk(Context& c, unsigned depth)
{
  ASTNode f = c.hf->CreateNode(EQ, c.mgr.CreateSymbol("t0", 0, 8),
                               c.mgr.CreateZeroConst(8));
  for (unsigned i = 1; i < depth; i++)
  {
    const std::string nm = "t" + std::to_string(i);
    f = c.hf->CreateNode(
        NOT, c.hf->CreateNode(
                 AND, c.hf->CreateNode(EQ, c.mgr.CreateSymbol(nm.c_str(), 0, 8),
                                       c.mgr.CreateZeroConst(8)),
                 f));
  }
  c.roots.push_back(f);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer at(&c.mgr, &simp);
  const ASTNode result = at.TransformFormula_TopLevel(f);
  c.roots.push_back(result);
  return result.GetKind() != UNDEFINED;
}

// Counterexample evaluation. TermToConstTermUsingModel and
// ComputeFormulaUsingModel evaluate the ORIGINAL formula against the model a
// sat answer produced, and reached each other once per level of it, so a term
// nested deeply enough took the stack with them. Two frames per level: a
// chain of 30,000 selects died here at the ordinary 8 MiB, and it was the
// last thing on that input's path that did.
//
// Neither generic tool fits, which is why it is a state machine. The term
// side has no memo to prime -- only CounterExampleMap, written for array
// reads and float encodings -- and a memo could not be keyed on the node
// alone anyway, since the answer depends on ArrayReadFlag and on whether the
// walk is already inside an encoded evaluation. And both sides evaluate an
// if-then-else's condition and then only the branch it leaves alive, where a
// dropped branch is not merely wasted work: it can be genuinely unevaluable
// against the model, and both call FatalError when it is. So priming would
// turn a working query into an abort.
//
// No solve is needed to reach it: with an empty model every symbol takes its
// default and the walk still descends the whole term.
bool counterExampleEvalOk(Context& c, unsigned depth)
{
  const ASTNode a = c.mgr.CreateSymbol("A", 8, 8);
  ASTNode t = c.mgr.CreateSymbol("i", 0, 8);
  for (unsigned i = 0; i < depth; i++)
    t = c.hf->CreateTerm(READ, 8, a, t);

  const ASTNode f = c.formula(t);
  c.roots.push_back(f);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer at(&c.mgr, &simp);
  AbsRefine_CounterExample ce(&c.mgr, &simp, &at);

  return ce.ComputeFormulaUsingModel(f).isConstant();
}

// The formula side's own spine, which is the arm nearly every query reaches:
// a connective evaluates each operand and rebuilds over the answers.
bool counterExampleFormulaOk(Context& c, unsigned depth)
{
  ASTNode f = c.hf->CreateNode(EQ, c.mgr.CreateSymbol("t0", 0, 8),
                               c.mgr.CreateZeroConst(8));
  for (unsigned i = 1; i < depth; i++)
  {
    const std::string nm = "t" + std::to_string(i);
    f = c.hf->CreateNode(
        NOT, c.hf->CreateNode(
                 AND, c.hf->CreateNode(EQ, c.mgr.CreateSymbol(nm.c_str(), 0, 8),
                                       c.mgr.CreateZeroConst(8)),
                 f));
  }
  c.roots.push_back(f);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer at(&c.mgr, &simp);
  AbsRefine_CounterExample ce(&c.mgr, &simp, &at);

  return ce.ComputeFormulaUsingModel(f).isConstant();
}

// A chain of if-then-else terms, which is the shape the two functions are
// mutually recursive for: each level evaluates a condition as a formula and
// then descends into the branch it leaves alive as a term.
//
// This case wanted the float format of each level derived as the chain was
// built, because asking a nested if-then-else its type used to overflow
// deriving that format before this walk got a turn. deep_fp_format_ite below
// is that recursion, converted and tested on its own, so the chain is left
// cold here.
bool counterExampleTermIteOk(Context& c, unsigned depth)
{
  const ASTNode t = iteChain(c, depth);
  c.roots.push_back(t);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer at(&c.mgr, &simp);
  AbsRefine_CounterExample ce(&c.mgr, &simp, &at);

  // ModelValueOfTerm asks with the read-tolerant flag off, so every level has
  // to come back a constant.
  return ce.ModelValueOfTerm(t).GetKind() == BVCONST;
}

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

// The LISP printer, which is what operator<< on a node uses -- so a deep
// node cannot even be printed, including from an error path.
bool printerLispOk(Context& c, unsigned depth)
{
  const ASTNode f = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(f);
  std::ostringstream os;
  os << f;
  return os.str().size() > 0;
}

// The SMT-LIB2 printer, behind --print-back-SMTLIB2. The same shape as the
// LISP printer, which is done, but about thirty arms each interleaving
// their own text with their operands, so it is a long mechanical
// conversion rather than a subtle one. Its output is exactly checkable,
// which is what makes it low risk.
bool printerSMTLIB2Ok(Context& c, unsigned depth)
{
  const ASTNode f = c.formula(c.chain(BVXOR, depth));
  c.roots.push_back(f);
  std::ostringstream os;
  printer::SMTLIB2_Print1(os, f, 0, false);
  return os.str().size() > 0;
}

/* Control cases: the same properties on a chain shallow enough for the
   recursive implementations. These pass today, so a deep case failing is
   about stack depth and nothing else. */
TEST(DeepDag, shallow_dependencies_build)
{
  Context c;
  EXPECT_TRUE(dependenciesChainOk(c, SHALLOW));
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

TEST(DeepDag, shallow_extract_over_concat)
{
  Context c;
  EXPECT_TRUE(extractOverConcatOk(c, SHALLOW));
}

TEST(DeepDag, shallow_remainder_folding)
{
  Context c;
  EXPECT_TRUE(remainderFoldingOk(c, SHALLOW));
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

TEST(DeepDag, shallow_incremental_driver)
{
  Context c;
  EXPECT_TRUE(incrementalDriverOk(c, SHALLOW));
}

TEST(DeepDag, shallow_split_extracts)
{
  Context c;
  EXPECT_TRUE(splitExtractsOk(c, SHALLOW));
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

TEST(DeepDag, work_list_shared_edges_are_visited_once)
{
  Context c;
  const ASTNode symbol = c.mgr.CreateSymbol("work-list-shared", 0, 8);
  const ASTNode one = c.mgr.CreateOneConst(8);
  const ASTNode dependsOnConstant = c.hf->CreateTerm(BVXOR, 8, symbol, one);
  const ASTNode shared = c.hf->CreateTerm(BVNOT, 8, dependsOnConstant);
  const ASTNode top = c.hf->CreateTerm(BVXOR, 8, shared, shared);

  simplifier::constantBitP::WorkList workList(top);
  ASSERT_EQ(1, workList.size());
  EXPECT_EQ(dependsOnConstant, workList.pop());
  EXPECT_TRUE(workList.isEmpty());
}

TEST(DeepDag, shallow_strength_reduction)
{
  Context c;
  EXPECT_TRUE(strengthReductionOk(c, SHALLOW));
}

TEST(DeepDag, shallow_simplify)
{
  Context c;
  EXPECT_TRUE(simplifyOk(c, SHALLOW));
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

TEST(DeepDag, simplify_term_preserves_mixed_operand_positions)
{
  Context c;
  EXPECT_TRUE(simplifyMixedTermOperandsOk(c));
}

TEST(DeepDag, simplify_term_preserves_prechecked_substitution)
{
  Context c;
  EXPECT_TRUE(simplifyPrecheckedSubstitutionOk(c));
}

TEST(DeepDag, simplify_not_atomic_preserves_memo_edges)
{
  Context c;
  EXPECT_TRUE(simplifyNotAtomicMemoOk(c));
}

TEST(DeepDag, simplifier_root_fast_paths_preserve_results)
{
  Context c;
  EXPECT_TRUE(simplifyRootFastPathsOk(c));
}

TEST(DeepDag, simplifier_consumes_ready_descendants_in_place)
{
  Context c;
  EXPECT_TRUE(simplifyReadyDescendantsOk(c));
}

TEST(DeepDag, shallow_simplify_alternating_term_formula)
{
  Context c;
  EXPECT_TRUE(simplifyAlternatingTermFormulaOk(c, SHALLOW));
}

TEST(DeepDag, shallow_simplify_internally_generated_fp_term)
{
  Context c;
  EXPECT_TRUE(simplifyInternallyGeneratedFpTermOk(c, 5));
}

TEST(DeepDag, shallow_concat_equality)
{
  Context c;
  EXPECT_TRUE(concatEqualityOk(c, SHALLOW));
}

TEST(DeepDag, shallow_concat_constant_equality)
{
  Context c;
  EXPECT_TRUE(concatConstantEqualityOk(c, SHALLOW));
}

TEST(DeepDag, shallow_leading_concat_constant_scan)
{
  Context c;
  EXPECT_TRUE(leadingConcatConstantScanOk(c, SHALLOW));
}

TEST(DeepDag, shallow_mutable_dag_walks)
{
  Context c;
  EXPECT_TRUE(mutableDagWalksOk(c, SHALLOW));
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

TEST(DeepDag, shallow_contains_kind_walk)
{
  Context c;
  EXPECT_TRUE(containsKindWalkOk(c, SHALLOW));
}

TEST(DeepDag, mutable_dag_root_fast_paths_preserve_no_ops)
{
  Context c;
  EXPECT_TRUE(mutableDagRootFastPathsOk(c));
}

TEST(DeepDag, mutable_dag_repeated_edges_are_detached_once)
{
  Context c;
  EXPECT_TRUE(mutableDagRepeatedEdgesOk(c));
}

TEST(DeepDag, mutable_dag_build_consumes_returned_children_in_order)
{
  Context c;
  EXPECT_TRUE(mutableDagBuildResumeOrderOk(c));
}

TEST(DeepDag, mutable_dag_shared_children_rebuild_in_operand_order)
{
  Context c;
  EXPECT_TRUE(mutableDagSharedRebuildOk(c));
}

TEST(DeepDag, counterexample_prechecked_heads_preserve_model_values)
{
  Context c;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer transformer(&c.mgr, &simp);
  AbsRefine_CounterExample ce(&c.mgr, &simp, &transformer);

  const ASTNode zero = c.mgr.CreateZeroConst(8);
  const ASTNode one = c.mgr.CreateOneConst(8);

  // Constants and Boolean constants are answered by the job head itself.
  EXPECT_EQ(zero, ce.ModelValueOfTerm(zero));
  EXPECT_EQ(c.mgr.ASTTrue, ce.ModelValueOfFormula(c.mgr.ASTTrue));
  EXPECT_EQ(c.mgr.ASTFalse, ce.ModelValueOfFormula(c.mgr.ASTFalse));

  // A recorded non-constant still needs a frame, but the map lookup that
  // discovered its image must carry through to that frame rather than being
  // repeated when it starts.
  const ASTNode x = c.mgr.CreateSymbol("ce-head-x", 0, 8);
  const ASTNode y = c.mgr.CreateSymbol("ce-head-y", 0, 8);
  ce.InsertIntoCounterExampleMap(x, y);
  ce.InsertIntoCounterExampleMap(y, one);
  EXPECT_EQ(one, ce.ModelValueOfTerm(x));

  const ASTNode p = c.mgr.CreateSymbol("ce-head-p", 0, 0);
  ce.InsertIntoCounterExampleMap(p, c.mgr.ASTTrue);
  EXPECT_EQ(c.mgr.ASTTrue, ce.ModelValueOfFormula(p));
  // The second question is a ComputeFormulaMap root hit.
  EXPECT_EQ(c.mgr.ASTTrue, ce.ModelValueOfFormula(p));

  // Exercise the corresponding prechecked image path in the read-over-write
  // expander, not merely the term and formula jobs.
  const ASTNode array = c.mgr.CreateSymbol("ce-head-array", 8, 8);
  const ASTNode write = c.hf->CreateArrayTerm(WRITE, 8, 8, array, zero, one);
  const ASTNode read = c.hf->CreateTerm(READ, 8, write, zero);
  const ASTNode recorded = c.mgr.CreateSymbol("ce-head-read", 0, 8);
  ce.InsertIntoCounterExampleMap(read, recorded);
  ce.InsertIntoCounterExampleMap(recorded, one);
  EXPECT_EQ(one, ce.Expand_ReadOverWrite_UsingModel(read, false));
}

TEST(DeepDag, counterexample_consumes_ready_descendants_in_place)
{
  Context c;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer transformer(&c.mgr, &simp);
  AbsRefine_CounterExample ce(&c.mgr, &simp, &transformer);

  const ASTNode zero = c.mgr.CreateZeroConst(8);
  const ASTNode one = c.mgr.CreateOneConst(8);
  const ASTNode x = c.mgr.CreateSymbol("ce-ready-x", 0, 8);
  const ASTNode y = c.mgr.CreateSymbol("ce-ready-y", 0, 8);
  ce.InsertIntoCounterExampleMap(x, one);
  ce.InsertIntoCounterExampleMap(y, zero);

  // Both term operands are immediate model-map hits. The containing formula
  // then consumes the completed term without suspending either job.
  const ASTNode sum = c.hf->CreateTerm(BVPLUS, 8, x, y);
  const ASTNode equality = c.hf->CreateNode(EQ, sum, one);
  EXPECT_EQ(c.mgr.ASTTrue, ce.ModelValueOfFormula(equality));

  // A formula memo hit follows the same continuation path.
  const ASTNode p = c.mgr.CreateSymbol("ce-ready-p", 0, 0);
  ce.InsertIntoCounterExampleMap(p, c.mgr.ASTTrue);
  EXPECT_EQ(c.mgr.ASTTrue, ce.ModelValueOfFormula(p));
  EXPECT_EQ(c.mgr.ASTTrue,
            ce.ModelValueOfFormula(c.hf->CreateNode(AND, p, p)));

  // The read-over-write expander consumes constant indexes and the selected
  // value directly as well.
  const ASTNode array = c.mgr.CreateSymbol("ce-ready-array", 8, 8);
  const ASTNode write = c.hf->CreateArrayTerm(WRITE, 8, 8, array, zero, one);
  const ASTNode read = c.hf->CreateTerm(READ, 8, write, zero);
  EXPECT_EQ(one, ce.Expand_ReadOverWrite_UsingModel(read, false));
}

TEST(DeepDag, counterexample_continuation_paths_preserve_model_values)
{
  Context c;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer transformer(&c.mgr, &simp);
  AbsRefine_CounterExample ce(&c.mgr, &simp, &transformer);

  const ASTNode zero = c.mgr.CreateZeroConst(8);
  const ASTNode one = c.mgr.CreateOneConst(8);
  const ASTNode two = c.mgr.CreateBVConst(8, 2);
  const ASTNode three = c.mgr.CreateBVConst(8, 3);
  const ASTNode maximum = c.mgr.CreateMaxConst(8);
  const ASTNode x = c.mgr.CreateSymbol("ce-path-x", 0, 8);
  const ASTNode y = c.mgr.CreateSymbol("ce-path-y", 0, 8);
  const ASTNode p = c.mgr.CreateSymbol("ce-path-p", 0, 0);
  const ASTNode q = c.mgr.CreateSymbol("ce-path-q", 0, 0);
  ce.InsertIntoCounterExampleMap(x, one);
  ce.InsertIntoCounterExampleMap(y, two);
  ce.InsertIntoCounterExampleMap(p, c.mgr.ASTTrue);
  ce.InsertIntoCounterExampleMap(q, c.mgr.ASTFalse);

  // Formula continuations: a term operand, formula operands, Boolean
  // extraction, and conditionally evaluating just one ITE branch.
  const ASTNode sum = c.hf->CreateTerm(BVPLUS, 8, x, y);
  EXPECT_EQ(c.mgr.ASTTrue,
            ce.ModelValueOfFormula(c.hf->CreateNode(EQ, sum, three)));
  EXPECT_EQ(c.mgr.ASTTrue, ce.ModelValueOfFormula(c.hf->CreateNode(
                               AND, p, c.hf->CreateNode(NOT, q))));
  EXPECT_EQ(c.mgr.ASTTrue, ce.ModelValueOfFormula(c.hf->CreateNode(
                               BOOLEXTRACT, x, c.mgr.CreateBVConst(32, 0))));
  EXPECT_EQ(c.mgr.ASTFalse,
            ce.ModelValueOfFormula(c.hf->CreateNode(ITE, p, q, c.mgr.ASTTrue)));

  // Term continuations: ordinary operands and a selected ITE branch.
  EXPECT_EQ(three, ce.ModelValueOfTerm(sum));
  EXPECT_EQ(one, ce.ModelValueOfTerm(c.hf->CreateTerm(ITE, 8, p, x, y)));

  const ASTNode base = c.mgr.CreateSymbol("ce-path-array", 8, 8);
  const ASTNode other = c.mgr.CreateSymbol("ce-path-other", 8, 8);
  const ASTNode symbolicIndex = c.mgr.CreateSymbol("ce-path-index", 0, 8);
  const ASTNode plainRead = c.hf->CreateTerm(READ, 8, base, symbolicIndex);

  // The formerly uncovered completion path: a read requested as a concrete
  // value, with array equality disabled and no model entry, is all ones.
  c.mgr.UserFlags.enable_array_equality = false;
  EXPECT_EQ(maximum, ce.ModelValueOfTerm(plainRead));

  // Expansion resumes both when a write hits and when it misses and pushes
  // the read into the base array.
  const ASTNode write = c.hf->CreateArrayTerm(WRITE, 8, 8, base, zero, one);
  EXPECT_EQ(one, ce.Expand_ReadOverWrite_UsingModel(
                     c.hf->CreateTerm(READ, 8, write, zero), false));
  EXPECT_EQ(maximum, ce.Expand_ReadOverWrite_UsingModel(
                         c.hf->CreateTerm(READ, 8, write, two), false));

  // A read over an array ITE keeps its evaluated index while the condition
  // and selected read are evaluated below it.
  const ASTNode otherAtZero = c.mgr.CreateTerm(READ, 8, other, zero);
  ce.InsertIntoCounterExampleMap(otherAtZero, two);
  const ASTNode arrayChoice = c.hf->CreateArrayTerm(ITE, 8, 8, q, base, other);
  EXPECT_EQ(two,
            ce.ModelValueOfTerm(c.hf->CreateTerm(READ, 8, arrayChoice, zero)));

  // Equality propagation can leave an array symbol as an alias for an array
  // term. The definition continuation must evaluate the read through it.
  const ASTNode alias = c.mgr.CreateSymbol("ce-path-alias", 8, 8);
  ce.InsertIntoCounterExampleMap(alias, write);
  EXPECT_EQ(one, ce.ModelValueOfTerm(c.hf->CreateTerm(READ, 8, alias, zero)));
}

TEST(DeepDag, array_transformer_job_specific_operands_preserve_paths)
{
  Context c;
  const ASTNode guard = c.mgr.CreateSymbol("array-guard", 0, 0);
  const ASTNode cond = c.mgr.CreateSymbol("array-cond", 0, 0);
  const ASTNode array = c.mgr.CreateSymbol("array-buffer", 8, 8);
  const ASTNode index = c.mgr.CreateSymbol("array-index", 0, 8);
  const ASTNode read = c.hf->CreateTerm(READ, 8, array, index);
  const ASTNode sum = c.hf->CreateTerm(
      BVXOR, 8, read, c.mgr.CreateOneConst(8));
  const ASTNode choice = c.hf->CreateTerm(
      ITE, 8, cond, sum, c.mgr.CreateZeroConst(8));
  const ASTNode equality = c.hf->CreateNode(
      EQ, choice, c.mgr.CreateSymbol("array-rhs", 0, 8));
  // Transforming equality suspends below an already completed guard. This
  // pins the shared operand arena's nonzero child range: finishing the
  // equality must remove only its suffix, leaving the parent's guard intact.
  const ASTNode input = c.hf->CreateNode(AND, guard, equality);

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer transformer(&c.mgr, &simp);
  const ASTNode result = transformer.TransformFormula_TopLevel(input);

  bool sawIte = false;
  bool sawGenericTerm = false;
  bool sawRead = false;
  bool sawGuard = false;
  ASTNodeSet visited;
  ASTVec pending{result};
  while (!pending.empty())
  {
    const ASTNode n = pending.back();
    pending.pop_back();
    if (!visited.insert(n).second)
      continue;
    sawIte |= n.GetKind() == ITE;
    sawGenericTerm |= n.GetKind() == BVXOR;
    sawRead |= n.GetKind() == READ;
    sawGuard |= n == guard;
    pending.insert(pending.end(), n.begin(), n.end());
  }

  EXPECT_EQ(AND, result.GetKind());
  EXPECT_TRUE(sawIte);
  EXPECT_TRUE(sawGenericTerm);
  EXPECT_TRUE(sawGuard);
  EXPECT_FALSE(sawRead);
  ASSERT_EQ(1U, transformer.arrayToIndexToRead.count(array));
  EXPECT_EQ(1U, transformer.arrayToIndexToRead.at(array).count(index));
}

TEST(DeepDag, array_transformer_read_state_survives_nested_arena_growth)
{
  Context c;
  const ASTNode cond = c.mgr.CreateSymbol("read-state-cond", 0, 0);
  const ASTNode thnArray = c.mgr.CreateSymbol("read-state-thn", 8, 8);
  const ASTNode elsArray = c.mgr.CreateSymbol("read-state-els", 8, 8);
  const ASTNode index = c.mgr.CreateSymbol("read-state-index", 0, 8);
  const ASTNode arrayIte = c.hf->CreateArrayTerm(
      ITE, 8, 8, cond, thnArray, elsArray);
  const ASTNode read = c.hf->CreateTerm(READ, 8, arrayIte, index);
  const ASTNode input = c.hf->CreateNode(
      EQ, read, c.mgr.CreateSymbol("read-state-rhs", 0, 8));

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer transformer(&c.mgr, &simp);
  const ASTNode result = transformer.TransformFormula_TopLevel(input);

  // Transforming each ITE arm pushes another Read frame. The outer frame's
  // condition and pending else-read must survive growth of the shared
  // continuation arena.
  bool sawIte = false;
  bool sawRead = false;
  ASTNodeSet visited;
  ASTVec pending{result};
  while (!pending.empty())
  {
    const ASTNode n = pending.back();
    pending.pop_back();
    if (!visited.insert(n).second)
      continue;
    sawIte |= n.GetKind() == ITE;
    sawRead |= n.GetKind() == READ;
    pending.insert(pending.end(), n.begin(), n.end());
  }

  EXPECT_TRUE(sawIte);
  EXPECT_FALSE(sawRead);
  ASSERT_EQ(1U, transformer.arrayToIndexToRead.count(thnArray));
  ASSERT_EQ(1U, transformer.arrayToIndexToRead.count(elsArray));
  EXPECT_EQ(1U, transformer.arrayToIndexToRead.at(thnArray).count(index));
  EXPECT_EQ(1U, transformer.arrayToIndexToRead.at(elsArray).count(index));
}

TEST(DeepDag, array_transformer_selected_and_write_continuations)
{
  Context c;
  const ASTNode zero = c.mgr.CreateZeroConst(8);
  const ASTNode one = c.mgr.CreateOneConst(8);
  const ASTNode two = c.mgr.CreateBVConst(8, 2);
  const ASTNode base = c.mgr.CreateSymbol("transform-path-base", 8, 8);
  const ASTNode dropped = c.mgr.CreateSymbol("transform-path-dropped", 8, 8);
  const ASTNode write = c.hf->CreateArrayTerm(WRITE, 8, 8, base, zero, one);
  const ASTNode writeHit = c.hf->CreateTerm(READ, 8, write, zero);
  const ASTNode writeMiss = c.hf->CreateTerm(READ, 8, write, two);
  const ASTNode baseRead = c.hf->CreateTerm(READ, 8, base, zero);
  const ASTNode droppedRead = c.hf->CreateTerm(READ, 8, dropped, zero);

  // Both term ITE and read-over-array-ITE should transform only the branch
  // selected by a constant condition. The write cases exercise both the
  // direct hit and the read pushed into the base array after a miss.
  const ASTNode termChoice =
      c.hf->CreateTerm(ITE, 8, c.mgr.ASTTrue, baseRead, droppedRead);
  const ASTNode arrayChoice =
      c.hf->CreateArrayTerm(ITE, 8, 8, c.mgr.ASTTrue, base, dropped);
  const ASTNode arrayChoiceRead = c.hf->CreateTerm(READ, 8, arrayChoice, zero);
  const ASTNode input =
      c.hf->CreateNode(AND, ASTVec{c.hf->CreateNode(EQ, writeHit, one),
                                   c.hf->CreateNode(EQ, writeMiss, two),
                                   c.hf->CreateNode(EQ, termChoice, one),
                                   c.hf->CreateNode(EQ, arrayChoiceRead, one)});

  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer transformer(&c.mgr, &simp);
  const ASTNode result = transformer.TransformFormula_TopLevel(input);

  bool sawRead = false;
  ASTNodeSet visited;
  ASTVec pending{result};
  while (!pending.empty())
  {
    const ASTNode n = pending.back();
    pending.pop_back();
    if (!visited.insert(n).second)
      continue;
    sawRead |= n.GetKind() == READ;
    pending.insert(pending.end(), n.begin(), n.end());
  }

  EXPECT_FALSE(sawRead);
  EXPECT_EQ(0U, transformer.arrayToIndexToRead.count(dropped));
  ASSERT_EQ(1U, transformer.arrayToIndexToRead.count(base));
  EXPECT_EQ(1U, transformer.arrayToIndexToRead.at(base).count(zero));
  EXPECT_EQ(1U, transformer.arrayToIndexToRead.at(base).count(two));
}

TEST(DeepDag, array_transformer_root_fast_paths_preserve_leaf_formulas)
{
  Context c;
  SubstitutionMap sm(&c.mgr);
  Simplifier simp(&c.mgr, &sm);
  ArrayTransformer transformer(&c.mgr, &simp);
  const ASTNode symbol = c.mgr.CreateSymbol("array-root-symbol", 0, 0);

  EXPECT_EQ(c.mgr.ASTTrue,
            transformer.TransformFormula_TopLevel(c.mgr.ASTTrue));
  EXPECT_EQ(c.mgr.ASTFalse,
            transformer.TransformFormula_TopLevel(c.mgr.ASTFalse));
  EXPECT_EQ(symbol, transformer.TransformFormula_TopLevel(symbol));
}

/* The same properties on inputs deeper than the call stack can hold.
   Depths are picked so each case reaches the traversal it is named for:
   buildShareCount's frames are far smaller than rewrite's, so it only
   fails first on a much deeper input.

   The cases still marked DISABLED_ are the traversals that have not been
   converted yet; each is enabled by the commit that converts the traversal
   it names. deep_rewriting_share_count needs both buildShareCount and
   rewrite, since topLevel runs them back to back and there is no way in
   from outside to run only the first. */
TEST(DeepDag, deep_dependencies_build)
{
  EXPECT_STACK_SAFE(dependenciesChainOk, 50000);
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

TEST(DeepDag, deep_incremental_driver)
{
  EXPECT_STACK_SAFE(incrementalDriverOk, 20000);
}

TEST(DeepDag, deep_split_extracts)
{
  EXPECT_STACK_SAFE(splitExtractsOk, 50000);
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

TEST(DeepDag, deep_extract_over_concat)
{
  EXPECT_STACK_SAFE(extractOverConcatOk, 20000);
}

TEST(DeepDag, deep_remainder_folding)
{
  EXPECT_STACK_SAFE(remainderFoldingOk, 20000);
}

TEST(DeepDag, deep_simplify)
{
  EXPECT_STACK_SAFE(simplifyOk, 20000);
}

TEST(DeepDag, deep_simplify_formula_spine)
{
  EXPECT_STACK_SAFE(simplifyFormulaSpineOk, 20000);
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
TEST(DeepDag, deep_work_list)          { EXPECT_STACK_SAFE(workListOk, 20000); }
TEST(DeepDag, deep_remove_unconstrained) { EXPECT_STACK_SAFE(removeUnconstrainedOk, 20000); }
TEST(DeepDag, deep_simplify_term)      { EXPECT_STACK_SAFE(simplifyTermOk, 20000); }
TEST(DeepDag, deep_simplify_term_substituted) { EXPECT_STACK_SAFE(simplifyTermSubstitutedOk, 20000); }
TEST(DeepDag, deep_simplify_alternating_term_formula)
{
  EXPECT_STACK_SAFE(simplifyAlternatingTermFormulaOk, 20000);
}
TEST(DeepDag, deep_simplify_internally_generated_fp_term)
{
  EXPECT_STACK_SAFE(simplifyInternallyGeneratedFpTermOk, 11);
}

TEST(DeepDag, deep_concat_equality)
{
  EXPECT_STACK_SAFE(concatEqualityOk, 20000);
}
TEST(DeepDag, deep_concat_constant_equality)
{
  EXPECT_STACK_SAFE(concatConstantEqualityOk, 4000);
}
TEST(DeepDag, deep_leading_concat_constant_scan)
{
  EXPECT_STACK_SAFE(leadingConcatConstantScanOk, 20000);
}
TEST(DeepDag, deep_mutable_dag_walks)
{
  EXPECT_STACK_SAFE(mutableDagWalksOk, 20000);
}
TEST(DeepDag, DISABLED_deep_use_ite_context)    { EXPECT_STACK_SAFE(useITEContextOk, 20000); }
TEST(DeepDag, deep_node_domain)        { EXPECT_STACK_SAFE(nodeDomainOk, 20000); }
TEST(DeepDag, deep_node_iterator)      { EXPECT_STACK_SAFE(nodeIteratorOk, 20000); }
TEST(DeepDag, deep_vars_in_expression) { EXPECT_STACK_SAFE(varsInExpressionOk, 20000); }
TEST(DeepDag, deep_propagate_equalities) { EXPECT_STACK_SAFE(propagateEqualitiesOk, 20000); }
TEST(DeepDag, deep_array_transformer)  { EXPECT_STACK_SAFE(arrayTransformerOk, 20000); }
TEST(DeepDag, deep_array_read_chain)   { EXPECT_STACK_SAFE(arrayReadChainOk, 20000); }
TEST(DeepDag, deep_array_read_count_walk)
{
  EXPECT_STACK_SAFE(numberOfReadsWalkOk, 20000);
}
TEST(DeepDag, deep_contains_kind_walk)
{
  EXPECT_STACK_SAFE(containsKindWalkOk, 20000);
}
TEST(DeepDag, deep_array_write_chain)  { EXPECT_STACK_SAFE(arrayWriteChainOk, 20000); }
TEST(DeepDag, deep_array_equality_lowering)
{
  EXPECT_STACK_SAFE(arrayEqualityLoweringOk, 20000);
}
TEST(DeepDag, deep_transform_formula_spine) { EXPECT_STACK_SAFE(transformFormulaSpineOk, 20000); }
TEST(DeepDag, deep_fp_totalise)        { EXPECT_STACK_SAFE(fpTotaliseChainOk, 20000); }

TEST(DeepDag, deep_printer_lisp)       { EXPECT_STACK_SAFE(printerLispOk, 20000); }
TEST(DeepDag, deep_counterexample_eval) { EXPECT_STACK_SAFE(counterExampleEvalOk, 20000); }
TEST(DeepDag, deep_counterexample_formula) { EXPECT_STACK_SAFE(counterExampleFormulaOk, 20000); }
TEST(DeepDag, deep_counterexample_term_ite) { EXPECT_STACK_SAFE(counterExampleTermIteOk, 20000); }
TEST(DeepDag, deep_fp_format_ite)      { EXPECT_STACK_SAFE(fpFormatIteChainOk, 20000); }
TEST(DeepDag, deep_fp_format_store)    { EXPECT_STACK_SAFE(fpFormatStoreChainOk, 20000); }
TEST(DeepDag, deep_source_sort_ite)    { EXPECT_STACK_SAFE(sourceSortIteChainOk, 20000); }
TEST(DeepDag, deep_source_sort_store)  { EXPECT_STACK_SAFE(sourceSortStoreChainOk, 20000); }

TEST(DeepDag, DISABLED_deep_printer_smtlib2)    { EXPECT_STACK_SAFE(printerSMTLIB2Ok, 20000); }

} // namespace

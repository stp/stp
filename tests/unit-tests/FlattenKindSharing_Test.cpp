/********************************************************************
 * AUTHORS: Trevor Hansen
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

// FlattenKind over a shared DAG: no flattener may emit one entry per
// root-to-leaf *path*.
//
// On a tree, "expand each same-kind child once" and "expand it every time it
// is reached" are the same function. On a DAG they differ by an exponential: a
// child reachable by k paths has its whole subtree emitted k times, and k
// multiplies at every level of sharing. A depth budget does not bound this --
// it bounds how far down the walk goes, and the cost is in how many ways it
// gets there.
//
// This was not hypothetical. On QF_BV/Sage2/bench_16265.smt2, BVSolver.cpp:160
// flattens a BVPLUS the flattening pass has re-shaped, and the resulting
// ASTVec grew until the process was killed -- >20GB on a file that answers sat
// in seconds without flattening. A stack sample 25s in sat in
// _M_realloc_insert under FlattenKind, and page-fault profiling put 100% of
// the faults in those two frames.
//
// Repeats cannot simply be dropped the way FlattenKindNoDuplicates drops them
// for AND / OR / BVAND / BVOR: those are idempotent and BVPLUS is not, so
// x + x may not become x. What bounds the walk instead is an output budget --
// every step either pushes an operand or descends a level, so capping the
// pushes caps the walk -- and passing it hands the operands back unflattened.
//
// The two properties that matter are therefore: the blow-up is bounded, and
// the bail is a *whole* operand list rather than a prefix. Both are below,
// along with what the budget costs a legitimately wide sum.
//
// Chains are built with the hashing factory: the simplifying factory folds
// x+x to 2*x, and the shared DAG under test would no longer be the one the
// test means to build.

#include "stp/AST/AST.h"
#include "stp/NodeFactory/HashingNodeFactory.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include <cstdlib>
#include <gtest/gtest.h>
#include <string>

#ifndef _WIN32
#include <sys/resource.h>
#endif

using namespace stp;

namespace
{

// The depth cap BVSolver.cpp:160 passes, so these run against the same
// budget the failing solve does.
const int SOLVER_MAX_DEPTH = 50;

// Matches FLATTEN_OUTPUT_BUDGET in ASTmisc.cpp. Kept as its own constant so a
// change there shows up here as a failure rather than as a silent shift in
// what these tests mean.
const size_t OUTPUT_BUDGET = 100000;

// Deep enough that path-enumeration would be unmistakable: 2^22 operands from
// 23 nodes, which is ~32MB of ASTVec if nothing stops it.
const unsigned OBSERVABLE_DEPTH = 22;

// Past any budget: 2^34 operands is ~137GB. A flattener that bounds its
// output returns from this immediately; one that enumerates paths cannot,
// whatever the machine. Only ever run behind a memory limit, in a child.
const unsigned HOPELESS_DEPTH = 34;

// Exit codes of the forked child, so an OOM is one failing test rather than
// a dead test binary.
const int EXIT_OK = 0;
const int EXIT_TOO_BIG = 2;

// Cap how much address space the child may claim, so "cannot allocate 137GB"
// is decided by the test rather than by how much memory the box happens to
// have. Cores are suppressed with it: a child that aborts out of the
// allocator would otherwise leave a multi-GB core behind.
void capChild()
{
#ifndef _WIN32
  const rlim_t bytes = rlim_t(2) * 1024 * 1024 * 1024;
  struct rlimit rl;
  if (getrlimit(RLIMIT_AS, &rl) == 0)
  {
    rl.rlim_cur = bytes;
    setrlimit(RLIMIT_AS, &rl);
  }

  struct rlimit noCore = {0, 0};
  setrlimit(RLIMIT_CORE, &noCore);
#endif
}

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* hf; // hashing factory: builds the DAG without folding it.

  // Kept alive for the lifetime of the case: dropping the last handle on a
  // chain this deep starts a teardown the test has no reason to measure.
  ASTVec roots;

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

  // A maximally shared chain: every level is one node of kind k whose two
  // children are both the level below it. `depth` levels is depth+1 nodes and
  // 2^depth root-to-leaf paths -- the smallest DAG that separates "expanded
  // once per node" from "expanded once per path".
  //
  // This is the shape the flattening pass leaves behind. Flatten::flatten
  // merges a same-kind child into its parent only when that child is unshared
  // (Flatten.cpp:234), because merging a shared one would duplicate it -- so
  // the nodes that survive nested under a widened BVPLUS are the shared ones.
  ASTNode sharedTermChain(Kind k, unsigned depth, unsigned width = 8)
  {
    ASTNode n = mgr.CreateSymbol("x", 0, width);
    for (unsigned i = 0; i < depth; i++)
      n = hf->CreateTerm(k, width, n, n);
    roots.push_back(n);
    return n;
  }

  // The same shape over a formula kind, for the idempotent control.
  ASTNode sharedFormulaChain(Kind k, unsigned depth)
  {
    ASTNode n = mgr.CreateSymbol("b", 0, 0);
    for (unsigned i = 0; i < depth; i++)
      n = hf->CreateNode(k, n, n);
    roots.push_back(n);
    return n;
  }

  // An ordinary nested sum over `count` distinct symbols: no sharing at all,
  // so flattening it is exactly the job the pass exists to do, and the output
  // is `count` operands. This is what the budget gets spent on.
  ASTNode nestedTermChain(Kind k, unsigned count, unsigned width = 8)
  {
    ASTNode n = mgr.CreateSymbol("n0", 0, width);
    for (unsigned i = 1; i < count; i++)
    {
      const std::string name = "n" + std::to_string(i);
      n = hf->CreateTerm(k, width, n,
                         mgr.CreateSymbol(name.c_str(), 0, width));
    }
    roots.push_back(n);
    return n;
  }

  // Nodes in the DAG, which is what a flattener's output should be measured
  // against: depth levels plus the leaf symbol.
  static size_t dagNodes(unsigned depth) { return depth + 1; }
};

// The control. AND is idempotent, so it routes to FlattenKindNoDuplicates,
// and its `alreadyFlattened` set collapses the sharing: one entry out, however
// deep the chain, with no budget involved. This passes today, which is what
// makes the cases below a property of the flattener rather than of the DAG
// builder or of the machine.
TEST(FlattenKindSharing_Test, IdempotentKindIsLinearInSharedDag)
{
  Context c;

  for (unsigned depth : {8u, OBSERVABLE_DEPTH, HOPELESS_DEPTH})
  {
    const ASTNode root = c.sharedFormulaChain(AND, depth);
    const ASTVec flat = FlattenKind(AND, root.GetChildren(), SOLVER_MAX_DEPTH);

    EXPECT_LE(flat.size(), Context::dagNodes(depth))
        << "AND at depth " << depth << " expanded to " << flat.size()
        << " operands from " << Context::dagNodes(depth) << " nodes";
  }
}

// The blow-up, at a size that would fit in memory if it happened, so a
// regression is a number rather than a dead process.
TEST(FlattenKindSharing_Test, SharedBvplusDoesNotEnumeratePaths)
{
  Context c;
  const ASTNode root = c.sharedTermChain(BVPLUS, OBSERVABLE_DEPTH);

  const ASTVec flat =
      FlattenKind(BVPLUS, root.GetChildren(), SOLVER_MAX_DEPTH);

  EXPECT_LE(flat.size(), OUTPUT_BUDGET + 1)
      << "BVPLUS at depth " << OBSERVABLE_DEPTH << " produced " << flat.size()
      << " operands from " << Context::dagNodes(OBSERVABLE_DEPTH) << " nodes";
}

// BVMULT reaches this walk too: it falls through to the BVPLUS arm of
// Simplifier::simplify_term_switch and arrives with the default maxDepth of
// INT_MAX, so nothing bounds its depth either.
TEST(FlattenKindSharing_Test, SharedBvmultDoesNotEnumeratePaths)
{
  Context c;
  const ASTNode root = c.sharedTermChain(BVMULT, OBSERVABLE_DEPTH);

  const ASTVec flat = FlattenKind(BVMULT, root.GetChildren());

  EXPECT_LE(flat.size(), OUTPUT_BUDGET + 1)
      << "BVMULT at depth " << OBSERVABLE_DEPTH << " produced " << flat.size()
      << " operands";
}

// The property the budget must not get wrong. Passing it discards the partial
// output and returns the operands as they arrived: a truncated sum is a
// different sum, and every caller rebuilds a node from this vector.
TEST(FlattenKindSharing_Test, OverBudgetReturnsTheOperandsUntouched)
{
  Context c;
  const ASTNode root = c.sharedTermChain(BVPLUS, OBSERVABLE_DEPTH);

  const ASTVec flat =
      FlattenKind(BVPLUS, root.GetChildren(), SOLVER_MAX_DEPTH);

  EXPECT_EQ(flat, toASTVec(root.GetChildren()))
      << "over budget, so the operands must come back whole and unflattened";
}

// What the budget costs. A sum of distinct operands has nothing to collapse,
// so its flattened width is just how many there are: under the budget it is
// flattened in full, and over it the pass declines and the caller keeps a
// nested sum it would previously have flattened.
TEST(FlattenKindSharing_Test, BudgetDecidesWhetherAWideSumFlattens)
{
  {
    Context c;
    const ASTNode root = c.nestedTermChain(BVPLUS, OUTPUT_BUDGET - 100);
    const ASTVec flat = FlattenKind(BVPLUS, root.GetChildren());
    EXPECT_EQ(flat.size(), OUTPUT_BUDGET - 100) << "under budget: full flatten";
  }
  {
    Context c;
    const ASTNode root = c.nestedTermChain(BVPLUS, OUTPUT_BUDGET + 100);
    const ASTVec flat = FlattenKind(BVPLUS, root.GetChildren());
    EXPECT_EQ(flat, toASTVec(root.GetChildren()))
        << "over budget: declined, and the sum stays nested";
  }
}

// The same defect stated as the failure it caused. 2^34 operands cannot be
// allocated, so a flattener that enumerates paths dies here against the
// address-space limit however much memory the box has, while a bounded one
// returns at once and exits clean. The child is where the allocation happens,
// so an OOM is contained to it.
TEST(FlattenKindSharing_Test, DeepSharedBvplusTerminatesWithinMemory)
{
  EXPECT_EXIT(
      {
        capChild();
        Context* c = new Context();
        const ASTNode root = c->sharedTermChain(BVPLUS, HOPELESS_DEPTH);
        const ASTVec flat =
            FlattenKind(BVPLUS, root.GetChildren(), SOLVER_MAX_DEPTH);
        std::exit(flat.size() <= OUTPUT_BUDGET + 1 ? EXIT_OK : EXIT_TOO_BIG);
      },
      ::testing::ExitedWithCode(EXIT_OK), "");
}

// The depth cap was never a bound: it limits how far down the walk goes, and
// the cost is in how many ways it gets there. Halving it must not change that.
TEST(FlattenKindSharing_Test, MaxDepthDoesNotBoundOutput)
{
  Context c;
  const ASTNode root = c.sharedTermChain(BVPLUS, OBSERVABLE_DEPTH);

  const ASTVec capped =
      FlattenKind(BVPLUS, root.GetChildren(), OBSERVABLE_DEPTH / 2);

  EXPECT_LE(capped.size(), OUTPUT_BUDGET + 1)
      << "a depth budget of " << OBSERVABLE_DEPTH / 2 << " produced "
      << capped.size() << " operands";
}

} // namespace

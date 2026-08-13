/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

// The incremental driver's read registry is session-long: rows survive pops
// so that their congruence axioms stay permanently valid clauses. But a
// popped row's defining equations -- its index anchor and value binding --
// were encoded under the root literal of the conjunct that introduced it,
// and stop holding the moment that root is no longer assumed. Such a row's
// SAT variables float, and if it reaches the per-solve counterexample
// tables, model construction pairs a still-evaluating index with a floating
// value: the shadowed cell makes the model checker reject every candidate,
// and refinement loops without progress (terminating only when the solver's
// free phase choice happens to align -- which is why the failure appeared
// and disappeared with SAT solver versions).
//
// The invariant under test: the batch-side read table a check-sat seeds for
// refinement contains exactly the rows of the currently active conjuncts,
// however many rows the persistent registry keeps for popped scopes.

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include <algorithm>
#include <gtest/gtest.h>
#include <utility>
#include <vector>

using namespace stp;

namespace
{

typedef std::vector<std::pair<ASTNode, ASTNode>> ReadRows;

ReadRows sorted(ReadRows rows)
{
  std::sort(rows.begin(), rows.end());
  return rows;
}

TEST(IncrementalActiveReads, popped_rows_leave_the_seeded_tables)
{
  STPMgr mgr;
  SubstitutionMap sm(&mgr);
  Simplifier simp(&mgr, &sm);
  ArrayTransformer at(&mgr, &simp);
  AbsRefine_CounterExample ce(&mgr, &simp, &at);
  IncrementalSolver inc(&mgr, &ce, &simp, &at);

  NodeFactory* nf = mgr.defaultNodeFactory;
  const ASTNode A = mgr.CreateSymbol("A", 4, 8);
  const ASTNode i = mgr.CreateSymbol("i", 0, 4);
  const ASTNode j = mgr.CreateSymbol("j", 0, 4);

  // Non-constant, non-symbol indexes, so each read needs an index anchor --
  // the shape whose floating variables caused the livelock.
  const ASTNode baseIdx =
      nf->CreateTerm(BVPLUS, 4, i, mgr.CreateBVConst(4, 1));
  const ASTNode base = nf->CreateNode(
      EQ, nf->CreateTerm(READ, 8, A, baseIdx), mgr.CreateBVConst(8, 1));

  const ASTNode pushedIdx =
      nf->CreateTerm(BVPLUS, 4, j, mgr.CreateBVConst(4, 2));
  const ASTNode pushed = nf->CreateNode(
      EQ, nf->CreateTerm(READ, 8, A, pushedIdx), mgr.CreateBVConst(8, 2));

  // Base level only.
  ASTVec baseOnly;
  baseOnly.push_back(base);
  ASSERT_EQ(SOLVER_SATISFIABLE, inc.checkSat(baseOnly));
  const ReadRows r1 = sorted(inc.seededReadsForTesting());
  ASSERT_FALSE(r1.empty());

  // Push a level with its own read: its rows join the seeded tables.
  ASTVec withPush;
  withPush.push_back(base);
  withPush.push_back(pushed);
  ASSERT_EQ(SOLVER_SATISFIABLE, inc.checkSat(withPush));
  const ReadRows r2 = sorted(inc.seededReadsForTesting());
  EXPECT_GT(r2.size(), r1.size());

  // Pop. The registry still holds the pushed level's rows -- by design --
  // but the seeded tables must be exactly the base level's again.
  ASSERT_EQ(SOLVER_SATISFIABLE, inc.checkSat(baseOnly));
  const ReadRows r3 = sorted(inc.seededReadsForTesting());
  EXPECT_EQ(r1, r3);

  // Re-push the identical level: the same rows return.
  ASSERT_EQ(SOLVER_SATISFIABLE, inc.checkSat(withPush));
  const ReadRows r4 = sorted(inc.seededReadsForTesting());
  EXPECT_EQ(r2, r4);

  // Repeat the identical stack: the seeding may take its memoised path,
  // and the rows must still be exactly the active cone's.
  ASSERT_EQ(SOLVER_SATISFIABLE, inc.checkSat(withPush));
  const ReadRows r5 = sorted(inc.seededReadsForTesting());
  EXPECT_EQ(r2, r5);

  // And the memo must not survive a stack change: back to base only.
  ASSERT_EQ(SOLVER_SATISFIABLE, inc.checkSat(baseOnly));
  const ReadRows r6 = sorted(inc.seededReadsForTesting());
  EXPECT_EQ(r1, r6);
}

} // namespace

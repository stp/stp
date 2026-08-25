/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "stp/Sat/SATSolver.h"
#ifdef USE_CRYPTOMINISAT
#include "stp/Sat/CryptoMinisat5.h"
#endif
#ifdef USE_MINISAT
#include "stp/Sat/MinisatCore.h"
#endif
#include <gtest/gtest.h>

#include <chrono>
#include <vector>

// A conflict budget belongs to the query it was armed for, measured from
// the arming point -- NOT from the solver's birth. The distinction was
// invisible while every query got a fresh solver; the incremental driver
// re-arms per check-sat on one long-lived solver, where birth-relative
// accounting shrank every successive budget until each solve gave up on
// arrival.
//
// The recipe makes the bug deterministic: a pigeonhole formula, guarded by
// a selector so it can be retracted by assumption, burns far more than the
// budget under {s}; the re-armed solve under {~s} satisfies every guarded
// clause by propagation alone and MUST come back sat, not exhausted.

namespace
{

#if defined(USE_CRYPTOMINISAT) || defined(USE_MINISAT)

// Pigeonhole 6 pigeons / 5 holes over fresh solver variables, every clause
// guarded by ~sel so the whole formula is retractable.
void addGuardedPigeonhole(stp::SATSolver& s, uint32_t sel, int P = 6)
{
  const int H = P - 1;
  std::vector<std::vector<uint32_t>> var(P, std::vector<uint32_t>(H));
  for (int p = 0; p < P; p++)
    for (int h = 0; h < H; h++)
      var[p][h] = s.newVar();

  // Each pigeon sits somewhere.
  for (int p = 0; p < P; p++)
  {
    stp::SATSolver::vec_literals c;
    c.push(stp::SATSolver::mkLit(sel, true));
    for (int h = 0; h < H; h++)
      c.push(stp::SATSolver::mkLit(var[p][h], false));
    s.addClause(c);
  }

  // No two pigeons share a hole.
  for (int h = 0; h < H; h++)
    for (int p1 = 0; p1 < P; p1++)
      for (int p2 = p1 + 1; p2 < P; p2++)
      {
        stp::SATSolver::vec_literals c;
        c.push(stp::SATSolver::mkLit(sel, true));
        c.push(stp::SATSolver::mkLit(var[p1][h], true));
        c.push(stp::SATSolver::mkLit(var[p2][h], true));
        s.addClause(c);
      }
}

void budgetIsPerArming(stp::SATSolver& s)
{
  const uint32_t sel = s.newVar();
  addGuardedPigeonhole(s, sel);

  // Far too little budget for the pigeonhole: exhausted, and the budget's
  // conflicts are spent.
  s.setMaxConflicts(10);
  bool timeout = false;
  stp::SATSolver::vec_literals on;
  on.push(stp::SATSolver::mkLit(sel, false));
  bool sat = s.solveWithAssumptions(on, timeout);
  EXPECT_FALSE(sat);
  EXPECT_TRUE(timeout);

  // Re-armed, the retracted formula is satisfied by propagating ~sel: this
  // must answer sat within any budget. Birth-relative accounting answered
  // "exhausted on arrival" here.
  s.setMaxConflicts(10);
  timeout = false;
  stp::SATSolver::vec_literals off;
  off.push(stp::SATSolver::mkLit(sel, true));
  sat = s.solveWithAssumptions(off, timeout);
  EXPECT_TRUE(sat);
  EXPECT_FALSE(timeout);
}

// Only compiled where something calls it: a MiniSat-only build against a
// MiniSat with no terminator hook has neither caller.
#if defined(USE_CRYPTOMINISAT) || defined(STP_MINISAT_HAS_TERMINATOR)
// A time budget has to be able to stop a search already in progress, not only
// be noticed between calls into the solver. MiniSat counts work rather than
// time and cannot be handed a deadline, so STP connects a terminator that
// reads the one SATSolver keeps; this is that path end to end.
//
// The formula is a pigeonhole far too large to refute in the budget, so an
// enforcement that only looked between calls would run it to completion --
// minutes, not the second it was given.
void timeBudgetStopsASearchInProgress(stp::SATSolver& s)
{
  const uint32_t sel = s.newVar();
  addGuardedPigeonhole(s, sel, 11);

  s.setMaxTime(1);
  ASSERT_TRUE(s.hasTimeLimit());

  stp::SATSolver::vec_literals on;
  on.push(stp::SATSolver::mkLit(sel, false));

  bool timeout = false;
  const auto start = std::chrono::steady_clock::now();
  const bool sat = s.solveWithAssumptions(on, timeout);
  const auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(
                           std::chrono::steady_clock::now() - start)
                           .count();

  EXPECT_FALSE(sat);
  EXPECT_TRUE(timeout) << "the budget ran out and nobody said so";
  // Generous: the point is the difference between "stopped" and "ran to
  // completion", not the precision of the deadline.
  // A backend that cannot be interrupted mid-search runs this to completion
  // instead, which takes far longer than the budget it was given.
  EXPECT_LT(elapsed, 30) << "the search was not stopped, it finished";
}
#endif

#endif

} // namespace

#ifdef USE_CRYPTOMINISAT
TEST(SatSolverBudget, cryptominisat_budget_is_per_arming)
{
  stp::CryptoMiniSat5 s(1);
  budgetIsPerArming(s);
}
#endif

#ifdef USE_MINISAT
TEST(SatSolverBudget, minisat_budget_is_per_arming)
{
  stp::MinisatCore s;
  budgetIsPerArming(s);
}

// Only where the MiniSat underneath carries the terminator hook; without it
// the budget is enforced between calls into the solver and this search runs to
// completion, which is the behaviour, not a failure.
#ifdef STP_MINISAT_HAS_TERMINATOR
TEST(SatSolverBudget, minisat_time_budget_stops_a_search_in_progress)
{
  stp::MinisatCore s;
  timeBudgetStopsASearchInProgress(s);
}
#endif
#endif

#ifdef USE_CRYPTOMINISAT
TEST(SatSolverBudget, cryptominisat_time_budget_stops_a_search_in_progress)
{
  stp::CryptoMiniSat5 s(1);
  timeBudgetStopsASearchInProgress(s);
}
#endif

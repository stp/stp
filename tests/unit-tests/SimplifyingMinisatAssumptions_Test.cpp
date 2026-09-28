#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>
#include <vector>

#ifdef USE_MINISAT
#include "stp/Sat/SimplifyingMinisat.h"

TEST(SimplifyingMinisatAssumptions, ReportsTheFailedAssumptionWithItsSign)
{
  for (bool negative : {false, true})
  {
    SCOPED_TRACE(negative);
    stp::SimplifyingMinisat solver;
    ASSERT_TRUE(solver.supportsAssumptions());
    const auto irrelevant = solver.newVar();
    const auto variable = solver.newVar();
    stp::SATSolver::vec_literals unit;
    unit.push(stp::SATSolver::mkLit(variable, !negative));
    solver.addClause(unit);

    stp::SATSolver::vec_literals assumptions;
    assumptions.push(stp::SATSolver::mkLit(irrelevant, false));
    const auto culprit = stp::SATSolver::mkLit(variable, negative);
    assumptions.push(culprit);
    bool timeout = false;
    EXPECT_FALSE(solver.solveWithAssumptions(assumptions, timeout));
    EXPECT_FALSE(timeout);
    EXPECT_TRUE(solver.okay());

    std::vector<int> failed;
    solver.unsatAssumptions(assumptions, failed);
    ASSERT_EQ(1u, failed.size());
    EXPECT_EQ(static_cast<int>(culprit.x), failed.front());

    // The failed assumption was temporary; the permanent formula is SAT.
    assumptions.clear();
    EXPECT_TRUE(solver.solveWithAssumptions(assumptions, timeout));
    EXPECT_FALSE(timeout);
    EXPECT_EQ(negative ? solver.true_literal() : solver.false_literal(),
              solver.modelValue(variable));
  }
}

TEST(SimplifyingMinisatAssumptions, AssumptionsCanChangeBetweenSolves)
{
  stp::SimplifyingMinisat solver;
  const auto variable = solver.newVar();
  for (bool negative : {false, true, false})
  {
    stp::SATSolver::vec_literals assumptions;
    assumptions.push(stp::SATSolver::mkLit(variable, negative));
    bool timeout = false;
    ASSERT_TRUE(solver.solveWithAssumptions(assumptions, timeout));
    EXPECT_FALSE(timeout);
    EXPECT_EQ(negative ? solver.false_literal() : solver.true_literal(),
              solver.modelValue(variable));
  }
}

TEST(SimplifyingMinisatAssumptions, AnExpiredBudgetDoesNotBecomeAnUnsatAnswer)
{
  stp::SimplifyingMinisat solver;
  const auto variable = solver.newVar();
  stp::SATSolver::vec_literals assumptions;
  assumptions.push(stp::SATSolver::mkLit(variable, false));
  solver.setMaxTime(0);
  bool timeout = false;
  EXPECT_FALSE(solver.solveWithAssumptions(assumptions, timeout));
  EXPECT_TRUE(timeout);
  EXPECT_TRUE(solver.okay());
}
#endif

#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>

#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"

TEST(CadicalClauseResult, AcceptedAndContradictoryClausesReportConsistency)
{
  for (bool factor : {false, true})
  {
    SCOPED_TRACE(factor);
    stp::Cadical solver;
    if (factor && !solver.enableBVA())
      continue;
    const auto variable = solver.newVar();
    stp::SATSolver::vec_literals positive;
    positive.push(stp::SATSolver::mkLit(variable, false));
    EXPECT_TRUE(solver.addClause(positive));
    EXPECT_TRUE(solver.okay());

    bool timeout = false;
    ASSERT_TRUE(solver.solve(timeout));
    EXPECT_FALSE(timeout);
    EXPECT_EQ(solver.true_literal(), solver.modelValue(variable));

    stp::SATSolver::vec_literals negative;
    negative.push(stp::SATSolver::mkLit(variable, true));
    const bool accepted = solver.addClause(negative);
    EXPECT_EQ(solver.okay(), accepted);
    EXPECT_FALSE(solver.solve(timeout));
    EXPECT_FALSE(timeout);
    EXPECT_FALSE(solver.okay());
    EXPECT_EQ(2u, solver.submittedClauses());
  }
}

TEST(CadicalClauseResult, EmptyClauseMatchesTheCurrentSolverState)
{
  stp::Cadical solver;
  stp::SATSolver::vec_literals empty;
  const bool accepted = solver.addClause(empty);
  EXPECT_EQ(solver.okay(), accepted);
  bool timeout = false;
  EXPECT_FALSE(solver.solve(timeout));
  EXPECT_FALSE(timeout);
  EXPECT_FALSE(solver.okay());
}
#endif

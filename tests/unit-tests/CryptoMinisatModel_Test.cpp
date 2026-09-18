#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>

#ifdef USE_CRYPTOMINISAT
#include "stp/Sat/CryptoMinisat5.h"

TEST(CryptoMinisatModel, ForcedValuesUseTheBackendTruthConstants)
{
  stp::CryptoMiniSat5 solver(1);
  const auto positive = solver.newVar();
  const auto negative = solver.newVar();
  stp::SATSolver::vec_literals clause;
  clause.push(stp::SATSolver::mkLit(positive, false));
  solver.addClause(clause);
  clause.clear();
  clause.push(stp::SATSolver::mkLit(negative, true));
  solver.addClause(clause);

  bool timeout = false;
  ASSERT_TRUE(solver.solve(timeout));
  ASSERT_FALSE(timeout);
  EXPECT_EQ(solver.true_literal(), solver.modelValue(positive));
  EXPECT_EQ(solver.false_literal(), solver.modelValue(negative));
  EXPECT_NE(solver.undef_literal(), solver.modelValue(negative));
}

TEST(CryptoMinisatModel, MissingModelEntriesAreUndefined)
{
  stp::CryptoMiniSat5 solver(1);
  const auto variable = solver.newVar();
  // Allocating a variable does not create a model assignment.
  EXPECT_EQ(solver.undef_literal(), solver.modelValue(variable));
  EXPECT_EQ(solver.undef_literal(), solver.modelValue(solver.nVars()));
}
#endif

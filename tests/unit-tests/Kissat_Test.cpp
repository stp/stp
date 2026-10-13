#include "stp/Sat/Kissat.h"
#include <gtest/gtest.h>

using stp::SATSolver;

namespace
{
SATSolver::vec_literals clause(std::initializer_list<SATSolver::Lit> lits)
{
  SATSolver::vec_literals result;
  for (auto lit : lits)
    result.push(lit);
  return result;
}
} // namespace

TEST(Kissat, OneShotCompleteFormulaHasAValidModel)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.configureOneShot());
  EXPECT_FALSE(solver.supportsAssumptions());
  const auto x = solver.newVar(), y = solver.newVar();
  solver.setFrozen(x);
  solver.setFrozen(y);
  solver.addClause(clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)}));
  solver.addClause(clause({SATSolver::mkLit(x, true), SATSolver::mkLit(y, false)}));
  // STP's batch loader can also make these requests after loading the CNF.
  solver.setFrozen(x);
  solver.setFrozen(y);
  bool timeout = false;
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_FALSE(timeout);
  EXPECT_EQ(solver.true_literal(), solver.modelValue(y));
  EXPECT_THROW(solver.addClause(clause({SATSolver::mkLit(y, true)})), std::logic_error);
  EXPECT_THROW(solver.solve(timeout), std::logic_error);
}

TEST(Kissat, OneShotSearchBiasKeepsTheNonIncrementalConfiguration)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.configureOneShot());
  ASSERT_TRUE(solver.setSearchBias(stp::SearchBias::SAT));
  EXPECT_FALSE(solver.enableTrailReuse(SATSolver::TrailReuse::ALL));
  const auto x = solver.newVar();
  solver.setFrozen(x);
  solver.addClause(clause({SATSolver::mkLit(x, false)}));
  bool timeout = false;
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_FALSE(timeout);
  EXPECT_EQ(solver.true_literal(), solver.modelValue(x));
}

TEST(Kissat, OneShotConfigurationRequiresAnEmptyBackend)
{
  stp::Kissat solver;
  const auto x = solver.newVar();
  solver.addClause(clause({SATSolver::mkLit(x, false)}));
  EXPECT_THROW(solver.configureOneShot(), std::logic_error);
  EXPECT_TRUE(solver.supportsAssumptions());
}

TEST(Kissat, AssumptionsRetractAfterUnsat)
{
  stp::Kissat solver;
  const auto x = solver.newVar(), y = solver.newVar();
  ASSERT_TRUE(solver.addClause(
      clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)})));
  bool timeout = false;
  const auto noXY =
      clause({SATSolver::mkLit(x, true), SATSolver::mkLit(y, true)});
  EXPECT_FALSE(solver.solveWithAssumptions(noXY, timeout));
  EXPECT_FALSE(timeout);
  EXPECT_TRUE(solver.okay());
  std::vector<int> core;
  solver.unsatAssumptions(noXY, core);
  EXPECT_FALSE(core.empty());
  EXPECT_TRUE(solver.solve(timeout));
}

TEST(Kissat, FailedAssumptionsExcludeUnrelatedSelectors)
{
  stp::Kissat solver;
  const auto x = solver.newVar(), unrelated = solver.newVar();
  solver.addClause(clause({SATSolver::mkLit(x, false)}));
  const auto assumptions =
      clause({SATSolver::mkLit(unrelated, false), SATSolver::mkLit(x, true)});
  bool timeout = false;
  EXPECT_FALSE(solver.solveWithAssumptions(assumptions, timeout));
  std::vector<int> core;
  solver.unsatAssumptions(assumptions, core);
  ASSERT_EQ(1u, core.size());
  EXPECT_EQ(static_cast<int>(SATSolver::mkLit(x, true).x), core[0]);
  EXPECT_TRUE(solver.solve(timeout));
}

TEST(Kissat, VariablesAddedAfterSearchUseTheSameTranslation)
{
  stp::Kissat solver;
  EXPECT_TRUE(solver.enableBVA());
  bool timeout = false;
  for (unsigned round = 0; round != 25; ++round)
  {
    const auto x = solver.newVar(), y = solver.newVar();
    const auto notX = clause({SATSolver::mkLit(x, true)});
    ASSERT_TRUE(solver.addClause(
        clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)})));
    ASSERT_TRUE(solver.solveWithAssumptions(notX, timeout));
    EXPECT_EQ(solver.false_literal(), solver.modelValue(x));
    EXPECT_EQ(solver.true_literal(), solver.modelValue(y));
    ASSERT_TRUE(solver.addClause(clause({SATSolver::mkLit(x, false)})));
    EXPECT_FALSE(solver.solveWithAssumptions(notX, timeout));
    ASSERT_TRUE(solver.okay());
    ASSERT_TRUE(solver.solve(timeout));
    EXPECT_EQ(solver.true_literal(), solver.modelValue(x));
  }
  EXPECT_FALSE(timeout);
}

TEST(Kissat, FrozenVariablesAndSubmittedClausesSurviveRefinement)
{
  stp::Kissat solver;
  const auto x = solver.newVar(), y = solver.newVar();
  solver.setFrozen(x);
  solver.setFrozen(x);
  solver.addClause(
      clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)}));
  bool timeout = false;
  ASSERT_TRUE(solver.solve(timeout));
  solver.addClause(clause({SATSolver::mkLit(x, true)}));
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_EQ(solver.false_literal(), solver.modelValue(x));
  EXPECT_EQ(solver.true_literal(), solver.modelValue(y));
  solver.addClause(clause({SATSolver::mkLit(y, true)}));
  EXPECT_FALSE(solver.solve(timeout));
  EXPECT_FALSE(solver.okay());
  EXPECT_EQ(3u, solver.submittedClauses());
}

TEST(Kissat, FactoringCannotClaimAnAllocatedUnmentionedVariable)
{
  stp::Kissat solver;
  solver.enableBVA();
  uint32_t common[5];
  for (auto& var : common)
  {
    var = solver.newVar();
    solver.setFrozen(var);
  }
  for (unsigned i = 0; i != 100; ++i)
  {
    const auto branch = solver.newVar();
    solver.setFrozen(branch);
    for (unsigned suffix : {3u, 4u})
    {
      SATSolver::vec_literals input;
      for (unsigned c = 0; c != 3; ++c)
        input.push(SATSolver::mkLit(common[c], false));
      input.push(SATSolver::mkLit(common[suffix], false));
      input.push(SATSolver::mkLit(branch, false));
      solver.addClause(input);
    }
  }
  const auto unused = solver.newVar();
  SATSolver::vec_literals noCommon;
  for (auto var : common)
    noCommon.push(SATSolver::mkLit(var, true));
  bool timeout = false;
  ASSERT_TRUE(solver.solveWithAssumptions(noCommon, timeout));
  EXPECT_EQ(solver.undef_literal(), solver.modelValue(unused));
  solver.addClause(clause({SATSolver::mkLit(unused, true)}));
  EXPECT_TRUE(solver.solveWithAssumptions(noCommon, timeout));
  EXPECT_EQ(solver.false_literal(), solver.modelValue(unused));
}

TEST(Kissat, DeadlineAndStopPollCanBeCleared)
{
  stp::Kissat solver;
  const auto x = solver.newVar();
  solver.addClause(clause({SATSolver::mkLit(x, false)}));
  bool timeout = false;
  solver.setMaxTime(0);
  EXPECT_FALSE(solver.solve(timeout));
  EXPECT_TRUE(timeout);
  solver.clearDeadline();
  timeout = false;
  solver.setStopPoll([](void*) { return true; }, nullptr);
  EXPECT_FALSE(solver.solve(timeout));
  EXPECT_TRUE(timeout);
  solver.setStopPoll(nullptr, nullptr);
  timeout = false;
  EXPECT_TRUE(solver.solve(timeout));
  EXPECT_FALSE(timeout);
}

TEST(Kissat, StopPollInterruptsAnActiveSearchAndCanResume)
{
  stp::Kissat solver;
  uint32_t pigeons[8][7];
  for (auto& pigeon : pigeons)
    for (auto& hole : pigeon)
      hole = solver.newVar();
  for (auto& pigeon : pigeons)
  {
    SATSolver::vec_literals someHole;
    for (auto hole : pigeon)
      someHole.push(SATSolver::mkLit(hole, false));
    solver.addClause(someHole);
  }
  for (unsigned h = 0; h != 7; ++h)
    for (unsigned p = 0; p != 8; ++p)
      for (unsigned q = 0; q != p; ++q)
        solver.addClause(clause({SATSolver::mkLit(pigeons[p][h], true),
                                 SATSolver::mkLit(pigeons[q][h], true)}));
  unsigned polls = 0;
  solver.setStopPoll([](void* state)
                     { return ++*static_cast<unsigned*>(state) >= 2; }, &polls);
  bool timeout = false;
  EXPECT_FALSE(solver.solve(timeout));
  EXPECT_TRUE(timeout);
  EXPECT_GE(polls, 2u);
  solver.setStopPoll(nullptr, nullptr);
  timeout = false;
  EXPECT_FALSE(solver.solve(timeout));
  EXPECT_FALSE(timeout);
}

TEST(Kissat, SharedAssumptionsSurvivePushPopAndNewClauses)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.enableTrailReuse(SATSolver::TrailReuse::ASSUMPTIONS));
  uint32_t variables[12];
  for (auto& var : variables)
  {
    var = solver.newVar();
    solver.setFrozen(var);
  }
  for (unsigned i = 1; i != 12; ++i)
    solver.addClause(clause({SATSolver::mkLit(variables[i - 1], true),
                             SATSolver::mkLit(variables[i], false)}));
  bool timeout = false;
  for (unsigned round = 0; round != 10; ++round)
  {
    const auto positive = clause({SATSolver::mkLit(variables[0], false),
                                  SATSolver::mkLit(variables[5], false)});
    ASSERT_TRUE(solver.solveWithAssumptions(positive, timeout));
    EXPECT_EQ(solver.true_literal(), solver.modelValue(variables[11]));
    const auto contradiction = clause({SATSolver::mkLit(variables[0], false),
                                       SATSolver::mkLit(variables[11], true)});
    EXPECT_FALSE(solver.solveWithAssumptions(contradiction, timeout));
    EXPECT_TRUE(solver.okay());
    ASSERT_TRUE(solver.solveWithAssumptions(
        clause({SATSolver::mkLit(variables[0], true)}), timeout));
    EXPECT_EQ(solver.false_literal(), solver.modelValue(variables[0]));
  }
  EXPECT_FALSE(timeout);
}

TEST(Kissat, RefinementBacktracksAReusedModelForClausesAndUnits)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.enableTrailReuse(SATSolver::TrailReuse::ALL));
  uint32_t variables[10];
  for (auto& var : variables)
  {
    var = solver.newVar();
    solver.setFrozen(var);
  }
  for (unsigned i = 0; i != 9; ++i)
    solver.addClause(clause({SATSolver::mkLit(variables[i], false),
                             SATSolver::mkLit(variables[i + 1], false)}));
  bool timeout = false;
  ASSERT_TRUE(solver.solve(timeout));
  ASSERT_TRUE(solver.solve(timeout));
  const bool x = solver.modelValue(variables[0]) == solver.true_literal();
  const bool y = solver.modelValue(variables[9]) == solver.true_literal();
  solver.addClause(clause(
      {SATSolver::mkLit(variables[0], x), SATSolver::mkLit(variables[9], y)}));
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_TRUE((solver.modelValue(variables[0]) == solver.true_literal()) != x ||
              (solver.modelValue(variables[9]) == solver.true_literal()) != y);
  const bool z = solver.modelValue(variables[4]) == solver.true_literal();
  solver.addClause(clause({SATSolver::mkLit(variables[4], z)}));
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_NE(z, solver.modelValue(variables[4]) == solver.true_literal());
  EXPECT_FALSE(timeout);
}

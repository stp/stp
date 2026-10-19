#include "stp/Sat/Kissat.h"
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <gtest/gtest.h>
#include <vector>

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

#ifdef KISSAT_HAS_INTERRUPTIBLE_LUCKY
namespace
{
// The policy counts original submissions, including redundant clauses.
// Tautologies reach its size threshold without making these regressions hard.
void addProbeGrowth(stp::Kissat& solver, uint32_t var, unsigned count = 100000)
{
  const auto tautology =
      clause({SATSolver::mkLit(var, false), SATSolver::mkLit(var, true)});
  for (unsigned i = 0; i < count; ++i)
    ASSERT_TRUE(solver.addClause(tautology));
}
} // namespace

TEST(Kissat, LuckyProbeModelSurvivesNewVariablesAndAssumptionsRetract)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.enableLuckyProbe());
  const auto x = solver.newVar(), y = solver.newVar();
  solver.setFrozen(x);
  solver.setFrozen(y);
  ASSERT_TRUE(solver.addClause(
      clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)})));
  addProbeGrowth(solver, x);
  bool timeout = false;
  const auto notX = clause({SATSolver::mkLit(x, true)});
  ASSERT_TRUE(solver.solveWithAssumptions(notX, timeout));
  ASSERT_FALSE(timeout);
  ASSERT_EQ(1u, solver.luckyProbeStatistics().attempts);
  ASSERT_EQ(1u, solver.luckyProbeStatistics().successes);
  EXPECT_EQ(solver.false_literal(), solver.modelValue(x));
  EXPECT_EQ(solver.true_literal(), solver.modelValue(y));

  const auto fresh = solver.newVar();
  EXPECT_EQ(solver.true_literal(), solver.modelValue(y));
  EXPECT_EQ(solver.undef_literal(), solver.modelValue(fresh));
  ASSERT_TRUE(solver.addClause(clause({SATSolver::mkLit(fresh, true)})));
  const auto notY = clause({SATSolver::mkLit(y, true)});
  ASSERT_TRUE(solver.solveWithAssumptions(notY, timeout));
  EXPECT_EQ(solver.true_literal(), solver.modelValue(x));
  EXPECT_EQ(solver.false_literal(), solver.modelValue(y));
  EXPECT_EQ(solver.false_literal(), solver.modelValue(fresh));
  EXPECT_EQ(1u, solver.luckyProbeStatistics().attempts);
  EXPECT_TRUE(solver.okay());
  EXPECT_FALSE(timeout);
}

TEST(Kissat, LuckyProbeUnsatFallsBackToFailedAssumptions)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.enableLuckyProbe());
  const auto x = solver.newVar(), y = solver.newVar();
  solver.addClause(
      clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)}));
  addProbeGrowth(solver, x);
  const auto assumptions =
      clause({SATSolver::mkLit(x, true), SATSolver::mkLit(y, true)});
  bool timeout = false;
  ASSERT_FALSE(solver.solveWithAssumptions(assumptions, timeout));
  ASSERT_FALSE(timeout);
  EXPECT_EQ(1u, solver.luckyProbeStatistics().attempts);
  EXPECT_EQ(0u, solver.luckyProbeStatistics().successes);
  EXPECT_EQ(1u, solver.luckyProbeStatistics().inconclusive);
  std::vector<int> core;
  solver.unsatAssumptions(assumptions, core);
  EXPECT_FALSE(core.empty());
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_TRUE(solver.okay());
}

TEST(Kissat, LuckyProbeInconclusiveFallsBackToSearch)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.enableLuckyProbe());
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
  for (unsigned h = 0; h < 7; ++h)
    for (unsigned a = 0; a < 8; ++a)
      for (unsigned b = a + 1; b < 8; ++b)
        solver.addClause(clause({SATSolver::mkLit(pigeons[a][h], true),
                                 SATSolver::mkLit(pigeons[b][h], true)}));
  addProbeGrowth(solver, pigeons[0][0]);
  bool timeout = false;
  EXPECT_FALSE(solver.solve(timeout));
  EXPECT_FALSE(timeout);
  EXPECT_EQ(1u, solver.luckyProbeStatistics().attempts);
  EXPECT_EQ(0u, solver.luckyProbeStatistics().successes);
  EXPECT_EQ(1u, solver.luckyProbeStatistics().inconclusive);
}

TEST(Kissat, LuckyProbeSkipsSmallChangesAndIsOptIn)
{
  for (bool enabled : {false, true})
  {
    stp::Kissat solver;
    if (enabled)
    {
      ASSERT_TRUE(solver.enableLuckyProbe());
    }
    const auto x = solver.newVar();
    solver.addClause(clause({SATSolver::mkLit(x, false)}));
    bool timeout = false;
    ASSERT_TRUE(solver.solve(timeout));
    EXPECT_EQ(0u, solver.luckyProbeStatistics().attempts);
    EXPECT_EQ(enabled ? 2u : 0u,
              solver.luckyProbeStatistics().retained_literals);
  }
}

TEST(Kissat, LuckyProbeHonorsResourceControls)
{
  for (unsigned control = 0; control < 3; ++control)
  {
    stp::Kissat solver;
    ASSERT_TRUE(solver.enableLuckyProbe());
    const auto x = solver.newVar();
    addProbeGrowth(solver, x);
    if (control == 0)
      solver.setMaxTime(30);
    else if (control == 1)
      solver.setStopPoll([](void*) { return false; }, nullptr);
    else
      solver.setMaxConflicts(1000);
    bool timeout = false;
    ASSERT_TRUE(solver.solve(timeout));
    EXPECT_FALSE(timeout);
    EXPECT_EQ(control == 2 ? 0u : 1u, solver.luckyProbeStatistics().attempts);
  }
}

TEST(Kissat, LuckyProbeCancellationDoesNotLeavePendingAssumptions)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.enableLuckyProbe());
  const auto x = solver.newVar(), y = solver.newVar();
  solver.addClause(
      clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)}));
  addProbeGrowth(solver, x);
  unsigned polls = 0;
  solver.setStopPoll([](void* p) { return ++*static_cast<unsigned*>(p) == 10; },
                     &polls);
  const auto notX = clause({SATSolver::mkLit(x, true)});
  bool timeout = false;
  EXPECT_FALSE(solver.solveWithAssumptions(notX, timeout));
  EXPECT_TRUE(timeout);
  EXPECT_EQ(1u, solver.luckyProbeStatistics().attempts);
  EXPECT_EQ(0u, solver.luckyProbeStatistics().successes);
  solver.setStopPoll(nullptr, nullptr);
  timeout = false;
  const auto notY = clause({SATSolver::mkLit(y, true)});
  ASSERT_TRUE(solver.solveWithAssumptions(notY, timeout));
  EXPECT_EQ(solver.true_literal(), solver.modelValue(x));
  EXPECT_EQ(solver.false_literal(), solver.modelValue(y));
  EXPECT_FALSE(timeout);
}

TEST(Kissat, LuckyProbeIsDisabledForOneShot)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.enableLuckyProbe());
  ASSERT_TRUE(solver.configureOneShot());
  EXPECT_FALSE(solver.enableLuckyProbe());
  const auto x = solver.newVar();
  addProbeGrowth(solver, x);
  bool timeout = false;
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_EQ(0u, solver.luckyProbeStatistics().attempts);
  EXPECT_EQ(0u, solver.luckyProbeStatistics().retained_literals);
}

TEST(Kissat, LuckyProbeReleasesJournalAtVariableLimit)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.enableLuckyProbe());
  const auto x = solver.newVar();
  solver.addClause(clause({SATSolver::mkLit(x, false)}));
  EXPECT_EQ(2u, solver.luckyProbeStatistics().retained_literals);
  while (solver.nVars() <= 1000000)
    solver.newVar();
  EXPECT_EQ(0u, solver.luckyProbeStatistics().retained_literals);
  addProbeGrowth(solver, x);
  bool timeout = false;
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_EQ(0u, solver.luckyProbeStatistics().attempts);
}

TEST(Kissat, LuckyProbeReleasesJournalAtLiteralLimit)
{
  stp::Kissat solver;
  ASSERT_TRUE(solver.enableLuckyProbe());
  const auto x = solver.newVar();
  SATSolver::vec_literals large;
  for (unsigned i = 0; i < 2000000; ++i)
  {
    large.push(SATSolver::mkLit(x, false));
    large.push(SATSolver::mkLit(x, true));
  }
  ASSERT_TRUE(solver.addClause(large));
  EXPECT_EQ(0u, solver.luckyProbeStatistics().retained_literals);
  addProbeGrowth(solver, x);
  bool timeout = false;
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_EQ(0u, solver.luckyProbeStatistics().attempts);
}

#else
TEST(Kissat, LuckyProbeRequiresAnInterruptibleBackend)
{
  stp::Kissat solver;
  EXPECT_FALSE(solver.enableLuckyProbe());
}
#endif

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

TEST(Kissat, InitialImportOrdersPreserveModelsAssumptionsAndLaterVariables)
{
  for (int order : {0, 1, 2})
    for (const bool factoring : {false, true})
    {
      SCOPED_TRACE(order);
      SCOPED_TRACE(factoring);
      stp::Kissat solver;
      solver.setImportOrder(order);
      if (factoring)
      {
        ASSERT_TRUE(solver.enableBVA());
      }
      const auto x = solver.newVar(), y = solver.newVar();
      solver.setFrozen(x);
      solver.setFrozen(y);
      ASSERT_TRUE(solver.addClause(
          clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)})));
      bool timeout = false;
      const auto noX = clause({SATSolver::mkLit(x, true)});
      ASSERT_TRUE(solver.solveWithAssumptions(noX, timeout));
      EXPECT_EQ(solver.false_literal(), solver.modelValue(x));
      EXPECT_EQ(solver.true_literal(), solver.modelValue(y));

      const auto z = solver.newVar();
      solver.setFrozen(z);
      ASSERT_TRUE(solver.addClause(clause({SATSolver::mkLit(z, true)})));
      const auto noXY =
          clause({SATSolver::mkLit(x, true), SATSolver::mkLit(y, true)});
      ASSERT_FALSE(solver.solveWithAssumptions(noXY, timeout));
      EXPECT_TRUE(solver.okay());
      std::vector<int> core;
      solver.unsatAssumptions(noXY, core);
      EXPECT_FALSE(core.empty());
      ASSERT_TRUE(solver.solve(timeout));
      EXPECT_EQ(solver.false_literal(), solver.modelValue(z));
      EXPECT_FALSE(timeout);
    }
}

TEST(Kissat, InitialImportOrdersPreserveOneShotModels)
{
  for (int order : {0, 1, 2})
  {
    SCOPED_TRACE(order);
    stp::Kissat solver;
    solver.setImportOrder(order);
    ASSERT_TRUE(solver.configureOneShot());
    const auto x = solver.newVar(), y = solver.newVar();
    solver.setFrozen(x);
    solver.setFrozen(y);
    ASSERT_TRUE(solver.addClause(
        clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)})));
    ASSERT_TRUE(solver.addClause(clause({SATSolver::mkLit(x, true)})));
    bool timeout = false;
    ASSERT_TRUE(solver.solve(timeout));
    EXPECT_EQ(solver.false_literal(), solver.modelValue(x));
    EXPECT_EQ(solver.true_literal(), solver.modelValue(y));
    EXPECT_FALSE(timeout);
    EXPECT_FALSE(solver.supportsAssumptions());
  }
}

TEST(Kissat, ImportOrderRejectsInvalidValuesAndLateChanges)
{
  stp::Kissat solver;
  EXPECT_THROW(solver.setImportOrder(-1), std::invalid_argument);
  EXPECT_THROW(solver.setImportOrder(3), std::invalid_argument);
  solver.setImportOrder(2);
  const auto x = solver.newVar();
  ASSERT_TRUE(solver.addClause(clause({SATSolver::mkLit(x, false)})));
  bool timeout = false;
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_THROW(solver.setImportOrder(0), std::logic_error);
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

TEST(Kissat, OneShotSearchModeKeepsItsModeAndModelAcrossBiasChanges)
{
  for (int mode : {-1, 0, 1, 2})
  {
    SCOPED_TRACE(mode);
    stp::Kissat solver(true, 1);
    solver.setOneShotSearchMode(mode);
    ASSERT_TRUE(solver.setSearchBias(stp::SearchBias::UNSAT));
    ASSERT_TRUE(solver.configureOneShot());
    ASSERT_TRUE(solver.setSearchBias(stp::SearchBias::SAT));
    testing::internal::CaptureStderr();
    solver.printStats();
    const std::string stats = testing::internal::GetCapturedStderr();
    EXPECT_NE(
        stats.find(" stable=" + std::to_string(mode < 0 ? 1 : mode) + " "),
        std::string::npos);
    EXPECT_FALSE(solver.supportsAssumptions());
    const auto x = solver.newVar(), y = solver.newVar();
    solver.setFrozen(x);
    solver.setFrozen(y);
    ASSERT_TRUE(solver.addClause(
        clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)})));
    ASSERT_TRUE(solver.addClause(clause({SATSolver::mkLit(x, true)})));
    bool timeout = false;
    ASSERT_TRUE(solver.solve(timeout));
    EXPECT_FALSE(timeout);
    EXPECT_EQ(solver.false_literal(), solver.modelValue(x));
    EXPECT_EQ(solver.true_literal(), solver.modelValue(y));
  }
}

TEST(Kissat, OneShotSearchModeLeavesIncrementalModelsAndAssumptionsAlone)
{
  stp::Kissat solver(true, 2);
  solver.setOneShotSearchMode(0);
  const auto x = solver.newVar(), y = solver.newVar();
  ASSERT_TRUE(solver.addClause(
      clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)})));
  bool timeout = false;
  ASSERT_TRUE(solver.solveWithAssumptions(clause({SATSolver::mkLit(x, true)}),
                                          timeout));
  EXPECT_EQ(solver.true_literal(), solver.modelValue(y));
  const auto conflict =
      clause({SATSolver::mkLit(x, true), SATSolver::mkLit(y, true)});
  ASSERT_FALSE(solver.solveWithAssumptions(conflict, timeout));
  EXPECT_TRUE(solver.okay());
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_TRUE(solver.supportsAssumptions());
  testing::internal::CaptureStderr();
  solver.printStats();
  const std::string stats = testing::internal::GetCapturedStderr();
  EXPECT_NE(stats.find(" stable=2 "), std::string::npos);
  EXPECT_FALSE(timeout);
}

TEST(Kissat, OneShotSearchModeRejectsInvalidAndLateChoices)
{
  stp::Kissat solver;
  EXPECT_THROW(solver.setOneShotSearchMode(-2), std::invalid_argument);
  EXPECT_THROW(solver.setOneShotSearchMode(3), std::invalid_argument);
  solver.setOneShotSearchMode(0);
  solver.setOneShotSearchMode(-1);
  ASSERT_TRUE(solver.configureOneShot());
  EXPECT_THROW(solver.setOneShotSearchMode(1), std::logic_error);
  stp::Kissat loaded;
  const auto x = loaded.newVar();
  ASSERT_TRUE(loaded.addClause(clause({SATSolver::mkLit(x, false)})));
  EXPECT_THROW(loaded.setOneShotSearchMode(0), std::logic_error);
}

TEST(Kissat, EliminationControlSurvivesSearchBiasAndIncrementalSolves)
{
  for (int elimination : {-1, 0, 1})
    for (const auto bias :
         {stp::SearchBias::NONE, stp::SearchBias::SAT, stp::SearchBias::UNSAT})
    {
      stp::Kissat solver(true, -1, false, 2, elimination);
      ASSERT_TRUE(solver.setSearchBias(bias));
      testing::internal::CaptureStderr();
      solver.printStats();
      const std::string stats = testing::internal::GetCapturedStderr();
      EXPECT_NE(stats.find("probe=0"), std::string::npos);
      EXPECT_NE(stats.find(elimination == 0 ? "eliminate=0" : "eliminate=1"),
                std::string::npos);
      const auto x = solver.newVar(), y = solver.newVar();
      solver.setFrozen(x);
      solver.setFrozen(y);
      ASSERT_TRUE(solver.addClause(
          clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)})));
      bool timeout = false;
      const auto noX = clause({SATSolver::mkLit(x, true)});
      ASSERT_TRUE(solver.solveWithAssumptions(noX, timeout));
      EXPECT_EQ(solver.true_literal(), solver.modelValue(y));
      ASSERT_TRUE(solver.addClause(clause({SATSolver::mkLit(x, false)})));
      EXPECT_FALSE(solver.solveWithAssumptions(noX, timeout));
      std::vector<int> core;
      solver.unsatAssumptions(noX, core);
      ASSERT_EQ(core.size(), 1u);
      EXPECT_EQ(core[0], static_cast<int>(noX[0].x));
      ASSERT_TRUE(solver.solve(timeout));
      EXPECT_FALSE(timeout);
    }
}

TEST(Kissat, EliminationControlRejectsOutOfRangeValues)
{
  EXPECT_THROW(stp::Kissat(true, -1, true, -1, -2), std::invalid_argument);
  EXPECT_THROW(stp::Kissat(true, -1, true, -1, 2), std::invalid_argument);
}

TEST(Kissat, OneShotEliminationControlHasAValidModel)
{
  for (int elimination : {0, 1})
  {
    stp::Kissat solver(true, -1, true, -1, elimination);
    ASSERT_TRUE(solver.configureOneShot());
    ASSERT_TRUE(solver.setSearchBias(stp::SearchBias::UNSAT));
    const auto x = solver.newVar(), y = solver.newVar();
    solver.setFrozen(x);
    solver.setFrozen(y);
    ASSERT_TRUE(solver.addClause(
        clause({SATSolver::mkLit(x, false), SATSolver::mkLit(y, false)})));
    ASSERT_TRUE(solver.addClause(clause({SATSolver::mkLit(x, true)})));
    bool timeout = false;
    ASSERT_TRUE(solver.solve(timeout));
    EXPECT_FALSE(timeout);
    EXPECT_EQ(solver.false_literal(), solver.modelValue(x));
    EXPECT_EQ(solver.true_literal(), solver.modelValue(y));
  }
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

TEST(Kissat, GrowingProtectedFormulaRetainsModelsAndFailedAssumptions)
{
  for (bool reuse : {false, true})
  {
    SCOPED_TRACE(reuse);
    stp::Kissat solver(reuse);
    if (reuse)
    {
      ASSERT_TRUE(solver.enableTrailReuse(SATSolver::TrailReuse::ALL));
    }
    const auto first = solver.newVar();
    solver.setFrozen(first);
    auto last = first;
    bool timeout = false;
    for (unsigned round = 0; round != 16; ++round)
    {
      // Repeated growth crosses the capacities of several backend arrays,
      // while protection keeps the earlier variables available for reuse.
      for (unsigned i = 0; i != 256; ++i)
      {
        const auto next = solver.newVar();
        solver.setFrozen(next);
        ASSERT_TRUE(solver.addClause(clause(
            {SATSolver::mkLit(last, true), SATSolver::mkLit(next, false)})));
        last = next;
      }
      ASSERT_TRUE(solver.solveWithAssumptions(
          clause({SATSolver::mkLit(first, false)}), timeout));
      EXPECT_EQ(solver.true_literal(), solver.modelValue(last));
      const auto conflict = clause(
          {SATSolver::mkLit(first, false), SATSolver::mkLit(last, true)});
      ASSERT_FALSE(solver.solveWithAssumptions(conflict, timeout));
      EXPECT_TRUE(solver.okay());
      std::vector<int> core;
      solver.unsatAssumptions(conflict, core);
      EXPECT_EQ(2u, core.size());
      ASSERT_TRUE(solver.solveWithAssumptions(
          clause({SATSolver::mkLit(first, true)}), timeout));
      EXPECT_EQ(solver.false_literal(), solver.modelValue(first));
    }
    EXPECT_FALSE(timeout);
  }
}

#ifdef STP_KISSAT_HAS_CLAUSE_EXCHANGE
namespace
{
// Pigeons into holes, one more pigeon than holes: unsatisfiable, and it
// takes a few thousand conflicts, so there is something to exchange.
void addPigeonholes(SATSolver& solver, unsigned holes)
{
  std::vector<std::vector<uint32_t>> in(holes + 1);
  for (auto& pigeon : in)
    for (unsigned h = 0; h < holes; ++h)
      pigeon.push_back(solver.newVar());
  for (const auto& pigeon : in)
  {
    SATSolver::vec_literals somewhere;
    for (uint32_t var : pigeon)
      somewhere.push(SATSolver::mkLit(var, false));
    ASSERT_TRUE(solver.addClause(somewhere));
  }
  for (unsigned h = 0; h < holes; ++h)
    for (unsigned p = 0; p < in.size(); ++p)
      for (unsigned q = p + 1; q < in.size(); ++q)
        solver.addClause(clause({SATSolver::mkLit(in[p][h], true),
                                 SATSolver::mkLit(in[q][h], true)}));
}

// Clauses out into `learned`; clauses in from `inbox`.
struct Recorder final : SATSolver::ClauseExchange
{
  std::vector<std::vector<int>> learned_clauses, inbox;
  std::size_t at = 0, polls = 0;
  bool closed = false;
  SATSolver::ExchangeCounters final_counters;
  void learned(const int* literals, std::size_t size) override
  {
    learned_clauses.emplace_back(literals, literals + size);
  }
  bool next(std::vector<int>& literals) override
  {
    if (at == inbox.size())
      return false;
    literals.insert(literals.end(), inbox[at].begin(), inbox[at].end());
    ++at;
    return true;
  }
  void beginImport(std::size_t) override { ++polls; }
  void closing(const SATSolver::ExchangeCounters& counters) override
  {
    closed = true;
    final_counters = counters;
  }
};
} // namespace

TEST(Kissat, DiversifyOnlyBeforeTheFirstSolve)
{
  // Exactly one of a and b, and c when a: three models, none forced, for
  // every search mode (0 the backend's, 1 focused only, 2 stable only).
  for (std::int32_t mode : {0, 1, 2})
  {
    SCOPED_TRACE(mode);
    stp::Kissat solver;
    const auto a = solver.newVar(), b = solver.newVar(), c = solver.newVar();
    ASSERT_TRUE(solver.addClause(
        clause({SATSolver::mkLit(a, false), SATSolver::mkLit(b, false)})));
    ASSERT_TRUE(solver.addClause(
        clause({SATSolver::mkLit(a, true), SATSolver::mkLit(b, true)})));
    ASSERT_TRUE(solver.addClause(
        clause({SATSolver::mkLit(a, true), SATSolver::mkLit(c, false)})));
    SATSolver::Diversification d;
    d.seed = 3;
    d.phase = 0;
    d.shuffle = true;
    d.mode = mode;
    EXPECT_TRUE(solver.diversify(d));
    bool timeout = false;
    ASSERT_TRUE(solver.solve(timeout));
    // A solve has run: refused, and nothing changed.
    EXPECT_FALSE(solver.diversify(d));
    ASSERT_TRUE(solver.solve(timeout));
    const bool va = solver.modelValue(a) == solver.true_literal();
    const bool vb = solver.modelValue(b) == solver.true_literal();
    EXPECT_NE(va, vb);
    if (va)
    {
      EXPECT_EQ(solver.true_literal(), solver.modelValue(c));
    }
  }
  stp::Kissat solver;
  SATSolver::Diversification negative;
  negative.seed = -1;
  EXPECT_FALSE(solver.diversify(negative));
}

TEST(Kissat, CopiesOfOneFormulaShareLearnedClauses)
{
  // One copy exports what it learns, over the variables that existed at
  // connection; another, given those clauses, imports them and reaches the
  // same answer. Both report their counters as they are destroyed.
  Recorder first, second;
  {
    stp::Kissat exporter, importer;
    addPigeonholes(exporter, 6);
    addPigeonholes(importer, 6);
    const auto variables = exporter.nVars();
    SATSolver::ExchangeSettings settings;
    settings.importInterval = 1;
    ASSERT_TRUE(exporter.connectClauseExchange(&first, settings));
    bool timeout = false;
    EXPECT_FALSE(exporter.solve(timeout));
    ASSERT_FALSE(first.learned_clauses.empty());
    for (const auto& c : first.learned_clauses)
    {
      ASSERT_FALSE(c.empty());
      ASSERT_LE(c.size(), settings.maxSize);
      for (int lit : c)
        ASSERT_TRUE(lit != 0 && std::abs(lit) <= int(variables));
    }
    const auto out = exporter.exchangeCounters();
    EXPECT_TRUE(out.connected);
    EXPECT_EQ(out.variables, variables);
    EXPECT_EQ(out.exported, first.learned_clauses.size());

    second.inbox = first.learned_clauses;
    ASSERT_TRUE(importer.connectClauseExchange(&second, settings));
    EXPECT_FALSE(importer.solve(timeout));
    const auto in = importer.exchangeCounters();
    EXPECT_GT(in.polls, 0u);
    EXPECT_EQ(in.polls, second.polls);
    EXPECT_GT(in.imported, 0u);
  }
  EXPECT_TRUE(first.closed);
  EXPECT_TRUE(second.closed);
  EXPECT_EQ(first.final_counters.exported, first.learned_clauses.size());
  EXPECT_GT(second.final_counters.imported, 0u);
}

TEST(Kissat, ClausesThatCannotBeImportedAreDropped)
{
  // An empty clause, a zero literal, INT_MIN and literals beyond the
  // exchange's variables are skipped before Kissat sees them; a clause over
  // a variable no clause mentions is dropped by Kissat.
  Recorder junk;
  junk.inbox = {{}, {1, 0, 2}, {INT_MIN}, {1, 2000000000}, {-2000000000}};
  stp::Kissat solver;
  addPigeonholes(solver, 6);
  const auto unused = solver.newVar();
  junk.inbox.push_back({int(unused) + 1, 1});
  SATSolver::ExchangeSettings settings;
  settings.importInterval = 1;
  ASSERT_TRUE(solver.connectClauseExchange(&junk, settings));
  bool timeout = false;
  EXPECT_FALSE(solver.solve(timeout));
  const auto counters = solver.exchangeCounters();
  ASSERT_GT(counters.polls, 0u);
  EXPECT_EQ(counters.dropped, 6u);
  EXPECT_EQ(counters.imported, 0u);
}
#endif

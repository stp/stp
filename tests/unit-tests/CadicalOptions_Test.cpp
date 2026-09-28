#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/Sat/SearchBias.h"
#include <gtest/gtest.h>
#include <climits>
#include <memory>
#include <stdexcept>
#include <string>

#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif

TEST(CadicalOptions, UnspecifiedSettingsDoNotRequireCadical)
{
  stp::UserDefinedFlags flags;
  flags.solver_to_use = stp::UserDefinedFlags::MINISAT_SOLVER;
  EXPECT_FALSE(flags.cadical_options.hasOverrides());
  EXPECT_NO_THROW(stp::validateCadicalOptions(flags));
  flags.cadical_options.elim = 0;
  EXPECT_THROW(stp::validateCadicalOptions(flags), std::invalid_argument);
}

#ifdef USE_CADICAL
namespace
{

// elimmineff and elimmaxeff are CaDiCaL 3.x's names. 2.x has the same
// controls as elimineff and elimaxeff, and STP rejects its own options there
// rather than map them, so against 2.x only the elimination switch is set.
bool efficiencyControls()
{
  return CaDiCaL::Solver::is_valid_option("elimmineff") &&
         CaDiCaL::Solver::is_valid_option("elimmaxeff");
}

void expectOptions(const stp::SATSolver& solver, int elim, int minimum, int maximum)
{
  testing::internal::CaptureStderr();
  solver.printStats();
  const std::string output = testing::internal::GetCapturedStderr();
  const std::string efficiency =
      efficiencyControls() ? " elimmineff=" + std::to_string(minimum) +
                                 " elimmaxeff=" + std::to_string(maximum)
                           : " elimmineff=unavailable elimmaxeff=unavailable";
  const std::string expected =
      "CaDiCaL elimination: elim=" + std::to_string(elim) + efficiency + "\n";
  EXPECT_NE(output.find(expected), std::string::npos) << output;
}

stp::CadicalOptions settings(int elim, int minimum = 10000, int maximum = 100000)
{
  if (!efficiencyControls())
    return stp::CadicalOptions{elim, std::nullopt, std::nullopt};
  return stp::CadicalOptions{elim, minimum, maximum};
}

void addUnit(stp::SATSolver& solver, uint32_t variable, bool negative)
{
  stp::SATSolver::vec_literals clause;
  clause.push(stp::SATSolver::mkLit(variable, negative));
  solver.addClause(clause);
}

} // namespace

TEST(CadicalOptions, FactoryAndSearchBiasPreserveExplicitSettings)
{
  for (int elim : {0, 1})
    for (stp::SearchBias bias : {stp::SearchBias::NONE, stp::SearchBias::SAT,
                                stp::SearchBias::UNSAT})
    {
      stp::UserDefinedFlags flags;
      flags.solver_to_use = stp::UserDefinedFlags::CADICAL_SOLVER;
      flags.search_bias = bias;
      flags.cadical_options = settings(elim);
      ASSERT_NO_THROW(stp::validateCadicalOptions(flags));
      // Fresh construction is also how STP rebuilds its SAT backend.
      for (unsigned rebuild = 0; rebuild != 2; ++rebuild)
      {
        std::unique_ptr<stp::SATSolver> solver(stp::createSATSolver(flags));
        stp::applySearchBias(*solver, flags, false);
        expectOptions(*solver, elim, 10000, 100000);
      }
    }
}

TEST(CadicalOptions, RetirementYieldsToExplicitEnable)
{
  stp::Cadical enabled(settings(1));
  EXPECT_FALSE(enabled.disableEliminationAndShrinking());
  expectOptions(enabled, 1, 10000, 100000);

  stp::Cadical disabled(settings(0));
  EXPECT_TRUE(disabled.disableEliminationAndShrinking());
  expectOptions(disabled, 0, 10000, 100000);

  // Specifying only effort bounds must not prevent automatic retirement.
  if (efficiencyControls())
  {
    stp::Cadical effortOnly(stp::CadicalOptions{std::nullopt, 10000, 100000});
    EXPECT_TRUE(effortOnly.disableEliminationAndShrinking());
    expectOptions(effortOnly, 0, 10000, 100000);
  }
}

TEST(CadicalOptions, RejectsClampingAndAcceptsZero)
{
  for (stp::CadicalOptions invalid : {
           stp::CadicalOptions{-1, {}, {}}, stp::CadicalOptions{2, {}, {}},
           stp::CadicalOptions{{}, -1, {}}, stp::CadicalOptions{{}, {}, -1},
           stp::CadicalOptions{{}, INT_MAX, {}},
           stp::CadicalOptions{{}, {}, INT_MAX}})
  {
    EXPECT_THROW(stp::Cadical solver(invalid), std::invalid_argument);
  }
  stp::Cadical zero(settings(0, 0, 0));
  expectOptions(zero, 0, 0, 0);
}

TEST(CadicalOptions, OlderCadicalRejectsEfficiencyControls)
{
  if (efficiencyControls())
    GTEST_SKIP() << "this CaDiCaL has elimmineff and elimmaxeff";
  for (stp::CadicalOptions unavailable :
       {stp::CadicalOptions{{}, 10000, {}}, stp::CadicalOptions{{}, {}, 100000}})
  {
    try
    {
      stp::Cadical solver(unavailable);
      ADD_FAILURE() << "an unavailable CaDiCaL option was accepted";
    }
    catch (const std::invalid_argument& error)
    {
      EXPECT_NE(std::string(error.what()).find("is unavailable in this CaDiCaL build"),
                std::string::npos)
          << error.what();
    }
  }
}

TEST(CadicalOptions, SearchResetKeepsSettingsAndModelSemantics)
{
  for (int elim : {0, 1})
  {
    stp::Cadical solver(settings(elim));
    ASSERT_TRUE(solver.setSearchBias(stp::SearchBias::SAT));
    const uint32_t x = solver.newVar();
    const uint32_t y = solver.newVar();
    stp::SATSolver::vec_literals clause;
    clause.push(stp::SATSolver::mkLit(x, false));
    clause.push(stp::SATSolver::mkLit(y, false));
    solver.addClause(clause);
    addUnit(solver, x, true);
    bool timedOut = false;
    ASSERT_TRUE(solver.solve(timedOut));
    EXPECT_FALSE(timedOut);
    EXPECT_EQ(solver.modelValue(y), solver.true_literal());

    ASSERT_TRUE(solver.resetSearch());
    expectOptions(solver, elim, 10000, 100000);
    ASSERT_TRUE(solver.solve(timedOut));
    EXPECT_FALSE(timedOut);
    EXPECT_EQ(solver.modelValue(y), solver.true_literal());
    addUnit(solver, y, true);
    EXPECT_FALSE(solver.solve(timedOut));
    EXPECT_FALSE(timedOut);
  }
}
#else
TEST(CadicalOptions, RejectsUnavailableBackend)
{
  stp::UserDefinedFlags flags;
  flags.solver_to_use = stp::UserDefinedFlags::CADICAL_SOLVER;
  flags.cadical_options.elim = 0;
  EXPECT_THROW(stp::validateCadicalOptions(flags), std::invalid_argument);
}
#endif

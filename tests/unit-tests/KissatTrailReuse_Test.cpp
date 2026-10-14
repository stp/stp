/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Oct, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>

#ifdef USE_KISSAT
#include "stp/Sat/Kissat.h"

namespace
{
void expectMode(const stp::Kissat& solver, int mode)
{
  testing::internal::CaptureStderr();
  solver.printStats();
  const std::string stats = testing::internal::GetCapturedStderr();
  EXPECT_NE(stats.find(" trail-reuse=" + std::to_string(mode) + "\n"),
            std::string::npos)
      << stats;
}
} // namespace

TEST(KissatTrailReuse, ExplicitModesAndOptOut)
{
  using Solver = stp::SATSolver;
  for (int mode : {-1, 0, 1, 2})
  {
    stp::Kissat solver(true, 2, false, mode);
    expectMode(solver, mode < 0 ? 0 : mode);
    EXPECT_EQ(solver.enableTrailReuse(Solver::TrailReuse::ASSUMPTIONS),
              mode != 0);
    expectMode(solver, mode < 0 ? 1 : mode);
    EXPECT_EQ(solver.enableTrailReuse(Solver::TrailReuse::ALL),
              mode == -1 || mode == 2);
    expectMode(solver, mode < 0 ? 2 : mode);
  }
  stp::Kissat disabled(false, 2, false, 2);
  EXPECT_FALSE(disabled.enableTrailReuse(Solver::TrailReuse::ALL));
  expectMode(disabled, 0);
  stp::Kissat one_shot(true, 2, false, 2);
  ASSERT_TRUE(one_shot.configureOneShot());
  EXPECT_FALSE(one_shot.enableTrailReuse(Solver::TrailReuse::ALL));
  expectMode(one_shot, 0);
  EXPECT_THROW(stp::Kissat(true, 2, false, -2), std::invalid_argument);
  EXPECT_THROW(stp::Kissat(true, 2, false, 3), std::invalid_argument);
}

TEST(KissatTrailReuse, RefinementAndChangedAssumptions)
{
  using Solver = stp::SATSolver;
  for (int mode : {0, 1, 2})
  {
    stp::Kissat solver(true, 2, false, mode);
    solver.enableTrailReuse(Solver::TrailReuse::ASSUMPTIONS);
    const auto guard = solver.newVar();
    std::vector<uint32_t> variables;
    Solver::vec_literals some_true, some_false;
    some_true.push(Solver::mkLit(guard, true));
    some_false.push(Solver::mkLit(guard, true));
    for (int i = 0; i != 3; ++i)
    {
      const auto var = solver.newVar();
      variables.push_back(var);
      solver.setFrozen(var);
      some_true.push(Solver::mkLit(var, false));
      some_false.push(Solver::mkLit(var, true));
    }
    solver.addClause(some_true);
    solver.addClause(some_false);
    Solver::vec_literals active;
    active.push(Solver::mkLit(guard, false));
    bool timed_out = false;
    std::set<unsigned> models;
    while (solver.solveWithAssumptions(active, timed_out))
    {
      ASSERT_FALSE(timed_out);
      Solver::vec_literals blocking;
      blocking.push(Solver::mkLit(guard, true));
      unsigned model = 0;
      for (unsigned i = 0; i != variables.size(); ++i)
      {
        const auto value = solver.modelValue(variables[i]);
        ASSERT_NE(value, solver.undef_literal());
        const bool positive = value == solver.true_literal();
        model |= unsigned(positive) << i;
        blocking.push(Solver::mkLit(variables[i], positive));
      }
      ASSERT_NE(model, 0u);
      ASSERT_NE(model, 7u);
      ASSERT_TRUE(models.insert(model).second);
      solver.addClause(blocking);
    }
    EXPECT_FALSE(timed_out);
    EXPECT_EQ(models.size(), 6u);
    Solver::vec_literals inactive;
    inactive.push(Solver::mkLit(guard, true));
    ASSERT_TRUE(solver.solveWithAssumptions(inactive, timed_out));
    EXPECT_EQ(solver.modelValue(guard), solver.false_literal());
    EXPECT_FALSE(solver.solveWithAssumptions(active, timed_out));
    // Fresh variables and permanent units arrive after several searches.
    const auto fresh = solver.newVar();
    Solver::vec_literals unit;
    unit.push(Solver::mkLit(fresh, false));
    solver.addClause(unit);
    inactive.push(Solver::mkLit(fresh, true));
    EXPECT_FALSE(solver.solveWithAssumptions(inactive, timed_out));
    inactive.pop();
    ASSERT_TRUE(solver.solveWithAssumptions(inactive, timed_out));
    EXPECT_EQ(solver.modelValue(fresh), solver.true_literal());
    EXPECT_FALSE(timed_out);
  }
}
#endif

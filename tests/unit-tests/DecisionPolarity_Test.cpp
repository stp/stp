#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>
#include <stdexcept>
#include <vector>

#if defined(USE_CADICAL) && defined(STP_CADICAL_HAS_DECISION_POLARITY)
#define STP_TEST_CADICAL_POLARITY
#include "stp/Sat/Cadical.h"
#endif
#if defined(USE_CRYPTOMINISAT) && defined(STP_CRYPTOMINISAT_HAS_UP)
#define STP_TEST_CRYPTOMINISAT_POLARITY
#include "stp/Sat/CryptoMinisat5.h"
#endif

#if defined(STP_TEST_CADICAL_POLARITY) ||                                      \
    defined(STP_TEST_CRYPTOMINISAT_POLARITY)
namespace {
using stp::SATSolver;

struct Advice final : SATSolver::TheoryPropagator
{
  enum Mode { Disabled, Abstain, Flip, Throw } mode;
  std::vector<SATSolver::Lit> offered, assigned;
  explicit Advice(Mode m) : mode(m) {}
  void notifyAssigned(const std::vector<SATSolver::Lit>& ls) override
  {
    assigned.insert(assigned.end(), ls.begin(), ls.end());
  }
  void notifyNewLevel() override {}
  void notifyBacktrack(size_t) override {}
  bool checkFoundModel() override { return true; }
  bool takeClause(std::vector<SATSolver::Lit>&) override { return false; }
  bool failed() const override { return false; }
  bool wantsDecisionPolarity() const override { return mode != Disabled; }
  bool decisionPolarity(uint32_t variable, bool& value) override
  {
    offered.push_back(SATSolver::mkLit(variable, !value));
    if (mode == Throw)
      throw std::runtime_error("advice is optional");
    if (mode != Flip)
      return false;
    value = !value;
    return true;
  }
};

// On a fresh solver, which is disconnected again before this returns.
std::vector<SATSolver::Lit> exercise(SATSolver& solver, Advice::Mode mode)
{
  Advice advice(mode);
  auto a = solver.newVar(), b = solver.newVar();
  auto guard = solver.newVar(), root = solver.newVar();
  auto add = [&](std::initializer_list<SATSolver::Lit> literals) {
    SATSolver::vec_literals clause;
    for (auto lit : literals)
      clause.push(lit);
    EXPECT_TRUE(solver.addClause(clause));
  };
  add({SATSolver::mkLit(guard, true), SATSolver::mkLit(a, false), SATSolver::mkLit(b, false)});
  add({SATSolver::mkLit(guard, true), SATSolver::mkLit(a, true), SATSolver::mkLit(b, true)});
  add({SATSolver::mkLit(root, false)});
  EXPECT_TRUE(solver.connectTheoryPropagator(&advice, {a, b, guard, root}));
  SATSolver::vec_literals assumptions;
  assumptions.push(SATSolver::mkLit(guard, false));
  bool timeout = false;
  EXPECT_TRUE(solver.solveWithAssumptions(assumptions, timeout));
  EXPECT_FALSE(timeout);
  EXPECT_NE(solver.modelValue(a), solver.modelValue(b));
  if (mode == Advice::Disabled)
    EXPECT_TRUE(advice.offered.empty());
  else
  {
    EXPECT_FALSE(advice.offered.empty());
    for (auto lit : advice.offered)
      EXPECT_TRUE(SATSolver::var(lit) == a || SATSolver::var(lit) == b);
    if (!advice.offered.empty())
    {
      auto chosen = advice.offered.front();
      bool saw = false;
      for (auto lit : advice.assigned)
        if (SATSolver::var(lit) == SATSolver::var(chosen))
        {
          EXPECT_EQ(SATSolver::sign(lit), SATSolver::sign(chosen) ^ (mode == Advice::Flip));
          saw = true;
          break;
        }
      EXPECT_TRUE(saw);
    }
  }
  // Both XOR inputs are fixed by the second query's assumptions/propagation:
  // the advice callback must not touch either assumption or the root unit.
  auto calls = advice.offered.size();
  assumptions.push(SATSolver::mkLit(a, false));
  EXPECT_TRUE(solver.solveWithAssumptions(assumptions, timeout));
  EXPECT_EQ(advice.offered.size(), calls);
  EXPECT_EQ(solver.modelValue(a), solver.true_literal());
  EXPECT_EQ(solver.modelValue(b), solver.false_literal());
  solver.disconnectTheoryPropagator();
  return advice.offered;
}

// The advice changes the sign of a decision and nothing else: the first
// decision offered is the same whatever the advice was.
template <class Run> void preservesSelection(Run run)
{
  auto baseline = run(Advice::Abstain);
  auto flipped = run(Advice::Flip);
  auto throwing = run(Advice::Throw);
  run(Advice::Disabled);
  ASSERT_FALSE(baseline.empty());
  ASSERT_FALSE(flipped.empty());
  ASSERT_FALSE(throwing.empty());
  EXPECT_EQ(baseline.front().x, flipped.front().x);
  EXPECT_EQ(baseline.front().x, throwing.front().x);
}
} // namespace
#endif

#if defined(STP_TEST_CADICAL_POLARITY)
TEST(DecisionPolarity, PreservesVariableSelectionAndTranslatesSigns)
{
  for (bool factor : {false, true})
    preservesSelection(
        [factor](Advice::Mode mode)
        {
          stp::Cadical solver;
          if (factor)
          {
            EXPECT_TRUE(solver.enableBVA());
          }
          return exercise(solver, mode);
        });
}
#endif

#if defined(STP_TEST_CRYPTOMINISAT_POLARITY)
TEST(DecisionPolarity, CryptoMiniSatTranslatesSigns)
{
  preservesSelection(
      [](Advice::Mode mode)
      {
        stp::CryptoMiniSat5 solver(1);
        return exercise(solver, mode);
      });
}
#endif

#if !defined(STP_TEST_CADICAL_POLARITY) &&                                     \
    !defined(STP_TEST_CRYPTOMINISAT_POLARITY)
TEST(DecisionPolarity, BackendCapabilityUnavailable)
{
  GTEST_SKIP() << "this backend has no decision-polarity API";
}
#endif

// A theory propagator may only be connected once a CNF exists, and the CNF
// that first carries the theory's atoms can be several solves into a query --
// BV equality abstraction refines the formula and the atoms arrive with a
// later round. CaDiCaL meanwhile only lets a variable become observed while
// it is still "clean": nothing may have put it on the extension stack.
//
// SATSolver::expectTheoryPropagator() is the notice that closes that gap. It
// is given before the first solve, while there is still time to stop the
// inprocessing that would make an atom unobservable later. Without it STP
// aborts inside CaDiCaL's add_observed_var contract check on a QF_FPLRA query
// -- no answer, exit 134.

#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>
#include <string>
#include <vector>

#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"

namespace
{
using stp::SATSolver;

// Bounded variable elimination is the technique that witness-marks an atom in
// the observed QF_FPLRA failure, and the only one of the six whose setting
// printStats() reports, so it stands for the rest here.
void expectElimination(const SATSolver& solver, int expected)
{
  testing::internal::CaptureStderr();
  solver.printStats();
  const std::string output = testing::internal::GetCapturedStderr();
  const std::string wanted = "elim=" + std::to_string(expected) + " ";
  EXPECT_NE(output.find(wanted), std::string::npos) << output;
}

// Enough of the interface to be connected; this test is about the backend's
// bookkeeping, not about any theory's answers.
struct Inert final : SATSolver::TheoryPropagator
{
  void notifyAssigned(const std::vector<SATSolver::Lit>&) override {}
  void notifyNewLevel() override {}
  void notifyBacktrack(size_t) override {}
  bool checkFoundModel() override { return true; }
  bool takeClause(std::vector<SATSolver::Lit>&) override { return false; }
  bool failed() const override { return false; }
};

void addClause(SATSolver& solver, std::initializer_list<SATSolver::Lit> literals)
{
  SATSolver::vec_literals clause;
  for (auto literal : literals)
    clause.push(literal);
  ASSERT_TRUE(solver.addClause(clause));
}

} // namespace

TEST(TheoryPropagatorExpectation, RetiresInprocessingThatUnobserves)
{
  stp::Cadical solver;
  expectElimination(solver, 1);
  solver.expectTheoryPropagator();
  expectElimination(solver, 0);
}

TEST(TheoryPropagatorExpectation, IsIdempotent)
{
  stp::Cadical solver;
  solver.expectTheoryPropagator();
  solver.expectTheoryPropagator();
  expectElimination(solver, 0);
}

// The ordering the LRA coordinator actually produces: notice, a solve, more
// clauses, and only then the connection naming the atoms. Against a CaDiCaL
// that still carries its own add_observed_var contract check this aborts the
// process without the notice above.
TEST(TheoryPropagatorExpectation, ObserveAfterASolve)
{
  Inert theory; // outlives the solver's connection
  stp::Cadical solver;
  solver.expectTheoryPropagator();

  const auto a = solver.newVar(), b = solver.newVar(), c = solver.newVar();
  // b appears only here, so elimination would resolve it away and record a
  // witness for it -- which is what makes observing it later illegal.
  addClause(solver, {SATSolver::mkLit(a, false), SATSolver::mkLit(b, false)});
  addClause(solver, {SATSolver::mkLit(a, true), SATSolver::mkLit(b, true)});

  bool timeout = false;
  ASSERT_TRUE(solver.solve(timeout));
  ASSERT_FALSE(timeout);

  const auto atom = solver.newVar();
  addClause(solver, {SATSolver::mkLit(c, false), SATSolver::mkLit(atom, false)});

  ASSERT_TRUE(solver.connectTheoryPropagator(&theory, {a, b, c, atom}));
  ASSERT_TRUE(solver.solve(timeout));
  EXPECT_FALSE(timeout);
  solver.disconnectTheoryPropagator();
}
#endif

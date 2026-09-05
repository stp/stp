// The submitted-clause count belongs to the backend-neutral facade: theory
// refinement and other generic clients only hold SATSolver&, and every one of
// their clauses must be visible to persistent-solver accounting regardless of
// what a backend later simplifies away.
#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>

namespace
{

class StubSolver : public stp::SATSolver
{
  bool accept = true;

public:
  void setAccept(bool value) { accept = value; }

  bool okay() const override { return true; }
  uint8_t modelValue(uint32_t) const override { return undef_literal(); }
  uint32_t newVar() override { return 0; }
  uint32_t nVars() const override { return 0; }
  void printStats() const override {}
  void setVerbosity(int) override {}
  lbool true_literal() const override { return 0; }
  lbool false_literal() const override { return 1; }
  lbool undef_literal() const override { return 2; }

protected:
  bool addClauseInternal(const vec_literals&) override { return accept; }
  bool solveInternal(bool&) override { return false; }
};

TEST(SATSolver, CountsEverySubmittedClause)
{
  StubSolver solver;
  stp::SATSolver& generic = solver;
  stp::SATSolver::vec_literals clause;
  clause.push(stp::SATSolver::mkLit(0, false));

  EXPECT_EQ(0u, generic.submittedClauses());
  EXPECT_TRUE(generic.addClause(clause));
  EXPECT_EQ(1u, generic.submittedClauses());

  // A rejected clause is still a submission and must remain in the retained
  // input accounting; it commonly means this add discovered inconsistency.
  solver.setAccept(false);
  EXPECT_FALSE(generic.addClause(clause));
  EXPECT_EQ(2u, generic.submittedClauses());
}

} // namespace

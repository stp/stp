// Guards --cadical-factor. Bounded variable addition invents extension
// variables in CaDiCaL's external index space, so once it is on every STP
// variable travels through a translation table (declared ranges are placed
// by CaDiCaL, not by STP). These tests pin the two ways that could do
// damage: a backend must report honestly whether it can enable BVA (that
// drives the warning STP prints for an explicit --cadical-factor=on), and
// with BVA enabled the verdicts and model values across incremental solve
// calls -- the pattern the refinement loop relies on -- must be unchanged.
#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>

#ifdef USE_MINISAT
#include "stp/Sat/MinisatCore.h"
#endif
#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif

using stp::SATSolver;

#ifdef USE_MINISAT
// Minisat has no BVA, and has to say so rather than silently drop the
// request: STP warns on the back of this.
TEST(Bva, MinisatReportsNoSupport)
{
  stp::MinisatCore s;
  EXPECT_FALSE(s.enableBVA());
}
#endif

#ifdef USE_CADICAL

// Only the Cadical tests below build clauses; without USE_CADICAL these
// helpers would be unused and -Werror=unused-function rejects the file.
namespace
{

void addUnit(SATSolver& s, uint32_t var, bool negated)
{
  SATSolver::vec_literals c;
  c.push(SATSolver::mkLit(var, negated));
  s.addClause(c);
}

void addBinary(SATSolver& s, uint32_t a, bool a_neg, uint32_t b, bool b_neg)
{
  SATSolver::vec_literals c;
  c.push(SATSolver::mkLit(a, a_neg));
  c.push(SATSolver::mkLit(b, b_neg));
  s.addClause(c);
}

} // namespace

// Whether Cadical can enable BVA is decided at configure time from the
// CaDiCaL version, and the answer at runtime has to match that decision.
TEST(Bva, CadicalReportsConfigureTimeSupport)
{
  stp::Cadical s;
#ifdef STP_CADICAL_HAS_FACTOR
  EXPECT_TRUE(s.enableBVA());
#else
  EXPECT_FALSE(s.enableBVA());
#endif
}

// The incremental driver's pattern with BVA on: everything retractable is
// solved under assumptions, and an assumption may name a variable created
// after the last declared batch. Assumption literals must travel through
// the same declare/translate machinery as clause literals -- an assumption
// placed under a raw STP index binds a different CaDiCaL variable than the
// clauses and the model lookups use, which first shows up as an assumption
// that silently fails to constrain anything (sat where unsat, model values
// contradicting the assumption). The final unsat/sat pair is the
// deterministic version of that: a unit clause against an assumed negation
// must conflict, and must stop conflicting when the assumption is dropped.
TEST(Bva, CadicalAssumptionsShareTheTranslation)
{
  stp::Cadical s;
  // On pre-3.0 CaDiCaL this declines and the same expectations pin the
  // untranslated path instead.
  s.enableBVA();

  bool timed_out = false;
  const uint32_t x = s.newVar();
  const uint32_t y = s.newVar();
  addBinary(s, x, false, y, false); // (x | y)

  SATSolver::vec_literals notX;
  notX.push(SATSolver::mkLit(x, true));
  ASSERT_TRUE(s.solveWithAssumptions(notX, timed_out));
  EXPECT_EQ(s.modelValue(y), s.true_literal());

  // A variable no clause has mentioned yet: assuming it is what forces the
  // declaration to happen at assume time, not first at the next addClause.
  const uint32_t z = s.newVar();
  SATSolver::vec_literals notZ;
  notZ.push(SATSolver::mkLit(z, true));
  ASSERT_TRUE(s.solveWithAssumptions(notZ, timed_out));
  EXPECT_EQ(s.modelValue(z), s.false_literal());

  addUnit(s, z, false); // (z)
  EXPECT_FALSE(s.solveWithAssumptions(notZ, timed_out));
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_EQ(s.modelValue(z), s.true_literal());
}

// The refinement-loop pattern with BVA on: solve, read the model, add
// clauses over fresh variables, solve again. Every variable here crosses
// the declare/translate machinery, so a mapping mistake shows up as a
// wrong verdict or a wrong model value.
TEST(Bva, CadicalIncrementalVerdictsAndModelAreStable)
{
  stp::Cadical s;
  s.enableBVA();

  const uint32_t x = s.newVar();
  const uint32_t y = s.newVar();
  addBinary(s, x, false, y, false); // (x | y)
  addUnit(s, x, true);              // (~x)

  bool timed_out = false;
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_FALSE(timed_out);
  EXPECT_EQ(s.modelValue(y), s.true_literal());

  const uint32_t z = s.newVar();
  addBinary(s, y, true, z, false); // (~y | z)
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_EQ(s.modelValue(y), s.true_literal());
  EXPECT_EQ(s.modelValue(z), s.true_literal());

  addUnit(s, z, true); // (~z), contradicting the two clauses above
  EXPECT_FALSE(s.solve(timed_out));
}

#endif

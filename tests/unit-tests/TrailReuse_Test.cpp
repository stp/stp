// Guards enableTrailReuse (CaDiCaL's incremental lazy backtracking).
// Correctness under trail reuse is the solver's own business; what these
// tests pin is the wrapper contract the incremental driver relies on: a
// backend without the mechanism says so, and with it enabled the driver's
// exact usage pattern -- solves whose assumption sequences share prefixes,
// clauses added between solves under unchanged assumptions -- keeps
// producing the right verdicts and model values.
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
TEST(TrailReuse, MinisatReportsNoSupport)
{
  stp::MinisatCore s;
  EXPECT_FALSE(s.enableTrailReuse());
}
#endif

#ifdef USE_CADICAL

namespace
{
void addBinary(SATSolver& s, uint32_t a, bool a_neg, uint32_t b, bool b_neg)
{
  SATSolver::vec_literals c;
  c.push(SATSolver::mkLit(a, a_neg));
  c.push(SATSolver::mkLit(b, b_neg));
  s.addClause(c);
}
} // namespace

// The driver's shape: a stable assumption prefix, a varying suffix, and
// definitional clauses arriving between solves. Every answer and model
// read below crosses whatever trail the solver kept from the call before.
TEST(TrailReuse, CadicalPrefixStableAssumptionRounds)
{
  stp::Cadical s;
  // On a CaDiCaL without the option this declines, and the same
  // expectations pin the ordinary re-descending path instead.
  s.enableTrailReuse();

  bool timed_out = false;
  const uint32_t base = s.newVar();
  const uint32_t x = s.newVar();
  const uint32_t y = s.newVar();
  addBinary(s, base, true, x, false); // base -> x

  SATSolver::vec_literals a1;
  a1.push(SATSolver::mkLit(base, false));
  ASSERT_TRUE(s.solveWithAssumptions(a1, timed_out));
  EXPECT_EQ(s.modelValue(x), s.true_literal());

  // Extend the prefix: [base] -> [base, y].
  addBinary(s, y, true, x, true); // y -> ~x, contradicting base -> x
  SATSolver::vec_literals a2;
  a2.push(SATSolver::mkLit(base, false));
  a2.push(SATSolver::mkLit(y, false));
  EXPECT_FALSE(s.solveWithAssumptions(a2, timed_out));

  // Retreat to the shared prefix again: satisfiable as before.
  ASSERT_TRUE(s.solveWithAssumptions(a1, timed_out));
  EXPECT_EQ(s.modelValue(x), s.true_literal());

  // Diverge the suffix: [base, z] with z forcing a fresh chain encoded
  // only now -- clauses added after three solves already ran.
  const uint32_t z = s.newVar();
  const uint32_t w = s.newVar();
  addBinary(s, z, true, w, false); // z -> w
  SATSolver::vec_literals a3;
  a3.push(SATSolver::mkLit(base, false));
  a3.push(SATSolver::mkLit(z, false));
  ASSERT_TRUE(s.solveWithAssumptions(a3, timed_out));
  EXPECT_EQ(s.modelValue(x), s.true_literal());
  EXPECT_EQ(s.modelValue(w), s.true_literal());

  // And a permanent unit added between solves must invalidate what the
  // kept trail believed: base becomes false, so assuming it is now unsat.
  SATSolver::vec_literals unit;
  unit.push(SATSolver::mkLit(base, true));
  s.addClause(unit);
  EXPECT_FALSE(s.solveWithAssumptions(a1, timed_out));
}

#endif

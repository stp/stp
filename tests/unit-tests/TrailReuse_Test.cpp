// Guards enableTrailReuse (CaDiCaL's incremental lazy backtracking).
// Correctness under trail reuse is the solver's own business; what these
// tests pin is the wrapper contract the incremental driver relies on: a
// backend without the mechanism says so, and with it enabled the driver's
// exact usage pattern -- solves whose assumption sequences share prefixes,
// clauses added between solves under unchanged assumptions -- keeps
// producing the right verdicts and model values.
#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>

#include <set>
#include <vector>

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
  EXPECT_FALSE(s.enableTrailReuse(SATSolver::TrailReuse::ALL));
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


// The batch pipeline's shape: no assumptions at all, a model read after
// every solve, and between solves the clauses that refute the model just
// read. Under the ASSUMPTIONS scope a call with no assumptions keeps
// nothing; under ALL the trail survives each addition and is unwound only
// as far as the new clause reaches. Enumerating every model by blocking
// clauses is the refinement loop with the theory taken out: each round's
// clause is falsified by the trail the solver kept, which is exactly the
// case the partial backtrack has to get right, and the count at the end
// says whether any model was found twice or never.
TEST(TrailReuse, CadicalKeepsTrailAcrossRefinementRounds)
{
  stp::Cadical s;
#if defined(CADICAL_MAJOR) && CADICAL_MAJOR >= 3
  EXPECT_TRUE(s.enableTrailReuse(SATSolver::TrailReuse::ALL));
#else
  // Older CaDiCaLs may decline the scope; the checks below then pin the
  // ordinary re-descending path instead.
  s.enableTrailReuse(SATSolver::TrailReuse::ALL);
#endif

  const unsigned n = 4;
  std::vector<uint32_t> v;
  for (unsigned i = 0; i < n; i++)
    v.push_back(s.newVar());

  // Not all false, not all true: 14 of the 16 assignments remain.
  SATSolver::vec_literals someTrue, someFalse;
  for (unsigned i = 0; i < n; i++)
  {
    someTrue.push(SATSolver::mkLit(v[i], false));
    someFalse.push(SATSolver::mkLit(v[i], true));
  }
  s.addClause(someTrue);
  s.addClause(someFalse);

  std::set<unsigned> seen;
  bool timed_out = false;
  unsigned rounds = 0;
  while (s.solve(timed_out))
  {
    ASSERT_FALSE(timed_out);
    unsigned model = 0;
    for (unsigned i = 0; i < n; i++)
      if (s.modelValue(v[i]) == s.true_literal())
        model |= 1u << i;
    EXPECT_NE(model, 0u) << "a model that falsifies the first clause";
    EXPECT_NE(model, (1u << n) - 1) << "a model that falsifies the second";
    EXPECT_TRUE(seen.insert(model).second)
        << "model " << model << " was found twice: a blocking clause was "
        << "lost across the kept trail";

    // Refute it, the way a refinement round refutes a candidate.
    SATSolver::vec_literals block;
    for (unsigned i = 0; i < n; i++)
      block.push(SATSolver::mkLit(v[i], (model >> i) & 1u));
    s.addClause(block);

    ASSERT_LE(++rounds, 14u) << "more rounds than there are models";
  }
  EXPECT_FALSE(timed_out);
  EXPECT_EQ(rounds, 14u) << "a model was never found";
  EXPECT_EQ(seen.size(), 14u);
}

// The whole trail kept, then a call that does carry assumptions, and
// units added between calls: the guard the batch pipeline assumes for
// injectivity is exactly this mixture. Every verdict has to be right
// against a trail the previous call left behind.
TEST(TrailReuse, CadicalAllScopeHonoursAssumptionsAndUnits)
{
  stp::Cadical s;
  s.enableTrailReuse(SATSolver::TrailReuse::ALL);

  bool timed_out = false;
  const uint32_t a = s.newVar();
  const uint32_t b = s.newVar();
  addBinary(s, a, false, b, false); // a | b

  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_TRUE(s.modelValue(a) == s.true_literal() ||
              s.modelValue(b) == s.true_literal());

  // Both assumed false contradicts the clause, whatever the kept trail
  // believed about a and b.
  SATSolver::vec_literals bothFalse;
  bothFalse.push(SATSolver::mkLit(a, true));
  bothFalse.push(SATSolver::mkLit(b, true));
  EXPECT_FALSE(s.solveWithAssumptions(bothFalse, timed_out));

  // One assumed false leaves the other forced.
  SATSolver::vec_literals notA;
  notA.push(SATSolver::mkLit(a, true));
  ASSERT_TRUE(s.solveWithAssumptions(notA, timed_out));
  EXPECT_EQ(s.modelValue(b), s.true_literal());

  // A unit added between calls: the kept trail may have b true.
  SATSolver::vec_literals unitNotB;
  unitNotB.push(SATSolver::mkLit(b, true));
  s.addClause(unitNotB);
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_EQ(s.modelValue(a), s.true_literal());
  EXPECT_EQ(s.modelValue(b), s.false_literal());

  // And the assumption that used to be satisfiable now is not.
  EXPECT_FALSE(s.solveWithAssumptions(notA, timed_out));

  SATSolver::vec_literals unitNotA;
  unitNotA.push(SATSolver::mkLit(a, true));
  s.addClause(unitNotA);
  EXPECT_FALSE(s.solve(timed_out));
}

#endif

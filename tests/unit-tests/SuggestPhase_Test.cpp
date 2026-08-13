// Guards suggestPhase, the phase-hint the incremental driver uses to
// steer the search away from retracted levels. The contract is
// deliberately weak -- hints are search advice a backend may ignore and
// can never change a verdict -- so that is what these tests pin, plus
// the one sharp edge: with CaDiCaL's factor enabled, a hint must travel
// through the same declared-variable translation as clause and
// assumption literals. (Which model a hint produces is solver-internal:
// CaDiCaL's lucky-phase probing can satisfy small instances before any
// decision consults a phase, so asserting model shapes here would test
// the solver's mood, not our contract.)
#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>

#ifdef USE_MINISAT
#include "stp/Sat/MinisatCore.h"
#endif
#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif

using stp::SATSolver;

// The base-class default ignores hints; solving must be unaffected.
#ifdef USE_MINISAT
TEST(SuggestPhase, MinisatIgnoresHints)
{
  stp::MinisatCore s;
  const uint32_t a = s.newVar();
  SATSolver::vec_literals c;
  c.push(SATSolver::mkLit(a, false));
  s.addClause(c);
  s.suggestPhase(a, false); // advice against the unit; must change nothing
  bool timed_out = false;
  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_EQ(s.modelValue(a), s.true_literal());
}
#endif

#ifdef USE_CADICAL

// Hints never move a verdict: a satisfiable clause stays satisfiable
// under hostile hints (and the model still satisfies it), an unsat core
// stays unsat under helpful ones.
TEST(SuggestPhase, CadicalVerdictsUnmovedByHints)
{
  bool timed_out = false;
  {
    stp::Cadical s;
    const uint32_t a = s.newVar();
    const uint32_t b = s.newVar();
    SATSolver::vec_literals c;
    c.push(SATSolver::mkLit(a, false));
    c.push(SATSolver::mkLit(b, false));
    s.addClause(c);
    s.suggestPhase(a, false);
    s.suggestPhase(b, false);
    ASSERT_TRUE(s.solve(timed_out));
    EXPECT_TRUE(s.modelValue(a) == s.true_literal() ||
                s.modelValue(b) == s.true_literal());
  }
  {
    stp::Cadical s;
    const uint32_t a = s.newVar();
    SATSolver::vec_literals pos, neg;
    pos.push(SATSolver::mkLit(a, false));
    neg.push(SATSolver::mkLit(a, true));
    s.addClause(pos);
    s.addClause(neg);
    s.suggestPhase(a, true);
    EXPECT_FALSE(s.solve(timed_out));
  }
}

// With factor enabled every literal travels through the declared-variable
// translation table; a hint on a raw STP index would phase a different
// CaDiCaL variable than the clauses use. This exercises hints before and
// after the variable's declaring clause, plus one on a variable no clause
// has mentioned (which must be safely ignorable, not a crash).
TEST(SuggestPhase, CadicalHintsTranslateUnderFactor)
{
  stp::Cadical s;
  s.enableBVA();

  bool timed_out = false;
  const uint32_t a = s.newVar();
  const uint32_t b = s.newVar();
  s.suggestPhase(a, false); // before any clause names a
  SATSolver::vec_literals c;
  c.push(SATSolver::mkLit(a, false));
  c.push(SATSolver::mkLit(b, false));
  s.addClause(c);
  s.suggestPhase(b, true); // after declaration

  const uint32_t never_claused = s.newVar();
  s.suggestPhase(never_claused, true);

  ASSERT_TRUE(s.solve(timed_out));
  EXPECT_TRUE(s.modelValue(a) == s.true_literal() ||
              s.modelValue(b) == s.true_literal());

  SATSolver::vec_literals killA, killB;
  killA.push(SATSolver::mkLit(a, true));
  killB.push(SATSolver::mkLit(b, true));
  s.addClause(killA);
  s.addClause(killB);
  EXPECT_FALSE(s.solve(timed_out));
}

#endif

// The backend configuration window.
//
// Backends may only accept configuration while they are still empty: CaDiCaL
// closes its option window at the first clause and answers a late setter by
// aborting the process. SATSolver.h stated that rule in prose beside five
// separate methods and checked it nowhere, so the only thing standing between
// a mis-ordered rebuild and an abort inside a third-party library was the
// call order happening to be right. The setters are now non-virtual facades
// that check the window before dispatching, and the window is the clause
// counter STP already keeps -- no new state, and a rebuild's fresh backend
// starts open again.
#include "stp/Sat/SATSolver.h"
#include <gtest/gtest.h>

#ifdef USE_CADICAL
#include "stp/Sat/Cadical.h"
#endif
#ifdef USE_MINISAT
#include "stp/Sat/MinisatCore.h"
#endif

using stp::SATSolver;

namespace
{
// Only the two backends below drive clauses into a solver here; a build with
// neither compiles every use away, and an unguarded definition is then an
// unused function.
#if defined(USE_CADICAL) || defined(USE_MINISAT)
void addUnit(SATSolver& s, uint32_t var)
{
  s.newVar();
  SATSolver::vec_literals c;
  c.push(SATSolver::mkLit(var, false));
  s.addClause(c);
}
#endif
} // namespace

#ifdef USE_CADICAL
// Open until the first clause, closed from it on.
TEST(SATSolverConfigWindow, ClosesAtTheFirstClause)
{
  stp::Cadical s;
  EXPECT_TRUE(s.configurationOpen());
  // configuration inside the window is accepted (or honestly declined)
  s.disableLuckyPhases();
  EXPECT_TRUE(s.configurationOpen());
  addUnit(s, 0);
  EXPECT_FALSE(s.configurationOpen());
}

// Every setter that carries the window rule is reachable while open. This is
// the ordering the driver relies on at every rebuild.
TEST(SATSolverConfigWindow, AllConfigurationIsAcceptedWhileOpen)
{
  stp::Cadical s;
  s.setSearchBias(stp::SearchBias::NONE);
  s.enableBVA();
  s.enableTrailReuse();
  if (s.supportsInprobingControl())
  {
    s.disableInprobing();
    s.disableEliminationAndShrinking();
    s.disableLuckyPhases();
  }
  EXPECT_TRUE(s.configurationOpen());
  addUnit(s, 0);
  EXPECT_FALSE(s.configurationOpen());
}
#endif

#ifdef USE_MINISAT
// The window is a property of the facade, not of any one backend: a backend
// that declines every hint still reports the window honestly.
TEST(SATSolverConfigWindow, HoldsForABackendThatDeclinesEveryHint)
{
  stp::MinisatCore s;
  EXPECT_TRUE(s.configurationOpen());
  EXPECT_FALSE(s.enableBVA());
  EXPECT_TRUE(s.configurationOpen());
  addUnit(s, 0);
  EXPECT_FALSE(s.configurationOpen());
}
#endif

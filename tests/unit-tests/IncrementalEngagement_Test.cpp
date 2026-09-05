// The two engagement policies: when a session that never asked for the
// incremental driver should start using it anyway, and when a session that
// DID ask is making its forced first solve.
//
// This was a literal in two places. The SMT-LIB2 reader read
// --incremental-auto-engage-at and applied a per-logic default; the C API
// hard-coded "from the third solve" and consulted nothing, so the documented
// override was inert for every embedder and the two frontends could drift
// apart silently. These pin the policy itself, which both now call.
#include "stp/Incremental/IncrementalSolver.h"
#include <gtest/gtest.h>

using stp::IncrementalSolver;

namespace
{
// `solvesRun` is checks already made, so the Nth check asks with N-1.
bool readyOnCheck(int64_t threshold, bool delayedBv, size_t nthCheck)
{
  return IncrementalSolver::automaticEngagementReady(threshold, delayedBv,
                                                     nthCheck - 1);
}
} // namespace

// A negative threshold selects the measured per-logic default. Pure
// QF_BV/QF_ABV repay the persistent encoding later than anything else, so
// they keep the batch pipeline through solve 31 and engage on 32.
TEST(IncrementalEngagement, BvDefaultEngagesOnTheThirtySecondCheck)
{
  EXPECT_FALSE(readyOnCheck(-1, true, 1));
  EXPECT_FALSE(readyOnCheck(-1, true, 31));
  EXPECT_TRUE(readyOnCheck(-1, true, 32));
  EXPECT_TRUE(readyOnCheck(-1, true, 4000));
}

// Everything else -- floating point, arrays outside QF_ABV, unknown logics,
// and any caller with no set-logic to consult -- keeps two batch warm-ups.
TEST(IncrementalEngagement, OtherLogicsEngageOnTheThirdCheck)
{
  EXPECT_FALSE(readyOnCheck(-1, false, 1));
  EXPECT_FALSE(readyOnCheck(-1, false, 2));
  EXPECT_TRUE(readyOnCheck(-1, false, 3));
}

// The override reaches the policy, which is the whole point of it existing:
// it must beat the per-logic default in both directions.
TEST(IncrementalEngagement, ConfiguredThresholdOverridesTheLogicDefault)
{
  EXPECT_TRUE(readyOnCheck(1, true, 1));
  EXPECT_TRUE(readyOnCheck(1, false, 1));
  EXPECT_FALSE(readyOnCheck(50, true, 49));
  EXPECT_TRUE(readyOnCheck(50, true, 50));
  // later than the BV default, on a logic that would otherwise engage at 3
  EXPECT_FALSE(readyOnCheck(40, false, 39));
  EXPECT_TRUE(readyOnCheck(40, false, 40));
}

// Zero disables automatic engagement without disabling the frontend's
// verdict cache. It must never engage, at any depth, on any logic.
TEST(IncrementalEngagement, ZeroNeverEngagesAutomatically)
{
  EXPECT_FALSE(readyOnCheck(0, true, 1));
  EXPECT_FALSE(readyOnCheck(0, false, 1));
  EXPECT_FALSE(readyOnCheck(0, true, 100000));
  EXPECT_FALSE(readyOnCheck(0, false, 100000));
}

// The threshold arrives from a signed flag whose validator lives in the CLI,
// so the policy must not turn a stray negative into an enormous unsigned
// comparison. Any negative means "use the default", not "engage at once".
TEST(IncrementalEngagement, NegativeThresholdsAreTheDefaultNotAnUnderflow)
{
  EXPECT_FALSE(readyOnCheck(-7, true, 2));
  EXPECT_TRUE(readyOnCheck(-7, true, 32));
  EXPECT_FALSE(readyOnCheck(-7, false, 2));
  EXPECT_TRUE(readyOnCheck(-7, false, 3));
}

// The forced-first policy. Both frontends computed this identically and
// separately, and four preprocessing policies in the driver key on it: a
// speculative whole-stack block, a skipped constant-bit bootstrap, a
// pure-literal pass over a base-only stack, and the scoped-preprocessing gate.
TEST(IncrementalEngagement, ForcedFirstIsTheFirstCheckOfAForcedSession)
{
  EXPECT_TRUE(IncrementalSolver::forcedFirstSolve(true, 0));
  EXPECT_FALSE(IncrementalSolver::forcedFirstSolve(true, 1));
  EXPECT_FALSE(IncrementalSolver::forcedFirstSolve(true, 99));
}

// A session that never forced the driver has no forced first solve, at any
// ordinal -- including the one the automatic policy engages on. That solve
// HAS had batch-preprocessed predecessors, and the four policies above must
// not reach it; conflating the two is why deriving this from the driver's own
// `engagedSolves == 0` would be wrong.
TEST(IncrementalEngagement, AutomaticEngagementIsNeverAForcedFirstSolve)
{
  EXPECT_FALSE(IncrementalSolver::forcedFirstSolve(false, 0));
  EXPECT_FALSE(IncrementalSolver::forcedFirstSolve(false, 2));
  EXPECT_FALSE(IncrementalSolver::forcedFirstSolve(false, 31));
  // the automatic policy says engage here; the forced policy still says no
  EXPECT_TRUE(IncrementalSolver::automaticEngagementReady(-1, true, 31));
  EXPECT_FALSE(IncrementalSolver::forcedFirstSolve(false, 31));
}

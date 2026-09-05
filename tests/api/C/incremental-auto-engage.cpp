// The C API's automatic-engagement threshold.
//
// The C API used to hard-code "engage the incremental driver from the third
// query" as a literal, consulting nothing. --incremental-auto-engage-at was
// documented as the override for that ordinal and could not reach this path
// at all, so it was inert for every embedder, and the two frontends' copies
// of one policy were free to drift apart. Both now call
// IncrementalSolver::automaticEngagementReady, and INCREMENTAL_AUTO_ENGAGE_AT
// is how a C API client sets it.
//
// The VC handle IS the stp::STP object, and on this path the driver is only
// constructed when a query actually engages it -- so asking whether one
// exists is an honest probe for "did this session engage?".
#include "stp/STPManager/STP.h"
#include "stp/c_interface.h"
#include <gtest/gtest.h>

namespace
{
bool engaged(VC vc)
{
  return ((stp::STP*)vc)->hasIncrementalSolver();
}

// assert (a = 0) and query it, so each call is one real query
int oneQuery(VC vc)
{
  Type bv8 = vc_bvType(vc, 8);
  Expr a = vc_varExpr(vc, "a", bv8);
  Expr zero = vc_bvConstExprFromInt(vc, 8, 0);
  Expr eq = vc_eqExpr(vc, a, zero);
  const int r = vc_query(vc, eq);
  return r;
}
} // namespace

// Default policy: two batch warm-ups, so a two-query session never engages.
TEST(incremental_auto_engage, DefaultKeepsTheFirstTwoQueriesOnBatch)
{
  VC vc = vc_createValidityChecker();
  vc_push(vc);
  ASSERT_FALSE(oneQuery(vc));
  EXPECT_FALSE(engaged(vc));
  ASSERT_FALSE(oneQuery(vc));
  EXPECT_FALSE(engaged(vc));
  // the third is the default ordinal
  ASSERT_FALSE(oneQuery(vc));
  EXPECT_TRUE(engaged(vc));
  vc_pop(vc);
  vc_Destroy(vc);
}

// The override reaches this path. Before it did, a threshold of 1 behaved
// exactly like the default above and this session stayed on batch.
TEST(incremental_auto_engage, ThresholdOfOneEngagesOnTheFirstQuery)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, INCREMENTAL_AUTO_ENGAGE_AT, 1);
  vc_push(vc);
  ASSERT_FALSE(oneQuery(vc));
  EXPECT_TRUE(engaged(vc));
  vc_pop(vc);
  vc_Destroy(vc);
}

// Zero disables automatic engagement, at any depth.
TEST(incremental_auto_engage, ZeroNeverEngages)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, INCREMENTAL_AUTO_ENGAGE_AT, 0);
  vc_push(vc);
  for (int i = 0; i < 6; i++)
    ASSERT_FALSE(oneQuery(vc));
  EXPECT_FALSE(engaged(vc));
  vc_pop(vc);
  vc_Destroy(vc);
}

// Engaging early must not change what the session answers. Same bracket,
// driver from query one against batch throughout, including the model.
TEST(incremental_auto_engage, EarlyEngagementDoesNotChangeAnswersOrModels)
{
  const int thresholds[2] = {0, 1};
  int verdicts[2][3];
  unsigned long long models[2];
  for (int t = 0; t < 2; t++)
  {
    VC vc = vc_createValidityChecker();
    vc_setInterfaceFlags(vc, INCREMENTAL_AUTO_ENGAGE_AT, thresholds[t]);
    Type bv8 = vc_bvType(vc, 8);
    Expr x = vc_varExpr(vc, "x", bv8);
    Expr y = vc_varExpr(vc, "y", bv8);
    vc_assertFormula(vc, vc_bvGtExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 3)));

    vc_push(vc);
    vc_assertFormula(vc, vc_bvLtExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 9)));
    verdicts[t][0] =
        vc_query(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 200)));
    verdicts[t][1] = vc_query(vc, vc_bvLtExpr(vc, x, y));
    vc_pop(vc);

    verdicts[t][2] =
        vc_query(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 0)));
    // the last query was invalid, so a counterexample is available
    Expr cx = vc_getCounterExample(vc, x);
    models[t] = getBVUnsignedLongLong(cx);
    EXPECT_EQ(thresholds[t] == 1, engaged(vc));
    vc_Destroy(vc);
  }
  for (int q = 0; q < 3; q++)
    EXPECT_EQ(verdicts[0][q], verdicts[1][q]) << "query " << q;
  // both models must satisfy the live base constraint x > 3
  EXPECT_GT(models[0], 3u);
  EXPECT_GT(models[1], 3u);
}

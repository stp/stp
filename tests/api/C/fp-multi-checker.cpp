#include <gtest/gtest.h>
#include <stp/c_interface.h>
#include <stp/STPManager/STPManager.h> // for the checker-reuse test
#include <cstdint>
#include <cstdlib>

// Two independent validity checkers, both using floating point, interleaved.
// This used to corrupt the second checker: floating-point blasting bound a
// process-global symfpu backend to the first checker to use it. Each checker
// now blasts into its own manager, so both give correct results.
TEST(fp_multi_checker, two_live_checkers)
{
  VC v1 = vc_createValidityChecker();
  VC v2 = vc_createValidityChecker();

  // v1: a is 2.0 (half); a*a is 4.0.
  Expr a = vc_varExpr(v1, "a", vc_fpType(v1, 5, 11));
  vc_assertFormula(
      v1, vc_fpEqExpr(v1, a,
                      vc_fpConstFromBits(v1, 5, 11,
                                         vc_bvConstExprFromLL(v1, 16, 0x4000))));
  Expr prod = vc_fpMulExpr(v1, vc_fpRoundingMode(v1, VC_RM_RNE), a, a);

  // v2: b is 3.0 (double).
  Expr b = vc_varExpr(v2, "b", vc_fpType(v2, 11, 53));
  vc_assertFormula(
      v2, vc_fpEqExpr(v2, b,
                      vc_fpConstFromBits(
                          v2, 11, 53,
                          vc_bvConstExprFromLL(v2, 64, 0x4008000000000000ULL))));

  ASSERT_EQ(0, vc_query(v1, vc_falseExpr(v1)));
  ASSERT_EQ(0, vc_query(v2, vc_falseExpr(v2)));

  // Read from both, interleaved.
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(v1, a)));
  EXPECT_EQ((unsigned long long)0x4008000000000000ULL,
            getBVUnsignedLongLong(vc_getCounterExample(v2, b)));
  EXPECT_EQ((unsigned long long)0x4400, // 2.0 * 2.0 = 4.0
            getBVUnsignedLongLong(vc_getCounterExample(v1, prod)));
  EXPECT_EQ((unsigned long long)0x4000, // v1 still intact after reading v2
            getBVUnsignedLongLong(vc_getCounterExample(v1, a)));

  vc_Destroy(v1);
  vc_Destroy(v2);
}

// Printing the FIRST checker's counterexample after the SECOND has queried:
// the model-printing path must evaluate against its own manager. (The
// blaster takes the manager explicitly; this pins that no path still leans
// on whichever manager bound last.)
TEST(fp_multi_checker, print_counterexample_across_checkers)
{
  VC v1 = vc_createValidityChecker();
  VC v2 = vc_createValidityChecker();

  Expr a = vc_varExpr(v1, "a", vc_fpType(v1, 5, 11));
  vc_assertFormula(v1, vc_fpEqExpr(v1, a, vc_fpConstFromBits(
                                              v1, 5, 11,
                                              vc_bvConstExprFromLL(v1, 16,
                                                                   0x4000))));
  EXPECT_EQ(0, vc_query(v1, vc_falseExpr(v1)));

  Expr b = vc_varExpr(v2, "b", vc_fpType(v2, 8, 24));
  vc_assertFormula(v2, vc_fpIsNormalExpr(v2, b));
  EXPECT_EQ(0, vc_query(v2, vc_falseExpr(v2))); // v2 queried last

  // Print v1's counterexample into a buffer; it must not touch v2's manager.
  char* buf = NULL;
  unsigned long len = 0;
  vc_printCounterExampleToBuffer(v1, &buf, &len);
  EXPECT_TRUE(buf != NULL);
  EXPECT_TRUE(len > 0);
  free(buf);

  // And v1's values still read correctly.
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(v1, a)));

  vc_Destroy(v1);
  vc_Destroy(v2);
}

// vc_createValidityCheckerReuse solves over nodes built through the C++
// objects' manager, and vc_Destroy still tears the pair down.
TEST(fp_multi_checker, checker_reuse_over_existing_manager)
{
  stp::STPMgr* bm = new stp::STPMgr();
  VC vc = vc_createValidityCheckerReuse(bm);

  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 5, 11));
  vc_assertFormula(vc, vc_fpIsZeroExpr(vc, x));
  vc_assertFormula(vc, vc_fpIsNegativeExpr(vc, x));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)0x8000, // -0.0 in binary16
            getBVUnsignedLongLong(vc_getCounterExample(vc, x)));

  vc_Destroy(vc);
}

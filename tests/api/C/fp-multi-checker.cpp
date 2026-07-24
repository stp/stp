#include <gtest/gtest.h>
#include <stp/c_interface.h>
#include <cstdint>

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

#include <gtest/gtest.h>
#include <stp/c_interface.h>
#include <cstdint>

// Build floating-point arithmetic through the C API and read the results back.
// All values are half precision (eb=5, sb=11): 2.0 is 0x4000, 4.0 is 0x4400 and
// -2.0 is 0xC000.
static Expr half(VC vc, unsigned long long bits)
{
  return vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, bits));
}

TEST(fp_arithmetic, results)
{
  VC vc = vc_createValidityChecker();
  Type f = vc_fpType(vc, 5, 11);
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);

  Expr a = vc_varExpr(vc, "a", f);
  vc_assertFormula(vc, vc_fpEqExpr(vc, a, half(vc, 0x4000))); // a = 2.0

  Expr prod = vc_fpMulExpr(vc, rne, a, a); // 4.0
  Expr sum = vc_fpAddExpr(vc, rne, a, a);  // 4.0
  Expr neg = vc_fpNegExpr(vc, a);          // -2.0

  // A floating-point operation returns a value of the operands' format.
  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(prod));
  EXPECT_EQ(5, vc_getExpWidth(prod));
  EXPECT_EQ(11, vc_getSigWidth(prod));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc))); // satisfiable
  EXPECT_EQ((unsigned long long)0x4400,
            getBVUnsignedLongLong(vc_getCounterExample(vc, prod)));
  EXPECT_EQ((unsigned long long)0x4400,
            getBVUnsignedLongLong(vc_getCounterExample(vc, sum)));
  EXPECT_EQ((unsigned long long)0xC000,
            getBVUnsignedLongLong(vc_getCounterExample(vc, neg)));
  vc_Destroy(vc);
}

TEST(fp_arithmetic, more_ops)
{
  VC vc = vc_createValidityChecker();
  Type f = vc_fpType(vc, 5, 11);
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);

  Expr a = vc_varExpr(vc, "a", f);
  vc_assertFormula(vc, vc_fpEqExpr(vc, a, half(vc, 0x4400))); // a = 4.0
  Expr two = half(vc, 0x4000);                               // 2.0

  Expr rt = vc_fpSqrtExpr(vc, rne, a);   // 2.0
  Expr dv = vc_fpDivExpr(vc, rne, a, two); // 2.0
  Expr mn = vc_fpMinExpr(vc, a, two);    // 2.0
  Expr mx = vc_fpMaxExpr(vc, a, two);    // 4.0

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(vc, rt)));
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(vc, dv)));
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(vc, mn)));
  EXPECT_EQ((unsigned long long)0x4400,
            getBVUnsignedLongLong(vc_getCounterExample(vc, mx)));
  vc_Destroy(vc);
}

// The predicates actually constrain the search: nothing is both NaN and zero,
// so this is unsatisfiable (vc_query of false returns 1 = valid = unsat).
TEST(fp_arithmetic, predicates_constrain)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 5, 11));
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, x));
  vc_assertFormula(vc, vc_fpIsZeroExpr(vc, x));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

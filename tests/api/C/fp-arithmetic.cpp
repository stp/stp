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

// Each source fp.add is rounded before its result feeds the next operation.
// In binary16, 2^-11 is exactly halfway between 1.0 and its successor. RNE
// therefore rounds 1.0 + 2^-11 back to the even 1.0 on both additions. If a
// lowering accidentally carried an unrounded intermediate across the chain,
// the mathematical sum 1.0 + 2^-10 would instead be 0x3C01.
TEST(fp_arithmetic, nested_add_rounds_after_each_operation)
{
  VC vc = vc_createValidityChecker();
  Type f = vc_fpType(vc, 5, 11);
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr x = vc_varExpr(vc, "x", f);
  Expr y = vc_varExpr(vc, "y", f);

  vc_assertFormula(vc, vc_fpEqExpr(vc, x, half(vc, 0x3C00))); // 1.0
  vc_assertFormula(vc, vc_fpEqExpr(vc, y, half(vc, 0x1000))); // 2^-11

  Expr once = vc_fpAddExpr(vc, rne, x, y);
  Expr twice = vc_fpAddExpr(vc, rne, once, y);

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)0x3C00,
            getBVUnsignedLongLong(vc_getCounterExample(vc, once)));
  EXPECT_EQ((unsigned long long)0x3C00,
            getBVUnsignedLongLong(vc_getCounterExample(vc, twice)));
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

TEST(fp_arithmetic, sub_fma_rem_roundtointegral_abs)
{
  VC vc = vc_createValidityChecker();
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr a = vc_varExpr(vc, "a", vc_fpType(vc, 5, 11));
  vc_assertFormula(vc, vc_fpEqExpr(vc, a, half(vc, 0x4400))); // 4.0
  Expr two = half(vc, 0x4000);

  Expr sub = vc_fpSubExpr(vc, rne, a, two);        // 2.0
  Expr fma = vc_fpFMAExpr(vc, rne, a, two, two);   // 4*2 + 2 = 10.0
  Expr rem = vc_fpRemExpr(vc, a, two);             // 0.0
  Expr rti = vc_fpRoundToIntegralExpr(vc, rne, half(vc, 0x4100)); // rti(2.5) = 2.0
  Expr ab = vc_fpAbsExpr(vc, half(vc, 0xC000));    // |-2.0| = 2.0

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(vc, sub)));
  EXPECT_EQ((unsigned long long)0x4900,
            getBVUnsignedLongLong(vc_getCounterExample(vc, fma)));
  EXPECT_EQ((unsigned long long)0x0000,
            getBVUnsignedLongLong(vc_getCounterExample(vc, rem)));
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(vc, rti)));
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(vc, ab)));
  vc_Destroy(vc);
}

TEST(fp_arithmetic, ordered_comparisons)
{
  VC vc = vc_createValidityChecker();
  Expr a = vc_varExpr(vc, "a", vc_fpType(vc, 5, 11));
  vc_assertFormula(vc, vc_fpEqExpr(vc, a, half(vc, 0x4200))); // 3.0
  vc_assertFormula(vc, vc_fpLtExpr(vc, a, half(vc, 0x4400))); // 3 < 4
  vc_assertFormula(vc, vc_fpLeqExpr(vc, a, half(vc, 0x4200))); // 3 <= 3
  vc_assertFormula(vc, vc_fpGtExpr(vc, a, half(vc, 0x4000))); // 3 > 2
  vc_assertFormula(vc, vc_fpGeqExpr(vc, a, half(vc, 0x4200))); // 3 >= 3
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));                // all hold
  vc_Destroy(vc);
}

TEST(fp_arithmetic, ordered_comparison_unsat)
{
  VC vc = vc_createValidityChecker();
  Expr a = vc_varExpr(vc, "a", vc_fpType(vc, 5, 11));
  vc_assertFormula(vc, vc_fpEqExpr(vc, a, half(vc, 0x4000))); // 2.0
  vc_assertFormula(vc, vc_fpGtExpr(vc, a, half(vc, 0x4400))); // 2 > 4
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));               // unsatisfiable
  vc_Destroy(vc);
}

TEST(fp_arithmetic, is_subnormal_and_normal)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 5, 11));
  vc_assertFormula(vc, vc_fpEqExpr(vc, x, half(vc, 0x0001))); // smallest subnormal
  vc_assertFormula(vc, vc_fpIsSubnormalExpr(vc, x));

  Expr y = vc_varExpr(vc, "y", vc_fpType(vc, 5, 11));
  vc_assertFormula(vc, vc_fpEqExpr(vc, y, half(vc, 0x3C00))); // 1.0
  vc_assertFormula(vc, vc_fpIsNormalExpr(vc, y));

  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

// getExprKind must label floating-point nodes correctly: the C enum is a
// numeric mirror of the internal kinds, and FP_TO_IEEE_BV was once missing
// from it, mislabelling every kind from fp.leq onward.
TEST(fp_arithmetic, expr_kinds)
{
  VC vc = vc_createValidityChecker();
  Type f = vc_fpType(vc, 5, 11);
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr x = vc_varExpr(vc, "x", f);
  Expr y = vc_varExpr(vc, "y", f);

  EXPECT_EQ(FP_ADD, getExprKind(vc_fpAddExpr(vc, rne, x, y)));
  // The factory mirrors the less-thans onto the greater-thans (as it does
  // BVLT onto BVGT), so vc_fpLeqExpr hands back an fp.geq node with the
  // operands swapped -- and getExprKind must label that node correctly.
  EXPECT_EQ(FP_GEQ, getExprKind(vc_fpLeqExpr(vc, x, y)));
  EXPECT_EQ(FP_EQ, getExprKind(vc_fpEqExpr(vc, x, y)));
  EXPECT_EQ(FP_ISNAN, getExprKind(vc_fpIsNaNExpr(vc, x)));
  EXPECT_EQ(FP_TO_IEEE_BV, getExprKind(vc_fpToIEEEBV(vc, x)));
  // The special values are packed constants, not operations.
  EXPECT_EQ(BVCONST, getExprKind(vc_fpNaN(vc, f)));
  EXPECT_EQ(BVCONST, getExprKind(vc_fpPlusInfinity(vc, f)));

  vc_Destroy(vc);
}

#include <gtest/gtest.h>
#include <stp/c_interface.h>
#include <cstdint>

// Solve (expecting satisfiable) and read the value of `v`.
static unsigned long long solveRead(VC vc, Expr v)
{
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  return getBVUnsignedLongLong(vc_getCounterExample(vc, v));
}

// The special-value constructors produce values that classify as claimed.
TEST(fp_constants, special_values)
{
  VC vc = vc_createValidityChecker();
  Type f = vc_fpType(vc, 5, 11);
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, vc_fpNaN(vc, f)));
  vc_assertFormula(vc, vc_fpIsInfiniteExpr(vc, vc_fpPlusInfinity(vc, f)));
  vc_assertFormula(vc, vc_fpIsPositiveExpr(vc, vc_fpPlusInfinity(vc, f)));
  vc_assertFormula(vc, vc_fpIsInfiniteExpr(vc, vc_fpMinusInfinity(vc, f)));
  vc_assertFormula(vc, vc_fpIsNegativeExpr(vc, vc_fpMinusInfinity(vc, f)));
  vc_assertFormula(vc, vc_fpIsZeroExpr(vc, vc_fpPlusZero(vc, f)));
  vc_assertFormula(vc, vc_fpIsPositiveExpr(vc, vc_fpPlusZero(vc, f)));
  vc_assertFormula(vc, vc_fpIsNegativeExpr(vc, vc_fpMinusZero(vc, f)));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc))); // all consistent
  vc_Destroy(vc);
}

TEST(fp_constants, plus_infinity_is_not_nan)
{
  VC vc = vc_createValidityChecker();
  Type f = vc_fpType(vc, 5, 11);
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, vc_fpPlusInfinity(vc, f)));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc))); // unsatisfiable
  vc_Destroy(vc);
}

// vc_fpConstFromDouble is exact when the target is binary64 (3.5 is 0x400C...),
// and rounds through fp.to_fp otherwise (2.0 in half precision is 0x4000).
TEST(fp_constants, from_double_exact)
{
  VC vc = vc_createValidityChecker();
  Type dbl = vc_fpType(vc, 11, 53);
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr x = vc_varExpr(vc, "x", dbl);
  vc_assertFormula(vc,
                   vc_fpEqExpr(vc, x, vc_fpConstFromDouble(vc, dbl, rne, 3.5)));
  EXPECT_EQ((unsigned long long)0x400C000000000000ULL, solveRead(vc, x));
  vc_Destroy(vc);
}

TEST(fp_constants, from_double_narrowed)
{
  VC vc = vc_createValidityChecker();
  Type half = vc_fpType(vc, 5, 11);
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr x = vc_varExpr(vc, "x", half);
  vc_assertFormula(vc,
                   vc_fpEqExpr(vc, x, vc_fpConstFromDouble(vc, half, rne, 2.0)));
  EXPECT_EQ((unsigned long long)0x4000, solveRead(vc, x));
  vc_Destroy(vc);
}

// float -> bitvector: fp.to_ubv and fp.to_sbv.
TEST(fp_conversions, to_bitvector)
{
  VC vc = vc_createValidityChecker();
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr two = vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x4000));
  Expr negtwo =
      vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0xC000));

  Expr ubv = vc_varExpr(vc, "ubv", vc_bvType(vc, 8));
  Expr sbv = vc_varExpr(vc, "sbv", vc_bvType(vc, 8));
  vc_assertFormula(vc, vc_eqExpr(vc, ubv, vc_fpToUBVExpr(vc, 8, rne, two)));
  vc_assertFormula(vc, vc_eqExpr(vc, sbv, vc_fpToSBVExpr(vc, 8, rne, negtwo)));

  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)2, getBVUnsignedLongLong(vc_getCounterExample(vc, ubv)));
  EXPECT_EQ((unsigned long long)0xFE,
            getBVUnsignedLongLong(vc_getCounterExample(vc, sbv))); // -2, 8-bit
  vc_Destroy(vc);
}

// bitvector -> float: reinterpret, signed conversion, unsigned conversion.
TEST(fp_conversions, to_float)
{
  VC vc = vc_createValidityChecker();
  Type half = vc_fpType(vc, 5, 11);
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);

  Expr rein = vc_varExpr(vc, "rein", half);
  Expr fromS = vc_varExpr(vc, "fromS", half);
  Expr fromU = vc_varExpr(vc, "fromU", half);
  vc_assertFormula(vc, vc_fpEqExpr(vc, rein,
                                   vc_fpToFPFromIEEEBV(
                                       vc, 5, 11,
                                       vc_bvConstExprFromLL(vc, 16, 0x4000))));
  vc_assertFormula(vc, vc_fpEqExpr(vc, fromS,
                                   vc_fpToFPFromSignedBV(
                                       vc, 5, 11, rne,
                                       vc_bvConstExprFromLL(vc, 8, 3))));
  vc_assertFormula(vc, vc_fpEqExpr(vc, fromU,
                                   vc_fpToFPFromUnsignedBV(
                                       vc, 5, 11, rne,
                                       vc_bvConstExprFromLL(vc, 8, 5))));

  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(vc, rein))); // 2.0
  EXPECT_EQ((unsigned long long)0x4200,
            getBVUnsignedLongLong(vc_getCounterExample(vc, fromS))); // 3.0
  EXPECT_EQ((unsigned long long)0x4500,
            getBVUnsignedLongLong(vc_getCounterExample(vc, fromU))); // 5.0
  vc_Destroy(vc);
}

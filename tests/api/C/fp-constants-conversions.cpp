#include <gtest/gtest.h>
#include <stp/c_interface.h>
#include <cstdint>

// Solve (expecting satisfiable) and read the value of `v`. ASSERT_* needs a
// void function, so guard by hand: reading a counterexample after a failed
// query is a FatalError, which would abort the whole test binary.
static unsigned long long solveRead(VC vc, Expr v)
{
  const int r = vc_query(vc, vc_falseExpr(vc));
  EXPECT_EQ(0, r);
  if (r != 0)
    return (unsigned long long)-1;
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

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
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

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(vc, rein))); // 2.0
  EXPECT_EQ((unsigned long long)0x4200,
            getBVUnsignedLongLong(vc_getCounterExample(vc, fromS))); // 3.0
  EXPECT_EQ((unsigned long long)0x4500,
            getBVUnsignedLongLong(vc_getCounterExample(vc, fromU))); // 5.0
  vc_Destroy(vc);
}

// vc_fpConstFromFloat: a native float into the single format is exact
// (1.5f is 0x3FC00000).
TEST(fp_constants, from_float)
{
  VC vc = vc_createValidityChecker();
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr sv = vc_varExpr(vc, "sv", vc_fpType(vc, 8, 24));
  vc_assertFormula(
      vc, vc_fpEqExpr(vc, sv,
                      vc_fpConstFromFloat(vc, vc_fpType(vc, 8, 24), rne, 1.5f)));
  EXPECT_EQ((unsigned long long)0x3FC00000ULL, solveRead(vc, sv));
  vc_Destroy(vc);
}

// vc_fpToFPFromFP: reformat a double to half precision (3.0 -> 0x4200).
TEST(fp_conversions, reformat_double_to_half)
{
  VC vc = vc_createValidityChecker();
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr d = vc_varExpr(vc, "d", vc_fpType(vc, 11, 53));
  vc_assertFormula(
      vc, vc_fpEqExpr(vc, d,
                      vc_fpConstFromDouble(vc, vc_fpType(vc, 11, 53), rne, 3.0)));
  Expr h = vc_varExpr(vc, "h", vc_fpType(vc, 5, 11));
  vc_assertFormula(vc, vc_fpEqExpr(vc, h, vc_fpToFPFromFP(vc, 5, 11, rne, d)));
  EXPECT_EQ((unsigned long long)0x4200, solveRead(vc, h));
  vc_Destroy(vc);
}

// Every rounding mode end-to-end, distinguished pairwise: fp.to_sbv of 2.5,
// -2.5 and 1.5 gives each mode a unique signature --
//   RNE (2, -2, 2), RNA (3, -3, 2), RTP (3, -2, 2),
//   RTN (2, -3, 1), RTZ (2, -2, 1).
// A wrong encoding in vc_fpRoundingMode (or a mode falling through symfpu's
// dispatch) breaks at least one probe.
TEST(fp_conversions, every_rounding_mode)
{
  const struct
  {
    enum VCRoundingMode mode;
    unsigned long long pos, neg, tie;
  } probes[] = {
      {VC_RM_RNE, 2, 0xFE, 2}, {VC_RM_RNA, 3, 0xFD, 2},
      {VC_RM_RTP, 3, 0xFE, 2}, {VC_RM_RTN, 2, 0xFD, 1},
      {VC_RM_RTZ, 2, 0xFE, 1},
  };

  for (const auto& p : probes)
  {
    VC vc = vc_createValidityChecker();
    Expr rm = vc_fpRoundingMode(vc, p.mode);
    Expr posHalf = vc_fpConstFromBits(vc, 5, 11,
                                      vc_bvConstExprFromLL(vc, 16, 0x4100));
    Expr negHalf = vc_fpConstFromBits(vc, 5, 11,
                                      vc_bvConstExprFromLL(vc, 16, 0xC100));
    Expr tieHalf = vc_fpConstFromBits(vc, 5, 11,
                                      vc_bvConstExprFromLL(vc, 16, 0x3E00));

    Expr a = vc_varExpr(vc, "a", vc_bvType(vc, 8));
    Expr b = vc_varExpr(vc, "b", vc_bvType(vc, 8));
    Expr c = vc_varExpr(vc, "c", vc_bvType(vc, 8));
    vc_assertFormula(vc, vc_eqExpr(vc, a, vc_fpToSBVExpr(vc, 8, rm, posHalf)));
    vc_assertFormula(vc, vc_eqExpr(vc, b, vc_fpToSBVExpr(vc, 8, rm, negHalf)));
    vc_assertFormula(vc, vc_eqExpr(vc, c, vc_fpToSBVExpr(vc, 8, rm, tieHalf)));

    ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
    EXPECT_EQ(p.pos, getBVUnsignedLongLong(vc_getCounterExample(vc, a)));
    EXPECT_EQ(p.neg, getBVUnsignedLongLong(vc_getCounterExample(vc, b)));
    EXPECT_EQ(p.tie, getBVUnsignedLongLong(vc_getCounterExample(vc, c)));
    vc_Destroy(vc);
  }
}

// SMT '=' vs fp.eq: +0 = -0 is false as bits but true as IEEE equality, and
// NaN equals itself as bits but not as IEEE equality.
TEST(fp_constants, eq_vs_smt_eq_semantics)
{
  {
    VC vc = vc_createValidityChecker();
    Type half = vc_fpType(vc, 5, 11);
    // fp.eq(+0, -0) holds.
    vc_assertFormula(
        vc, vc_fpEqExpr(vc, vc_fpPlusZero(vc, half), vc_fpMinusZero(vc, half)));
    // As raw values they differ.
    vc_assertFormula(
        vc, vc_notExpr(vc, vc_eqExpr(vc, vc_fpPlusZero(vc, half),
                                     vc_fpMinusZero(vc, half))));
    // fp.eq(NaN, NaN) does not hold.
    vc_assertFormula(
        vc, vc_notExpr(vc, vc_fpEqExpr(vc, vc_fpNaN(vc, half),
                                       vc_fpNaN(vc, half))));
    EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc))); // all consistent
    vc_Destroy(vc);
  }
}

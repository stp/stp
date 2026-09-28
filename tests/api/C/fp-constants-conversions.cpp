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

TEST(fp_constants, from_bits_rejects_invalid_smt_format)
{
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr bits = vc_bvConstExprFromLL(vc, 5, 0);
        (void)vc_fpConstFromBits(vc, 1, 4, bits);
      },
      "at least 2 exponent and 2 significand bits");
}

// The narrowest formats SMT-LIB allows used to be refused outright, because
// SymFPU's unpack aborted on them. They are fixed in patches/symfpu/ instead,
// so the API now builds and solves at them like any other format. (2, 3) is
// the case that needs both of those patches: the first makes it reachable at
// all, and doing so gives it an unpacked exponent width equal to its
// significand width, which is exactly the family the second one fixes.
TEST(fp_constants, from_bits_at_the_narrowest_formats)
{
  for (int sb = 2; sb <= 4; sb++)
    for (int eb = 2; eb <= 4; eb++)
    {
      VC vc = vc_createValidityChecker();
      // The all-ones exponent with a zero significand is an infinity at every
      // format, so the bits say what the value must classify as.
      Expr bits = vc_bvConstExprFromLL(vc, eb + sb,
                                       ((1ULL << eb) - 1) << (sb - 1));
      Expr x = vc_fpConstFromBits(vc, eb, sb, bits);
      vc_assertFormula(vc, vc_fpIsInfiniteExpr(vc, x));
      vc_assertFormula(vc, vc_fpIsPositiveExpr(vc, x));
      EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)))
          << "format (" << eb << ", " << sb << ")";
      vc_Destroy(vc);
    }
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
TEST(fp_constants, native_exact_conversion_checks_rounding_mode_sort)
{
  // Exact native-format conversions do not use the rounding mode
  // numerically, but it is still a required, source-sorted API operand.
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Type binary64 = vc_fpType(vc, 11, 53);
        Expr bv5 = vc_bvConstExprFromInt(vc, 5, 0);
        (void)vc_fpConstFromDouble(vc, binary64, bv5, 1.0);
      },
      "expected a rounding mode");

  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Type binary32 = vc_fpType(vc, 8, 24);
        Expr bv5 = vc_bvConstExprFromInt(vc, 5, 0);
        (void)vc_fpConstFromFloat(vc, binary32, bv5, 1.0f);
      },
      "expected a rounding mode");
}

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

// SMT '=' vs fp.eq: '=' keeps +0 and -0 distinct where fp.eq identifies
// them, and fp.eq(NaN, NaN) is false where '=' (which identifies every NaN
// with every NaN) holds.
TEST(fp_constants, eq_vs_smt_eq_semantics)
{
  VC vc = vc_createValidityChecker();
  Type half = vc_fpType(vc, 5, 11);
  // fp.eq(+0, -0) holds.
  vc_assertFormula(
      vc, vc_fpEqExpr(vc, vc_fpPlusZero(vc, half), vc_fpMinusZero(vc, half)));
  // As SMT '=' they differ.
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

// vc_simplify is another entrance to the source-level FP graph.  The partial
// operations are built at their public arity and acquire their internal
// unspecified-value child only when FpTotalise runs.  In particular, neither
// the zero tie of min/max nor an undefined float-to-BV conversion may reach the
// constant evaluator at its raw arity.
TEST(fp_simplify, totalises_partial_operations)
{
  VC vc = vc_createValidityChecker();
  Type half = vc_fpType(vc, 5, 11);
  Expr plus_zero = vc_fpPlusZero(vc, half);
  Expr minus_zero = vc_fpMinusZero(vc, half);

  Expr minimum = vc_simplify(vc, vc_fpMinExpr(vc, plus_zero, minus_zero));
  Expr maximum = vc_simplify(vc, vc_fpMaxExpr(vc, plus_zero, minus_zero));
  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(minimum));
  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(maximum));
  EXPECT_EQ(5, vc_getExpWidth(minimum));
  EXPECT_EQ(11, vc_getSigWidth(minimum));

  // Each result must be one of the two zero values, while SMT-LIB leaves the
  // choice between them unspecified.
  Expr min_is_zero =
      vc_orExpr(vc, vc_eqExpr(vc, minimum, plus_zero),
                vc_eqExpr(vc, minimum, minus_zero));
  vc_assertFormula(vc, vc_notExpr(vc, min_is_zero));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));

  // Use a fresh context for max: the previous context is intentionally
  // inconsistent.
  vc_Destroy(vc);
  vc = vc_createValidityChecker();
  half = vc_fpType(vc, 5, 11);
  plus_zero = vc_fpPlusZero(vc, half);
  minus_zero = vc_fpMinusZero(vc, half);
  maximum = vc_simplify(vc, vc_fpMaxExpr(vc, plus_zero, minus_zero));
  Expr max_is_zero = vc_orExpr(vc, vc_eqExpr(vc, maximum, plus_zero),
                               vc_eqExpr(vc, maximum, minus_zero));
  vc_assertFormula(vc, vc_notExpr(vc, max_is_zero));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));

  // Both undefined conversion forms must also remain usable after simplify.
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr nan = vc_fpNaN(vc, half);
  Expr ubv = vc_simplify(vc, vc_fpToUBVExpr(vc, 8, rne, nan));
  Expr sbv = vc_simplify(vc, vc_fpToSBVExpr(vc, 8, rne, nan));
  EXPECT_EQ(BITVECTOR_TYPE, getType(ubv));
  EXPECT_EQ(BITVECTOR_TYPE, getType(sbv));
  EXPECT_EQ(8, vc_getBVLength(vc, ubv));
  EXPECT_EQ(8, vc_getBVLength(vc, sbv));
  vc_Destroy(vc);
}

TEST(fp_simplify, preserves_defined_conversion_semantics)
{
  VC vc = vc_createValidityChecker();
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr two = vc_fpConstFromBits(
      vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x4000));
  Expr converted = vc_simplify(vc, vc_fpToUBVExpr(vc, 8, rne, two));

  vc_assertFormula(
      vc, vc_notExpr(vc, vc_eqExpr(vc, converted,
                                   vc_bvConstExprFromLL(vc, 8, 2))));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

TEST(fp_sort_checks, release_api_rejects_mixed_formats)
{
  // These formats have the same 32-bit packed carrier.  Width-only checks
  // therefore cannot distinguish them; the public source sorts must.
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 8, 24));
        Expr y = vc_varExpr(vc, "y", vc_fpType(vc, 11, 21));
        Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
        (void)vc_fpAddExpr(vc, rne, x, y);
      },
      "requires operands of the same sort");

  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 8, 24));
        Expr y = vc_varExpr(vc, "y", vc_fpType(vc, 11, 21));
        (void)vc_fpLtExpr(vc, x, y);
      },
      "requires operands of the same sort");

  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 8, 24));
        Expr y = vc_varExpr(vc, "y", vc_fpType(vc, 11, 21));
        (void)vc_fpEqExpr(vc, x, y);
      },
      "requires operands of the same sort");
}

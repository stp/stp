#include <gtest/gtest.h>
#include <stp/c_interface.h>
#include <cstdint>

// vc_fpToIEEEBV reinterprets a float as its packed bits, so the exponent and
// significand fields can be pulled out with vc_bvExtract. Half precision: 3.0
// is 0x4200 (sign 0, exponent 0b10000 = 16, significand 0x200).
TEST(fp_to_ieee_bv, extract_fields)
{
  VC vc = vc_createValidityChecker();
  const int eb = 5, sb = 11;
  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, eb, sb));
  vc_assertFormula(
      vc, vc_fpEqExpr(vc, x,
                      vc_fpConstFromBits(vc, eb, sb,
                                         vc_bvConstExprFromLL(vc, 16, 0x4200))));

  Expr bits = vc_fpToIEEEBV(vc, x);
  Expr expo = vc_bvExtract(vc, bits, sb + eb - 2, sb - 1); // exponent
  Expr sig = vc_bvExtract(vc, bits, sb - 2, 0);            // significand

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)0x4200,
            getBVUnsignedLongLong(vc_getCounterExample(vc, bits)));
  EXPECT_EQ((unsigned)16, getBVUnsigned(vc_getCounterExample(vc, expo)));
  EXPECT_EQ((unsigned)0x200, getBVUnsigned(vc_getCounterExample(vc, sig)));
  vc_Destroy(vc);
}

// The extracted field is a real symbolic bitvector: constraining a float's
// exponent to all-ones while asserting it is zero is unsatisfiable.
TEST(fp_to_ieee_bv, exponent_constrains_classification)
{
  VC vc = vc_createValidityChecker();
  const int eb = 5, sb = 11;
  Expr y = vc_varExpr(vc, "y", vc_fpType(vc, eb, sb));
  Expr expo = vc_bvExtract(vc, vc_fpToIEEEBV(vc, y), sb + eb - 2, sb - 1);
  vc_assertFormula(vc, vc_eqExpr(vc, expo, vc_bvConstExprFromLL(vc, eb, 0x1F)));
  vc_assertFormula(vc, vc_fpIsZeroExpr(vc, y));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc))); // unsatisfiable
  vc_Destroy(vc);
}

TEST(fp_to_ieee_bv, bitvector_operator_rejects_float_without_conversion)
{
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 8, 24));
        (void)vc_bvNotExpr(vc, x);
      },
      "requires bitvector operands");
}

TEST(fp_to_ieee_bv, ite_rejects_float_and_bitvector_branches)
{
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 8, 24));
        Expr bits = vc_bvConstExprFromLL(vc, 32, 0);
        (void)vc_iteExpr(vc, vc_trueExpr(vc), x, bits);
      },
      "requires operands of the same sort");
}

TEST(fp_to_ieee_bv, equality_rejects_float_and_bitvector_operands)
{
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 8, 24));
        Expr bits = vc_bvConstExprFromLL(vc, 32, 0);
        (void)vc_eqExpr(vc, x, bits);
      },
      "requires operands of the same sort");
}

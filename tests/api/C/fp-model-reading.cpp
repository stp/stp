#include <gtest/gtest.h>
#include <stp/c_interface.h>
#include <cstdint>

// Build a floating-point problem through the public C API, solve it, and read
// the model back. Exercises vc_fpType, vc_varExpr on a floating-point type,
// vc_fpConstFromBits, vc_fpEqExpr, the vc_getExpWidth/vc_getSigWidth format
// accessors, and reading a floating-point value out of a counterexample.

// (eb=3, sb=5): an 8-bit format that still has zeros, subnormals, normals,
// infinities and NaNs. 1.0 packs as 0b0 011 0000 = 0x30.
TEST(fp_model_reading, small_format)
{
  VC vc = vc_createValidityChecker();

  Type f = vc_fpType(vc, 3, 5);
  Expr x = vc_varExpr(vc, "x", f);

  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(x));
  EXPECT_EQ(3, vc_getExpWidth(x));
  EXPECT_EQ(5, vc_getSigWidth(x));

  // The accessors are documented to work on the type itself as well.
  EXPECT_EQ(3, vc_getExpWidth(f));
  EXPECT_EQ(5, vc_getSigWidth(f));

  Expr one =
      vc_fpConstFromBits(vc, 3, 5, vc_bvConstExprFromLL(vc, 8, 0x30ULL));
  EXPECT_EQ(3, vc_getExpWidth(one));
  EXPECT_EQ(5, vc_getSigWidth(one));

  vc_assertFormula(vc, vc_fpEqExpr(vc, x, one)); // x == 1.0
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));  // 0 => satisfiable

  Expr xval = vc_getCounterExample(vc, x);
  EXPECT_EQ((unsigned long long)0x30, getBVUnsignedLongLong(xval));

  vc_Destroy(vc);
}

// IEEE double (eb=11, sb=53): the packed value is a full 64 bits, so this also
// checks that reading a value at the width ceiling of getBVUnsignedLongLong
// works. 1.0 packs as 0x3FF0000000000000.
TEST(fp_model_reading, double_format)
{
  VC vc = vc_createValidityChecker();

  Type f = vc_fpType(vc, 11, 53);
  Expr x = vc_varExpr(vc, "x", f);

  EXPECT_EQ(11, vc_getExpWidth(x));
  EXPECT_EQ(53, vc_getSigWidth(x));

  Expr one = vc_fpConstFromBits(
      vc, 11, 53, vc_bvConstExprFromLL(vc, 64, 0x3FF0000000000000ULL));

  vc_assertFormula(vc, vc_fpEqExpr(vc, x, one)); // x == 1.0
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  Expr xval = vc_getCounterExample(vc, x);
  EXPECT_EQ((unsigned long long)0x3FF0000000000000ULL,
            getBVUnsignedLongLong(xval));

  vc_Destroy(vc);
}

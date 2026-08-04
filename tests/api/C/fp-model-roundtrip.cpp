#include <gtest/gtest.h>
#include <stp/c_interface.h>

// Regression tests: a model value must be a value *of the sort of the term
// it was read from*, so that feeding it straight back -- asserting
// (= term value) and re-solving -- is a well-sorted problem STP can answer.
//
// Model evaluation works in plain bitvector constants throughout, and the
// floating-point format used to be dropped on the way back out through
// vc_getCounterExample.  The caller then built a float/bitvector mix out of
// STP's own model:
//
//   Fatal Error: rhs of <fp> is not an fp
//
// or, where the type check does not run first, reached symfpu with the
// format's zero widths and asked for a zero-width exponent constant:
//
//   Fatal Error: CreateBVConst: trying to create bvconst using unsigned long
//   long of width: 0
//
// Either way STP aborted rather than re-check its own model.
//
// Found by fuzzing with murxla using -C, which re-asserts every reported
// model value and re-solves; delta-minimized.

// The fuzzer's case: fp.abs of a Float128 conversion from a signed
// bitvector, under a symbolic rounding mode.
TEST(fp_model_roundtrip, float128_abs_of_to_fp_from_signed_bv)
{
  VC vc = vc_createValidityChecker();

  Expr bv = vc_varExpr(vc, "x0", vc_bvType(vc, 15));
  Expr rm = vc_fpRoundingModeVar(vc, "x1");
  // (_ FloatingPoint 15 113)
  Expr t = vc_fpAbsExpr(vc, vc_fpToFPFromSignedBV(vc, 15, 113, rm, bv));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc))); // 0 => satisfiable

  Expr v = vc_getCounterExample(vc, t);
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(v));
  EXPECT_EQ(15, vc_getExpWidth(v));
  EXPECT_EQ(113, vc_getSigWidth(v));

  // Re-asserting STP's own value stays satisfiable...
  vc_assertFormula(vc, vc_eqExpr(vc, t, v));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  // ...and now pins the term to it.
  ASSERT_EQ(1, vc_query(vc, vc_eqExpr(vc, t, v)));

  vc_Destroy(vc);
}

// The same for the value of a plain floating-point variable, in a format
// small enough to compare bit-for-bit.
TEST(fp_model_roundtrip, float_variable)
{
  VC vc = vc_createValidityChecker();

  Type f = vc_fpType(vc, 5, 11);
  Expr x = vc_varExpr(vc, "x", f);
  Expr y = vc_varExpr(vc, "y", f);

  // 1.0 packs as 0x3C00 in binary16; y is x + 1.0 under RNE.
  Expr one =
      vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x3C00ULL));
  vc_assertFormula(vc, vc_eqExpr(vc, x, one));
  vc_assertFormula(
      vc,
      vc_eqExpr(vc, y,
                vc_fpAddExpr(vc, vc_fpRoundingMode(vc, VC_RM_RNE), x, one)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  Expr vy = vc_getCounterExample(vc, y);
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(vy));
  EXPECT_EQ(5, vc_getExpWidth(vy));
  EXPECT_EQ(11, vc_getSigWidth(vy));
  // 1.0 + 1.0 is exactly 2.0, which packs as 0x4000.
  EXPECT_EQ((unsigned long long)0x4000ULL, getBVUnsignedLongLong(vy));

  vc_assertFormula(vc, vc_eqExpr(vc, y, vy));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// NaN is the interesting value to feed back: the constant is canonicalised
// as it is built, so the value handed out need not have the model's bits --
// but '=' over floats holds between any two NaNs, so it still pins the term.
TEST(fp_model_roundtrip, nan_value)
{
  VC vc = vc_createValidityChecker();

  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 8, 24));
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, x));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  Expr v = vc_getCounterExample(vc, x);
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(v));
  EXPECT_EQ(8, vc_getExpWidth(v));
  EXPECT_EQ(24, vc_getSigWidth(v));

  vc_assertFormula(vc, vc_eqExpr(vc, x, v));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  ASSERT_EQ(1, vc_query(vc, vc_fpIsNaNExpr(vc, x)));

  vc_Destroy(vc);
}

// The whole-array model has the same obligation on both halves of every
// entry: the index must be usable as an index of that array, and the value
// must be equatable with the read.
TEST(fp_model_roundtrip, array_model_entries)
{
  VC vc = vc_createValidityChecker();

  Type f = vc_fpType(vc, 5, 11);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, f, f));
  Expr i = vc_varExpr(vc, "i", f);
  Expr one =
      vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x3C00ULL));

  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i), one));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  Expr* indices = NULL;
  Expr* values = NULL;
  int size = 0;
  vc_getCounterExampleArray(vc, a, &indices, &values, &size);
  ASSERT_EQ(1, size);

  // Both come back at the array's declared sorts. (Asserted, not expected:
  // vc_readExpr below refuses an index that is not one, and takes the
  // process down with it.)
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(indices[0]));
  EXPECT_EQ(5, vc_getExpWidth(indices[0]));
  EXPECT_EQ(11, vc_getSigWidth(indices[0]));
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(values[0]));
  EXPECT_EQ((unsigned long long)0x3C00ULL, getBVUnsignedLongLong(values[0]));

  // So the entry can be read back as an array access and re-asserted.
  Expr cell = vc_readExpr(vc, a, indices[0]);
  vc_assertFormula(vc, vc_eqExpr(vc, cell, values[0]));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_deleteCounterExampleArray(indices, values, size);
  vc_Destroy(vc);
}

// The whole-counterexample snapshot reads out of the raw model map rather
// than evaluating anything, so it re-stamps the format on its own way out.
TEST(fp_model_roundtrip, whole_counterexample_snapshot)
{
  VC vc = vc_createValidityChecker();

  Type f = vc_fpType(vc, 5, 11);
  Expr x = vc_varExpr(vc, "x", f);
  // 'unused' never reaches the solver, so the model does not record it and
  // the snapshot invents a value: +0.0, a float like any other.
  Expr unused = vc_varExpr(vc, "unused", f);
  Expr one =
      vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x3C00ULL));

  vc_assertFormula(vc, vc_eqExpr(vc, x, one));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  WholeCounterExample cc = vc_getWholeCounterExample(vc);

  Expr vx = vc_getTermFromCounterExample(vc, x, cc);
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(vx));
  EXPECT_EQ(5, vc_getExpWidth(vx));
  EXPECT_EQ(11, vc_getSigWidth(vx));
  EXPECT_EQ((unsigned long long)0x3C00ULL, getBVUnsignedLongLong(vx));

  Expr vu = vc_getTermFromCounterExample(vc, unused, cc);
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(vu));
  EXPECT_EQ(5, vc_getExpWidth(vu));
  EXPECT_EQ(11, vc_getSigWidth(vu));

  vc_deleteWholeCounterExample(cc);

  // Both are usable as values of their sort.
  vc_assertFormula(vc, vc_eqExpr(vc, x, vx));
  vc_assertFormula(vc, vc_eqExpr(vc, unused, vu));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// Partial operations introduce solve-local choices. Model evaluation must
// follow the exact totalisation used by that solve, and a later solve must
// replace (rather than retain) the old encoding/model context.
TEST(fp_model_roundtrip, partial_choice_uses_current_solve_encoding)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'd', 0); // construct and validate each counterexample

  Type f = vc_fpType(vc, 5, 11);
  Expr plus_zero = vc_fpPlusZero(vc, f);
  Expr minus_zero = vc_fpMinusZero(vc, f);
  Expr minimum = vc_fpMinExpr(vc, plus_zero, minus_zero);

  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, minimum, plus_zero));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  Expr first = vc_getCounterExample(vc, minimum);
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(first));
  EXPECT_EQ(0ULL, getBVUnsignedLongLong(first));
  vc_pop(vc);

  vc_push(vc); // clears the previous model and its encoding context
  vc_assertFormula(vc, vc_eqExpr(vc, minimum, minus_zero));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  Expr second = vc_getCounterExample(vc, minimum);
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(second));
  EXPECT_EQ(0x8000ULL, getBVUnsignedLongLong(second));
  vc_pop(vc);

  vc_Destroy(vc);
}

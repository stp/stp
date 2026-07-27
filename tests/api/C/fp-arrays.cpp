#include <gtest/gtest.h>
#include <stp/c_interface.h>
#include <cstdint>

// Arrays with floating-point and RoundingMode index and element sorts,
// built through the public C API: vc_arrayType over vc_fpType /
// vc_fpRoundingModeType, vc_varExpr on such array types, vc_readExpr /
// vc_writeExpr over them, and reading array models back.
//
// The semantic corners pinned here mirror SMT-LIB's (Array X Y) over those
// sorts: array indexes are compared by the index sort's '=', so for a
// float-indexed array every NaN addresses the one NaN cell (whatever its
// payload or sign bit) while +0 and -0 address distinct cells; and a read
// from a RoundingMode-element array always denotes one of the five modes.

// 1.0 in binary32 packs as 0x3F800000, 2.0 as 0x40000000.
static Expr float32(VC vc, uint64_t bits)
{
  return vc_fpConstFromBits(vc, 8, 24, vc_bvConstExprFromLL(vc, 32, bits));
}

TEST(fp_arrays, float_element_store_read)
{
  VC vc = vc_createValidityChecker();

  Type arrayType = vc_arrayType(vc, vc_bvType(vc, 2), vc_fpType(vc, 8, 24));
  Expr a = vc_varExpr(vc, "a", arrayType);

  // A read carries the element's floating-point sort.
  Expr read = vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 2, 0));
  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(read));
  EXPECT_EQ(8, vc_getExpWidth(read));
  EXPECT_EQ(24, vc_getSigWidth(read));

  // Store 1.0 and read it back: valid, whatever the rest of the array is.
  Expr one = float32(vc, 0x3F800000ULL);
  Expr idx = vc_bvConstExprFromInt(vc, 2, 1);
  Expr stored = vc_writeExpr(vc, a, idx, one);
  Expr back = vc_readExpr(vc, stored, idx);
  ASSERT_EQ(1, vc_query(vc, vc_eqExpr(vc, back, one)));

  vc_Destroy(vc);
}

TEST(fp_arrays, float_element_arithmetic_and_model)
{
  VC vc = vc_createValidityChecker();

  Type arrayType = vc_arrayType(vc, vc_bvType(vc, 2), vc_fpType(vc, 8, 24));
  Expr a = vc_varExpr(vc, "a", arrayType);

  Expr idx = vc_bvConstExprFromInt(vc, 2, 3);
  Expr read = vc_readExpr(vc, a, idx);

  // '=' pins the cell to exactly 1.0 (a non-NaN float has one bit
  // pattern); the addition uses the read as a float like any other, and is
  // consistent with it (1.0 + 1.0 is exactly 2.0 under RNE).
  vc_assertFormula(vc, vc_eqExpr(vc, read, float32(vc, 0x3F800000ULL)));
  Expr sum = vc_fpAddExpr(vc, vc_fpRoundingMode(vc, VC_RM_RNE),
                          float32(vc, 0x3F800000ULL), read);
  vc_assertFormula(vc, vc_eqExpr(vc, sum, float32(vc, 0x40000000ULL)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  Expr cell = vc_getCounterExample(vc, read);
  EXPECT_EQ((unsigned long long)0x3F800000ULL, getBVUnsignedLongLong(cell));

  // The whole-array model contains that cell, as a float of the element's
  // format at the read's index.
  Expr* indices = NULL;
  Expr* values = NULL;
  int size = 0;
  vc_getCounterExampleArray(vc, a, &indices, &values, &size);
  ASSERT_EQ(1, size);
  EXPECT_EQ((unsigned long long)3, getBVUnsignedLongLong(indices[0]));
  EXPECT_EQ((unsigned long long)0x3F800000ULL,
            getBVUnsignedLongLong(values[0]));

  vc_Destroy(vc);
}

TEST(fp_arrays, float_index_nan_payloads_share_one_cell)
{
  VC vc = vc_createValidityChecker();

  Type arrayType = vc_arrayType(vc, vc_fpType(vc, 8, 24), vc_bvType(vc, 8));
  Expr a = vc_varExpr(vc, "a", arrayType);

  // Two NaNs with different payloads and signs: the same abstract value,
  // so a store at one is read back at the other.
  Expr nan1 = float32(vc, 0x7F800001ULL);
  Expr nan2 = float32(vc, 0xFFC00F00ULL);
  Expr stored = vc_writeExpr(vc, a, nan1, vc_bvConstExprFromInt(vc, 8, 0x2A));
  Expr back = vc_readExpr(vc, stored, nan2);
  ASSERT_EQ(1,
            vc_query(vc, vc_eqExpr(vc, back,
                                   vc_bvConstExprFromInt(vc, 8, 0x2A))));

  vc_Destroy(vc);
}

TEST(fp_arrays, float_index_zeros_are_distinct_cells)
{
  VC vc = vc_createValidityChecker();

  Type arrayType = vc_arrayType(vc, vc_fpType(vc, 8, 24), vc_bvType(vc, 8));
  Expr a = vc_varExpr(vc, "a", arrayType);

  Expr plus_zero = float32(vc, 0x00000000ULL);
  Expr minus_zero = float32(vc, 0x80000000ULL);

  // Store 1 at +0, then 2 at -0: the second store does not shadow the
  // first, because the cells differ.
  Expr stored = vc_writeExpr(vc, a, plus_zero, vc_bvConstExprFromInt(vc, 8, 1));
  stored = vc_writeExpr(vc, stored, minus_zero, vc_bvConstExprFromInt(vc, 8, 2));

  ASSERT_EQ(1, vc_query(vc, vc_eqExpr(vc, vc_readExpr(vc, stored, plus_zero),
                                      vc_bvConstExprFromInt(vc, 8, 1))));
  ASSERT_EQ(1, vc_query(vc, vc_eqExpr(vc, vc_readExpr(vc, stored, minus_zero),
                                      vc_bvConstExprFromInt(vc, 8, 2))));

  vc_Destroy(vc);
}

TEST(fp_arrays, float_index_symbolic_congruence)
{
  VC vc = vc_createValidityChecker();

  Type arrayType = vc_arrayType(vc, vc_fpType(vc, 8, 24), vc_bvType(vc, 8));
  Expr a = vc_varExpr(vc, "a", arrayType);

  Type f = vc_fpType(vc, 8, 24);
  Expr x = vc_varExpr(vc, "x", f);
  Expr y = vc_varExpr(vc, "y", f);

  // Both NaN -- possibly under different bit patterns -- still means one
  // index value, so the reads agree.
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, x));
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, y));
  ASSERT_EQ(1, vc_query(vc, vc_eqExpr(vc, vc_readExpr(vc, a, x),
                                      vc_readExpr(vc, a, y))));

  vc_Destroy(vc);
}

TEST(fp_arrays, float_index_float_element_combined)
{
  VC vc = vc_createValidityChecker();

  Type f = vc_fpType(vc, 5, 11);
  Type arrayType = vc_arrayType(vc, f, f);
  Expr a = vc_varExpr(vc, "a", arrayType);

  // '=' on the float indexes (all NaNs one cell) and '=' on the float
  // elements (the read returns the stored float) in one query.
  Expr nan1 =
      vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x7C01ULL));
  Expr nan2 =
      vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0xFE00ULL));
  Expr v = vc_varExpr(vc, "v", f);

  Expr stored = vc_writeExpr(vc, a, nan1, v);
  Expr back = vc_readExpr(vc, stored, nan2);
  ASSERT_EQ(1, vc_query(vc, vc_eqExpr(vc, back, v)));

  vc_Destroy(vc);
}

TEST(fp_arrays, roundingmode_element_reads_are_modes)
{
  VC vc = vc_createValidityChecker();

  Type arrayType =
      vc_arrayType(vc, vc_bvType(vc, 2), vc_fpRoundingModeType(vc));
  Expr a = vc_varExpr(vc, "a", arrayType);
  Expr i = vc_varExpr(vc, "i", vc_bvType(vc, 2));

  // Whatever the array and index are, the read denotes one of the five
  // modes -- the 27 junk patterns of the 5-bit carrier are not values of
  // the sort.
  Expr read = vc_readExpr(vc, a, i);
  const VCRoundingMode modes[5] = {VC_RM_RNE, VC_RM_RTP, VC_RM_RTN, VC_RM_RTZ,
                                   VC_RM_RNA};
  Expr one_of[5];
  for (int m = 0; m < 5; m++)
    one_of[m] = vc_eqExpr(vc, read, vc_fpRoundingMode(vc, modes[m]));
  ASSERT_EQ(1, vc_query(vc, vc_orExprN(vc, one_of, 5)));

  vc_Destroy(vc);
}

TEST(fp_arrays, roundingmode_element_store_read_use)
{
  VC vc = vc_createValidityChecker();

  Type arrayType =
      vc_arrayType(vc, vc_bvType(vc, 2), vc_fpRoundingModeType(vc));
  Expr a = vc_varExpr(vc, "a", arrayType);

  Expr idx = vc_bvConstExprFromInt(vc, 2, 1);
  Expr stored =
      vc_writeExpr(vc, a, idx, vc_fpRoundingMode(vc, VC_RM_RTZ));
  Expr back = vc_readExpr(vc, stored, idx);
  ASSERT_EQ(1, vc_query(vc, vc_eqExpr(vc, back,
                                      vc_fpRoundingMode(vc, VC_RM_RTZ))));

  // The read is a rounding mode like any other: it can steer an operation.
  // Under any mode, 1.0 + 1.0 is exactly 2.0.
  Expr sum = vc_fpAddExpr(vc, back, float32(vc, 0x3F800000ULL),
                          float32(vc, 0x3F800000ULL));
  ASSERT_EQ(1, vc_query(vc, vc_eqExpr(vc, sum, float32(vc, 0x40000000ULL))));

  vc_Destroy(vc);
}

TEST(fp_arrays, roundingmode_element_model_value)
{
  VC vc = vc_createValidityChecker();

  Type arrayType =
      vc_arrayType(vc, vc_bvType(vc, 2), vc_fpRoundingModeType(vc));
  Expr a = vc_varExpr(vc, "a", arrayType);

  Expr read = vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 2, 2));
  vc_assertFormula(
      vc, vc_eqExpr(vc, read, vc_fpRoundingMode(vc, VC_RM_RTZ)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // The model value is the VCRoundingMode encoding, as for a RoundingMode
  // variable.
  Expr cell = vc_getCounterExample(vc, read);
  EXPECT_EQ((unsigned long long)VC_RM_RTZ, getBVUnsignedLongLong(cell));

  vc_Destroy(vc);
}

TEST(fp_arrays, roundingmode_index)
{
  VC vc = vc_createValidityChecker();

  Type arrayType =
      vc_arrayType(vc, vc_fpRoundingModeType(vc), vc_bvType(vc, 8));
  Expr a = vc_varExpr(vc, "a", arrayType);

  Expr stored = vc_writeExpr(vc, a, vc_fpRoundingMode(vc, VC_RM_RNE),
                             vc_bvConstExprFromInt(vc, 8, 0x11));

  // The RNE cell holds what was stored there...
  ASSERT_EQ(1, vc_query(vc, vc_eqExpr(
                                vc, vc_readExpr(vc, stored,
                                                vc_fpRoundingMode(vc, VC_RM_RNE)),
                                vc_bvConstExprFromInt(vc, 8, 0x11))));
  // ...while the RTZ cell is untouched by that store, so nothing forces its
  // value.
  ASSERT_EQ(0, vc_query(vc, vc_eqExpr(
                                vc, vc_readExpr(vc, stored,
                                                vc_fpRoundingMode(vc, VC_RM_RTZ)),
                                vc_bvConstExprFromInt(vc, 8, 0x11))));

  // A RoundingMode variable serves as an index too.
  Expr r = vc_fpRoundingModeVar(vc, "r");
  Expr read = vc_readExpr(vc, stored, r);
  vc_assertFormula(vc, vc_eqExpr(vc, r, vc_fpRoundingMode(vc, VC_RM_RNE)));
  ASSERT_EQ(1, vc_query(vc, vc_eqExpr(vc, read,
                                      vc_bvConstExprFromInt(vc, 8, 0x11))));

  vc_Destroy(vc);
}

TEST(fp_arrays, type_round_trip)
{
  VC vc = vc_createValidityChecker();

  Type arrayType =
      vc_arrayType(vc, vc_fpType(vc, 8, 24), vc_fpRoundingModeType(vc));
  Expr a = vc_varExpr(vc, "a", arrayType);
  EXPECT_EQ(ARRAY_TYPE, getType(a));

  // vc_getType rebuilds the declared index and element sorts, not their
  // bitvector carriers: a fresh variable of the returned type behaves like
  // the original -- its reads take float indexes and denote rounding modes.
  Type again = vc_getType(vc, a);
  Expr b = vc_varExpr(vc, "b", again);

  Expr read = vc_readExpr(vc, b, float32(vc, 0x3F800000ULL));
  const VCRoundingMode modes[5] = {VC_RM_RNE, VC_RM_RTP, VC_RM_RTN, VC_RM_RTZ,
                                   VC_RM_RNA};
  Expr one_of[5];
  for (int m = 0; m < 5; m++)
    one_of[m] = vc_eqExpr(vc, read, vc_fpRoundingMode(vc, modes[m]));
  ASSERT_EQ(1, vc_query(vc, vc_orExprN(vc, one_of, 5)));

  vc_Destroy(vc);
}

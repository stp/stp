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

// Regression test: evaluating a floating-point operation over a
// float-element array read that the solve never constrained.  Model
// evaluation resolves the operation's float operands and rebuilds it,
// but an out-of-model read used to come back as the symbolic READ
// rather than a constant.  Rebuilding over it mostly "worked" -- the
// blaster embeds a read like any term -- until an identity fold saw
// through the rebuild: here idx evaluates to -1.0, so idx*idx is
// exactly 1.0, and rebuilding (fp.mul rm 1.0 rd) folds to rd, the bare
// READ, which went to the float blaster as the whole term:
//   Fatal Error: FloatBlaster::BlastNode: unhandled kind: (READ ...)
// An out-of-model float operand must resolve to a concrete constant,
// as bit-vector operands already did.  The value itself is
// unconstrained, so only its shape and stability are checked.
//
// Found by fuzzing with murxla driving the C API; delta-minimized.
TEST(fp_arrays, float_element_read_as_operand_of_evaluated_term)
{
  VC vc = vc_createValidityChecker();

  Type fp = vc_fpType(vc, 5, 11);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, fp, fp));
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr rm = vc_fpRoundingModeVar(vc, "rm");
  Expr idx = vc_fpToFPFromSignedBV(vc, 5, 11, rm,
                                   vc_bvConstExprFromStr(vc, "1"));
  Expr rd = vc_readExpr(vc, a, idx);
  Expr m1 = vc_fpMulExpr(vc, rm, idx, idx);
  Expr m2 = vc_fpMulExpr(vc, rne, m1, rd);
  Expr ad = vc_fpAddExpr(vc, rm, m2, rd);
  Expr mn = vc_fpMinExpr(vc, ad, rd);
  Expr f = vc_fpMulExpr(vc, rm, mn, rd);

  // No assertions: FALSE is invalid, and nothing in the model constrains
  // the array or the operands.
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  Expr cv = vc_getCounterExample(vc, f);
  EXPECT_EQ(BVCONST, getExprKind(cv));
  // A model value carries the sort of the term it is a value of, so this is
  // a float of the term's format (16 bits packed) rather than a bitvector.
  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(cv));
  EXPECT_EQ(5, vc_getExpWidth(cv));
  EXPECT_EQ(11, vc_getSigWidth(cv));

  // Evaluation is memoised against the model, so asking again gives the
  // same value.
  Expr again = vc_getCounterExample(vc, f);
  EXPECT_EQ(getBVUnsignedLongLong(cv), getBVUnsignedLongLong(again));

  vc_Destroy(vc);
}

// Regression test: the same out-of-model float-element array read, but as
// the operand of a floating-point *predicate* rather than of an operation.
// Model evaluation of a predicate resolves its operands and rebuilds it too,
// and had no tolerance at all for an operand that did not come back a
// constant:
//   CounterExample.cpp: ComputeFormulaUsingModel:
//   Assertion `simp.GetKind() == BVCONST' failed.
// The read-tolerant flag is on inside the walk, so a read the solve never
// constrained arrives as the symbolic READ; it must be resolved to a value
// exactly as the operation arm above already does.
//
// Found by fuzzing with murxla driving the C API; delta-minimized.  On the
// branch that also has array extensionality the same defect aborts inside
// check-sat, when the counterexample check evaluates an fp.geq / SMT '='
// over array reads that the extensionality rewriting left out of the model.
TEST(fp_arrays, float_element_read_as_operand_of_fp_predicate)
{
  VC vc = vc_createValidityChecker();

  Type fp = vc_fpType(vc, 5, 11);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, fp, fp));
  Expr rm = vc_fpRoundingModeVar(vc, "rm");
  Expr idx =
      vc_fpToFPFromSignedBV(vc, 5, 11, rm, vc_bvConstExprFromStr(vc, "1"));
  Expr rd = vc_readExpr(vc, a, idx);
  Expr mzero = vc_fpMinusZero(vc, fp);
  Expr geq = vc_fpGeqExpr(vc, rd, mzero);
  Expr isNaN = vc_fpIsNaNExpr(vc, rd);

  // No assertions: FALSE is invalid, and nothing constrains the array.
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // A predicate has a truth value under the model -- one of TRUE / FALSE,
  // never a formula left standing over an unresolved read.
  Expr geqValue = vc_getCounterExample(vc, geq);
  Expr isNaNValue = vc_getCounterExample(vc, isNaN);
  ASSERT_TRUE(getExprKind(geqValue) == TRUE || getExprKind(geqValue) == FALSE);
  ASSERT_TRUE(getExprKind(isNaNValue) == TRUE ||
              getExprKind(isNaNValue) == FALSE);

  // The read itself resolves to a float of the element's format...
  Expr cell = vc_getCounterExample(vc, rd);
  ASSERT_EQ(BVCONST, getExprKind(cell));
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(cell));
  EXPECT_EQ(5, vc_getExpWidth(cell));
  EXPECT_EQ(11, vc_getSigWidth(cell));

  // ...and that is the value the predicates were evaluated over: asking the
  // same questions of the constant folds them outright, and the answers must
  // agree.  An arbitrary value is fine; an inconsistent one is not.
  EXPECT_EQ(getExprKind(geqValue),
            getExprKind(vc_getCounterExample(
                vc, vc_fpGeqExpr(vc, cell, mzero))));
  EXPECT_EQ(getExprKind(isNaNValue),
            getExprKind(vc_getCounterExample(vc, vc_fpIsNaNExpr(vc, cell))));

  // Evaluation is memoised against the model, so asking again agrees.
  EXPECT_EQ(getExprKind(geqValue),
            getExprKind(vc_getCounterExample(vc, geq)));

  vc_Destroy(vc);
}

// Every floating-point predicate takes the same route through model
// evaluation, so every one of them meets an out-of-model array read.  Walk
// the lot: the binary comparisons, SMT-LIB '=' over floats (what 'distinct'
// lowers to, and the kind the murxla trace tripped), fp.eq, and the seven
// classification predicates.
TEST(fp_arrays, fp_predicates_over_out_of_model_reads)
{
  VC vc = vc_createValidityChecker();

  Type fp = vc_fpType(vc, 5, 11);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, vc_bvType(vc, 10), fp));
  Expr x = vc_readExpr(vc, a, vc_bvConstExprFromStr(vc, "1100001111"));
  Expr y = vc_readExpr(vc, a, vc_bvConstExprFromStr(vc, "0001101011"));
  Expr mzero = vc_fpMinusZero(vc, fp);

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  Expr predicates[] = {
      vc_fpLtExpr(vc, x, mzero),  vc_fpLeqExpr(vc, x, mzero),
      vc_fpGtExpr(vc, x, mzero),  vc_fpGeqExpr(vc, x, mzero),
      vc_fpEqExpr(vc, x, y),      vc_eqExpr(vc, x, y),
      vc_fpIsNormalExpr(vc, x),   vc_fpIsSubnormalExpr(vc, x),
      vc_fpIsZeroExpr(vc, x),     vc_fpIsInfiniteExpr(vc, x),
      vc_fpIsNaNExpr(vc, x),      vc_fpIsNegativeExpr(vc, x),
      vc_fpIsPositiveExpr(vc, x),
  };

  for (size_t i = 0; i < sizeof(predicates) / sizeof(predicates[0]); i++)
  {
    Expr value = vc_getCounterExample(vc, predicates[i]);
    EXPECT_TRUE(getExprKind(value) == TRUE || getExprKind(value) == FALSE)
        << "predicate " << i << " did not evaluate to a truth value";
  }

  vc_Destroy(vc);
}

// The shape murxla reduced the report to, transcribed from its trace: an
// (Array (_ BitVec 10) Float16), a store chain over it, fp.geq of a read
// against -zero, 'distinct' of two reads (SMT-LIB '=' over floats, negated)
// where one index is a folded bvsdiv, and the disjunction of the two -- all
// asserted together and solved.  The counterexample self-check is turned on
// ('d'), so every assertion is evaluated against the model that comes back
// and STP rejects its own answer if any of them is not satisfied.
//
// The trace's third conjunct, 'distinct' over two array *terms*, needs array
// extensionality and cannot be built on this branch; what is left still
// drives every floating-point predicate in the evaluator over array reads.
TEST(fp_arrays, fp_predicates_over_array_reads_solve_and_self_check)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'd', 0); // construct and check the counterexample

  Type fp = vc_fpType(vc, 5, 11);
  Type bv10 = vc_bvType(vc, 10);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, bv10, fp));

  Expr i0 = vc_varExpr(vc, "i0", bv10);
  Expr i1 = vc_varExpr(vc, "i1", bv10);
  Expr c0 = vc_bvConstExprFromStr(vc, "1111101110");
  Expr c1 = vc_bvConstExprFromStr(vc, "0001101011");
  Expr c2 = vc_bvConstExprFromStr(vc, "1100001111");
  Expr mzero = vc_fpMinusZero(vc, fp);

  Expr read = vc_readExpr(vc, a, c2);

  // A store chain over the array, at both constant and symbolic indexes.
  Expr chain = vc_writeExpr(vc, a, i0, mzero);
  chain = vc_writeExpr(vc, chain, c0, read);
  chain = vc_writeExpr(vc, chain, c1, read);
  chain = vc_writeExpr(vc, chain, i0, read);
  chain = vc_writeExpr(vc, chain, i1, read);
  chain = vc_writeExpr(vc, chain, c1, mzero);
  chain = vc_writeExpr(vc, chain, c2, read);

  Expr geq = vc_fpGeqExpr(vc, read, mzero);
  // 'distinct' over floats is the negation of SMT-LIB '=', which is FP_SMT_EQ
  // -- the kind the reported abort came through.
  Expr sdiv = vc_sbvDivExpr(vc, 10, c1, c0);
  Expr distinct = vc_notExpr(
      vc, vc_eqExpr(vc, vc_readExpr(vc, a, i0), vc_readExpr(vc, a, sdiv)));

  vc_assertFormula(vc, vc_orExpr(vc, geq, distinct));
  vc_assertFormula(vc, geq);
  // Keep the store chain live: what it reads back at c2 is what was stored.
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, chain, c2), read));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // The asserted predicate holds under the model that came back.
  EXPECT_EQ(TRUE, getExprKind(vc_getCounterExample(vc, geq)));

  // What array extensionality does to the trace's reads -- leave one of the
  // operands of a float 'distinct' out of the model -- is reached here by
  // asking about a cell no assertion mentions.  It still has to answer.
  Expr elsewhere = vc_readExpr(vc, a, vc_bvConstExprFromStr(vc, "0101010101"));
  Expr apart = vc_notExpr(vc, vc_eqExpr(vc, elsewhere, read));
  Expr apartValue = vc_getCounterExample(vc, apart);
  EXPECT_TRUE(getExprKind(apartValue) == TRUE ||
              getExprKind(apartValue) == FALSE);

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

// The solve addresses a floating-point-indexed array through the canonical
// representative of the index. Model evaluation must use that same address:
// a symbolic NaN can have non-canonical carrier bits in the SAT model even
// though every NaN denotes the array sort's single NaN index value.
TEST(fp_arrays, float_index_model_uses_canonical_nan_cell)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'd', 0); // construct and validate the counterexample

  Type fp = vc_fpType(vc, 5, 11);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, fp, vc_bvType(vc, 8)));
  Expr x = vc_varExpr(vc, "x", fp);
  Expr read = vc_readExpr(vc, a, x);
  Expr expected = vc_bvConstExprFromInt(vc, 8, 0x2A);

  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, x));
  vc_assertFormula(vc, vc_eqExpr(vc, read, expected));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  EXPECT_EQ(0x2AULL,
            static_cast<unsigned long long>(
                getBVUnsignedLongLong(vc_getCounterExample(vc, read))));

  vc_Destroy(vc);
}

// Carrier reads nested below the encoded root still retain the array's source
// sort. Treat the whole encoded DAG as target language while evaluating it;
// otherwise expanding this read-over-write redispatches its canonical child
// as though it were a fresh source access and canonicalises forever.
TEST(fp_arrays, float_index_model_read_over_write_is_lowered_once)
{
  VC vc = vc_createValidityChecker();

  Type fp = vc_fpType(vc, 5, 11);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, fp, vc_bvType(vc, 8)));
  Expr x = vc_varExpr(vc, "x", fp);
  Expr y = vc_varExpr(vc, "y", fp);
  Expr expected = vc_bvConstExprFromInt(vc, 8, 0x2A);
  Expr stored = vc_writeExpr(vc, a, x, expected);
  Expr read = vc_readExpr(vc, stored, y);

  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, x));
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, y));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  EXPECT_EQ(0x2AULL,
            static_cast<unsigned long long>(
                getBVUnsignedLongLong(vc_getCounterExample(vc, read))));

  vc_Destroy(vc);
}

TEST(fp_arrays, float_index_constant_model_cell)
{
  VC vc = vc_createValidityChecker();

  Type fp = vc_fpType(vc, 5, 11);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, fp, vc_bvType(vc, 8)));
  Expr index =
      vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x3C00));
  Expr read = vc_readExpr(vc, a, index);
  Expr expected = vc_bvConstExprFromInt(vc, 8, 0x2A);

  vc_assertFormula(vc, vc_eqExpr(vc, read, expected));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(0x2AULL,
            static_cast<unsigned long long>(
                getBVUnsignedLongLong(vc_getCounterExample(vc, read))));

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

TEST(fp_arrays, unobserved_roundingmode_element_defaults_to_rne)
{
  VC vc = vc_createValidityChecker();

  Type arrayType =
      vc_arrayType(vc, vc_bvType(vc, 2), vc_fpRoundingModeType(vc));
  Expr a = vc_varExpr(vc, "a", arrayType);
  Expr read = vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 2, 0));

  // These two results distinguish the illegal 0b11111 carrier value from all
  // five rounding modes: it underflows upward like RTP but rounds 1/3 downward
  // like RTN/RTZ. Model completion chooses RNE, so both the reported mode and
  // every operation evaluated through it must have RNE's behaviour.
  Expr tiny = float32(vc, 0x0D800000ULL); // 2^-100
  Expr underflow = vc_fpMulExpr(vc, read, tiny, tiny);
  Expr third = vc_fpDivExpr(vc, read, float32(vc, 0x3F800000ULL),
                            float32(vc, 0x40400000ULL));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // Read the operations first so they cannot merely inherit a mode cached by
  // the direct get-value below.
  EXPECT_EQ((unsigned long long)0x00000000ULL,
            getBVUnsignedLongLong(vc_getCounterExample(vc, underflow)));
  EXPECT_EQ((unsigned long long)0x3EAAAAABULL,
            getBVUnsignedLongLong(vc_getCounterExample(vc, third)));
  EXPECT_EQ((unsigned long long)VC_RM_RNE,
            getBVUnsignedLongLong(vc_getCounterExample(vc, read)));

  vc_Destroy(vc);
}

// Regression test: evaluating a floating-point operation whose rounding
// mode is an array read that the solve never constrained.  The solve is
// fine; reading the term's value back used to abort.  Model evaluation
// re-totalises the term before blasting it, and the totalising pass
// pinned the rounding-mode-element read to the five legal encodings by
// conjoining a constraint onto its input -- sound for an asserted
// formula, but here the input is a *term*, and the wrap handed the
// blaster an AND it cannot blast:
//   Fatal Error: FloatBlaster::BlastNode: unhandled kind: (AND ...)
// The pinning must apply to formulas only.  The value itself is
// unconstrained (the model says nothing about the read, and an
// out-of-model read resolves arbitrarily), so only its shape is checked.
//
// Found by fuzzing with murxla driving the C API; delta-minimized.
TEST(fp_arrays, roundingmode_element_read_as_mode_of_evaluated_term)
{
  VC vc = vc_createValidityChecker();

  Type rm = vc_fpRoundingModeType(vc);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, rm, rm));
  Expr idx = vc_fpRoundingModeVar(vc, "x0");
  Expr rd = vc_readExpr(vc, a, idx);
  Expr b = vc_varExpr(vc, "b", vc_bvType(vc, 8));
  Expr f = vc_fpNegExpr(vc, vc_fpToFPFromUnsignedBV(vc, 8, 24, rd, b));

  // No assertions: FALSE is invalid, and the model leaves both the array
  // and the term's operands entirely unconstrained.
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // The read-back must produce a constant of the term's sort -- some float
  // of the term's format that it can take under a legal rounding mode --
  // not abort.
  Expr cv = vc_getCounterExample(vc, f);
  EXPECT_EQ(BVCONST, getExprKind(cv));
  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(cv));
  EXPECT_EQ(8, vc_getExpWidth(cv));
  EXPECT_EQ(24, vc_getSigWidth(cv));

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

// Model evaluation must compare array indexes by their carrier value, not by
// the source-sort decoration on the constant node.  The SAT model supplies a
// plain five-bit value for r, whereas the WRITE index is the source-sorted RNE
// constant.  Those denote the same RoundingMode even though they are not the
// same interned AST node.
TEST(fp_arrays, roundingmode_index_read_over_write_model)
{
  VC vc = vc_createValidityChecker();

  Type arrayType =
      vc_arrayType(vc, vc_fpRoundingModeType(vc), vc_bvType(vc, 8));
  Expr a = vc_varExpr(vc, "a", arrayType);
  Expr stored = vc_writeExpr(vc, a, vc_fpRoundingMode(vc, VC_RM_RNE),
                             vc_bvConstExprFromInt(vc, 8, 0x11));
  Expr r = vc_fpRoundingModeVar(vc, "r");
  Expr read = vc_readExpr(vc, stored, r);

  // Pin r to RNE without asserting r = RNE directly: direct substitution can
  // hide the typed/plain constant boundary exercised by model evaluation.
  const VCRoundingMode otherModes[4] = {VC_RM_RNA, VC_RM_RTP, VC_RM_RTN,
                                        VC_RM_RTZ};
  for (const VCRoundingMode mode : otherModes)
    vc_assertFormula(
        vc, vc_notExpr(vc, vc_eqExpr(vc, r, vc_fpRoundingMode(vc, mode))));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)0x11,
            getBVUnsignedLongLong(vc_getCounterExample(vc, read)));

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

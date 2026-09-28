#include <gtest/gtest.h>
#include <stp/c_interface.h>

// vc_fpRoundingModeVar: a RoundingMode variable made through the C API is a
// real variable of the sort -- it ranges over exactly the five modes, and
// works as the rounding-mode operand of the rounding operations. Guards the
// API-level twin of the parser's declaration constraint: a plain 5-bit
// vc_varExpr would satisfy the typechecker but denote 32 "modes".

TEST(fp_roundingmode_var, ranges_over_exactly_five_modes)
{
  VC vc = vc_createValidityChecker();
  Expr r = vc_fpRoundingModeVar(vc, "r");

  const enum VCRoundingMode modes[] = {VC_RM_RNE, VC_RM_RNA, VC_RM_RTP,
                                       VC_RM_RTN, VC_RM_RTZ};
  for (const enum VCRoundingMode m : modes)
    vc_assertFormula(
        vc, vc_notExpr(vc, vc_eqExpr(vc, r, vc_fpRoundingMode(vc, m))));

  // Distinct from all five modes: must be unsatisfiable.
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

// The sort-then-vc_varExpr idiom, as for every other sort, builds the same
// constrained variable.
TEST(fp_roundingmode_var, declared_through_the_type)
{
  VC vc = vc_createValidityChecker();
  Type rmt = vc_fpRoundingModeType(vc);
  EXPECT_EQ(ROUNDINGMODE, getExprKind(rmt));

  Expr r = vc_varExpr(vc, "r", rmt);
  const enum VCRoundingMode modes[] = {VC_RM_RNE, VC_RM_RNA, VC_RM_RTP,
                                       VC_RM_RTN, VC_RM_RTZ};
  for (const enum VCRoundingMode m : modes)
    vc_assertFormula(
        vc, vc_notExpr(vc, vc_eqExpr(vc, r, vc_fpRoundingMode(vc, m))));

  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

TEST(fp_roundingmode_var, source_sort_survives_public_expression_shapes)
{
  VC vc = vc_createValidityChecker();
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr r = vc_fpRoundingModeVar(vc, "r");
  Expr c = vc_varExpr(vc, "c", vc_boolType(vc));
  Expr choice = vc_iteExpr(vc, c, rne, r);
  Expr array = vc_varExpr(
      vc, "a",
      vc_arrayType(vc, vc_bvType(vc, 1), vc_fpRoundingModeType(vc)));
  Expr read = vc_readExpr(vc, array, vc_bvConstExprFromInt(vc, 1, 0));

  EXPECT_EQ(ROUNDINGMODE_TYPE, getType(rne));
  EXPECT_EQ(ROUNDINGMODE_TYPE, getType(r));
  EXPECT_EQ(ROUNDINGMODE_TYPE, getType(choice));
  EXPECT_EQ(ROUNDINGMODE_TYPE, getType(read));
  EXPECT_EQ(ROUNDINGMODE, getExprKind(vc_getType(vc, rne)));

  vc_Destroy(vc);
}

TEST(fp_roundingmode_var, release_api_rejects_carrier_source_mixes)
{
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
        Expr bits = vc_bvConstExprFromInt(vc, 5, 1);
        (void)vc_eqExpr(vc, rne, bits);
      },
      "requires operands of the same sort");

  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
        (void)vc_bvNotExpr(vc, rne);
      },
      "requires bitvector operands");

  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Type fp = vc_fpType(vc, 8, 24);
        Expr x = vc_varExpr(vc, "x", fp);
        Expr bits = vc_bvConstExprFromInt(vc, 5, 1);
        (void)vc_fpAddExpr(vc, bits, x, x);
      },
      "expected a rounding mode");

  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
        (void)vc_varExpr(vc, "not_a_type", (Type)rne);
      },
      "expects a type node");

  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        (void)vc_fpRoundingModeVar(vc, "same_name");
        (void)vc_varExpr(vc, "same_name", vc_bvType(vc, 5));
      },
      "cannot be redeclared");
}

TEST(fp_roundingmode_var, model_completion_after_declaration_scope)
{
  VC vc = vc_createValidityChecker();

  // Drop the declaration-time validity assertion without dropping the
  // hash-consed symbol. With no use in the solved formula, the model must
  // complete this RoundingMode value itself.
  vc_push(vc);
  Expr r = vc_fpRoundingModeVar(vc, "scoped_r");
  vc_pop(vc);
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  EXPECT_EQ((unsigned long long)VC_RM_RNE,
            getBVUnsignedLongLong(vc_getCounterExample(vc, r)));
  EXPECT_EQ(ROUNDINGMODE_TYPE, getType(vc_getCounterExample(vc, r)));

  // The snapshot model API has its own completion path and must preserve the
  // same sort invariant.
  WholeCounterExample whole = vc_getWholeCounterExample(vc);
  EXPECT_EQ((unsigned long long)VC_RM_RNE,
            getBVUnsignedLongLong(
                vc_getTermFromCounterExample(vc, r, whole)));
  EXPECT_EQ(ROUNDINGMODE_TYPE,
            getType(vc_getTermFromCounterExample(vc, r, whole)));
  vc_deleteWholeCounterExample(whole);

  vc_Destroy(vc);
}

TEST(fp_roundingmode_var, drives_an_operation_and_reads_back)
{
  VC vc = vc_createValidityChecker();
  Expr r = vc_fpRoundingModeVar(vc, "r");

  // 2.5 in half precision is 0x4100; fp.to_sbv of it under r gives 2 only
  // for the truncating modes -- forcing the result to 3 leaves r one of
  // RNA/RTP (round up), so the model's r must be a legal mode with that
  // behaviour.
  Expr twoAndAHalf =
      vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x4100));
  Expr out = vc_varExpr(vc, "out", vc_bvType(vc, 8));
  vc_assertFormula(
      vc, vc_eqExpr(vc, out, vc_fpToSBVExpr(vc, 8, r, twoAndAHalf)));
  vc_assertFormula(
      vc, vc_eqExpr(vc, out, vc_bvConstExprFromLL(vc, 8, 3)));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  const unsigned long long rv =
      getBVUnsignedLongLong(vc_getCounterExample(vc, r));
  EXPECT_TRUE(rv == (unsigned long long)VC_RM_RNA ||
              rv == (unsigned long long)VC_RM_RTP)
      << "r = " << rv;
  vc_Destroy(vc);
}

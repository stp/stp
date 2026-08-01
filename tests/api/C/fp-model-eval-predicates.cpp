#include <gtest/gtest.h>
#include <stp/c_interface.h>

// Regression tests for floating-point predicate evaluation in the model.
//
// STP's model-formula evaluator, ComputeFormulaUsingModel
// (lib/AbsRefineCounterExample/CounterExample.cpp), is walked while a
// counterexample is built and checked. It must be able to evaluate every
// floating-point predicate kind. A rewrite of that file dropped the cases for
// all thirteen of them (FP_EQ, FP_SMT_EQ, the four ordered comparisons, and the
// seven classification predicates), so a satisfiable query whose model reached
// one aborted with
//   FP_<X> Fatal Error: ComputeFormulaUsingModel: the kind has not been implemented
// instead of solving.
//
// A predicate only reaches the model evaluator when its node survives
// bit-blasting. A bare (fp.isZero x) is discharged in the SAT circuit and never
// gets there; a predicate over an fp.fp-reinterpreted value, kept inside an
// ite, is not, and the counterexample check then walks it. These build exactly
// that shape. Found by fuzzing with murxla; the first test is its minimized
// query, the second exercises the whole predicate family.

namespace
{

// A Float32 reinterpreted from 32 bit-vector bits (fp.fp). Its node is a
// reinterpret, not a leaf, so predicates over it survive to model evaluation.
Expr float32FromBits(VC vc, const char* name)
{
  return vc_fpToFPFromIEEEBV(vc, 8, 24, vc_varExpr(vc, name, vc_bvType(vc, 32)));
}

// The thirteen floating-point predicate kinds, as the C API builds them
// (vc_eqExpr over floats is FP_SMT_EQ; vc_fpEqExpr is FP_EQ).
Expr predicate(VC vc, int which, Expr a, Expr b)
{
  switch (which)
  {
    case 0: return vc_fpEqExpr(vc, a, b);
    case 1: return vc_eqExpr(vc, a, b);
    case 2: return vc_fpLeqExpr(vc, a, b);
    case 3: return vc_fpLtExpr(vc, a, b);
    case 4: return vc_fpGeqExpr(vc, a, b);
    case 5: return vc_fpGtExpr(vc, a, b);
    case 6: return vc_fpIsNaNExpr(vc, a);
    case 7: return vc_fpIsZeroExpr(vc, a);
    case 8: return vc_fpIsNormalExpr(vc, a);
    case 9: return vc_fpIsSubnormalExpr(vc, a);
    case 10: return vc_fpIsInfiniteExpr(vc, a);
    case 11: return vc_fpIsPositiveExpr(vc, a);
    default: return vc_fpIsNegativeExpr(vc, a);
  }
}
const int NUM_PREDICATES = 13;

} // namespace

// Each predicate kind, reached at model-evaluation time. The predicate under
// test is put in a boolean position (the condition of the ite the outer
// fp.isZero is taken over), so the counterexample walk reaches it. Before the
// fix each one aborted; here every kind solves. The query is satisfiable for
// every kind -- taking the ite's then-branch makes the selected value +zero,
// which is a zero -- so the query of 'false' is INVALID (0) throughout,
// independent of the predicate's own truth value.
TEST(fp_model_eval_predicates, every_predicate_kind_is_evaluated)
{
  for (int which = 0; which < NUM_PREDICATES; which++)
  {
    VC vc = vc_createValidityChecker();
    Type fp = vc_fpType(vc, 8, 24);

    Expr f = float32FromBits(vc, "f");
    Expr g = float32FromBits(vc, "g");
    Expr inner = predicate(vc, which, f, g);
    Expr other = vc_bvLtExpr(vc, vc_varExpr(vc, "k", vc_bvType(vc, 8)),
                             vc_bvConstExprFromLL(vc, 8, 42));
    Expr cond = vc_notExpr(vc, vc_iffExpr(vc, other, inner));
    Expr sel = vc_iteExpr(vc, cond, vc_fpPlusZero(vc, fp), f);

    vc_assertFormula(vc, vc_fpIsZeroExpr(vc, sel));

    EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)))
        << "predicate kind index " << which;
    vc_Destroy(vc);
  }
}

// The fuzzer's minimized query itself: fp.isZero over an ite whose condition
// pairs a bit-vector comparison with fp.eq of an fp.fp value with itself.
// bitwuzla agrees it is satisfiable, so the query of 'false' is INVALID (0).
TEST(fp_model_eval_predicates, fuzzed_iszero_over_ite_with_fp_eq_is_sat)
{
  VC vc = vc_createValidityChecker();
  Type fp = vc_fpType(vc, 8, 24);

  Expr f = float32FromBits(vc, "f");
  Expr bv = vc_bvGeExpr(vc, vc_varExpr(vc, "x", vc_bvType(vc, 23)),
                        vc_varExpr(vc, "y", vc_bvType(vc, 23)));
  Expr cond = vc_notExpr(vc, vc_iffExpr(vc, bv, vc_fpEqExpr(vc, f, f)));
  Expr sel = vc_iteExpr(vc, cond, vc_fpMaxExpr(vc, vc_fpPlusZero(vc, fp),
                                               vc_fpPlusZero(vc, fp)),
                        f);

  vc_assertFormula(vc, vc_fpIsZeroExpr(vc, sel));

  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

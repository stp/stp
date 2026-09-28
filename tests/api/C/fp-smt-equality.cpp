#include <gtest/gtest.h>
#include <stp/c_interface.h>

// SMT-LIB '=' over floating-point operands.
//
// The C API routes floating-point SMT-'=' through vc_eqExpr: the note on
// vc_fpEqExpr in c_interface.h directs callers there for '=' (as opposed to
// fp.eq). vc_eqExpr builds an FP_SMT_EQ node when either operand is of
// FLOATINGPOINT_TYPE, exactly as the parser does for '=' between floats
// (lib/Parser/smt2.y), giving the SMT-LIB semantics: +0 and -0 are
// distinct, and every NaN equals every NaN.
//
// Regression tests: vc_eqExpr used to build a generic EQ node
// unconditionally. A leaf-vs-leaf equality (x = y) folded to a bit-vector
// comparison and behaved, but once an operand was a composite
// floating-point term (here fp.neg x) the generic EQ over floats was not
// discharged by the floating-point solver, and the solve aborted with
//   Fatal Error: TopLevelSTPAux: reached the end without proper conclusion.
// rather than fail an EXPECT here.

// x = -x holds exactly for NaN under SMT '=' (NaN == NaN, and -NaN is NaN), so
// the constraint is satisfiable and the query of 'false' is INVALID (0).
TEST(fp_smt_equality, self_negation_is_sat)
{
  VC vc  = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 11, 53));

  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_fpNegExpr(vc, x)));

  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

// The only witness for x = -x is NaN -- in particular +0 = -0 is false under
// SMT '=' -- so ruling out NaN makes the same constraint unsatisfiable, and
// the query of 'false' is then VALID (1). This pins the FP_SMT_EQ semantics,
// not merely the absence of the abort.
TEST(fp_smt_equality, self_negation_requires_nan)
{
  VC vc  = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 11, 53));

  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_fpNegExpr(vc, x)));
  vc_assertFormula(vc, vc_notExpr(vc, vc_fpIsNaNExpr(vc, x)));

  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

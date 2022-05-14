// Issue reported https://github.com/stp/stp/issues/188

#include <gtest/gtest.h>
#include <stdio.h>
#include <stp/c_interface.h>

TEST(failing_solvermap, one)
{

  VC vc = vc_createValidityChecker();
  Expr falseExpr = vc_falseExpr(vc);

  Expr A = vc_varExpr(vc, "A", vc_bv32Type(vc));
  Expr B = vc_varExpr(vc, "B", vc_bv32Type(vc));

  vc_push(vc);

  Expr AplusB = vc_bv32PlusExpr(vc, A, B);
  Expr AplusBplus42 =
      vc_bv32PlusExpr(vc, AplusB, vc_bv32ConstExprFromInt(vc, 42));

  vc_assertFormula(vc,
                   vc_bvGtExpr(vc, AplusB, vc_bv32ConstExprFromInt(vc, 100)));
  assert(0 == vc_query(vc, falseExpr));
  vc_assertFormula(
      vc, vc_bvGtExpr(vc, AplusBplus42, vc_bv32ConstExprFromInt(vc, 5)));
  assert(0 == vc_query(vc, falseExpr));

  vc_Destroy(vc);
}

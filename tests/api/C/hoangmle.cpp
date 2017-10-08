#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <stdio.h>

TEST(hoangmle, one)
{
  VC vc = vc_createValidityChecker();
  Expr a = vc_bvConstExprFromStr(
      vc,
      "001111001110010101010100000000000000000000000000000000000000000000000");
  vc_printExpr(vc, a);
  printf("\nMy print:\n");
  printf("%s", exprString(a));
  vc_Destroy(vc);
}

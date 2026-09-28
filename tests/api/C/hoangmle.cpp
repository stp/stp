#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <stdio.h>
#include <stdlib.h>
#include <string>

// exprString's buffer is ours to free.
static std::string toString(Expr e)
{
  char* s = exprString(e);
  std::string result(s);
  free(s);
  return result;
}

TEST(hoangmle, one)
{
  VC vc = vc_createValidityChecker();
  Expr a = vc_bvConstExprFromStr(
      vc,
      "001111001110010101010100000000000000000000000000000000000000000000000");
  vc_printExpr(vc, a);
  // 69 bits is not a whole number of hex digits, so it prints in binary.
  EXPECT_EQ(
      "0b001111001110010101010100000000000000000000000000000000000000000000000 ",
      toString(a));
  vc_Destroy(vc);
}

/***********
AUTHORS:  Michael Katelman, Vijay Ganesh, Trevor Hansen, Dan Liew

BEGIN DATE: Oct, 2008

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
**********************/

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <stdio.h>

// FIXME: Pick a sensible testname that actually means something!
TEST(array_cvcl02, one)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'n');
  vc_setFlag(vc, 'd');
  vc_setFlag(vc, 'p');

  Expr cvcl_array = vc_varExpr1(vc, "a", 32, 32);
  Expr i = vc_varExpr1(vc, "i", 0, 8);
  Expr i32 = vc_bvConcatExpr(
      vc, vc_bvConstExprFromStr(vc, "000000000000000000000000"), i);
  Expr no_underflow = vc_bvLeExpr(vc, vc_bvConstExprFromInt(vc, 32, 0), i32);
  Expr no_overflow = vc_bvLeExpr(vc, i32, vc_bvConstExprFromInt(vc, 32, 9));
  Expr in_bounds = vc_andExpr(vc, no_underflow, no_overflow);
  Expr a_of_i = vc_bvSignExtend(vc, vc_readExpr(vc, cvcl_array, i32), 32);
  Expr a_of_i_eq_11 = vc_eqExpr(vc, vc_bvConcatExpr(vc, i32, a_of_i),
                                vc_bvConstExprFromInt(vc, 64, 11));

  vc_assertFormula(vc, in_bounds);
  vc_assertFormula(vc, a_of_i_eq_11);
  vc_query(vc, vc_falseExpr(vc));

  Expr pre = vc_bvConstExprFromInt(vc, 24, 0);
  int j;
  for (j = 0; j < 10; j++)
  {
    Expr exprj = vc_bvConstExprFromInt(vc, 8, j);
    Expr index = vc_bvConcatExpr(vc, pre, exprj);
    index = vc_simplify(vc, index);
    Expr a_of_j = vc_readExpr(vc, cvcl_array, index);
    (void)vc_getCounterExample(vc, a_of_j);
  }
  vc_Destroy(vc);
  // vc_printCounterExample(vc);

  // FIXME: Actually test something
  // ASSERT_TRUE(false && "FIXME: Actually test something");
}

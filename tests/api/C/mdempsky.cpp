/***********
AUTHORS:   Matthew Dempsky

BEGIN DATE: June, 2015

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

TEST(mdempsky, one)
{
  VC vc = vc_createValidityChecker();

  Expr A = vc_varExpr(vc, "A", vc_bv32Type(vc));
  Expr B = vc_varExpr(vc, "B", vc_bv32Type(vc));

  Expr AplusB = vc_bv32PlusExpr(vc, A, B);
  Expr AplusBplus42 =
      vc_bv32PlusExpr(vc, AplusB, vc_bv32ConstExprFromInt(vc, 42));

  Expr myexpr = vc_bvGtExpr(vc, AplusB, vc_bv32ConstExprFromInt(vc, 100));
  Expr myexpr2 = vc_bvGtExpr(vc, AplusBplus42, vc_bv32ConstExprFromInt(vc, 5));
  Expr both_of_them = vc_andExpr(vc, myexpr, myexpr2);
  Expr myexpr3 = vc_bvLtExpr(vc, AplusBplus42, vc_bv32ConstExprFromInt(vc, 5));
  Expr all_of_them = vc_andExpr(vc, both_of_them, myexpr3);

  vc_push(vc);
  assert(0 == vc_query(vc, myexpr));
  vc_pop(vc);

  vc_push(vc);
  assert(0 == vc_query(vc, both_of_them));
  vc_pop(vc);

  vc_push(vc);
  int ret = vc_query(vc, all_of_them);
  printf("ret: %d\n", ret);
  vc_pop(vc);

  vc_Destroy(vc);
}

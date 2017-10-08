/***********
AUTHORS:  Trevor Hansen, Dan Liew

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
#include <iostream>
#include <stdio.h>

TEST(sbdiv, one)
{
  VC vc = vc_createValidityChecker();
  //vc_setFlags(vc, 'p');
  vc_setFlags(vc, 'd');

  Type int_type = vc_bv32Type(vc);
  Expr zero = vc_bv32ConstExprFromInt(vc, 0);
  Expr int_max = vc_bvConstExprFromInt(vc, 32, 0x7fffffff);
  Expr a = vc_varExpr(vc, "a", int_type);
  Expr b = vc_varExpr(vc, "b", int_type);
  vc_assertFormula(vc, vc_sbvGtExpr(vc, b, zero));
  vc_assertFormula(vc, vc_sbvLeExpr(vc, a, vc_sbvDivExpr(vc, 32, int_max, b)));
  int query = vc_query(vc, vc_falseExpr(vc));
  ASSERT_FALSE(query);
}

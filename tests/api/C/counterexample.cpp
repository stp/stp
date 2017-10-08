/***********
AUTHORS:   Austin Clements

BEGIN DATE: November, 2015

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

TEST(counterexample, one)
{
  VC vc = vc_createValidityChecker();
  Expr falseExpr = vc_falseExpr(vc);

  Expr A = vc_varExpr(vc, "A", vc_bv32Type(vc));
  Expr c42 = vc_bvConstExprFromInt(vc, 32, 42);
  Expr eq = vc_eqExpr(vc, A, c42);

  vc_assertFormula(vc, eq);
  assert(0 == vc_query(vc, falseExpr));

  Expr ce = vc_getCounterExample(vc, A);
  assert(42 == getBVInt(ce));

  Expr Aplus42 = vc_bvPlusExpr(vc, 32, A, c42);
  ce = vc_getCounterExample(vc, Aplus42);
  assert(84 == getBVInt(ce));

  ce = vc_getCounterExample(vc, falseExpr);
  assert(0 == vc_isBool(ce));

  Expr trueExpr = vc_notExpr(vc, falseExpr);
  ce = vc_getCounterExample(vc, trueExpr);
  assert(1 == vc_isBool(ce));

  Expr eq2 = vc_eqExpr(vc, Aplus42, vc_bvConstExprFromInt(vc, 32, 84));
  ce = vc_getCounterExample(vc, eq2);
  assert(1 == vc_isBool(ce));

  vc_Destroy(vc);
}

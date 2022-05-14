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

TEST(multi_query_bug, one)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  vc_setFlags(vc, 'p');

  Expr a = vc_varExpr(vc, "a", vc_bv32Type(vc));
  Expr b = vc_varExpr(vc, "b", vc_bv32Type(vc));
  // a == b
  Expr expr = vc_eqExpr(vc, a, b);
  vc_printExpr(vc, expr);

  vc_push(vc);
  int res = vc_query(vc, expr);
  printf("vc_query result = %d\n", res);
  ASSERT_EQ(res, 0);
  vc_pop(vc);

  Expr expr2 = vc_bvGtExpr(vc, a, b);
  vc_printExpr(vc, expr2);

  vc_push(vc);
  int res2 = vc_query(vc, expr2);
  printf("vc_query result = %d\n", res2);
  ASSERT_EQ(res2, 0);
  vc_pop(vc);

  vc_Destroy(vc);
}

TEST(multi_query_bug, many)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  vc_setFlags(vc, 'p');

  Expr a = vc_varExpr(vc, "a", vc_bv32Type(vc));
  Expr b = vc_varExpr(vc, "b", vc_bv32Type(vc));

  // a == b
  Expr expr = vc_eqExpr(vc, a, b);
  vc_printExpr(vc, expr);
  vc_push(vc);
  int res = vc_query(vc, expr);
  printf("vc_query result = %d\n", res);
  ASSERT_EQ(res, 0);
  vc_pop(vc);

  // a >= b
  expr = vc_bvGeExpr(vc, a, b);
  vc_printExpr(vc, expr);
  vc_push(vc);
  res = vc_query(vc, expr);
  printf("vc_query result = %d\n", res);
  ASSERT_EQ(res, 0);
  vc_pop(vc);

  // a > b
  expr = vc_bvGtExpr(vc, a, b);
  vc_printExpr(vc, expr);
  vc_push(vc);
  res = vc_query(vc, expr);
  printf("vc_query result = %d\n", res);
  ASSERT_EQ(res, 0);
  vc_pop(vc);

  // a < b
  expr = vc_bvGtExpr(vc, b, a);
  vc_printExpr(vc, expr);
  vc_push(vc);
  res = vc_query(vc, expr);
  printf("vc_query result = %d\n", res);
  ASSERT_EQ(res, 0);
  vc_pop(vc);

  vc_Destroy(vc);
}

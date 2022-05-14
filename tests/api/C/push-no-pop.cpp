/***********
AUTHORS:  Michael Katelman, Vijay Ganesh, Trevor Hansen, Dan Liew, Khoo Yit
Phang

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

/* g++ -I$(HOME)/stp/c_interface push-no-pop.c -L$(HOME)/lib -lstp -o cc*/
#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <stdio.h>

TEST(push_no_pop, one)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'n');
  vc_setFlag(vc, 'd');
  vc_setFlag(vc, 'p');

  Type bv8 = vc_bvType(vc, 8);

  Expr a = vc_varExpr(vc, "a", bv8);
  Expr ct_0 = vc_bvConstExprFromInt(vc, 8, 0);

  Expr a_eq_0 = vc_eqExpr(vc, a, ct_0);

  int query = vc_query(vc, a_eq_0);
  printf("query = %d\n", query);

  Expr a_neq_0 = vc_notExpr(vc, a_eq_0);
  vc_assertFormula(vc, a_eq_0);
  vc_push(vc);

  Expr queryexp = vc_eqExpr(vc, a, vc_bvConstExprFromInt(vc, 8, 0));

  query = vc_query(vc, queryexp);
  vc_printCounterExample(vc);
  printf("query = %d\n", query);

  vc_DeleteExpr(queryexp);
  vc_DeleteExpr(a_neq_0);
  vc_DeleteExpr(a_eq_0);
  vc_DeleteExpr(a);

  vc_Destroy(vc);

  // FIXME: Actually test something
  // ASSERT_TRUE(false && "FIXME: Actually test something");
}

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

/* g++ -I $HOME/stp/c_interface stp-div-001.c -L $HOME/lib -lstp -o cc */

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <stdio.h>
#include <stdlib.h>

TEST(stp_div, one)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  // vc_setFlags(vc,'p');

  Expr a = vc_bvCreateMemoryArray(vc, "a");

  Expr index_3 = vc_bvConstExprFromInt(vc, 32, 3);

  Expr a_of_0 = vc_readExpr(vc, a, index_3);
  int i;
  for (i = 2; i >= 0; i--)
    a_of_0 = vc_bvConcatExpr(
        vc, a_of_0, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 32, i)));

  Expr ct_5 = vc_bvConstExprFromInt(vc, 32, 5);
  Expr a_of_0_div_5 = vc_bvDivExpr(vc, 32, a_of_0, ct_5);

  Expr a_of_0_div_5_eq_5 = vc_eqExpr(vc, a_of_0_div_5, ct_5);
  vc_printExpr(vc, a_of_0_div_5_eq_5);
  printf("\n");

  /* Query 1 */
  vc_push(vc);
  int query = vc_query(vc, a_of_0_div_5_eq_5);
  vc_pop(vc);
  printf("query = %d\n", query);

  vc_assertFormula(vc, a_of_0_div_5_eq_5);
  vc_printExpr(vc, a_of_0_div_5_eq_5);

  /* query(false) */
  vc_push(vc);
  query = vc_query(vc, vc_falseExpr(vc));
  vc_pop(vc);
  printf("query = %d\n", query);
  ASSERT_TRUE(!query);

  ASSERT_TRUE(vc_counterexample_size(vc));

  int* a_val = (int*)malloc(sizeof *a_val);
  char* p = (char*)a_val;
  // a_of_1 = vc_simplify(vc, a_of_1);  // BUG here
  for (i = 0; i <= 3; i++)
  {
    Expr elem = vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 32, i));
    Expr ce = vc_getCounterExample(vc, elem);
    unsigned long long v = getBVUnsigned(ce);
    fprintf(stderr, "a[%d] = %llu\n", i, v);
    *p = v;
    p++;
  }
  printf("a = %d\n", *a_val);
  ASSERT_TRUE((*a_val) / 5 == 5);

  vc_Destroy(vc);
}

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

// g++ <this-filename> -I/home/vganesh/stp/c_interface
// -L/home/vganesh/stp/lib -lstp -o cc

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <stdio.h>
#include <stdlib.h>

TEST(stp_counterex, one)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  // vc_setFlags(vc,'p');

  Expr a = vc_bvCreateMemoryArray(vc, "a");

  Expr index_1 = vc_bvConstExprFromInt(vc, 32, 1);
  Expr a_of_1 = vc_readExpr(vc, a, index_1);

  Expr ct_100 = vc_bvConstExprFromInt(vc, 8, 100);
  Expr a_of_1_eq_100 = vc_eqExpr(vc, a_of_1, ct_100);

  /* Query 1 */
  vc_push(vc);
  int query = vc_query(vc, a_of_1_eq_100);
  vc_pop(vc);
  printf("query = %d\n", query);

  vc_assertFormula(vc, a_of_1_eq_100);

  /* query(false) */
  vc_push(vc);
  query = vc_query(vc, vc_falseExpr(vc));
  vc_pop(vc);
  printf("query = %d\n", query);

  ASSERT_FALSE(vc_counterexample_size(vc) == 0);

  a_of_1 = vc_simplify(vc, a_of_1);
  // vc_printExpr(vc, a_of_1);
  Expr ce = vc_getCounterExample(vc, a_of_1);
  unsigned long long v = getBVUnsigned(ce);

  fprintf(stderr, "a[1] = %llu\n", v);

  vc_Destroy(vc);
  // FIXME: we should test more things!
}

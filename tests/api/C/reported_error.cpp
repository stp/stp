/********************************************************************
 * AUTHORS: Quark17, Mate Soos
 *
 * BEGIN DATE: Apr, 2014
 *
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
********************************************************************/

//Bugreport by https://github.com/quark17
//See https://github.com/stp/stp/issues/120

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <stdio.h>

TEST(reported_issue_120, one)
{
  VC vc = vc_createValidityChecker();

  // Numbers will be non-negatives integers bounded at 2^32
  Type bv32 = vc_bvType(vc, 32);

  // Determine whether the following equations are satisfiable:
  //   v + 4 = n
  //   4 = n

  // Construct variable n
  Expr n = vc_varExpr(vc, "n", bv32);

  // Construct v + 4
  Expr v = vc_varExpr(vc, "v", bv32);
  Expr ct_4 = vc_bvConstExprFromInt(vc, 32, 4);
  Expr add_v_4 = vc_bvPlusExpr(vc, 32, v, ct_4);

  // Because numbers are represented as bit vectors,
  // addition can roll over.  So construct a constraint
  // expresses that v+4 does not overflow the bounds:
  //   v + 4 >= v
  //
  Expr ge = vc_bvGeExpr(vc, add_v_4, v);

  // Push a new context
  printf("Push\n");
  vc_push(vc);

  // Assert v + 4 = n
  printf("Assert v + 4 = n\n");
  Expr f_add = vc_eqExpr(vc, add_v_4, n);
  vc_assertFormula(vc, f_add);
  vc_printExpr(vc, f_add);
  printf("\n------\n");

  // Assert the bounds constraint
  printf("Assert v + 4 >= v\n");
  vc_assertFormula(vc, ge);
  vc_printExpr(vc, ge);
  printf("\n------\n");

  // Assert 4 = n
  printf("Assert 4 = n\n");
  Expr f_numeq = vc_eqExpr(vc, ct_4, n);
  vc_assertFormula(vc, f_numeq);
  vc_printExpr(vc, f_numeq);
  printf("\n------\n");

  // Check for satisfiability
  printf("Check\n");
  vc_printAsserts(vc);
  printf("\n------\n");
  int query = vc_query(vc, vc_falseExpr(vc));
  ASSERT_EQ(query, 0);

  // Pop context
  printf("Pop\n");
  vc_pop(vc);

  printf("query = %d\n", query);
}

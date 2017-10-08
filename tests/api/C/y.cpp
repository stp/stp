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

// FIXME: This test name sucks!
TEST(y, one)
{
  VC vc = vc_createValidityChecker();
  //vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  //vc_setFlags(vc, 'p');

  Expr nresp1 = vc_varExpr(vc, "nresp1", vc_bv32Type(vc));
  Expr packet_get_int0 = vc_varExpr(vc, "packet_get_int0", vc_bv32Type(vc));
  Expr exprs[] = {// nresp1 == packet_get_int0
                  vc_eqExpr(vc, nresp1, packet_get_int0),
                  // nresp1 > 0
                  vc_bvGtExpr(vc, nresp1, vc_bv32ConstExprFromInt(vc, 0))};

  Expr res = vc_andExprN(vc, exprs, sizeof(exprs) / sizeof(exprs[0]));
  vc_printExpr(vc, res);

  int query = vc_query(vc, res);
  ASSERT_FALSE(query);
  vc_printCounterExample(vc);

  //Expr counter_example = vc_getCounterExample(vc, res);
  //vc_printExpr(vc, counter_example);
  vc_Destroy(vc);
}

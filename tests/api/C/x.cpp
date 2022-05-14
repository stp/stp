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

// FIXME: this test name sucks!
TEST(x, one)
{
  VC vc = vc_createValidityChecker();
  //vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  //vc_setFlags(vc, 'p');

  Expr nresp1 = vc_varExpr(vc, "nresp1", vc_bv32Type(vc));
  Expr packet_get_int0 = vc_varExpr(vc, "packet_get_int0", vc_bv32Type(vc));
  Expr sz = vc_varExpr(vc, "sz", vc_bv32Type(vc));

  Expr d0, d1, d2;
  Expr exprs[] = {
      // nresp1 == packet_get_int0
      vc_eqExpr(vc, nresp1, packet_get_int0),

      // nresp1 > 0
      vc_bvGtExpr(vc, nresp1, vc_bv32ConstExprFromInt(vc, 0)),

      // sz == nresp1 * 4
      vc_eqExpr(
          vc, sz,
          d0 = vc_bv32MultExpr(vc, nresp1, vc_bv32ConstExprFromInt(vc, 4))),

      // sz > nresp1 || sz < 0
      vc_orExpr(vc, d1 = vc_sbvGeExpr(vc, sz, nresp1),
                d2 = vc_sbvLtExpr(vc, sz, vc_bv32ConstExprFromInt(vc, 0))),
  };

  Expr res = vc_andExprN(vc, exprs, sizeof(exprs) / sizeof(exprs[0]));
  // vc_printExpr(vc, res);
  int query = vc_query(vc, res);
  ASSERT_FALSE(query);

  vc_DeleteExpr(nresp1);
  vc_DeleteExpr(packet_get_int0);
  vc_DeleteExpr(sz);

  vc_DeleteExpr(d0);
  vc_DeleteExpr(d1);
  vc_DeleteExpr(d2);

  vc_DeleteExpr(exprs[0]);
  vc_DeleteExpr(exprs[1]);
  vc_DeleteExpr(exprs[2]);
  vc_DeleteExpr(exprs[3]);
  vc_DeleteExpr(res);

  vc_Destroy(vc);
}

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
#include <stdio.h>

void go(enum ifaceflag_t f)
{
  VC vc;

  vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, f, 0);
  // vc_setFlags(vc,'s',0);

  // CVC_FILE is a macro that expands to a file path
  vc_parseExpr(vc, CVC_FILE);

  Expr a = vc_varExpr(vc, "a", vc_bvType(vc, 8));
  Expr ct_0 = vc_bvConstExprFromInt(vc, 8, 0);

  Expr a_eq_0 = vc_eqExpr(vc, a, ct_0);

  int query = vc_query(vc, a_eq_0);
  ASSERT_FALSE(query);
  vc_Destroy(vc);
}

TEST(stp_test, SMS)
{
  go(SMS);
}

TEST(stp_test, MS)
{
  go(MS);
}

TEST(stp_test, MSP)
{
  go(MSP);
}

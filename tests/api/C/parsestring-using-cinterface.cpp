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

TEST(parse_string, CVC)
{
  VC vc = vc_createValidityChecker();
  //vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  //vc_setFlags(vc, 'p');

  Expr q;
  Expr asserts;

  const char* s = "QUERY BVMOD(2,0bin10,0bin10) = 0bin00;\n";

  vc_parseMemExpr(vc, s, &q, &asserts);

  vc_printExpr(vc, q);
  vc_printExpr(vc, asserts);
  printf("\n");

  vc_DeleteExpr(q);
  vc_DeleteExpr(asserts);
  vc_Destroy(vc);
  // FIXME: Actually test something
  // ASSERT_TRUE(false && "FIXME: Actually test something");
}

TEST(parse_string, SMT)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  vc_setFlags(vc, 'p');
  vc_setFlags(vc, 'm');

  Expr q;
  Expr asserts;

  const char* s = "(benchmark fg.smt\n"
                  ":logic QF_AUFBV\n"
                  ":extrafuns ((x_32 BitVec[32]))\n"
                  ":extrafuns ((y32 BitVec[32]))\n"
                  ":assumption true\n)\n";

  vc_parseMemExpr(vc, s, &q, &asserts);

  vc_printExpr(vc, q);
  vc_printExpr(vc, asserts);
  printf("\n");

  vc_DeleteExpr(q);
  vc_DeleteExpr(asserts);
  vc_Destroy(vc);
  // FIXME: Actually test something
  // ASSERT_TRUE(false && "FIXME: Actually test something");
}

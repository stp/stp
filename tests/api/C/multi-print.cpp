/***********
AUTHORS:   Michael Katelman, Vijay Ganesh, Dan Liew

BEGIN DATE: Nov, 2008

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

// g++ -I$(HOME)/stp/c_interface print.c -L$(HOME)/stp/lib -lstp -o hex

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <stdio.h>

TEST(multiprint, one)
{
  VC vc = vc_createValidityChecker();
  VC vc2 = vc_createValidityChecker();

  vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  vc_setFlags(vc, 'p');

  Expr ct_3 = vc_bvConstExprFromStr(vc, "00000000000000000000000000000011");
  vc_printExpr(vc, ct_3);
  printf("\n");

  ct_3 = vc_bvConstExprFromInt(vc, 32, 5);
  vc_printExpr(vc, ct_3);
  printf("\n");

  vc_Destroy(vc);

  vc_setFlags(vc2, 'n');
  vc_setFlags(vc2, 'd');
  vc_setFlags(vc2, 'p');

  ct_3 = vc_bvConstExprFromStr(vc2, "00000000000000000000000000000011");
  vc_printExpr(vc2, ct_3);
  printf("\n");

  ct_3 = vc_bvConstExprFromInt(vc2, 32, 5);
  vc_printExpr(vc2, ct_3);
  printf("\n");

  vc_Destroy(vc2);

  // FIXME: Actually test something
  // ASSERT_TRUE(false && "FIXME: Actually test something");
}

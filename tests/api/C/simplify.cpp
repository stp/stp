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

/* g++ -I/home/vganesh/stp/c_interface simplify.c -L/home/vganesh/stp/lib -lstp
 * -g */

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <stdio.h>
#include <stdlib.h>

TEST(simplify, one)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  vc_setFlags(vc, 'p');

  Expr a = vc_bvCreateMemoryArray(vc, "a");
  Expr index_3 = vc_bvConstExprFromInt(vc, 32, 3);
  Expr a_of_0 = vc_readExpr(vc, a, index_3);
  for (int i = 2; i >= 0; i--) {
    a_of_0 = vc_bvConcatExpr(
        vc, a_of_0, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 32, i)));
  }
  Expr cast_32_to_8 = vc_bvExtract(vc, a_of_0, 7, 0);
  Expr cast_8_to_32 = vc_bvSignExtend(vc, cast_32_to_8, 32);
  vc_printExpr(vc, cast_8_to_32);
  vc_Destroy(vc);
  // FIXME: Actually test something
  // ASSERT_TRUE(false && "FIXME: Actually test something");
}

TEST(simplify, two)
{
  for (int j = 0; j < 3; j++)
  {
    VC vc = vc_createValidityChecker();
    vc_setFlags(vc, 'n');
    vc_setFlags(vc, 'd');
    vc_setFlags(vc, 'p');

    Expr a = vc_bvCreateMemoryArray(vc, "a");
    Expr index_3 = vc_bvConstExprFromLL(vc, 32, 3);

    Expr a_of_0 = vc_readExpr(vc, a, index_3);
    int i;
    for (i = 2; i >= 0; i--)
      a_of_0 = vc_bvConcatExpr(
          vc, a_of_0, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 32, i)));
    Expr cast_32_to_8 = vc_bvExtract(vc, a_of_0, 7, 0);
    Expr cast_8_to_32 = vc_bvSignExtend(vc, cast_32_to_8, 32);
    vc_printExpr(vc, cast_8_to_32);
    cast_8_to_32 = vc_simplify(vc, cast_8_to_32);
    vc_Destroy(vc);
  }
  // FIXME: Actually test something
  // ASSERT_TRUE(false && "FIXME: Actually test something");
}

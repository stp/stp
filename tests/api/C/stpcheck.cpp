/***********
AUTHORS:   Michael Katelman, Vijay Ganesh, Dan Liew

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

#include <gtest/gtest.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "stp/c_interface.h"

TEST(extend_adder_notexpr, one)
{

  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');

  // 8-bit variable 'x'
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));

  // 32 bit constant value 1
  Expr one = vc_bvConstExprFromInt(vc, 32, 1);

  // 24 bit constant value 0
  Expr bit24_zero = vc_bvConstExprFromInt(vc, 24, 0);
  // 32 bit constant value 0
  Expr bit32_zero = vc_bvConstExprFromInt(vc, 32, 0);

  // Extending 8-bit variable to 32-bit value
  Expr zero_concat_x = vc_bvConcatExpr(vc, bit24_zero, x);
  Expr xp1 = vc_bvPlusExpr(vc, 32, zero_concat_x, one);

  // Insteading of concat operation, I also tried with SignExtend
  // Expr signextend_x=vc_bvSignExtend(vc,x,32);
  // Expr xp1=vc_bvPlusExpr(vc,32,signextend_x,one);

  // x+1=0
  Expr eq = vc_eqExpr(vc, xp1, bit32_zero);

  // x+1!=0
  eq = vc_notExpr(vc, eq);

  int query = vc_query(vc, eq);
  ASSERT_TRUE(query);
  vc_printCounterExample(vc);
}

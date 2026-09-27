/***********
AUTHORS:  Trevor Hansen, Dan Liew, Alvin Cheung

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
#include <cassert>
#include <gtest/gtest.h>
#include <iostream>
#include <stdexcept>

// FIXME: This is a terrible name, all of the tests in this directory are
// interface tests!
TEST(interface_check, ONE)
{
  ::VC vc = vc_createValidityChecker();
  ::Expr b1 = ::vc_trueExpr(vc);
  ::Expr b2 = ::vc_falseExpr(vc);
  ::Expr andExpr = ::vc_andExpr(vc, b1, b2);

  ASSERT_TRUE(getExprKind(andExpr) == ::FALSE);

  ::Expr simplifiedExpr = ::vc_simplify(vc, andExpr);

  ASSERT_TRUE(getExprKind(simplifiedExpr) == ::FALSE);
}

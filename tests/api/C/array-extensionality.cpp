/***********
AUTHORS: Andrew V. Jones

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

// C API front end for the array-equality feature: with the 'x' flag,
// vc_eqExpr over array operands returns a fresh Boolean abstraction
// variable (the formula abstraction of Brummayer & Biere's
// lemmas-on-demand procedure for extensional arrays); with the flag
// off, the pre-existing warn-and-return-EQ behavior is preserved.

#include "stp/c_interface.h"
#include <gtest/gtest.h>

TEST(array_extensionality, equality_abstracted_to_boolean_variable)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);

  // The abstracted equality is an ordinary Boolean symbol, not an EQ
  // node.
  Expr eq = vc_eqExpr(vc, a, b);
  ASSERT_EQ(SYMBOL, getExprKind(eq));

  // Repeated requests reuse the same abstraction variable, in either
  // operand order.
  ASSERT_EQ(getExprID(eq), getExprID(vc_eqExpr(vc, a, b)));
  ASSERT_EQ(getExprID(eq), getExprID(vc_eqExpr(vc, b, a)));

  // A reflexive equality folds to true.
  ASSERT_EQ(TRUE, getExprKind(vc_eqExpr(vc, a, a)));

  vc_Destroy(vc);
}

TEST(array_extensionality, flag_off_preserves_eq_node)
{
  // Default-off: an array equality still builds an ordinary EQ node
  // (with the existing warning), exactly as before.
  VC vc = vc_createValidityChecker();

  Type bv8 = vc_bvType(vc, 8);
  Type bv4 = vc_bvType(vc, 4);
  Type arrT = vc_arrayType(vc, bv4, bv8);

  Expr a = vc_varExpr(vc, "a", arrT);
  Expr b = vc_varExpr(vc, "b", arrT);

  Expr eq = vc_eqExpr(vc, a, b);
  ASSERT_EQ(EQ, getExprKind(eq));
  vc_Destroy(vc);
}

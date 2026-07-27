/***********
AUTHORS: Andrew Teylu

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

// Array equality ('x' flag) over arrays whose index or element sorts
// are floating-point or RoundingMode, built through the C API. The
// equality operands are abstracted out of the formula when the
// equality is built, so every lowering the input formula receives
// (totalising partial operations, canonicalising float indexes,
// pinning RoundingMode reads) must also reach the recorded operands.

#include "stp/c_interface.h"
#include <gtest/gtest.h>

// (Array RoundingMode (_ FloatingPoint 5 11)): two stores at one
// RoundingMode index whose values are always =-equal floats --
// fp.min(f, x) against x where x is f converted to its own format.
// The fp.min inside the abstracted operand used to reach the float
// blaster without its totalised third child and abort the solve.
TEST(fp_array_extensionality, rm_indexed_equal_stores_sat)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Type rm = vc_fpRoundingModeType(vc);
  Type fp = vc_fpType(vc, 5, 11);
  Type arr = vc_arrayType(vc, rm, fp);

  Expr a = vc_varExpr(vc, "a", arr);
  Expr r = vc_fpRoundingModeVar(vc, "r");
  Expr f = vc_varExpr(vc, "f", fp);
  Expr tofp = vc_fpToFPFromFP(vc, 5, 11, r, f);
  Expr mn = vc_fpMinExpr(vc, f, tofp);
  Expr s1 = vc_writeExpr(vc, a, r, mn);
  Expr s2 = vc_writeExpr(vc, s1, r, tofp);

  vc_assertFormula(vc, vc_eqExpr(vc, s1, s2));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// The negation of the same equality is unsatisfiable: a same-format
// conversion is the identity on values, fp.min of a value with itself
// is that value, so the two stores agree at the written index and
// share the base everywhere else.
TEST(fp_array_extensionality, rm_indexed_equal_stores_distinct_unsat)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x');

  Type rm = vc_fpRoundingModeType(vc);
  Type fp = vc_fpType(vc, 5, 11);
  Type arr = vc_arrayType(vc, rm, fp);

  Expr a = vc_varExpr(vc, "a", arr);
  Expr r = vc_fpRoundingModeVar(vc, "r");
  Expr f = vc_varExpr(vc, "f", fp);
  Expr tofp = vc_fpToFPFromFP(vc, 5, 11, r, f);
  Expr mn = vc_fpMinExpr(vc, f, tofp);
  Expr s1 = vc_writeExpr(vc, a, r, mn);
  Expr s2 = vc_writeExpr(vc, s1, r, tofp);

  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, s1, s2)));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

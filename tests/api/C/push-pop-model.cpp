/***********
AUTHORS: Andrew Teylu

BEGIN DATE: Aug, 2026

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

// The C API's counterexample lifetime contract, as its idiomatic usage
// (push / query / pop, then read the model) depends on it:
//
//   - the counterexample describes the last vc_query and SURVIVES vc_pop;
//   - the next vc_push or vc_query discards it.
//
// This is deliberately different from the SMT-LIB frontend, where a pop
// invalidates the model. See vc_pop's documentation in c_interface.h.
TEST(push_pop_model, counterexample_survives_pop_until_next_query)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'c');
  vc_setFlags(vc, 'd');

  Type bv8 = vc_bvType(vc, 8);
  Expr x = vc_varExpr(vc, "x", bv8);
  Expr y = vc_varExpr(vc, "y", bv8);

  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 5)));

  // The classic bracket: push, query, pop -- then read the model.
  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, y, vc_bvConstExprFromInt(vc, 8, 7)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  // Both values are still readable after the pop.
  EXPECT_EQ(5ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, x)));
  EXPECT_EQ(7ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, y)));

  // A new bracket replaces the model wholesale.
  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, y, vc_bvConstExprFromInt(vc, 8, 9)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  EXPECT_EQ(5ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, x)));
  EXPECT_EQ(9ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, y)));

  vc_Destroy(vc);
}


/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
 *
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
********************************************************************/

// libstp2-fidelity.cpp -- 2.x behaviours libstp2 once got wrong.
//
// The 2.x suites in this directory run against libstp2 unchanged; the cases
// here pin what they did not reach, each against what 2.x itself did.

#include "stp/c_interface.h"

#include <gtest/gtest.h>

#include <cstdlib>
#include <string>

namespace
{

std::string text_of(Expr e)
{
  char* s = exprString(e);
  std::string out = s != nullptr ? s : "";
  std::free(s);
  return out;
}

// vc_parseMemExpr hands back the ASSERTs and the QUERY apart, asserting only
// the former. The query here is not valid, so neither it nor FALSE may come
// out valid after the parse.
TEST(libstp2_fidelity, a_parsed_query_that_is_not_valid_stays_so)
{
  VC vc = vc_createValidityChecker();
  Expr query = nullptr, asserts = nullptr;
  ASSERT_EQ(1, vc_parseMemExpr(vc, "x : BITVECTOR(8); ASSERT(x = 0hex01); QUERY x = 0hex02;", &query,
                               &asserts));
  EXPECT_NE(std::string::npos, text_of(asserts).find("0x01")) << text_of(asserts);
  EXPECT_EQ(std::string::npos, text_of(asserts).find("FALSE")) << text_of(asserts);
  EXPECT_EQ(0, vc_query(vc, query));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_DeleteExpr(query);
  vc_DeleteExpr(asserts);
  vc_Destroy(vc);
}

// vc_paramBoolExpr names its variable after the application as 2.x printed
// it, so a one-bit and a four-bit parameter of one value name two variables.
TEST(libstp2_fidelity, parameters_of_two_widths_name_two_variables)
{
  VC vc = vc_createValidityChecker();
  Expr p = vc_varExpr1(vc, "p", 0, 0);
  Expr one_bit = vc_paramBoolExpr(vc, p, vc_bvConstExprFromInt(vc, 1, 1));
  Expr four_bit = vc_paramBoolExpr(vc, p, vc_bvConstExprFromInt(vc, 4, 1));
  EXPECT_EQ("p (0b1 ) ", text_of(one_bit));
  EXPECT_EQ("p (0x1 ) ", text_of(four_bit));
  EXPECT_EQ(0, vc_query(vc, vc_iffExpr(vc, one_bit, four_bit)));
  // the same parameter names the same variable
  Expr again = vc_paramBoolExpr(vc, p, vc_bvConstExprFromInt(vc, 1, 1));
  EXPECT_EQ(1, vc_query(vc, vc_iffExpr(vc, one_bit, again)));
  vc_Destroy(vc);
}

std::string g_fatal;

// A whole counterexample answers for a symbol and for a cell of an array
// symbol the model has, as 2.x's map did, and hands any other term back as
// it is: a term built after the check is not evaluated against it.
TEST(libstp2_fidelity, a_whole_counterexample_hands_back_what_it_does_not_record)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr1(vc, "x", 0, 8);
  Expr y = vc_varExpr1(vc, "y", 0, 8);
  Expr a = vc_varExpr1(vc, "a", 8, 8);
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromInt(vc, 8, 7)));
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 8, 3)),
                                 vc_bvConstExprFromInt(vc, 8, 9)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  WholeCounterExample m = vc_getWholeCounterExample(vc);
  Expr x_value = vc_getTermFromCounterExample(vc, x, m);
  Expr y_value = vc_getTermFromCounterExample(vc, y, m); // left out: zero
  Expr cell = vc_getTermFromCounterExample(vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 8, 3)), m);
  Expr no_cell = vc_getTermFromCounterExample(vc, vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 8, 4)), m);
  Expr sum = vc_getTermFromCounterExample(vc, vc_bvPlusExpr(vc, 8, x, vc_bvConstExprFromInt(vc, 8, 1)), m);
  EXPECT_EQ(7, getBVInt(x_value));
  EXPECT_EQ(0, getBVInt(y_value));
  EXPECT_EQ(9, getBVInt(cell));
  EXPECT_EQ(READ, getExprKind(no_cell));
  EXPECT_EQ(BVPLUS, getExprKind(sum));
  // a Boolean that is not a variable is refused, as 2.x refused it
  vc_registerErrorHandler([](const char* msg) { g_fatal = msg; });
  vc_setErrorPolicy(STP_ON_ERROR_RETURN);
  EXPECT_EQ(nullptr, vc_getTermFromCounterExample(vc, vc_eqExpr(vc, x, y), m));
  vc_setErrorPolicy(STP_ON_ERROR_ABORT);
  vc_registerErrorHandler(nullptr);
  EXPECT_NE(std::string::npos, g_fatal.find("propositional variables")) << g_fatal;
  for (Expr e : {x_value, y_value, cell, no_cell, sum})
    vc_DeleteExpr(e);
  vc_deleteWholeCounterExample(m);
  vc_Destroy(vc);
}

// A Real term's counterexample value is the exact Real model's, and an
// assertion or a declaration since the query leaves that model none.
TEST(libstp2_fidelity, a_stale_real_model_has_no_counterexample_value)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_realType(vc));
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_realConstExprFromStr(vc, "1")));
  for (int stale = 0; stale < 2; ++stale)
  {
    ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
    Expr v = vc_getCounterExample(vc, x);
    ASSERT_NE(nullptr, v);
    EXPECT_EQ(REAL_CONST, getExprKind(v));
    vc_DeleteExpr(v);
    if (stale == 0)
      vc_assertFormula(vc, vc_trueExpr(vc));
    else
      vc_varExpr(vc, "y", vc_realType(vc));
    EXPECT_EQ(0, vc_hasRealModelValue(vc, x));
    EXPECT_EQ(nullptr, vc_getCounterExample(vc, x));
  }
  vc_Destroy(vc);
}

} // namespace

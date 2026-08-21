/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

// Why the last query had no answer, from the C API.
//
// vc_query reports a query it could not decide as 3 whatever stopped it, and
// that is the one verdict every way of giving up carries: a caller that only
// wants to know whether there is an answer has one test to make. Which cause
// it was is a separate question, and an SMT-LIB2 caller could already ask it
// through (get-info :reason-unknown) while a caller driving STP through vc_*
// could not -- it was told "3" for a budget no clock was involved in, with no
// way to find out which.
//
// So the record SMT-LIB2 reads is readable here too: vc_getReasonUnknown for
// the cause, vc_getReasonUnknownToBuffer for the sentence behind it.
#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <cstdlib>
#include <string>

namespace
{
// A real factorisation, zero-extended so the product cannot wrap: modular
// multiplication would make it trivially satisfiable and no budget would bind.
void assertFactoring(VC vc)
{
  Type bv = vc_bvType(vc, 32);
  Expr x = vc_varExpr(vc, "x", bv);
  Expr y = vc_varExpr(vc, "y", bv);
  Expr wide_x = vc_bvConcatExpr(vc, vc_bvConstExprFromInt(vc, 32, 0), x);
  Expr wide_y = vc_bvConcatExpr(vc, vc_bvConstExprFromInt(vc, 32, 0), y);
  vc_assertFormula(
      vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 64, wide_x, wide_y),
                    vc_bvConstExprFromLL(vc, 64, 0x7ffffffc80000005ULL)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, x, vc_bvConstExprFromInt(vc, 32, 1)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, y, vc_bvConstExprFromInt(vc, 32, 1)));
}

std::string detail(VC vc)
{
  char* buf = NULL;
  size_t len = 0;
  vc_getReasonUnknownToBuffer(vc, &buf, &len);
  EXPECT_NE(nullptr, buf);
  EXPECT_EQ(strlen(buf) + 1, len);
  const std::string out(buf);
  free(buf);
  return out;
}
} // namespace

// Nothing to explain while there is an answer, and the record describes the
// last query rather than the session.
TEST(reason_unknown, AnAnsweredQueryHasNoReason)
{
  VC vc = vc_createValidityChecker();
  EXPECT_EQ(REASON_UNKNOWN_NONE, vc_getReasonUnknown(vc));
  EXPECT_EQ("", detail(vc));

  assertFactoring(vc);
  ASSERT_EQ(0, vc_query_with_timeout(vc, vc_falseExpr(vc), -1, -1));
  EXPECT_EQ(REASON_UNKNOWN_NONE, vc_getReasonUnknown(vc));
  EXPECT_EQ("", detail(vc));
  vc_Destroy(vc);
}

// The two the SAT solver enforces keep the verdict they had. They share it, so
// the verdict alone cannot separate them -- which is what the reason is for:
// the clock may pass with more time on the same machine, the conflict budget
// is deterministic and will not.
TEST(reason_unknown, TheClockAndTheConflictBudgetAreToldApartByTheReason)
{
  VC clock = vc_createValidityChecker();
  assertFactoring(clock);
  EXPECT_EQ(3, vc_query_with_timeout(clock, vc_falseExpr(clock), -1, 0));
  EXPECT_EQ(REASON_UNKNOWN_TIMEOUT, vc_getReasonUnknown(clock));
  vc_Destroy(clock);

  VC conflicts = vc_createValidityChecker();
  assertFactoring(conflicts);
  EXPECT_EQ(3, vc_query_with_timeout(conflicts, vc_falseExpr(conflicts), 0, -1));
  EXPECT_EQ(REASON_UNKNOWN_CONFLICT_BUDGET, vc_getReasonUnknown(conflicts));
  vc_Destroy(conflicts);
}

// The AIG budget is neither of those two, so the clock's name is not what it
// reports: it is an encoding STP abandoned, and the sentence behind the value
// names the flag and the count it stopped at -- which the value alone cannot.
TEST(reason_unknown, TheAigBudgetIsNotReportedAsAClock)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, 50);
  assertFactoring(vc);
  EXPECT_EQ(3, vc_query_with_timeout(vc, vc_falseExpr(vc), -1, -1));
  EXPECT_EQ(REASON_UNKNOWN_INCOMPLETE, vc_getReasonUnknown(vc));

  const std::string why = detail(vc);
  EXPECT_NE(std::string::npos, why.find("--aig-node-budget")) << why;
  EXPECT_NE(std::string::npos, why.find("50")) << why;
  vc_Destroy(vc);
}

// Same query, no limit: decided. So the no-answer above is the budget
// speaking and not the query being hard.
TEST(reason_unknown, WithoutTheBudgetTheSameQueryIsDecided)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, AIG_NODE_BUDGET, -1);
  assertFactoring(vc);
  EXPECT_EQ(0, vc_query_with_timeout(vc, vc_falseExpr(vc), -1, -1));
  EXPECT_EQ(REASON_UNKNOWN_NONE, vc_getReasonUnknown(vc));
  vc_Destroy(vc);
}

// The one cause on this list that names a flag of this interface, and the one
// a caller should never see. UF_EQUALITY_INJECTIVITY asserts that
// equality-only uninterpreted functions are injective, which the query did not
// say and which can only remove models. An `unsat` over it therefore refutes
// the query with an assumption on top of it -- not the query -- and there was
// a time when vc_query reported exactly that as 1.
//
// It does not any more, and not by withholding the answer either: the
// assumption is installed behind an activation literal the search holds, so
// STP can ask whether the refutation used it and take it back when it did.
// The query below is satisfiable, plainly -- three pairwise-distinct two-bit
// arguments to a function into one bit, asserting that two of the three
// results collide, which three values into two must. So the answer is 0 with
// the flag and 0 without it, and REASON_UNKNOWN_ASSUMED_INJECTIVITY stays a
// value the header explains rather than one this returns.
namespace
{
void assertPigeonhole(VC vc)
{
  vc_setFlag(vc, 'u');
  Type bv2 = vc_bvType(vc, 2);
  Type bv1 = vc_bvType(vc, 1);
  const UFDeclHandle f =
      vc_declareUninterpretedFunction(vc, "f", &bv2, 1, bv1);
  EXPECT_NE(0u, f);

  Expr a = vc_varExpr(vc, "a", bv2);
  Expr b = vc_varExpr(vc, "b", bv2);
  Expr c = vc_varExpr(vc, "c", bv2);
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, a, b)));
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, b, c)));
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, a, c)));

  Expr fa = vc_applyUninterpretedFunction(vc, f, &a, 1);
  Expr fb = vc_applyUninterpretedFunction(vc, f, &b, 1);
  Expr fc = vc_applyUninterpretedFunction(vc, f, &c, 1);
  vc_assertFormula(
      vc, vc_orExpr(vc, vc_eqExpr(vc, fa, fb),
                    vc_orExpr(vc, vc_eqExpr(vc, fb, fc),
                              vc_eqExpr(vc, fa, fc))));
}
} // namespace

TEST(reason_unknown, AnAssumedInjectivityIsRetractedRatherThanReported)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, UF_EQUALITY_INJECTIVITY, 1);
  assertPigeonhole(vc);

  EXPECT_EQ(0, vc_query_with_timeout(vc, vc_falseExpr(vc), -1, -1));
  EXPECT_EQ(REASON_UNKNOWN_NONE, vc_getReasonUnknown(vc));
  EXPECT_EQ("", detail(vc));
  vc_Destroy(vc);
}

// Same query, flag clear. Equal to the above is the entire point: the flag is
// a search hint, and a hint that changed the answer would not be one.
TEST(reason_unknown, TheSameQueryAnswersTheSameWithoutTheAssumption)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, UF_EQUALITY_INJECTIVITY, 0);
  assertPigeonhole(vc);

  EXPECT_EQ(0, vc_query_with_timeout(vc, vc_falseExpr(vc), -1, -1));
  EXPECT_EQ(REASON_UNKNOWN_NONE, vc_getReasonUnknown(vc));
  vc_Destroy(vc);
}

// And an unsatisfiable query with the assumption installed over it keeps its
// refutation. Taking an answer back on the assumption's account is the cost of
// the rule; taking one back that the assumption had nothing to do with would
// be the rule quietly failing to be a search hint.
TEST(reason_unknown, AnUnsatisfiableQueryKeepsItsRefutationUnderTheAssumption)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, UF_EQUALITY_INJECTIVITY, 1);
  vc_setFlag(vc, 'u');
  Type bv4 = vc_bvType(vc, 4);
  const UFDeclHandle g =
      vc_declareUninterpretedFunction(vc, "g", &bv4, 1, bv4);
  EXPECT_NE(0u, g);

  Expr p = vc_varExpr(vc, "p", bv4);
  Expr q = vc_varExpr(vc, "q", bv4);
  Expr gp = vc_applyUninterpretedFunction(vc, g, &p, 1);
  Expr gq = vc_applyUninterpretedFunction(vc, g, &q, 1);
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, gp, gq)));
  vc_assertFormula(vc, vc_eqExpr(vc, p, q));

  EXPECT_EQ(1, vc_query_with_timeout(vc, vc_falseExpr(vc), -1, -1));
  EXPECT_EQ(REASON_UNKNOWN_NONE, vc_getReasonUnknown(vc));
  vc_Destroy(vc);
}

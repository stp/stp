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

// An addition of three or more operands, and the counters that say what the
// abstraction did with it.
//
// BVPLUS is n-ary, and Flatten folds every chain of additions into one such
// node, so an addition written a + b + c arrives at the bit-blaster as a
// single node of degree three however it was built. The term abstraction
// takes two operands, so before this it declined every one of them: which
// additions got abstracted was decided by the arity the front end happened to
// produce rather than by the width floor that is meant to decide it. They are
// lowered to genuine two-operand nodes first now, as BVMULT already was.
//
// The counters are the other half: a caller that turns an abstraction on and
// sees nothing abstracted cannot tell a flag that reached no eligible
// operation from a flag that is broken, so the candidate count -- what the
// abstraction was offered -- is kept alongside what it took, and both are
// readable through vc_getCounter.
#include "stp/c_interface.h"
#include <gtest/gtest.h>

namespace
{
// A satisfiable query that preprocessing cannot settle: the product pins both
// factors, so nothing is unconstrained and the bit-blaster actually runs. The
// sum is an operand of that product rather than equated to a constant, which
// is what keeps a substitution from removing it before bit-blasting.
VC checkerOverANAryAddition(int abstraction)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, abstraction);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION_PLUS, abstraction);
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, abstraction);
  // Every operand qualifies, so the arity is the only thing under test here.
  vc_setInterfaceFlags(vc, BV_ABSTRACTION_WIDTH, 1);

  Type bv = vc_bvType(vc, 32);
  Expr a = vc_varExpr(vc, "a", bv);
  Expr b = vc_varExpr(vc, "b", bv);
  Expr c = vc_varExpr(vc, "c", bv);
  Expr operands[3] = {a, b, c};
  Expr sum = vc_bvPlusExprN(vc, 32, operands, 3);

  vc_assertFormula(vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 32, sum, a),
                                 vc_bvConstExprFromInt(vc, 32, 3037 * 3041)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, a, vc_bvConstExprFromInt(vc, 32, 1)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, b, vc_bvConstExprFromInt(vc, 32, 1)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, c, vc_bvConstExprFromInt(vc, 32, 1)));
  return vc;
}

unsigned long long counter(VC vc, enum stp_counter_t c)
{
  return vc_getCounter(vc, c);
}
} // namespace

// The addition reaches the abstraction, which is what the lowering above is
// for: three operands become the two two-operand additions that the
// abstraction takes. Nothing here is about the width -- the floor is 1, so a
// declined abstraction can only be the arity.
TEST(bv_abstraction_nary_plus, AnNAryAdditionIsAbstracted)
{
  VC vc = checkerOverANAryAddition(1);
  vc_query(vc, vc_falseExpr(vc));

  EXPECT_GT(counter(vc, STP_COUNTER_QUERIES_BITBLASTED), 0u);
  EXPECT_EQ(2u, counter(vc, STP_COUNTER_BV_CANDIDATES_PLUS));
  EXPECT_EQ(2u, counter(vc, STP_COUNTER_BV_ABSTRACTED_PLUS));
  vc_Destroy(vc);
}

// With the abstraction off the same query offers the same two additions and
// none of them is taken. The candidate count is what makes a zero readable:
// it has to mean "no addition wide enough was here", not "the flag that
// lowers them was off", or a caller cannot tell the two apart -- so it counts
// what the lowering would have produced even when the lowering does not run.
TEST(bv_abstraction_nary_plus, CandidatesAreCountedWithTheAbstractionOff)
{
  VC vc = checkerOverANAryAddition(0);
  vc_query(vc, vc_falseExpr(vc));

  EXPECT_GT(counter(vc, STP_COUNTER_QUERIES_BITBLASTED), 0u);
  EXPECT_EQ(2u, counter(vc, STP_COUNTER_BV_CANDIDATES_PLUS));
  EXPECT_EQ(0u, counter(vc, STP_COUNTER_BV_ABSTRACTED_PLUS));
  vc_Destroy(vc);
}

// The abstraction is a way of searching, not a different question: the
// lowering reassociates the addition, and reassociating is sound modulo 2^n,
// so the verdict is the one the exact encoding gives.
TEST(bv_abstraction_nary_plus, TheVerdictIsTheOneTheExactEncodingGives)
{
  VC off = checkerOverANAryAddition(0);
  const int exact = vc_query(off, vc_falseExpr(off));
  vc_Destroy(off);

  VC on = checkerOverANAryAddition(1);
  const int abstracted = vc_query(on, vc_falseExpr(on));
  vc_Destroy(on);

  EXPECT_EQ(exact, abstracted);
}

// A fresh checker has done nothing, and the counters say so rather than
// carrying whatever the last one in this process reached.
TEST(bv_abstraction_nary_plus, AFreshCheckerHasCountedNothing)
{
  VC vc = vc_createValidityChecker();
  EXPECT_EQ(0u, counter(vc, STP_COUNTER_QUERIES_BITBLASTED));
  EXPECT_EQ(0u, counter(vc, STP_COUNTER_BV_CANDIDATES_PLUS));
  EXPECT_EQ(0u, counter(vc, STP_COUNTER_BV_ABSTRACTED_PLUS));
  EXPECT_EQ(0u, counter(vc, STP_COUNTER_BV_REFINEMENT_ROUNDS));
  EXPECT_EQ(0u, counter(vc, STP_COUNTER_UF_APPLICATIONS_LOWERED));
  vc_Destroy(vc);
}

// The persistent driver bit-blasts through a BitBlaster of its own, so a
// denominator taken only from the batch pipeline reads zero for a session
// that never uses it -- and an engagement rate over a zero denominator is
// worse than no rate at all.
TEST(bv_abstraction_nary_plus, TheIncrementalRouteCountsItsBitBlasting)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
  vc_setInterfaceFlags(vc, BV_ABSTRACTION_WIDTH, 1);

  Type bv = vc_bvType(vc, 32);
  Expr a = vc_varExpr(vc, "a", bv);
  Expr b = vc_varExpr(vc, "b", bv);
  Expr c = vc_varExpr(vc, "c", bv);
  Expr operands[3] = {a, b, c};
  Expr sum = vc_bvPlusExprN(vc, 32, operands, 3);
  vc_assertFormula(vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 32, sum, a),
                                 vc_bvConstExprFromInt(vc, 32, 3037 * 3041)));
  vc_assertFormula(vc, vc_bvGtExpr(vc, a, vc_bvConstExprFromInt(vc, 32, 1)));
  vc_query(vc, vc_falseExpr(vc));

  EXPECT_GT(counter(vc, STP_COUNTER_QUERIES_BITBLASTED), 0u);
  vc_Destroy(vc);
}

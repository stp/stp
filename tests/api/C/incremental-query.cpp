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

// The C API on the incremental driver. A session becomes incremental at
// its first vc_push (or with vc_setFlags 'i'), the driver engages from the
// second vc_query, and vc_query's negated query rides along as a
// retractable assumption -- so these tests answer many queries on one VC
// and every answer after the first exercises the persistent solver.

// The classic bracket, over rounds whose verdicts alternate: retraction of
// both the pushed level and the previous query's negation must be real.
TEST(incremental_query, brackets_alternate_verdicts)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'c');
  vc_setFlags(vc, 'd');

  Type bv8 = vc_bvType(vc, 8);
  Expr x = vc_varExpr(vc, "x", bv8);
  Expr five = vc_bvConstExprFromInt(vc, 8, 5);
  Expr six = vc_bvConstExprFromInt(vc, 8, 6);

  vc_assertFormula(vc, vc_eqExpr(vc, x, five));

  // x = 5 entails x = 5: valid.
  vc_push(vc);
  EXPECT_EQ(1, vc_query(vc, vc_eqExpr(vc, x, five)));
  vc_pop(vc);

  // x = 5 refutes x = 6: invalid, with a counterexample. A stuck negated
  // query from the previous round would make the assertions unsatisfiable
  // and everything vacuously valid -- this is the retraction pin.
  vc_push(vc);
  EXPECT_EQ(0, vc_query(vc, vc_eqExpr(vc, x, six)));
  vc_pop(vc);
  EXPECT_EQ(5ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, x)));

  // A pushed contradiction makes anything valid, and dies with its level.
  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, x, six));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  vc_push(vc);
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  vc_Destroy(vc);
}

// Arrays through the C API: read congruence needs the driver's refinement
// loop, across several queries on one solver.
TEST(incremental_query, arrays_refine_across_queries)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'c');
  vc_setFlags(vc, 'd');

  Type bv8 = vc_bvType(vc, 8);
  Type arr = vc_arrayType(vc, bv8, bv8);
  Expr a = vc_varExpr(vc, "a", arr);
  Expr i = vc_varExpr(vc, "i", bv8);
  Expr j = vc_varExpr(vc, "j", bv8);
  Expr one = vc_bvConstExprFromInt(vc, 8, 1);
  Expr two = vc_bvConstExprFromInt(vc, 8, 2);

  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, i), one));

  // a[i]=1, a[j]=2 and i=j contradict: the query "false" is valid.
  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, j), two));
  vc_assertFormula(vc, vc_eqExpr(vc, i, j));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  // With distinct indices the same reads are satisfiable again.
  vc_push(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, vc_readExpr(vc, a, j), two));
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, i, j)));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  // Write shadowing, still on the same persistent solver.
  vc_push(vc);
  Expr stored = vc_writeExpr(vc, a, i, two);
  EXPECT_EQ(1, vc_query(vc, vc_eqExpr(vc, vc_readExpr(vc, stored, i), two)));
  vc_pop(vc);

  vc_Destroy(vc);
}

// vc_setFlags 'i' engages the driver from the very first query, without
// any vc_push in the session.
TEST(incremental_query, flag_i_without_push)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'i');
  vc_setFlags(vc, 'c');
  vc_setFlags(vc, 'd');

  Type bv8 = vc_bvType(vc, 8);
  Expr x = vc_varExpr(vc, "x", bv8);
  Expr five = vc_bvConstExprFromInt(vc, 8, 5);

  vc_assertFormula(vc, vc_bvLtExpr(vc, x, five));

  // x < 5 (unsigned) does not entail x = 4...
  EXPECT_EQ(0, vc_query(vc, vc_eqExpr(vc, x,
                                      vc_bvConstExprFromInt(vc, 8, 4))));
  // ...but does entail x < 6, on the same solver, one query later.
  EXPECT_EQ(1, vc_query(vc, vc_bvLtExpr(vc, x,
                                        vc_bvConstExprFromInt(vc, 8, 6))));

  vc_Destroy(vc);
}

// Parse-time inlining of chained define-funs builds formulas tens of
// thousands of levels deep out of flat input (a 27k-define CPAchecker
// benchmark reaches depth ~25k); this loop builds the same shape
// directly. The driver's word-level passes walk such nodes by recursion,
// so the check-sat must run on the large-stack worker -- on a default
// stack this query dies of stack overflow before the solver ever sees a
// clause. The kinds must alternate: a same-kind chain is flattened wide
// at construction and never gets deep.
TEST(incremental_query, deep_alternating_chain)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'i');

  Expr chain = vc_varExpr(vc, "x0", vc_boolType(vc));
  for (int i = 1; i < 120000; i++)
  {
    char name[32];
    snprintf(name, sizeof name, "x%d", i);
    Expr v = vc_varExpr(vc, name, vc_boolType(vc));
    chain = (i % 2) ? vc_orExpr(vc, v, chain) : vc_andExpr(vc, v, chain);
  }
  vc_assertFormula(vc, chain);

  // Satisfiable -- every variable true -- so it does not entail false.
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// CBP adoption rewrites a ctx-substituted conjunct under the engine's
// fixings, and hash-consing can REBUILD the raw inner AND the feed fixed
// TRUE -- a node the original conjunct no longer contained, so the
// pinning-fact walk asserted nothing for it and the inner conjuncts
// (here the definer and the sdiv comparison) silently left the encoding.
// This is murxla's shape: flag 'i', no push, everything riding the C
// API's retractable levels. The model must satisfy every raw conjunct
// -- pre-fix it returned x4=0, falsifying (bvsgt (bvsdiv x4 x4) x4),
// whose only witnesses are 0b10 and 0b11 -- and disequalities excluding
// those witnesses (invisible to the bit-level engine) must flip the
// verdict rather than stay sat against the dropped conjunct.
TEST(incremental_query, cbp_adoption_keeps_rebuilt_fixed_node_constraint)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'i');
  vc_setFlags(vc, 'c');

  Type bv1 = vc_bvType(vc, 1);
  Type bv2 = vc_bvType(vc, 2);
  Expr x0 = vc_varExpr(vc, "x0", bv2);
  Expr x2 = vc_varExpr(vc, "x2", bv1);
  Expr x3 = vc_varExpr(vc, "x3", bv1);
  Expr x4 = vc_varExpr(vc, "x4", bv2);

  // (and (and (= x2 x3) (bvsgt (bvsdiv x4 x4) x4))
  //      (bvsle (bvlshr x0 x0) x0))
  Expr inner =
      vc_andExpr(vc, vc_eqExpr(vc, x2, x3),
                 vc_sbvGtExpr(vc, vc_sbvDivExpr(vc, 2, x4, x4), x4));
  Expr outer = vc_andExpr(
      vc, inner,
      vc_sbvLeExpr(vc, vc_bvRightShiftExprExpr(vc, 2, x0, x0), x0));
  vc_assertFormula(vc, outer);

  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // The model, checked against the raw conjuncts. Two-bit signed
  // domain: 0b10 = -2, 0b11 = -1.
  const uint64_t vx0 = getBVUnsignedLongLong(vc_getCounterExample(vc, x0));
  const uint64_t vx2 = getBVUnsignedLongLong(vc_getCounterExample(vc, x2));
  const uint64_t vx3 = getBVUnsignedLongLong(vc_getCounterExample(vc, x3));
  const uint64_t vx4 = getBVUnsignedLongLong(vc_getCounterExample(vc, x4));
  const auto asSigned = [](uint64_t b) {
    return b >= 2 ? static_cast<int>(b) - 4 : static_cast<int>(b);
  };
  EXPECT_EQ(vx2, vx3);
  // SMT-LIB bvsdiv: x/x is 1 except 0/0, which is -1.
  const int sdiv = vx4 == 0 ? -1 : 1;
  EXPECT_GT(sdiv, asSigned(vx4));
  const uint64_t lshr = vx0 >= 2 ? 0 : (vx0 >> vx0) & 3;
  EXPECT_LE(asSigned(lshr), asSigned(vx0));

  // Only the sdiv conjunct refutes these; the bit-level engine learns
  // nothing from a disequality, so a dropped conjunct answers sat.
  Expr two = vc_bvConstExprFromInt(vc, 2, 2);
  Expr three = vc_bvConstExprFromInt(vc, 2, 3);
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, x4, two)));
  vc_assertFormula(vc, vc_notExpr(vc, vc_eqExpr(vc, x4, three)));
  EXPECT_EQ(1, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// The 'c' flag alone -- construct counterexamples, no self-check -- must
// keep its counterexamples through the driver. construct_counterexample
// is a direct input here with no other trace of the request, and both the
// batch pipeline's derivation and the driver's used to recompute and
// clobber it, so a 'c'-only pure bit-vector session on a release build
// read empty models (assertion builds masked it by forcing construction).
TEST(incremental_query, c_flag_alone_keeps_counterexamples)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'i');
  vc_setFlags(vc, 'c');

  Type bv8 = vc_bvType(vc, 8);
  Expr x = vc_varExpr(vc, "x", bv8);
  Expr five = vc_bvConstExprFromInt(vc, 8, 5);

  vc_assertFormula(vc, vc_eqExpr(vc, x, five));

  // Two driver rounds, each with a readable model.
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(5ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, x)));

  Expr y = vc_varExpr(vc, "y", bv8);
  vc_assertFormula(vc, vc_eqExpr(vc, y, vc_bvConstExprFromInt(vc, 8, 9)));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ(9ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, y)));
  EXPECT_EQ(5ULL, getBVUnsignedLongLong(vc_getCounterExample(vc, x)));

  vc_Destroy(vc);
}

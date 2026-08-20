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

// Reading the model value of a floating-point term the solved query never
// mentioned.
//
// The value is a function of the model, not of the assertion stack: nothing
// about a float has to be asserted for the float to have a value once the
// bit-vectors under it do. The batch driver answers such a question, and so
// does the SMT-LIB2 frontend. The incremental driver aborted the process:
//
//   Fatal Error: floating-point model evaluation has no solve encoding context
//
// out of vc_getCounterExample -- a legal C API call, with no return value to
// check and nothing an embedder could do about it.
//
// The cause was what the driver published to the model machinery rather than
// how it evaluated anything. Its floating-point encoding context is made
// lazily, on first use *during encoding*, and it installed the context only
// when it had one -- so a stack with no float in it left the model machinery
// holding NULL. NULL there already means "no solve has run", which is what
// makes it fatal; the guard gave it a second meaning, "this solve had no
// float in it", and nothing downstream could tell the two apart.
//
// So these tests pin both halves of the distinction:
//
//   * a float the query never mentioned is answered, on the routes this API
//     can reach, and answered with the same value the batch driver gives;
//     and
//   * with no solve at all there is still no model, and the question is
//     still refused rather than answered with an invented value.
//
// "the routes this API can reach" is meant literally, and the cases below say
// which is which. The fix publishes the context from four places; the C API
// reaches two of them (ordinary check-sat, and the exact-stack round an
// asserted whole-array equality forces), the two query files reach a third
// (the deferred model, which no C API entry point can ask for), and the
// fourth -- the publish inside solvePlainExactStack -- is reached by nothing
// in the tree.
//
// Two places read that published context, and the last three cases here are
// the second of them. A float term's value goes through
// requireFpEncodingContext and aborted there; an equality between
// float-indexed arrays goes through arrayEqualityIsModelDecidable, which
// reads the same field directly rather than through that accessor, and
// aborted at its own site with a message of its own. One NULL, two readers.
// Neither arm stands in for the other: a fix that satisfied the accessor by
// conjuring a context at read time -- the alternative the fix commit weighed
// and rejected, because it would answer a question with no solve behind it
// by inventing one -- passes every case above and still aborts below.
//
// Found by a Murxla campaign cross-checking STP against STP under a differing
// option vector. The float-term arm was reduced from a 143-line trace; the
// array arm arrived separately out of the same campaign, from a 69-line one.

#include "stp/c_interface.h"
#include <gtest/gtest.h>

namespace
{

// binary16 (eb=5, sb=11): 1 sign bit + 5 exponent + 10 significand.
const int EB = 5;
const int SB = 11;

// 1.0 packs as 0 01111 0000000000.
const unsigned long long ONE_BITS = 0x3C00ULL;
const unsigned long long ONE_EXPONENT = 15; // 0b01111

// The float under test: a binary16 reinterpreted out of three bit-vectors,
// two of them symbols. Symbols on purpose -- a float built only from
// constants folds at construction and never reaches the encoding the bug was
// about. `sign` and `exponent` are handed back so a caller can pin them with
// bit-vector assertions, which is a real solve with no float anywhere in it.
Expr buildFloat(VC vc, Expr* sign, Expr* exponent)
{
  *sign = vc_varExpr(vc, "s", vc_bvType(vc, 1));
  *exponent = vc_varExpr(vc, "e", vc_bvType(vc, EB));
  Expr significand = vc_bvConstExprFromLL(vc, SB - 1, 0);
  return vc_fpToFPFromIEEEBV(
      vc, EB, SB,
      vc_bvConcatExpr(vc, *sign, vc_bvConcatExpr(vc, *exponent, significand)));
}

// Pin the carrier bits to 1.0 through the bit-vectors alone, so the float has
// exactly one value in the model and the test can name it. Nothing asserted
// here mentions a float.
void assertBitsAreOne(VC vc, Expr sign, Expr exponent)
{
  vc_assertFormula(vc, vc_eqExpr(vc, sign, vc_bvConstExprFromLL(vc, 1, 0)));
  vc_assertFormula(
      vc, vc_eqExpr(vc, exponent, vc_bvConstExprFromLL(vc, EB, ONE_EXPONENT)));
}

// vc_query of `false` asserts nothing and asks for a model of the stack as it
// stands; 0 is INVALID, i.e. satisfiable.
int solve(VC vc) { return vc_query(vc, vc_falseExpr(vc)); }

// Two arrays whose *index* sort is in the floating-point theory, which is
// what the array-equality reader gates on: arrayEqualityIsModelDecidable
// asks sort.index().usesFloatingPointTheory(), and RoundingMode satisfies it.
// No Float is needed anywhere, and neither array is ever asserted about, so
// nothing here reaches the encoder.
void buildRoundingModeArrays(VC vc, Expr* a, Expr* b)
{
  const Type rm = vc_fpRoundingModeType(vc);
  const Type arr = vc_arrayType(vc, rm, rm);
  *a = vc_varExpr(vc, "a", arr);
  *b = vc_varExpr(vc, "b", arr);
}

// Four bits pinned to 3: a real solve with a forced value in it, and nothing
// in it about an array or a float. The array cases read it back alongside
// the equality so that they stay anchored to a model that exists and has
// something in it -- a change that made the solve vacuous would fail them
// rather than leave them quietly exercising nothing.
const unsigned long long ANCHOR_BITS = 3;

Expr assertAnchor(VC vc)
{
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 4));
  vc_assertFormula(vc,
                   vc_eqExpr(vc, x, vc_bvConstExprFromLL(vc, 4, ANCHOR_BITS)));
  return x;
}

} // namespace

// The reduced reproducer, as filed: incremental from the first query, nothing
// on the stack at all, and a float built and never mentioned again. The read
// is what used to abort, one call after a query that answered.
TEST(fp_model_no_fp_in_query, incremental_empty_stack_answers)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);

  ASSERT_EQ(0, solve(vc));

  Expr value = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, value);
  // Nothing constrains the sign or the exponent, so their bits are the
  // solver's to choose and the packed value is not the test's to name. The
  // significand is a constant, and the model has to carry it through.
  EXPECT_EQ((unsigned long long)0,
            getBVUnsignedLongLong(value) & ((1ULL << (SB - 1)) - 1));

  vc_Destroy(vc);
}

// The second row of the defect's table: a real solve with a real assertion
// stack, none of it floating-point. Pinning the carrier bits makes the
// float's value the test's to name -- the answer is 1.0 and nothing else.
TEST(fp_model_no_fp_in_query, incremental_bitvector_only_stack_answers)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);
  assertBitsAreOne(vc, sign, exponent);

  ASSERT_EQ(0, solve(vc));

  Expr value = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, value);
  EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(value));

  vc_Destroy(vc);
}

// The same question with the counterexample asked for explicitly. That is a
// weaker distinction than it looks: vc_createValidityChecker applies 'd' to
// every checker it hands out, so check_counterexample_flag is already set and
// every C API solve builds its model during the solve. Deferral is gated on
// that flag being clear, and no C API entry point clears it -- so the fourth
// publishing site, IncrementalSolver::buildPendingModel, is not reachable
// from this file at all. The two query files reach it (measured under a
// breakpoint: once and twice respectively), and that is where that arm of
// the fix is covered. This case pins that the extra flag does not perturb
// the answer.
TEST(fp_model_no_fp_in_query, incremental_eager_model_answers)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');
  vc_setFlag(vc, 'c'); // ask for the counterexample explicitly

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);
  assertBitsAreOne(vc, sign, exponent);

  ASSERT_EQ(0, solve(vc));

  Expr value = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, value);
  EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(value));

  vc_Destroy(vc);
}

// An asserted whole-array equality ('x') puts the driver on the exact-stack
// route, which encodes the complete active stack as one block and publishes
// the context from its own place -- IncrementalExactStack.cpp -- rather than
// the ordinary check-sat path's. The arrays are bit-vector arrays: still not
// one float in the query.
//
// The equality has to be between two array symbols. A write chain equated
// with its own base -- write(a, i, read(a, i)) = a -- reads like a better
// test and is not one: the node factory folds that shape to an equality
// between the two reads, so no ARRAY_EQ survives to the driver and the round
// takes the ordinary route with the exact-stack publish never reached. That
// is what this case did before, silently; it was confirmed here under a
// breakpoint on the publishing site, and the shape below is what reaches it.
TEST(fp_model_no_fp_in_query, incremental_exact_stack_route_answers)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Type arr = vc_arrayType(vc, vc_bvType(vc, 4), vc_bvType(vc, 8));
  Expr a = vc_varExpr(vc, "a", arr);
  Expr b = vc_varExpr(vc, "b", arr);
  // Nothing else constrains either array, so the equality is satisfiable and
  // extensionality has to decide it rather than fold it away.
  vc_assertFormula(vc, vc_eqExpr(vc, a, b));

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);
  assertBitsAreOne(vc, sign, exponent);

  ASSERT_EQ(0, solve(vc));

  Expr value = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, value);
  EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(value));

  vc_Destroy(vc);
}

// The invariant behind all of the above, asked directly: the two drivers are
// answering one question about one model, so they answer it the same way.
// The value is pinned by bit-vector assertions precisely so that "the same"
// is a property of the question and not of which unconstrained bits each
// driver's solver happened to pick.
TEST(fp_model_no_fp_in_query, incremental_agrees_with_batch)
{
  unsigned long long answers[2];

  for (int incremental = 0; incremental < 2; incremental++)
  {
    VC vc = vc_createValidityChecker();
    if (incremental)
      vc_setFlag(vc, 'i');

    Expr sign, exponent;
    Expr f = buildFloat(vc, &sign, &exponent);
    assertBitsAreOne(vc, sign, exponent);

    ASSERT_EQ(0, solve(vc));

    Expr value = vc_getCounterExample(vc, f);
    ASSERT_NE((Expr)NULL, value);
    answers[incremental] = getBVUnsignedLongLong(value);

    vc_Destroy(vc);
  }

  EXPECT_EQ(answers[0], answers[1]);
  EXPECT_EQ(ONE_BITS, answers[1]);
}

// Repeated solves over one checker: the context is per encoding epoch and the
// batch driver may install its own between rounds, so publishing it once is
// not enough. Each answer has to be the one belonging to the solve that
// produced the model being read.
TEST(fp_model_no_fp_in_query, incremental_repeated_solves_keep_answering)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);
  assertBitsAreOne(vc, sign, exponent);

  for (int round = 0; round < 3; round++)
  {
    ASSERT_EQ(0, solve(vc)) << "round " << round;
    Expr value = vc_getCounterExample(vc, f);
    ASSERT_NE((Expr)NULL, value) << "round " << round;
    EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(value)) << "round " << round;
  }

  vc_Destroy(vc);
}

// Across a scope, which is where the driver does its level bookkeeping: a
// solve inside the pushed scope and another after it is gone. Everything
// asserted at either depth is a bit-vector, so neither solve has a float in
// it and neither may refuse the float's value.
TEST(fp_model_no_fp_in_query, incremental_answers_either_side_of_a_scope)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Expr sign, exponent;
  Expr f = buildFloat(vc, &sign, &exponent);
  assertBitsAreOne(vc, sign, exponent);

  vc_push(vc);
  Expr g = vc_varExpr(vc, "g", vc_bvType(vc, 8));
  vc_assertFormula(vc, vc_eqExpr(vc, g, vc_bvConstExprFromLL(vc, 8, 3)));

  ASSERT_EQ(0, solve(vc));
  Expr inScope = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, inScope);
  EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(inScope));

  vc_pop(vc);

  ASSERT_EQ(0, solve(vc));
  Expr afterPop = vc_getCounterExample(vc, f);
  ASSERT_NE((Expr)NULL, afterPop);
  EXPECT_EQ(ONE_BITS, getBVUnsignedLongLong(afterPop));

  vc_Destroy(vc);
}

// The other half of the distinction, and the reason the fix publishes a
// context per solve rather than conjuring one at read time: with no solve
// there is no model, and a model value asked for anyway must not be invented.
//
// The abort itself is a separate defect -- a model query with no solve behind
// it should be refused through the API, not by taking the process down, and
// it reaches this same message from the same NULL. This test does not bless
// it. It pins the part that matters here: whatever that refusal is later made
// to look like, it stays a refusal.
TEST(fp_model_no_fp_in_query, no_solve_is_still_not_answered)
{
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        vc_setFlag(vc, 'i');
        Expr sign;
        Expr exponent;
        Expr f = buildFloat(vc, &sign, &exponent);
        (void)vc_getCounterExample(vc, f);
      },
      "no solve encoding context");
}

// The other reader of the same published context, and the other place the
// same NULL was fatal. Everything above asks for a float term's value and
// goes through requireFpEncodingContext; these ask whether two float-indexed
// arrays are equal, which goes through arrayEqualityIsModelDecidable -- a
// gate that reads the field directly rather than through that accessor, and
// aborted at its own site with its own message:
//
//   Fatal Error: array-equality: cannot evaluate an opaque equality over
//                float-indexed arrays that was not reachable in the most
//                recent solve
//
// Nothing here asserts anything about an array, so no float reaches the
// encoder, no context is built, and the driver published NULL -- which the
// gate read as "no solve has run" for a query that had just been solved.
//
// The answer is true because neither array is in the model at all: with no
// cells recorded against either, ArraysEqualUsingModel has no index at which
// they could disagree. That makes it the evaluator's answer rather than the
// SAT search's, which is the only reason this file names it. Nothing
// constrains these arrays, so a value the search had picked freely would not
// be the test's to pin -- the same care the float cases take by holding
// their carrier bits, arrived at from the other direction.
TEST(fp_model_no_fp_in_query, incremental_float_indexed_array_equality_answers)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Expr a, b;
  buildRoundingModeArrays(vc, &a, &b);
  Expr x = assertAnchor(vc);

  ASSERT_EQ(0, solve(vc));

  Expr anchor = vc_getCounterExample(vc, x);
  ASSERT_NE((Expr)NULL, anchor);
  ASSERT_EQ(ANCHOR_BITS, getBVUnsignedLongLong(anchor));

  Expr value = vc_getCounterExample(vc, vc_eqExpr(vc, a, b));
  ASSERT_NE((Expr)NULL, value);
  EXPECT_EQ(1, vc_isBool(value));

  vc_Destroy(vc);
}

// The campaign's own reproducer, which reaches "the solve never encoded
// them" by a different road: the arrays *are* mentioned, in an assumption
// that happens to be a tautology, so the rewriter removes it before encoding
// and they still never arrive.
//
// The case above does not depend on that rewrite and this one does, which is
// why both are here. If the rewriter ever stops folding an implication from
// a formula to itself, this case stops exercising the gate -- it would still
// pass, having encoded the arrays and built a context the honest way -- and
// the case above is what would still be covering the site.
TEST(fp_model_no_fp_in_query,
     incremental_array_equality_mentioned_but_rewritten_away)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Expr a, b;
  buildRoundingModeArrays(vc, &a, &b);
  Expr equality = vc_eqExpr(vc, a, b);
  vc_assertFormula(vc, vc_impliesExpr(vc, equality, equality));
  Expr x = assertAnchor(vc);

  ASSERT_EQ(0, solve(vc));

  Expr anchor = vc_getCounterExample(vc, x);
  ASSERT_NE((Expr)NULL, anchor);
  ASSERT_EQ(ANCHOR_BITS, getBVUnsignedLongLong(anchor));

  Expr value = vc_getCounterExample(vc, equality);
  ASSERT_NE((Expr)NULL, value);
  EXPECT_EQ(1, vc_isBool(value));

  vc_Destroy(vc);
}

// The invariant the two above are instances of, as the float cases have it:
// one question about one model, so the two drivers answer it the same way.
// The batch driver has always answered this one.
TEST(fp_model_no_fp_in_query, incremental_array_equality_agrees_with_batch)
{
  int answers[2];

  for (int incremental = 0; incremental < 2; incremental++)
  {
    VC vc = vc_createValidityChecker();
    if (incremental)
      vc_setFlag(vc, 'i');
    vc_setFlag(vc, 'x'); // must precede creation of any term

    Expr a, b;
    buildRoundingModeArrays(vc, &a, &b);
    Expr x = assertAnchor(vc);

    ASSERT_EQ(0, solve(vc)) << "incremental " << incremental;

    Expr anchor = vc_getCounterExample(vc, x);
    ASSERT_NE((Expr)NULL, anchor) << "incremental " << incremental;
    ASSERT_EQ(ANCHOR_BITS, getBVUnsignedLongLong(anchor))
        << "incremental " << incremental;

    Expr value = vc_getCounterExample(vc, vc_eqExpr(vc, a, b));
    ASSERT_NE((Expr)NULL, value) << "incremental " << incremental;
    answers[incremental] = vc_isBool(value);

    vc_Destroy(vc);
  }

  EXPECT_EQ(answers[0], answers[1]);
  EXPECT_EQ(1, answers[1]);
}

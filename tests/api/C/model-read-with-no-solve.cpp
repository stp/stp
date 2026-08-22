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

// vc_getCounterExample when no query has been run.
//
// There is no model to read, and the only honest answer is to say so. What
// the C API did instead depended on the sort asked about:
//
//   bit-vector    a value, invented out of an empty model
//   Boolean       a value, invented the same way
//   floating pt   Fatal Error -> abort(), taking the process down
//
// The first two are the worse half. A caller that reads a model it never
// asked for gets a number back with nothing to distinguish it from a real
// one, and the abort at least could not be mistaken for an answer.
//
// The SMT-LIB2 frontend has never had this: a get-value with no check-sat
// behind it answers "unsupported", because Cpp_interface::model_valid records
// whether a solve produced a model and the get-value path consults it. The C
// API reaches AbsRefine_CounterExample directly and had no equivalent, so
// what came back was whatever an empty counterexample map happened to
// evaluate to.
//
// So: refused, through the API rather than through abort(), and refused the
// same way whatever the sort. The shape of the refusal is the one this
// interface already uses for a nonfatal misuse -- a diagnostic through the
// handler vc_registerErrorHandler installs, and NULL -- which is what the
// header documents for this call, and for the sibling entry point
// vc_getUninterpretedFunctionValue.
//
// Note what is NOT being changed. A model read after a query that came back
// VALID is a different question, with a different answer: the query was
// decided, and that there is no counterexample is itself the answer. That
// path is AbsRefine_CounterExample's ValidFlag arm and it keeps its existing
// behaviour, which the last case here pins so a future narrowing of this
// refusal does not quietly swallow it.
//
// And note the one thing the refusal does not reach: a constant. It already
// is its own value, so there is nothing about it to read out of a model and
// nothing to invent, and it answers with no query behind it -- which is what
// this entry point has always done, and what reading the value of a literal
// through the bindings relies on. The cases at the end pin both sides of
// that line: what counts as a constant answers, and a term that still has to
// be evaluated does not, however much of it is constant.

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <string>

namespace
{

// The most recent diagnostic the library reported through the C API's
// handler, which is process-global; every case that installs it takes it
// back down again.
std::string lastDiagnostic;

void recordDiagnostic(const char* message)
{
  lastDiagnostic = message != NULL ? message : "";
}

// A float that has to be evaluated rather than folded: built out of a
// symbolic sign and exponent, so it is not already a constant.
Expr buildFloat(VC vc)
{
  Expr sign = vc_varExpr(vc, "s", vc_bvType(vc, 1));
  Expr exponent = vc_varExpr(vc, "e", vc_bvType(vc, 5));
  return vc_fpToFPFromIEEEBV(
      vc, 5, 11,
      vc_bvConcatExpr(vc, sign,
                      vc_bvConcatExpr(vc, exponent,
                                      vc_bvConstExprFromLL(vc, 10, 0))));
}

} // namespace

// A bit-vector, which used to come back as an invented value.
TEST(model_read_with_no_solve, bitvector_is_refused_not_invented)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));

  EXPECT_EQ((Expr)NULL, vc_getCounterExample(vc, x));

  vc_Destroy(vc);
}

// A Boolean, likewise.
TEST(model_read_with_no_solve, boolean_is_refused_not_invented)
{
  VC vc = vc_createValidityChecker();
  Expr b = vc_varExpr(vc, "b", vc_boolType(vc));

  EXPECT_EQ((Expr)NULL, vc_getCounterExample(vc, b));

  vc_Destroy(vc);
}

// A float, which used to abort. The case is an ordinary EXPECT rather than a
// death test precisely because the call has to return at all.
TEST(model_read_with_no_solve, float_is_refused_not_aborted)
{
  VC vc = vc_createValidityChecker();
  Expr f = buildFloat(vc);

  EXPECT_EQ((Expr)NULL, vc_getCounterExample(vc, f));

  vc_Destroy(vc);
}

// The other model read that was fatal with no solve behind it, and the reason
// this is not just about the sort asked for. Whether two float-indexed arrays
// are equal is decided by the model evaluator through a gate of its own, which
// reads the published encoding context directly rather than through the
// accessor the float cases above go through, and aborted at its own site with
// its own message:
//
//   Fatal Error: array-equality: cannot evaluate an opaque equality over
//                float-indexed arrays that was not reachable in the most
//                recent solve
//
// A NULL context means "no solve has run", which is exactly the state this
// refuses in, so the refusal reaches it first and the second abort site goes
// with the first.
TEST(model_read_with_no_solve, float_indexed_array_equality_is_refused_too)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'x'); // must precede creation of any term

  Type arrayOfFloat =
      vc_arrayType(vc, vc_fpType(vc, 5, 11), vc_bvType(vc, 8));
  Expr a = vc_varExpr(vc, "a", arrayOfFloat);
  Expr b = vc_varExpr(vc, "b", arrayOfFloat);

  EXPECT_EQ((Expr)NULL, vc_getCounterExample(vc, vc_eqExpr(vc, a, b)));

  vc_Destroy(vc);
}

// The incremental driver reaches the model machinery by its own route, so it
// is asked separately.
TEST(model_read_with_no_solve, incremental_is_refused_too)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  Expr f = buildFloat(vc);

  EXPECT_EQ((Expr)NULL, vc_getCounterExample(vc, x));
  EXPECT_EQ((Expr)NULL, vc_getCounterExample(vc, f));

  vc_Destroy(vc);
}

// A query that ran out of budget decided nothing, and the tables it cleared on
// the way in are not refilled -- so the model that was readable before it is
// gone, and no model has taken its place. This is the case where inventing a
// value is at its most convincing: a read here used to come back with a plain
// 0 for a variable the previous query had pinned to 7, so the answer was not
// even stale, it was made up.
//
// The budget is zero conflicts, which is a budget rather than the absence of
// one, so the give-up is decided before the search rather than by the clock.
TEST(model_read_with_no_solve, a_timed_out_query_leaves_no_model)
{
  VC vc = vc_createValidityChecker();

  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromLL(vc, 8, 7)));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  Expr before = vc_getCounterExample(vc, x);
  ASSERT_NE((Expr)NULL, before);
  ASSERT_EQ((unsigned long long)7, getBVUnsignedLongLong(before));

  // 486579698794948075013401 == 703873773913 * 691288291777, both prime; the
  // factors are held below 2^40 so the 96-bit multiply cannot wrap, which is
  // what keeps this a factoring problem rather than a triviality.
  Type wide = vc_bvType(vc, 96);
  Expr a = vc_varExpr(vc, "a", wide);
  Expr b = vc_varExpr(vc, "b", wide);
  Expr limit = vc_bvConstExprFromDecStr(vc, 96, "1099511627776");
  Expr one = vc_bvConstExprFromDecStr(vc, 96, "1");
  vc_assertFormula(
      vc, vc_eqExpr(vc, vc_bvMultExpr(vc, 96, a, b),
                    vc_bvConstExprFromDecStr(vc, 96, "486579698794948075013401")));
  vc_assertFormula(vc, vc_bvGtExpr(vc, a, one));
  vc_assertFormula(vc, vc_bvGtExpr(vc, b, one));
  vc_assertFormula(vc, vc_bvLtExpr(vc, a, limit));
  vc_assertFormula(vc, vc_bvLtExpr(vc, b, limit));
  vc_assertFormula(vc, vc_bvLeExpr(vc, a, b));

  ASSERT_EQ(3, vc_query_with_timeout(vc, vc_falseExpr(vc), 0, -1)); // 3 == timeout

  EXPECT_EQ((Expr)NULL, vc_getCounterExample(vc, x));

  vc_Destroy(vc);
}

// Refusing is not the same as going quiet: the caller is told, through the
// handler the header documents for exactly this class of failure.
TEST(model_read_with_no_solve, the_refusal_is_reported)
{
  lastDiagnostic.clear();
  vc_registerErrorHandler(recordDiagnostic);

  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  EXPECT_EQ((Expr)NULL, vc_getCounterExample(vc, x));

  vc_Destroy(vc);
  vc_registerErrorHandler(NULL); // process-global; put it back

  EXPECT_NE(std::string::npos, lastDiagnostic.find("no model"))
      << "diagnostic was: " << lastDiagnostic;
}

// The other side of the refusal, so that it stays as narrow as it claims to
// be: once a query has been answered, every one of these sorts answers.
TEST(model_read_with_no_solve, a_solved_query_still_answers)
{
  VC vc = vc_createValidityChecker();

  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  Expr b = vc_varExpr(vc, "b", vc_boolType(vc));
  Expr f = buildFloat(vc);
  vc_assertFormula(vc, vc_eqExpr(vc, x, vc_bvConstExprFromLL(vc, 8, 7)));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc))); // 0 == INVALID == satisfiable

  Expr xval = vc_getCounterExample(vc, x);
  ASSERT_NE((Expr)NULL, xval);
  EXPECT_EQ((unsigned long long)7, getBVUnsignedLongLong(xval));
  EXPECT_NE((Expr)NULL, vc_getCounterExample(vc, b));
  EXPECT_NE((Expr)NULL, vc_getCounterExample(vc, f));

  vc_Destroy(vc);
}

// And a query that was decided the other way keeps the answer it already
// gave. There is no counterexample to a valid query, but that is a decided
// question rather than an unanswerable one, and it is not what this refusal
// is about: the call still returns a wrapper rather than NULL.
TEST(model_read_with_no_solve, a_valid_query_is_not_the_same_as_no_query)
{
  VC vc = vc_createValidityChecker();
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));

  ASSERT_EQ(1, vc_query(vc, vc_trueExpr(vc))); // 1 == VALID

  EXPECT_NE((Expr)NULL, vc_getCounterExample(vc, x));

  vc_Destroy(vc);
}

// A constant carries its own value, so it needs no query behind it.
TEST(model_read_with_no_solve, a_constant_answers_with_no_query)
{
  VC vc = vc_createValidityChecker();

  Expr value = vc_getCounterExample(vc, vc_bvConstExprFromLL(vc, 32, 18));
  ASSERT_NE((Expr)NULL, value);
  EXPECT_EQ((unsigned long long)18, getBVUnsignedLongLong(value));

  // The Boolean constants are constants too, and answer the same way.
  EXPECT_NE((Expr)NULL, vc_getCounterExample(vc, vc_trueExpr(vc)));
  EXPECT_NE((Expr)NULL, vc_getCounterExample(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

// A term over constants answers exactly when it is a constant by the time it
// is asked about -- which, with the simplifying factory a validity checker
// installs, a product of two literals is. The point of the case is that this
// is the same rule and not a second one: what answers is a constant, not a
// term that merely has constant leaves.
TEST(model_read_with_no_solve, a_folded_term_is_a_constant_like_any_other)
{
  VC vc = vc_createValidityChecker();

  Expr folded = vc_bvMultExpr(vc, 32, vc_bvConstExprFromLL(vc, 32, 18),
                              vc_bvConstExprFromLL(vc, 32, 2));
  Expr value = vc_getCounterExample(vc, folded);
  ASSERT_NE((Expr)NULL, value);
  EXPECT_EQ((unsigned long long)36, getBVUnsignedLongLong(value));

  vc_Destroy(vc);
}

// A float constant goes through the same door, and it is worth saying so
// explicitly: this is the sort that used to take the process down. What comes
// back is the constant itself, with nothing evaluated against an empty model,
// so the fatal is not on this path. A float that does have to be evaluated is
// still refused -- float_is_refused_not_aborted above is that case.
TEST(model_read_with_no_solve, a_float_constant_answers_with_no_query)
{
  VC vc = vc_createValidityChecker();

  // 0x3C00 is 1.0 in binary16, and built out of constant bits it folds to a
  // constant rather than staying a term to evaluate.
  Expr f = vc_fpToFPFromIEEEBV(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x3C00));
  EXPECT_NE((Expr)NULL, vc_getCounterExample(vc, f));

  vc_Destroy(vc);
}

// The other side of that line: one symbol anywhere in the term and there is
// something a model has to supply, so the refusal applies as before.
TEST(model_read_with_no_solve, a_term_with_a_symbol_in_it_is_still_refused)
{
  VC vc = vc_createValidityChecker();

  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 32));
  Expr mixed = vc_bvPlusExpr(vc, 32, x, vc_bvConstExprFromLL(vc, 32, 36));

  EXPECT_EQ((Expr)NULL, vc_getCounterExample(vc, mixed));

  vc_Destroy(vc);
}

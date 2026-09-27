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

// api3-model-read-with-no-solve.cpp -- reading a model when no check has
// answered sat.
//
// There is no model to read, and the only honest answer is to say so. What
// 2.x's vc_getCounterExample did instead depended on the sort asked about: a
// bit-vector or a Boolean came back as a value invented out of an empty model,
// and a float took the process down with a Fatal Error. The first two were the
// worse half: a caller that reads a model it never asked for gets a number
// back with nothing to distinguish it from a real one. The SMT-LIB 2 frontend
// never had this: a get-value with no check-sat behind it answers
// "unsupported".
//
// In 3.x a model is what Solver::model() returns, and it returns one only
// after a check that answered sat. Before any check, and after a check that
// answered unsat or unknown, it refuses with NO_MODEL whatever the term, and
// the refusal says what the last check answered; Solver::value(t) is
// model().value(t) and refuses the same way. A Model taken earlier is a
// detached snapshot and outlives every later check.
//
// Two things differ from 2.x on purpose. A read after a valid entailment is
// refused too: there is no counterexample to a valid query, and 2.x's answer
// there was an invented one. And a constant needs no model at all: a value
// term is decoded by the Term readers (to_uint64, to_bool, to_fp, ...) with or
// without a check, while a term with a symbol anywhere in it is not a value,
// however much of it is constant, and has to be evaluated in a model. The
// cases at the end pin both sides of that line.

#include "api3_common.hpp"

#include <optional>
#include <string>

using namespace stp;

namespace
{

// A float that has to be evaluated rather than folded: built out of a symbolic
// sign and exponent, so it is not already a value.
Term buildFloat(TermManager& tm)
{
  const Term sign = tm.declare("s", tm.mk_bv_sort(1));
  const Term exponent = tm.declare("e", tm.mk_bv_sort(5));
  return to_fp_from_bits(tm.mk_fp16_sort(),
                         concat(sign, concat(exponent, tm.mk_bv(10, 0))));
}

// The options of a 2.x checker: vc_createValidityChecker set 'd', so every
// 2.x case ran with the counterexample self-check on, and every solver here
// runs with check-sanity.
Options checkerOptions()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

} // namespace

// A bit-vector, which 2.x answered with an invented value.
TEST(model_read_with_no_solve, bitvector_is_refused_not_invented)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  const Term x = tm.declare("x", tm.mk_bv_sort(8));

  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(x));
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
}

// A Boolean, likewise.
TEST(model_read_with_no_solve, boolean_is_refused_not_invented)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  const Term b = tm.declare("b", tm.mk_bool_sort());

  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(b));
}

// A float, which used to abort. The case is an ordinary check rather than a
// death test precisely because the call has to return at all.
TEST(model_read_with_no_solve, float_is_refused_not_aborted)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  const Term f = buildFloat(tm);
  ASSERT_FALSE(f.is_value());

  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(f));
}

// The other read that was fatal in 2.x with no solve behind it, and the reason
// this is not just about the sort asked for. Whether two float-indexed arrays
// are equal was decided by the model evaluator through a gate of its own,
// which read the published encoding context directly and aborted at its own
// site with its own message:
//
//   Fatal Error: array-equality: cannot evaluate an opaque equality over
//                float-indexed arrays that was not reachable in the most
//                recent solve
//
// In 3.x there is no model to evaluate against, and the equality is refused
// like every other read. (2.x's 'x' had to precede the creation of any term;
// 3.x's array-equality option never gates construction.)
TEST(model_read_with_no_solve, float_indexed_array_equality_is_refused_too)
{
  TermManager tm;
  Options o = checkerOptions();
  o.set("array-equality", "on"); // 'x'
  Solver s(tm, o);

  const Sort arrayOfFloat = tm.mk_array_sort(tm.mk_fp16_sort(), tm.mk_bv_sort(8));
  const Term a = tm.declare("a", arrayOfFloat);
  const Term b = tm.declare("b", arrayOfFloat);

  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(a == b));
}

// The incremental driver reaches the model machinery by its own route, so it
// is asked separately.
TEST(model_read_with_no_solve, incremental_is_refused_too)
{
  TermManager tm;
  Options o = checkerOptions();
  o.set("incremental", "on"); // 'i'
  Solver s(tm, o);

  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  const Term f = buildFloat(tm);

  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(x));
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(f));
}

// A check that ran out of budget decided nothing, and no model takes the place
// of the one before it. This is where an invented value is at its most
// convincing: 2.x read a plain 0 here for a variable the previous query had
// pinned to 7, so the answer was not even stale, it was made up.
//
// The budget is zero conflicts, which is a budget rather than the absence of
// one, so the give-up is decided before the search rather than by the clock.
TEST(model_read_with_no_solve, an_unknown_query_leaves_no_model)
{
  TermManager tm;
  Solver s(tm, checkerOptions());

  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  s.add(x == 7);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model before = s.model();
  ASSERT_EQ(before.uint64_value(x), 7u);

  // The 2.x case's 96-bit factoring instance (two 40-bit prime factors, held
  // below 2^40 so the multiply cannot wrap).
  api3::add_hard_factoring(tm, s);

  const Result r = s.check_sat({}, CheckBudget{std::nullopt, 0});
  ASSERT_TRUE(r.is_unknown());
  ASSERT_EQ(r.reason(), UnknownReason::CONFLICT_LIMIT);

  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(x));
  // The model taken before the check is a detached snapshot: it outlives it.
  EXPECT_EQ(before.uint64_value(x), 7u);
}

// Refusing is not the same as going quiet: the caller is told, and told why.
// (2.x reported through the process-global handler of
// vc_registerErrorHandler; 3.x's refusal is the exception itself.)
TEST(model_read_with_no_solve, the_refusal_is_reported)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  const Term x = tm.declare("x", tm.mk_bv_sort(8));

  const auto e = API3_ERROR_OF(s.value(x));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::NO_MODEL);
  EXPECT_EQ(e->function(), "Solver::model");
  EXPECT_NE(std::string(e->what()).find("no model"), std::string::npos)
      << "diagnostic was: " << e->what();
  EXPECT_NE(std::string(e->what()).find("nothing yet"), std::string::npos)
      << "diagnostic was: " << e->what();
}

// The other side of the refusal, so that it stays as narrow as it claims to
// be: once a check has answered sat, every one of these sorts answers.
TEST(model_read_with_no_solve, a_solved_query_still_answers)
{
  TermManager tm;
  Solver s(tm, checkerOptions());

  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  const Term b = tm.declare("b", tm.mk_bool_sort());
  const Term f = buildFloat(tm);
  s.add(x == 7);

  ASSERT_TRUE(s.check_sat().is_sat());

  EXPECT_EQ(s.value(x).to_uint64(), 7u);
  EXPECT_TRUE(s.value(b).is_value());
  const Term fv = s.value(f);
  EXPECT_TRUE(fv.is_value());
  EXPECT_TRUE(fv.sort() == tm.mk_fp16_sort());
}

// A valid entailment decided its question: there is no counterexample to it,
// but that is a decided question rather than an unanswerable one. 2.x still
// returned a value here.
TEST(model_read_with_no_solve, a_valid_query_is_not_the_same_as_no_query)
{
  TermManager tm;
  Solver s(tm, checkerOptions());
  const Term x = tm.declare("x", tm.mk_bv_sort(8));

  ASSERT_TRUE(s.entails(tm.mk_true()).is_valid());

  // 3.x: no model after an entailment holds; the refusal names the answer
  // (the negation was unsat) rather than "nothing yet".
  const auto e = API3_ERROR_OF(s.value(x));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::NO_MODEL);
  EXPECT_NE(std::string(e->what()).find("unsat"), std::string::npos) << e->what();
  EXPECT_EQ(std::string(e->what()).find("nothing yet"), std::string::npos) << e->what();
}

// A constant carries its own value, so it needs no check behind it: the Term
// readers decode a value term directly, and no model is involved.
TEST(model_read_with_no_solve, a_constant_answers_with_no_query)
{
  TermManager tm;
  Solver s(tm, checkerOptions());

  const Term value = tm.mk_bv(32, 18);
  ASSERT_TRUE(value.is_value());
  EXPECT_EQ(value.to_uint64(), 18u);

  // The Boolean constants are values too, and answer the same way.
  EXPECT_TRUE(tm.mk_true().to_bool());
  EXPECT_FALSE(tm.mk_false().to_bool());

  // and the solver still has no model
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
}

// A term over constants answers exactly when it is a value by the time it is
// asked about -- which, with the manager's construction-time folding (on by
// default), a product of two literals is. The point of the case is that this
// is the same rule and not a second one: what answers is a value, not a term
// that merely has constant leaves.
TEST(model_read_with_no_solve, a_folded_term_is_a_constant_like_any_other)
{
  TermManager tm;

  const Term folded = bvmul(tm.mk_bv(32, 18), tm.mk_bv(32, 2));
  ASSERT_TRUE(folded.is_value());
  EXPECT_EQ(folded.to_uint64(), 36u);

  // Without the folding the product is a term until something folds it.
  TermManager raw = api3::raw_manager();
  const Term product = bvmul(raw.mk_bv(32, 18), raw.mk_bv(32, 2));
  EXPECT_FALSE(product.is_value());
  API3_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, product.to_uint64());
  EXPECT_EQ(raw.simplify(product).to_uint64(), 36u);
}

// A float constant goes through the same door, and it is worth saying so
// explicitly: this is the sort that used to take the process down. What comes
// back is the constant itself, with nothing evaluated against an empty model.
// A float that does have to be evaluated is still refused --
// float_is_refused_not_aborted above is that case.
TEST(model_read_with_no_solve, a_float_constant_answers_with_no_query)
{
  TermManager tm;

  // 0x3C00 is 1.0 in binary16, and built out of constant bits it folds to a
  // value rather than staying a term to evaluate.
  const Term f = to_fp_from_bits(tm.mk_fp16_sort(), tm.mk_bv(16, 0x3C00));
  ASSERT_TRUE(f.is_value());
  EXPECT_EQ(f.to_fp().to_double(), std::optional<double>(1.0));
}

// The other side of that line: one symbol anywhere in the term and there is
// something a model has to supply, so the refusal applies as before.
TEST(model_read_with_no_solve, a_term_with_a_symbol_in_it_is_still_refused)
{
  TermManager tm;
  Solver s(tm, checkerOptions());

  const Term x = tm.declare("x", tm.mk_bv_sort(32));
  const Term mixed = bvadd(x, tm.mk_bv(32, 36));

  EXPECT_FALSE(mixed.is_value());
  API3_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, mixed.to_uint64());
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(mixed));
}

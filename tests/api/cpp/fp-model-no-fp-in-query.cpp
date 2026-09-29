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

// fp-model-no-fp-in-query.cpp -- reading the model value of a
// floating-point term the solved query never mentioned.
//
// The value is a function of the model, not of the assertion stack: nothing
// about a float has to be asserted for the float to have a value once the
// bit-vectors under it do. The batch driver answers such a question, and so
// does the SMT-LIB2 frontend. The incremental driver used to abort the
// process when the model reader asked:
//
//   Fatal Error: floating-point model evaluation has no solve encoding context
//
// The cause was what the driver published to the model machinery rather than
// how it evaluated anything. Its floating-point encoding context is made
// lazily, on first use *during encoding*, and it installed the context only
// when it had one -- so a stack with no float in it left the model machinery
// holding NULL. NULL there already means "no solve has run", which is what
// makes it fatal; the guard gave it a second meaning, "this solve had no
// float in it", and nothing downstream could tell the two apart. The fix
// publishes the context on every route that builds a model.
//
// So these tests pin both halves of the distinction:
//
//   * a float the query never mentioned is answered, on each route below,
//     and answered with the same value the batch driver gives; and
//   * with no check at all there is still no model, and the question is
//     refused rather than answered with an invented value.
//
// The routes: every solver here runs with check-sanity on, as every 2.x
// checker did, so the incremental driver builds and checks the model during
// the check -- on the ordinary route, or, when an asserted whole-array
// equality puts the check on the exact-stack route, from that route's own
// place (incremental_exact_stack_route_answers). 3.x's default leaves
// check-sanity off, and then the driver defers the model to its first read
// and Solver::model() materialises it (the deferred route, which publishes
// the context itself); incremental_eager_model_answers asks on both.
//
// The same NULL had a second reader: whether an equality between two
// float-indexed arrays can be decided from the model. The last three cases
// ask that question. Model::value answers both questions over the check's
// model snapshot -- a float from the values under it, an array equality cell
// by cell -- rather than through the engine's readers of the published
// context, so what every case here pins for the API is the answer, on each
// route, and its agreement with the batch driver. The engine's readers are
// still what the SMT-LIB 2 frontend's get-value goes through, and the cases
// that ran the incremental driver ask them directly too (engineReadsFloat,
// engineCanDecideArrayEquality): the defect itself, which the answers alone
// would no longer show.
//
// Found by a Murxla campaign cross-checking STP against STP under a differing
// option vector. The float-term arm was reduced from a 143-line trace; the
// array arm arrived separately out of the same campaign, from a 69-line one.

#include "api_engine.hpp"

#include <cstdint>
#include <string>

using namespace stp::api;

namespace
{

// A 2.x checker's configuration: the counterexample self-check on (3.x's
// default is off), so every satisfiable check constructs its model and checks
// each assertion against it.
Options self_checking()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

// binary16 (eb=5, sb=11): 1 sign bit + 5 exponent + 10 significand.
const std::uint32_t EB = 5;
const std::uint32_t SB = 11;

// 1.0 packs as 0 01111 0000000000.
const std::uint64_t ONE_BITS = 0x3C00;
const std::uint64_t ONE_EXPONENT = 15; // 0b01111

// 2.x's 'i': the incremental driver from the first check.
void incremental(Solver& s)
{
  s.options().set("incremental", "on");
}

// 2.x's 'x': the extensional array machinery on. 3.x builds an array
// equality without it; the option only forces the machinery on.
void arrayEquality(Solver& s)
{
  s.options().set("array-equality", "on");
}

// The packed interchange bits of a float's value in the model.
std::uint64_t packed(const Model& m, const Term& f)
{
  return std::stoull(m.fp_value(f).bits(), nullptr, 2);
}

// The float under test: a binary16 reinterpreted out of three bit-vectors,
// two of them symbols. Symbols on purpose -- a float built only from
// constants folds at construction and never reaches the encoding the bug was
// about. `sign` and `exponent` are handed back so a caller can pin them with
// bit-vector assertions, which is a real solve with no float anywhere in it.
Term buildFloat(TermManager& tm, Term& sign, Term& exponent)
{
  sign = tm.declare("s", tm.mk_bv_sort(1));
  exponent = tm.declare("e", tm.mk_bv_sort(EB));
  const Term significand = tm.mk_bv(SB - 1, 0);
  return to_fp_from_bits(tm.mk_fp_sort(EB, SB), concat(sign, concat(exponent, significand)));
}

// Pin the carrier bits to 1.0 through the bit-vectors alone, so the float has
// exactly one value in the model and the test can name it. Nothing asserted
// here mentions a float.
void assertBitsAreOne(TermManager& tm, Solver& s, const Term& sign, const Term& exponent)
{
  s.add(sign == tm.mk_bv(1, 0));
  s.add(exponent == tm.mk_bv(EB, ONE_EXPONENT));
}

// Two arrays whose *index* sort is in the floating-point theory, which is
// what the array-equality reader gated on; RoundingMode satisfies it. No
// Float is needed anywhere, and neither array is ever asserted about, so
// nothing here reaches the encoder.
void buildRoundingModeArrays(TermManager& tm, Term& a, Term& b)
{
  const Sort rm = tm.mk_rm_sort();
  const Sort arr = tm.mk_array_sort(rm, rm);
  a = tm.declare("a", arr);
  b = tm.declare("b", arr);
}

// The engine's own reader of a float's model value, which needs the
// floating-point encoding context the check published: it refused with "no
// solve encoding context" when the incremental driver left it unset.
bool engineReadsFloat(const Solver& s, const Term& f)
{
  const stp::ASTNode value =
      api_test::engine_solver(s).Ctr_Example->GetCounterExample(api_test::engine_node(f));
  return !value.IsNull() && value.isConstant();
}

// Whether the engine's model can decide an equality over this array, which
// for a floating-point-indexed one needs the same published context.
bool engineCanDecideArrayEquality(const Solver& s, const Term& array)
{
  return api_test::engine_solver(s).Ctr_Example->arrayEqualityIsModelDecidable(
      api_test::engine_node(array));
}

// Four bits pinned to 3: a real solve with a forced value in it, and nothing
// in it about an array or a float. The array cases read it back alongside
// the equality so that they stay anchored to a model that exists and has
// something in it -- a change that made the solve vacuous would fail them
// rather than leave them quietly exercising nothing.
const std::uint64_t ANCHOR_BITS = 3;

Term assertAnchor(TermManager& tm, Solver& s)
{
  const Term x = tm.declare("x", tm.mk_bv_sort(4));
  s.add(x == tm.mk_bv(4, ANCHOR_BITS));
  return x;
}

} // namespace

// The reduced reproducer, as filed: incremental from the first check, nothing
// on the stack at all, and a float built and never mentioned again. The read
// is what used to abort, one call after a check that answered.
TEST(fp_model_no_fp_in_query, incremental_empty_stack_answers)
{
  TermManager tm;
  Solver s(tm, self_checking());
  incremental(s);

  Term sign, exponent;
  const Term f = buildFloat(tm, sign, exponent);

  ASSERT_TRUE(s.check_sat().is_sat());

  const Term value = s.model().value(f);
  ASSERT_TRUE(value.is_value());
  // Nothing constrains the sign or the exponent, so their bits are the
  // model's to choose and the packed value is not the test's to name. The
  // significand is a constant, and the model has to carry it through.
  EXPECT_EQ(std::stoull(value.to_fp().bits(), nullptr, 2) & ((1ULL << (SB - 1)) - 1), 0u);
}

// The second row of the defect's table: a real solve with a real assertion
// stack, none of it floating-point. Pinning the carrier bits makes the
// float's value the test's to name -- the answer is 1.0 and nothing else.
TEST(fp_model_no_fp_in_query, incremental_bitvector_only_stack_answers)
{
  TermManager tm;
  Solver s(tm, self_checking());
  incremental(s);

  Term sign, exponent;
  const Term f = buildFloat(tm, sign, exponent);
  assertBitsAreOne(tm, s, sign, exponent);

  ASSERT_TRUE(s.check_sat().is_sat());

  EXPECT_EQ(packed(s.model(), f), ONE_BITS);
  EXPECT_TRUE(engineReadsFloat(s, f));
}

// The same question with the model asked for explicitly (produce-models,
// 2.x's 'c'), in a 2.x checker's configuration and in 3.x's default one. 2.x
// switched check-sanity on for every checker, so every 2.x solve built its
// model during the check and the deferred route was out of its reach; 3.x's
// default leaves it off, and then the driver defers the model until
// Solver::model() reads it. This case pins that neither construction perturbs
// the answer; its second arm is the one place here that runs the default
// configuration, on purpose.
TEST(fp_model_no_fp_in_query, incremental_eager_model_answers)
{
  for (const bool self_check : {true, false})
  {
    TermManager tm;
    Solver s(tm, self_check ? self_checking() : Options());
    incremental(s);
    s.options().set_bool("produce-models", true); // ask for the model explicitly

    Term sign, exponent;
    const Term f = buildFloat(tm, sign, exponent);
    assertBitsAreOne(tm, s, sign, exponent);

    ASSERT_TRUE(s.check_sat().is_sat()) << "check-sanity " << self_check;

    EXPECT_EQ(packed(s.model(), f), ONE_BITS) << "check-sanity " << self_check;
    EXPECT_TRUE(engineReadsFloat(s, f)) << "check-sanity " << self_check;
  }
}

// An asserted whole-array equality puts the driver on the exact-stack route,
// which encodes the complete active stack as one block and, with
// check-sanity on, builds the model from its own place rather than the
// ordinary check's (with it off the route defers the model like any other).
// The arrays are bit-vector arrays: still not one float in the query.
//
// The equality has to be between two array symbols. A write chain equated
// with its own base -- store(a, i, a[i]) = a -- reads like a better test and
// is not one: the manager folds that shape away (to true: the store writes
// back what is there), so no array equality survives to the driver and the
// round takes the ordinary route.
TEST(fp_model_no_fp_in_query, incremental_exact_stack_route_answers)
{
  TermManager tm;
  Solver s(tm, self_checking());
  incremental(s);
  arrayEquality(s);

  const Sort arr = tm.mk_array_sort(tm.mk_bv_sort(4), tm.mk_bv_sort(8));
  const Term a = tm.declare("a", arr);
  const Term b = tm.declare("b", arr);
  // Nothing else constrains either array, so the equality is satisfiable and
  // extensionality has to decide it rather than fold it away.
  s.add(a == b);

  Term sign, exponent;
  const Term f = buildFloat(tm, sign, exponent);
  assertBitsAreOne(tm, s, sign, exponent);

  ASSERT_TRUE(s.check_sat().is_sat());

  EXPECT_EQ(packed(s.model(), f), ONE_BITS);
  EXPECT_TRUE(engineReadsFloat(s, f));
}

// The invariant behind all of the above, asked directly: the two drivers are
// answering one question about one model, so they answer it the same way.
// The value is pinned by bit-vector assertions precisely so that "the same"
// is a property of the question and not of which unconstrained bits each
// driver's solver happened to pick.
TEST(fp_model_no_fp_in_query, incremental_agrees_with_batch)
{
  std::uint64_t answers[2];

  for (int incremental = 0; incremental < 2; incremental++)
  {
    TermManager tm;
    Solver s(tm, self_checking());
    s.options().set("incremental", incremental ? "on" : "off");

    Term sign, exponent;
    const Term f = buildFloat(tm, sign, exponent);
    assertBitsAreOne(tm, s, sign, exponent);

    ASSERT_TRUE(s.check_sat().is_sat()) << "incremental " << incremental;

    answers[incremental] = packed(s.model(), f);
  }

  EXPECT_EQ(answers[0], answers[1]);
  EXPECT_EQ(answers[1], ONE_BITS);
}

// Repeated checks on one solver: the context is per encoding epoch and the
// batch driver may install its own between rounds, so publishing it once is
// not enough. Each answer has to be the one belonging to the check that
// produced the model being read.
TEST(fp_model_no_fp_in_query, incremental_repeated_solves_keep_answering)
{
  TermManager tm;
  Solver s(tm, self_checking());
  incremental(s);

  Term sign, exponent;
  const Term f = buildFloat(tm, sign, exponent);
  assertBitsAreOne(tm, s, sign, exponent);

  for (int round = 0; round < 3; round++)
  {
    ASSERT_TRUE(s.check_sat().is_sat()) << "round " << round;
    EXPECT_EQ(packed(s.model(), f), ONE_BITS) << "round " << round;
  }
}

// Across a scope, which is where the driver does its level bookkeeping: a
// check inside the pushed scope and another after it is gone. Everything
// asserted at either depth is a bit-vector, so neither check has a float in
// it and neither may refuse the float's value.
TEST(fp_model_no_fp_in_query, incremental_answers_either_side_of_a_scope)
{
  TermManager tm;
  Solver s(tm, self_checking());
  incremental(s);

  Term sign, exponent;
  const Term f = buildFloat(tm, sign, exponent);
  assertBitsAreOne(tm, s, sign, exponent);

  s.push();
  const Term g = tm.declare("g", tm.mk_bv_sort(8));
  s.add(g == tm.mk_bv(8, 3));

  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(packed(s.model(), f), ONE_BITS);

  s.pop();

  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(packed(s.model(), f), ONE_BITS);
}

// The other half of the distinction, and the reason the fix publishes a
// context per solve rather than conjuring one at read time: with no check
// there is no model, and a model value asked for anyway must not be invented.
// 3.x: that read is a RecoverableError (NO_MODEL), where 2.x answered NULL;
// model-read-with-no-solve.cpp owns that behaviour across sorts and
// drivers. The property this case is here for has not moved: a future fix
// that made a context up at read time would answer here.
TEST(fp_model_no_fp_in_query, no_solve_is_still_not_answered)
{
  TermManager tm;
  Solver s(tm, self_checking());
  incremental(s);

  Term sign;
  Term exponent;
  const Term f = buildFloat(tm, sign, exponent);

  API_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
  API_EXPECT_ERROR(ErrorCode::NO_MODEL, s.value(f));
}

// The other question the same NULL used to break: whether two float-indexed
// arrays are equal in the model. Nothing here asserts anything about an
// array, so no float reaches the encoder and no context is built -- which the
// reader once took for "no solve has run" about a check that had just
// answered.
//
// The answer is true because neither array is in the model at all: with no
// cells recorded against either, there is no index at which they could
// disagree, and both are completed with the same fill (the element sort's
// default). That makes it the model's answer rather than the SAT search's,
// which is the only reason this file names it. Nothing constrains these
// arrays, so a value the search had picked freely would not be the test's to
// pin -- the same care the float cases take by holding their carrier bits,
// arrived at from the other direction.
TEST(fp_model_no_fp_in_query, incremental_float_indexed_array_equality_answers)
{
  TermManager tm;
  Solver s(tm, self_checking());
  incremental(s);
  arrayEquality(s);

  Term a, b;
  buildRoundingModeArrays(tm, a, b);
  const Term x = assertAnchor(tm, s);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  ASSERT_EQ(m.uint64_value(x), ANCHOR_BITS);

  const Term value = m.value(a == b);
  ASSERT_TRUE(value.is_value());
  EXPECT_TRUE(value.to_bool());
  EXPECT_TRUE(engineCanDecideArrayEquality(s, a));
}

// The campaign's own reproducer, which reaches "the solve never encoded
// them" by a different road: the arrays *are* mentioned, in an assertion
// that happens to be a tautology, so the manager folds it away before
// encoding and they still never arrive.
//
// The case above does not depend on that rewrite and this one does, which is
// why both are here. If the manager ever stops folding an implication from a
// formula to itself, this case stops exercising the question -- it would
// still pass, having encoded the arrays the honest way -- and the case above
// is what would still be covering it.
TEST(fp_model_no_fp_in_query, incremental_array_equality_mentioned_but_rewritten_away)
{
  TermManager tm;
  Solver s(tm, self_checking());
  incremental(s);
  arrayEquality(s);

  Term a, b;
  buildRoundingModeArrays(tm, a, b);
  const Term equality = a == b;
  s.add(implies(equality, equality));
  const Term x = assertAnchor(tm, s);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  ASSERT_EQ(m.uint64_value(x), ANCHOR_BITS);

  const Term value = m.value(equality);
  ASSERT_TRUE(value.is_value());
  EXPECT_TRUE(value.to_bool());
  EXPECT_TRUE(engineCanDecideArrayEquality(s, a));
}

// The invariant the two above are instances of, as the float cases have it:
// one question about one model, so the two drivers answer it the same way.
// The batch driver has always answered this one.
TEST(fp_model_no_fp_in_query, incremental_array_equality_agrees_with_batch)
{
  bool answers[2];

  for (int incremental = 0; incremental < 2; incremental++)
  {
    TermManager tm;
    Solver s(tm, self_checking());
    s.options().set("incremental", incremental ? "on" : "off");
    arrayEquality(s);

    Term a, b;
    buildRoundingModeArrays(tm, a, b);
    const Term x = assertAnchor(tm, s);

    ASSERT_TRUE(s.check_sat().is_sat()) << "incremental " << incremental;
    const Model m = s.model();

    ASSERT_EQ(m.uint64_value(x), ANCHOR_BITS) << "incremental " << incremental;

    answers[incremental] = m.bool_value(a == b);
  }

  EXPECT_EQ(answers[0], answers[1]);
  EXPECT_TRUE(answers[1]);
}

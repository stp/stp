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

// api3-fp-model-roundtrip.cpp -- a floating-point model value fed straight
// back to the solver.
//
// Regression tests: a model value must be a value *of the sort of the term it
// was read from*, so that feeding it straight back -- asserting
// (= term value) and re-solving -- is a well-sorted problem STP can answer.
//
// Model evaluation works in plain bit-vector constants throughout, and the
// floating-point format used to be dropped on the way back out of the model
// reader. The caller then built a float/bit-vector mix out of STP's own
// model:
//
//   Fatal Error: rhs of <fp> is not an fp
//
// or, where the type check does not run first, reached symfpu with the
// format's zero widths and asked for a zero-width exponent constant:
//
//   Fatal Error: CreateBVConst: trying to create bvconst using unsigned long
//   long of width: 0
//
// Either way STP aborted rather than re-check its own model.
//
// Found by fuzzing with murxla using -C, which re-asserts every reported
// model value and re-solves; delta-minimized.

#include "api3_common.hpp"

#include <cstdint>
#include <optional>
#include <string>

using namespace stp;

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

// The packed interchange bits of a float value (formats up to 64 bits).
std::uint64_t packed(const Term& value)
{
  return std::stoull(value.to_fp().bits(), nullptr, 2);
}

} // namespace

// The fuzzer's case: fp.abs of a Float128 conversion from a signed
// bit-vector, under a symbolic rounding mode.
TEST(fp_model_roundtrip, float128_abs_of_to_fp_from_signed_bv)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Term bv = tm.declare("x0", tm.mk_bv_sort(15));
  const Term rm = tm.declare("x1", tm.mk_rm_sort());
  // (_ FloatingPoint 15 113)
  const Term t = fp_abs(to_fp(tm.mk_fp_sort(15, 113), rm, bv));

  ASSERT_TRUE(s.check_sat().is_sat());

  const Term v = s.model().value(t);
  ASSERT_TRUE(v.is_value());
  ASSERT_EQ(v.sort().kind(), SortKind::FP);
  EXPECT_EQ(v.sort().fp_exp_size(), 15u);
  EXPECT_EQ(v.sort().fp_sig_size(), 113u);

  // Re-asserting STP's own value stays satisfiable...
  s.add(t == v);
  ASSERT_TRUE(s.check_sat().is_sat());
  // ...and now pins the term to it.
  ASSERT_TRUE(s.entails(t == v).is_valid());
}

// The same for the value of a plain floating-point variable, in a format
// small enough to compare bit-for-bit.
TEST(fp_model_roundtrip, float_variable)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort f = tm.mk_fp_sort(5, 11);
  const Term x = tm.declare("x", f);
  const Term y = tm.declare("y", f);

  // 1.0 packs as 0x3C00 in binary16; y is x + 1.0 under RNE.
  const Term one = tm.mk_fp_from_bits(f, tm.mk_bv(16, 0x3C00));
  s.add(x == one);
  s.add(y == fp_add(tm.mk_rm(RoundingMode::RNE), x, one));
  ASSERT_TRUE(s.check_sat().is_sat());

  const Term vy = s.model().value(y);
  ASSERT_EQ(vy.sort().kind(), SortKind::FP);
  EXPECT_EQ(vy.sort().fp_exp_size(), 5u);
  EXPECT_EQ(vy.sort().fp_sig_size(), 11u);
  // 1.0 + 1.0 is exactly 2.0, which packs as 0x4000.
  EXPECT_EQ(packed(vy), 0x4000u);

  s.add(y == vy);
  ASSERT_TRUE(s.check_sat().is_sat());
}

// NaN is the interesting value to feed back: the constant is canonicalised
// as it is built, so the value handed out need not have the model's bits --
// but '=' over floats holds between any two NaNs, so it still pins the term.
TEST(fp_model_roundtrip, nan_value)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Term x = tm.declare("x", tm.mk_fp_sort(8, 24));
  s.add(fp_is_nan(x));
  ASSERT_TRUE(s.check_sat().is_sat());

  const Term v = s.model().value(x);
  ASSERT_EQ(v.sort().kind(), SortKind::FP);
  EXPECT_EQ(v.sort().fp_exp_size(), 8u);
  EXPECT_EQ(v.sort().fp_sig_size(), 24u);

  s.add(x == v);
  ASSERT_TRUE(s.check_sat().is_sat());
  ASSERT_TRUE(s.entails(fp_is_nan(x)).is_valid());
}

// The whole-array model has the same obligation on both halves of every
// entry: the index must be usable as an index of that array, and the value
// must be equatable with the read.
TEST(fp_model_roundtrip, array_model_entries)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort f = tm.mk_fp_sort(5, 11);
  const Term a = tm.declare("a", tm.mk_array_sort(f, f));
  const Term i = tm.declare("i", f);
  const Term one = tm.mk_fp_from_bits(f, tm.mk_bv(16, 0x3C00));

  s.add(a[i] == one);
  ASSERT_TRUE(s.check_sat().is_sat());

  const ArrayValue av = s.model().array_value(a);
  ASSERT_EQ(av.size(), 1u);
  const ArrayValue::Entry entry = av.entry(0);

  // Both come back at the array's declared sorts. (Asserted, not expected:
  // the read below needs an index of the array's index sort.)
  ASSERT_EQ(entry.index.sort().kind(), SortKind::FP);
  EXPECT_EQ(entry.index.sort().fp_exp_size(), 5u);
  EXPECT_EQ(entry.index.sort().fp_sig_size(), 11u);
  ASSERT_EQ(entry.element.sort().kind(), SortKind::FP);
  EXPECT_EQ(packed(entry.element), 0x3C00u);

  // So the entry can be read back as an array access and re-asserted.
  const Term cell = select(a, entry.index);
  s.add(cell == entry.element);
  ASSERT_TRUE(s.check_sat().is_sat());
}

// The model is a detached snapshot of the whole assignment (2.x read it out of
// a separate whole-counterexample object); every value read from it carries
// its format.
TEST(fp_model_roundtrip, whole_counterexample_snapshot)
{
  TermManager tm;
  Solver s(tm, self_checking());

  const Sort f = tm.mk_fp_sort(5, 11);
  const Term x = tm.declare("x", f);
  // 'unused' never reaches the solver, so the model does not record it and
  // reading it completes it with its sort's default: +0.0, a float like any
  // other.
  const Term unused = tm.declare("unused", f);
  const Term one = tm.mk_fp_from_bits(f, tm.mk_bv(16, 0x3C00));

  s.add(x == one);
  ASSERT_TRUE(s.check_sat().is_sat());

  Term vx, vu;
  {
    const Model cc = s.model();

    vx = cc.value(x);
    ASSERT_EQ(vx.sort().kind(), SortKind::FP);
    EXPECT_EQ(vx.sort().fp_exp_size(), 5u);
    EXPECT_EQ(vx.sort().fp_sig_size(), 11u);
    EXPECT_EQ(packed(vx), 0x3C00u);

    vu = cc.value(unused);
    ASSERT_EQ(vu.sort().kind(), SortKind::FP);
    EXPECT_EQ(vu.sort().fp_exp_size(), 5u);
    EXPECT_EQ(vu.sort().fp_sig_size(), 11u);
    // 3.x: the completion is visible as such.
    EXPECT_FALSE(cc.in_core(unused));
    EXPECT_FALSE(cc.try_value(unused).has_value());
  } // the snapshot handle is gone; the values are terms of their own

  // Both are usable as values of their sort.
  s.add(x == vx);
  s.add(unused == vu);
  ASSERT_TRUE(s.check_sat().is_sat());
}

// Partial operations introduce solve-local choices. Model evaluation must
// follow the exact totalisation used by that solve, and a later solve must
// replace (rather than retain) the old encoding and model.
TEST(fp_model_roundtrip, partial_choice_uses_current_solve_encoding)
{
  TermManager tm;
  Solver s(tm, self_checking()); // construct and check each counterexample

  const Sort f = tm.mk_fp_sort(5, 11);
  const Term plus_zero = tm.mk_fp_pos_zero(f);
  const Term minus_zero = tm.mk_fp_neg_zero(f);
  const Term minimum = fp_min(plus_zero, minus_zero);

  s.push();
  s.add(minimum == plus_zero);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model first_model = s.model();
  const Term first = first_model.value(minimum);
  ASSERT_EQ(first.sort().kind(), SortKind::FP);
  EXPECT_EQ(packed(first), 0u);
  s.pop();

  s.push();
  s.add(minimum == minus_zero);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Term second = s.model().value(minimum);
  ASSERT_EQ(second.sort().kind(), SortKind::FP);
  EXPECT_EQ(packed(second), 0x8000u);
  s.pop();

  // 3.x: the first check's model is a snapshot of that solve, and keeps its
  // choice.
  EXPECT_EQ(packed(first_model.value(minimum)), 0u);
}

// Which zero fp.min returns for (+0, -0), and what fp.to_ubv and fp.to_sbv
// return for NaN, an infinity or a value out of range, is unspecified: a
// check may pick any answer. simplify() folds the specified cases only, and
// leaves an unspecified one alone rather than pick for the check.
TEST(fp_model_roundtrip, simplify_leaves_an_unspecified_case_to_the_check)
{
  TermManager tm;
  const Sort f = tm.mk_fp_sort(5, 11);
  const Term plus_zero = tm.mk_fp_pos_zero(f);
  const Term minus_zero = tm.mk_fp_neg_zero(f);
  const Term minimum = fp_min(plus_zero, minus_zero);
  EXPECT_NE(tm.simplify(minimum == plus_zero).kind(), Kind::VALUE);
  EXPECT_NE(tm.simplify(minimum).kind(), Kind::VALUE);
  for (const Term& zero : {plus_zero, minus_zero})
  {
    Solver s(tm, self_checking());
    s.add(minimum == zero);
    EXPECT_TRUE(s.check_sat().is_sat()) << zero;
  }

  const Term unspecified[] = {fp_to_ubv(8, RoundingMode::RTZ, tm.mk_fp_nan(f)),
                              fp_to_ubv(8, RoundingMode::RNE, tm.mk_fp_pos_inf(f)),
                              fp_to_sbv(8, RoundingMode::RTZ, tm.mk_fp(f, RoundingMode::RNE, 300.0))};
  for (const Term& t : unspecified)
  {
    EXPECT_NE(tm.simplify(t).kind(), Kind::VALUE) << t;
    for (const std::uint64_t v : {0u, 5u})
    {
      Solver s(tm, self_checking());
      s.add(t == tm.mk_bv(8, v));
      EXPECT_TRUE(s.check_sat().is_sat()) << t << " = " << v;
    }
  }

  // a specified case folds
  const Term two = tm.simplify(fp_to_sbv(8, RoundingMode::RTZ, tm.mk_fp(f, RoundingMode::RNE, 2.5)));
  EXPECT_TRUE(two.same_as(tm.mk_bv(8, 2))) << two;
  EXPECT_EQ(packed(tm.simplify(fp_min(plus_zero, plus_zero))), 0u);
}

// The operations are still functions: an application the check never saw,
// over operand values one it did see had, takes that one's choice, rather
// than a completion that contradicts it.
TEST(fp_model_roundtrip, an_unseen_application_takes_the_choice_its_operand_values_had)
{
  TermManager tm;
  const Sort f = tm.mk_fp_sort(5, 11);
  const Term x = tm.declare("x", f);
  const Term z = tm.declare("z", f);
  const Term b = tm.declare("b", tm.mk_bv_sort(8));
  Solver s(tm, self_checking());
  s.add(fp_is_nan(x));
  s.add(fp_is_nan(z));
  s.add(b == fp_to_ubv(8, RoundingMode::RTZ, x));
  s.add(b == tm.mk_bv(8, 7));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  // every NaN is one value, so these are the application the check saw
  const Term of_z = fp_to_ubv(8, RoundingMode::RTZ, z);
  EXPECT_TRUE(m.value(of_z).same_as(tm.mk_bv(8, 7))) << m.value(of_z);
  EXPECT_TRUE(m.value(fp_to_ubv(8, RoundingMode::RTZ, tm.mk_fp_nan(f))).same_as(tm.mk_bv(8, 7)));
  EXPECT_TRUE(m.try_value(of_z).has_value());
  // another rounding mode is another input, which the check left open
  EXPECT_FALSE(m.try_value(fp_to_ubv(8, RoundingMode::RTN, z)).has_value());

  // fp.min's zero, likewise
  const Term p = tm.declare("p", f);
  const Term q = tm.declare("q", f);
  const Term r = tm.declare("r", f);
  const Term t = tm.declare("t", f);
  Solver zeros(tm, self_checking());
  zeros.add(p == tm.mk_fp_pos_zero(f));
  zeros.add(q == tm.mk_fp_neg_zero(f));
  zeros.add(r == tm.mk_fp_pos_zero(f));
  zeros.add(t == tm.mk_fp_neg_zero(f));
  // +0: the choice a completion would not make, so the answer below is the check's
  zeros.add(fp_min(p, q) == tm.mk_fp_pos_zero(f));
  ASSERT_TRUE(zeros.check_sat().is_sat());
  EXPECT_EQ(packed(zeros.model().value(fp_min(r, t))), 0u);
}

// A model keeps its manager alive, so it may be the last thing holding it:
// then destroying the model frees the manager, and every engine node the model
// kept -- the partial operations' choices among them -- has to be let go
// before that. (A node let go afterwards touches freed memory, which a run
// under valgrind or a sanitizer reports.)
TEST(fp_model_roundtrip, a_model_that_outlives_its_manager_is_destroyed_cleanly)
{
  std::optional<Model> model;
  {
    TermManager tm;
    Solver s(tm, self_checking());
    const Term x = tm.declare("x", tm.mk_fp32_sort());
    const Term conversion = fp_to_ubv(8, RoundingMode::RNE, x);
    s.add(fp_is_nan(x));
    s.add(conversion == tm.mk_bv(8, 42));
    ASSERT_TRUE(s.check_sat().is_sat());
    model = s.model();
    EXPECT_EQ(model->uint64_value(conversion), 42u);
  }
  model.reset();
}

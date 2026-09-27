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

// api3-fp-cpp-wrapper.cpp -- floating-point problems in plain C++: RAII
// handles, typed floats and Booleans, operators, solving, and native doubles
// read back. These are the scenarios of the header-only stp/fp.hpp wrapper
// over the 2.x API (which stays, with its own test, for libstp2 users); the
// 3.x C++ API offers each of them directly.
//
// Two spellings differ from the wrapper's. Its == on floats was IEEE
// equality, which the API names fp_eq (the API's == is SMT-LIB '='), so the
// formulas below use fp_eq wherever the wrapper compared. And the API has no
// <, <=, > or >= on terms: fp_lt, fp_leq, fp_gt and fp_geq take a double on
// either side. The arithmetic operators round under the manager's default
// rounding mode, RNE unless it is set, as the wrapper's rounded under its
// solver's.

#include "api3_common.hpp"

#include <cmath>
#include <optional>
#include <string>
#include <utility>

using namespace stp;

namespace
{

// Every solver here runs with the engine's counterexample self-check on
// (check-sanity), as every 2.x validity checker did.
Options sanity_checked()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

// A float's value in the model of the solver's last check, as a native double.
double model_double(const Solver& s, const Term& f)
{
  const std::optional<double> d = s.model().fp_value(f).to_double();
  EXPECT_TRUE(d.has_value()) << f;
  return d.value_or(std::nan(""));
}

// A float's packed IEEE bits in the model of the solver's last check.
std::uint64_t ieee_bits(const Solver& s, const Term& f)
{
  return std::stoull(s.model().fp_value(f).bits(), nullptr, 2);
}

} // namespace

TEST(fp_cpp_wrapper, arithmetic_and_model)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Sort f64 = tm.mk_fp64_sort(); // IEEE double
  const Term a = tm.declare("a", f64);
  s.add(fp_eq(a, 4.0));
  const Term prod = a * a;
  const Term rt = fp_sqrt(RoundingMode::RNE, a);
  s.add(fp_gt(a, 0.0) && fp_is_normal(a));

  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(model_double(s, a), 4.0);
  EXPECT_EQ(model_double(s, prod), 16.0);
  EXPECT_EQ(model_double(s, rt), 2.0);
  EXPECT_EQ(model_double(s, fp_abs(-a)), 4.0);
  EXPECT_EQ(model_double(s, fp_min(a, tm.mk_fp(f64, RoundingMode::RNE, 2.0))), 2.0);
}

// Two independent solvers, both floating point, each over its own manager --
// also exercises the per-manager backend binding through the C++ layer.
TEST(fp_cpp_wrapper, two_solvers)
{
  TermManager tm1;
  Solver s1(tm1, sanity_checked());
  const Term a = tm1.declare("a", tm1.mk_fp32_sort()); // single
  s1.add(fp_eq(a, 1.5));

  TermManager tm2;
  Solver s2(tm2, sanity_checked());
  const Term b = tm2.declare("b", tm2.mk_fp64_sort()); // double
  s2.add(fp_eq(b, 3.5));

  ASSERT_TRUE(s1.check_sat().is_sat());
  ASSERT_TRUE(s2.check_sat().is_sat());
  EXPECT_EQ(model_double(s1, a), 1.5);
  EXPECT_EQ(model_double(s2, b), 3.5);
}

// A conflicting pair of classifications is unsatisfiable.
TEST(fp_cpp_wrapper, classification_unsat)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Term x = tm.declare("x", tm.mk_fp16_sort());
  s.add(fp_is_nan(x));
  s.add(fp_is_zero(x));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(fp_cpp_wrapper, more_ops)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Sort f64 = tm.mk_fp64_sort();
  const Term a = tm.declare("a", f64);
  const Term b = tm.declare("b", f64);
  s.add(fp_eq(a, 4.0));
  s.add(fp_eq(b, 2.0));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(model_double(s, a - b), 2.0);
  EXPECT_EQ(model_double(s, a / b), 2.0);
  EXPECT_EQ(model_double(s, fp_fma(RoundingMode::RNE, a, b, b)), 10.0); // 4*2 + 2
  EXPECT_EQ(model_double(s, fp_rem(a, b)), 0.0);
  EXPECT_EQ(model_double(s, fp_min(a, b)), 2.0);
  EXPECT_EQ(model_double(s, fp_max(a, b)), 4.0);
  EXPECT_EQ(model_double(s, fp_rti(RoundingMode::RNE, a)), 4.0);
}

TEST(fp_cpp_wrapper, constants_and_comparisons)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Sort f16 = tm.mk_fp16_sort();
  s.add(fp_is_nan(tm.mk_fp_nan(f16)));
  s.add(fp_is_neg(tm.mk_fp_neg_inf(f16)));
  s.add(fp_is_neg(tm.mk_fp_neg_zero(f16)));
  s.add(fp_is_normal(tm.mk_fp_from_bits(f16, tm.mk_bv(16, 0x3C00)))); // 1.0

  const Term a = tm.declare("a", f16);
  s.add(fp_eq(a, 3.0));
  s.add(fp_lt(a, 4.0));
  s.add(fp_leq(a, 3.0));
  s.add(fp_geq(a, 3.0));
  s.add(!fp_eq(a, 5.0));
  s.add(fp_is_pos(a));
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST(fp_cpp_wrapper, bits_and_conversions)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Sort f16 = tm.mk_fp16_sort();
  const Term x = tm.declare("x", f16);
  s.add(fp_eq(x, tm.mk_fp_from_bits(f16, tm.mk_bv(16, 0x4200)))); // half 3.0
  const Term bits = fp_to_ieee_bv(x);
  const Term ubv = fp_to_ubv(8, RoundingMode::RNE, x);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(ieee_bits(s, x), 0x4200u);
  EXPECT_EQ(s.model().uint64_value(bits), 0x4200u);
  EXPECT_EQ(s.model().uint64_value(ubv), 3u);

  TermManager tm2;
  Solver s2(tm2, sanity_checked());
  const Sort g16 = tm2.mk_fp16_sort();
  const Term y = tm2.declare("y", g16);
  s2.add(fp_eq(y, tm2.mk_fp_from_bits(g16, tm2.mk_bv(16, 0xC000)))); // -2.0
  ASSERT_TRUE(s2.check_sat().is_sat());
  EXPECT_EQ(s2.model().uint64_value(fp_to_sbv(8, RoundingMode::RNE, y)), 0xFEu);
}

// The double can be on either side of an operator.
TEST(fp_cpp_wrapper, double_on_the_left)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Term x = tm.declare("dl_x", tm.mk_fp32_sort());
  s.add(fp_eq(2.0 * x, 3.0));
  s.add(fp_lt(1.0, x));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(model_double(s, x), 1.5);
}

// Half-precision models decode to native doubles (exactly representable).
TEST(fp_cpp_wrapper, half_precision_model)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Sort f16 = tm.mk_fp16_sort();
  const Term h = tm.declare("hp_h", f16);
  s.add(fp_eq(h, tm.mk_fp_from_bits(f16, tm.mk_bv(16, 0x4100)))); // 2.5
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(model_double(s, h), 2.5);
}

// Mixed formats are refused instead of building a malformed node: a sort
// error, thrown as a RecoverableError (the wrapper threw
// std::invalid_argument).
TEST(fp_cpp_wrapper, mixed_formats_throw)
{
  TermManager tm;
  const Term a = tm.declare("mf_a", tm.mk_fp32_sort());
  const Term b = tm.declare("mf_b", tm.mk_fp64_sort());
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(a + b));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)fp_eq(a, b));
}

// A Solver can be moved (e.g. returned from a factory). It keeps its manager
// alive by itself, and a moved-from Solver gives up the solver: it destroys
// nothing and refuses every call.
namespace
{

Solver make_solver()
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Term x = tm.declare("mv_x", tm.mk_fp32_sort());
  s.add(fp_eq(x, 2.0));
  return s;
}

} // namespace

TEST(fp_cpp_wrapper, solver_is_movable)
{
  Solver s = make_solver();
  ASSERT_TRUE(s.check_sat().is_sat());

  Solver moved = std::move(s);
  ASSERT_TRUE(moved.check_sat().is_sat());
  const std::optional<Term> x = moved.manager().symbol("mv_x");
  ASSERT_TRUE(x.has_value());
  EXPECT_EQ(model_double(moved, *x), 2.0);
  API3_EXPECT_ERROR(ErrorCode::STATE, s.check_sat());
}

// The wrapper could wrap a checker it did not own, leaving it alive for its
// real owner. A manager is shared by every handle to it: a second handle, and
// a solver made over that handle, go away without taking the manager along.
TEST(fp_cpp_wrapper, non_owning_wrap)
{
  TermManager tm;
  {
    TermManager handle = tm;
    Solver s(handle, sanity_checked());
    const Term x = handle.declare("no_x", handle.mk_fp32_sort());
    handle.set_default_rounding_mode(RoundingMode::RTZ);
    EXPECT_EQ(handle.default_rounding_mode(), RoundingMode::RTZ);
    s.add(fp_is_normal(x) || !fp_is_normal(x)); // exercises || and !
    ASSERT_TRUE(s.check_sat().is_sat());
  }
  // Still usable after the handle and its solver died: they did not destroy
  // the manager, and what they declared and set belongs to it.
  EXPECT_EQ(tm.default_rounding_mode(), RoundingMode::RTZ);
  EXPECT_TRUE(tm.symbol("no_x").has_value());
  Solver s(tm, sanity_checked());
  s.add(tm.mk_true());
  EXPECT_TRUE(s.check_sat().is_sat());
}

// The wrapper decoded only the half, single and double formats to a double
// and threw on any other. The API decodes every format that a double holds
// exactly, so (3, 5) reads as +0.0; only a format wider than binary64 has no
// double, which to_double() reports as empty rather than by throwing. The
// bits read at every width.
TEST(fp_cpp_wrapper, model_throws_on_odd_format)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Sort odd = tm.mk_fp_sort(3, 5);
  const Term t = tm.declare("of_t", odd);
  // fp.eq alone would leave two legal models (fp.eq(+0, -0) holds); pin the
  // sign too, or the expected bits depend on the solver's choice.
  s.add(fp_eq(t, tm.mk_fp_pos_zero(odd)));
  s.add(fp_is_pos(t));
  ASSERT_TRUE(s.check_sat().is_sat());
  const std::optional<double> d = s.model().fp_value(t).to_double();
  ASSERT_TRUE(d.has_value());
  EXPECT_EQ(*d, 0.0);
  EXPECT_FALSE(std::signbit(*d));
  EXPECT_EQ(ieee_bits(s, t), 0u);

  const Sort wide = tm.mk_fp128_sort();
  const Term w = tm.declare("of_w", wide);
  s.add(fp_eq(w, tm.mk_fp_pos_zero(wide)));
  s.add(fp_is_pos(w));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_FALSE(s.model().fp_value(w).to_double().has_value());
  EXPECT_EQ(s.model().fp_value(w).bits(), std::string(128, '0'));
}

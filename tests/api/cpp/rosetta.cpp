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

// rosetta.cpp -- seven small end-to-end programs, one per theory and one
// for solver control (the Python versions are in tests/api/python), each run
// against the real API and checked for its expected outcome; the checks stand
// where a user program would print.

#include "api_common.hpp"

#include <cmath>
#include <sstream>

using namespace stp;

namespace
{

// R1: x, y : BV32, w : BV128; x*3 = 7, y = x >>u 1, w = zext96(x) << 64.
// Expected x = 0xaaaaaaad.
TEST(Rosetta, R1_bitvectors)
{
  stp::TermManager tm;
  stp::Solver s(tm);
  auto x = tm.declare("x", tm.mk_bv_sort(32)), y = tm.declare("y", tm.mk_bv_sort(32));
  auto w = tm.declare("w", tm.mk_bv_sort(128));
  s.add(x * 3 == 7);
  s.add(y == stp::bvlshr(x, 1));
  s.add(w == (stp::zero_extend(96, x) << 64));
  ASSERT_TRUE(s.check_sat().is_sat());
  auto m = s.model();
  EXPECT_EQ(m.uint64_value(x), 0xaaaaaaadu);
  EXPECT_EQ(m.int64_value(x), -1431655763); // the same bits, signed
  EXPECT_EQ(m.bv_string(x, 16), "aaaaaaad");
  EXPECT_EQ(m.uint64_value(y), 0xaaaaaaadu >> 1);
  EXPECT_EQ(m.bv_string(w, 10), "52818775052551961234351587328"); // 0xaaaaaaad * 2^64, exact
  EXPECT_EQ(m.bv_string(w, 16), "00000000aaaaaaad0000000000000000");
  EXPECT_FALSE(m.value(w).fits_uint64());
  std::ostringstream out;
  out << m.uint64_value(x) << " " << m.int64_value(x) << " " << m.bv_string(x, 16) << "\n";
  out << m.uint64_value(y) << " " << m.bv_string(w, 10) << "\n";
  EXPECT_EQ(out.str(), "2863311533 -1431655763 aaaaaaad\n1431655766 52818775052551961234351587328\n");
}

// R2: a : Float32, b : Float64, rm : RoundingMode; fp.eq(fp.add RNE a 1.5, 3.0);
// not isNaN(b) and b < 0; not fp.eq(fp.div rm 1 3, fp.div RNE 1 3).
TEST(Rosetta, R2_floating_point)
{
  using stp::RoundingMode;
  stp::TermManager tm;
  stp::Solver s(tm);
  auto f32 = tm.mk_fp32_sort(), f64 = tm.mk_fp64_sort();
  auto a = tm.declare("a", f32), b = tm.declare("b", f64), rm = tm.declare("rm", tm.mk_rm_sort());
  s.add(stp::fp_eq(stp::fp_add(RoundingMode::RNE, a, 1.5), 3.0));
  s.add(!stp::fp_is_nan(b) && stp::fp_lt(b, 0.0));
  auto one = tm.mk_fp(f64, RoundingMode::RNE, 1.0), three = tm.mk_fp(f64, RoundingMode::RNE, 3.0);
  s.add(!stp::fp_eq(stp::fp_div(rm, one, three), stp::fp_div(tm.mk_rm(RoundingMode::RNE), one, three)));
  ASSERT_TRUE(s.check_sat().is_sat());
  auto m = s.model();
  auto av = m.fp_value(a), bv = m.fp_value(b);
  ASSERT_TRUE(av.to_double().has_value());
  EXPECT_NEAR(*av.to_double(), 1.5, 1e-6); // a + 1.5 rounds to 3.0 in binary32
  EXPECT_TRUE(m.bool_value(stp::fp_eq(stp::fp_add(RoundingMode::RNE, m.value(a), 1.5), 3.0)));
  EXPECT_EQ(av.bits().size(), 32u);
  EXPECT_FALSE(av.sign);
  EXPECT_EQ(av.biased_exponent, 127u); // a is in [1, 2)
  ASSERT_EQ(av.significand.size(), 1u);
  EXPECT_LT(av.significand[0], 1ull << 23); // 23 trailing bits
  EXPECT_NE(bv.cls, FloatValue::Class::NOT_A_NUMBER);
  EXPECT_TRUE(bv.sign);
  ASSERT_TRUE(bv.to_double().has_value());
  EXPECT_LT(*bv.to_double(), 0.0);
  EXPECT_TRUE(bv.cls == FloatValue::Class::NORMAL || bv.cls == FloatValue::Class::SUBNORMAL ||
              bv.cls == FloatValue::Class::INF);
  // 1/3 has no tie, so RNA agrees with RNE: the mode is one of the directed ones
  const RoundingMode mode = m.rm_value(rm);
  EXPECT_TRUE(mode == RoundingMode::RTP || mode == RoundingMode::RTN || mode == RoundingMode::RTZ)
      << stp::to_string(mode);
  std::ostringstream out;
  out << stp::to_string(m.rm_value(rm)) << "\n";
  EXPECT_EQ(out.str(), std::string(stp::to_string(mode)) + "\n");
}

// R3: 3x + 2y = 1, x > 1/2; exact rationals and doubles.
TEST(Rosetta, R3_reals)
{
  stp::TermManager tm;
  stp::Solver s(tm);
  auto x = tm.declare("x", tm.mk_real_sort()), y = tm.declare("y", tm.mk_real_sort());
  s.add(3 * x + 2 * y == 1);
  s.add(stp::real_gt(x, tm.mk_real(1, 2)));
  ASSERT_TRUE(s.check_sat().is_sat());
  auto m = s.model();
  auto xv = m.real_value(x), yv = m.real_value(y);
  ASSERT_TRUE(xv.fits_int64());
  ASSERT_TRUE(yv.fits_int64());
  // exactly: the values rebuilt as Real constants, whose arithmetic the
  // manager folds at construction, satisfy both constraints
  const stp::Term xc = tm.mk_real(xv.num64(), xv.den64());
  const stp::Term yc = tm.mk_real(yv.num64(), yv.den64());
  EXPECT_TRUE((3 * xc + 2 * yc).same_as(tm.mk_real(1)));
  EXPECT_TRUE(tm.simplify(stp::real_gt(xc, tm.mk_real(1, 2))).same_as(tm.mk_true()));
  EXPECT_GT(xv.to_double(), 0.5);
  EXPECT_NEAR(3 * xv.to_double() + 2 * yv.to_double(), 1.0, 1e-9);
  EXPECT_LT(yv.to_double(), -0.25); // y = (1 - 3x) / 2 < -1/4
  EXPECT_EQ(xv.str(), xv.denominator == "1" ? xv.numerator : xv.numerator + "/" + xv.denominator);
  EXPECT_TRUE(m.bool_value(3 * x + 2 * y == 1));
  std::ostringstream out;
  out << xv.str() << " = " << xv.to_double() << "\n" << yv.str() << " = " << yv.to_double() << "\n";
  EXPECT_NE(out.str().find(" = "), std::string::npos);
}

// R4: a, b : Array BV32 BV8, c = store(const #x00, 5, #x2a); a != b,
// a[0] = b[0], b = c; a's and b's entries and default, and a[5].
TEST(Rosetta, R4_arrays)
{
  stp::TermManager tm;
  stp::Solver s(tm);
  auto A = tm.mk_array_sort(tm.mk_bv_sort(32), tm.mk_bv_sort(8));
  auto a = tm.declare("a", A), b = tm.declare("b", A);
  auto c = stp::store(tm.mk_const_array(A, tm.mk_bv(8, 0)), tm.mk_bv(32, 5), tm.mk_bv(8, 0x2a));
  s.add(a != b);
  s.add(a[tm.mk_bv(32, 0)] == b[tm.mk_bv(32, 0)]);
  s.add(b == c); // an equality against a store over a constant array
  ASSERT_TRUE(s.check_sat().is_sat());
  auto m = s.model();
  EXPECT_TRUE(m.bool_value(b == c));
  EXPECT_EQ(m.array_value(b).default_value().to_uint64(), 0u);
  std::ostringstream out;
  for (auto arr : {a, b})
  {
    auto v = m.array_value(arr);
    out << arr << ": default " << v.default_value();
    for (auto& e : v.entries())
      out << " [" << e.index << " -> " << e.element << "]";
    out << "\n";
  }
  out << "a[5] = " << m.value(a[tm.mk_bv(32, 5)]) << "\n";
  EXPECT_NE(out.str().find("a: default"), std::string::npos);
  EXPECT_NE(out.str().find("b: default"), std::string::npos);
  EXPECT_NE(out.str().find("a[5] = "), std::string::npos);
  EXPECT_EQ(m.uint64_value(b[tm.mk_bv(32, 5)]), 0x2au);
  EXPECT_EQ(m.uint64_value(b[tm.mk_bv(32, 0)]), 0u);
  EXPECT_EQ(m.uint64_value(a[tm.mk_bv(32, 0)]), 0u);
  EXPECT_TRUE(m.bool_value(a != b)); // extensional: they differ somewhere
  EXPECT_FALSE(m.bool_value(a == b));
  EXPECT_EQ(m.array_value(b).at(tm.mk_bv(32, 5)).to_uint64(), 0x2au);
  EXPECT_TRUE(m.array_value(a).default_value().is_value());
  EXPECT_TRUE(m.value(a[tm.mk_bv(32, 5)]).is_value());
}

// R5: f : BV8 -> BV8, g : BV8 x BV8 -> Bool; f(x) != f(y), g(x, f(x)), x = 3;
// f's and g's entries and else; f(3) and f(y).
TEST(Rosetta, R5_uninterpreted_functions)
{
  stp::TermManager tm;
  stp::Solver s(tm);
  auto B8 = tm.mk_bv_sort(8);
  auto f = tm.declare("f", tm.mk_fun_sort({B8}, B8)), g = tm.declare("g", tm.mk_fun_sort({B8, B8}, tm.mk_bool_sort()));
  auto x = tm.declare("x", B8), y = tm.declare("y", B8);
  s.add(f(x) != f(y));
  s.add(g(x, f(x)));
  s.add(x == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  auto m = s.model();
  std::ostringstream out;
  for (auto fn : {f, g})
  {
    auto v = m.function_value(fn);
    out << fn << ": else " << v.else_value();
    for (auto& e : v.entries())
    {
      out << " (";
      for (auto& arg : e.args)
        out << arg << " ";
      out << "-> " << e.value << ")";
    }
    out << "\n";
  }
  out << "f(3) = " << m.value(f(tm.mk_bv(8, 3))) << ", f(y) = " << m.value(f(y)) << "\n";
  EXPECT_NE(out.str().find("f: else"), std::string::npos) << out.str();
  EXPECT_NE(out.str().find("g: else"), std::string::npos) << out.str();
  EXPECT_NE(out.str().find("f(3) = "), std::string::npos);
  EXPECT_EQ(m.uint64_value(x), 3u);
  EXPECT_NE(m.uint64_value(y), 3u); // f(x) != f(y) forces x != y
  EXPECT_TRUE(m.value(f(tm.mk_bv(8, 3))).same_as(m.value(f(x))));
  EXPECT_FALSE(m.value(f(y)).same_as(m.value(f(x))));
  EXPECT_TRUE(m.bool_value(g(x, f(x))));
  EXPECT_TRUE(m.bool_value(g(tm.mk_bv(8, 3), m.value(f(x)))));
  auto fv = m.function_value(f);
  EXPECT_GE(fv.size(), 2u);
  EXPECT_TRUE(fv.apply({tm.mk_bv(8, 3)}).same_as(m.value(f(x))));
  EXPECT_TRUE(fv.else_value().is_value());
  auto gv = m.function_value(g);
  EXPECT_TRUE(gv.apply({tm.mk_bv(8, 3), m.value(f(x))}).to_bool());
  EXPECT_TRUE(gv.else_value().sort().is_bool());
}

// R6: models on, a 500 ms limit and a seed; push; p => x = 0;
// check-sat-assuming [p, x != 0]; failed assumptions; pop; check again.
TEST(Rosetta, R6_solver_control)
{
  stp::TermManager tm;
  stp::Options o;
  o.set_bool(stp::Option::PRODUCE_MODELS, true);
  o.set_duration("max-time", std::chrono::milliseconds(500));
  o.set_uint("random-seed", 7);
  stp::Solver s(tm, o);
  s.push();
  auto p = tm.declare("p", tm.mk_bool_sort()), x = tm.declare("x", tm.mk_bv_sort(32));
  auto x_is_0 = (x == 0);
  s.add(stp::implies(p, x_is_0));
  auto r = s.check_sat({p, !x_is_0});
  EXPECT_TRUE(r.is_unsat());
  std::ostringstream out;
  if (r.is_unsat())
    for (auto& t : s.unsat_assumptions())
      out << "failed: " << t << "\n";
  EXPECT_NE(out.str().find("failed: "), std::string::npos);
  EXPECT_FALSE(s.unsat_assumptions().empty());
  EXPECT_LE(s.unsat_assumptions().size(), 2u);
  for (auto& t : s.unsat_assumptions())
    EXPECT_TRUE(t.same_as(p) || t.same_as(!x_is_0));
  EXPECT_EQ(s.level(), 1u); // the assumptions were not asserted
  s.pop();
  r = s.check_sat();
  EXPECT_TRUE(r.is_sat()) << r;
  std::ostringstream out2;
  if (r.is_unknown())
    out2 << "unknown: " << r.reason() << " (" << r.reason_message() << ")\n";
  else
    out2 << r << "\n";
  EXPECT_EQ(out2.str(), "sat\n");
  EXPECT_EQ(s.options().get_duration("max-time").count(), 500);
  EXPECT_EQ(s.options().get_uint("random-seed"), 7u);
  EXPECT_TRUE(s.options().get_bool("produce-models"));
  EXPECT_EQ(s.assertions().size(), 0u); // the implication went with the pop
}

// R7: bvadd u v with u : BV8, v : BV16; the error surfaces and the solver
// stays usable.
TEST(Rosetta, R7_errors)
{
  stp::TermManager tm;
  stp::Solver s(tm);
  auto u = tm.declare("u", tm.mk_bv_sort(8)), v = tm.declare("v", tm.mk_bv_sort(16));
  std::ostringstream out;
  try
  {
    stp::bvadd(u, v);
    FAIL() << "the mismatch was not reported";
  }
  catch (const stp::RecoverableError& e)
  {
    out << stp::to_string(e.code()) << " at argument " << *e.argument_index() << ": " << e.what() << "\n";
  }
  EXPECT_EQ(out.str().rfind("SORT_MISMATCH at argument 1: invalid call to 'bvadd'", 0), 0u);
  s.add(u == 1);
  std::ostringstream still;
  still << "solver still works: " << s.check_sat() << "\n";
  EXPECT_EQ(still.str(), "solver still works: sat\n");
  EXPECT_EQ(s.model().uint64_value(u), 1u);
}

} // namespace

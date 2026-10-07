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

// fp-to-real.cpp -- fp.to_real over symbolic floats: the term's view and
// printing, exact values through the solver in several formats, NaN and the
// infinities as functions, models of conversions built after the check,
// substitution, simplification, parsing, and the formats the exact
// arithmetic cannot hold.

#include "api_common.hpp"

#include <string>

using namespace stp;

namespace
{

class FpToReal : public ::testing::Test
{
protected:
  TermManager tm;
  Solver s{tm};
  Sort f16 = tm.mk_fp_sort(5, 11), f32 = tm.mk_fp32_sort(), f64 = tm.mk_fp64_sort();
  Sort f128 = tm.mk_fp_sort(15, 113), R = tm.mk_real_sort();
  Term x = tm.declare("x", f32), y = tm.declare("y", f32);
  Term rx = fp_to_real(x), ry = fp_to_real(y);

  Term finite(const Term& f) { return !fp_is_nan(f) && !fp_is_inf(f); }

  // The exact value of a float value, from its fields.
  static std::string exact(const Term& v)
  {
    const std::optional<RationalValue> q = v.to_fp().to_rational();
    return q ? q->str() : "none";
  }
};

TEST_F(FpToReal, the_term_is_the_conversion)
{
  for (const bool simplify : {true, false})
  {
    TermManager::Config cfg;
    cfg.simplify = simplify;
    TermManager m(cfg);
    const Term a = m.declare("a", m.mk_fp32_sort());
    const Term t = fp_to_real(a);
    EXPECT_EQ(t.kind(), Kind::FP_TO_REAL);
    EXPECT_TRUE(t.sort() == m.mk_real_sort());
    ASSERT_EQ(t.num_children(), 1u);
    EXPECT_TRUE(t.child(0).same_as(a));
    EXPECT_TRUE(t.indices().empty());
    EXPECT_FALSE(t.is_value());
    EXPECT_FALSE(t.is_const());
    EXPECT_FALSE(t.symbol().has_value());
    // both doors, and the view's round trip, lead to one term
    EXPECT_TRUE(m.mk_term(Kind::FP_TO_REAL, {a}).same_as(t));
    EXPECT_TRUE(m.mk_term(t.kind(), t.children()).same_as(t));
    EXPECT_TRUE(fp_to_real(a).same_as(t));
    // printed as what it is, in every SMT-LIB form
    EXPECT_EQ(t.str(), "(fp.to_real a)");
    EXPECT_NE(real_add(t, m.mk_real(1)).str().find("(fp.to_real a)"), std::string::npos);
    const std::string shared = t.to_string(Format::SMTLIB2, true);
    EXPECT_NE(shared.find("fp.to_real"), std::string::npos) << shared;
    EXPECT_EQ(shared.find('@'), std::string::npos) << shared;
  }
  // the operand may be any float term
  const Term sum = fp_add(RoundingMode::RNE, x, y);
  EXPECT_TRUE(fp_to_real(sum).child(0).same_as(sum));
  EXPECT_EQ(fp_to_real(sum).str(), "(fp.to_real (fp.add RNE x y))");
  // a non-float operand is a sort error
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, fp_to_real(tm.declare("bv", tm.mk_bv_sort(32))));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, fp_to_real(tm.mk_real(1)));
  EXPECT_EQ(capabilities()["kind.FP_TO_REAL"], "true");
}

TEST_F(FpToReal, values_fold_exactly)
{
  EXPECT_TRUE(fp_to_real(tm.mk_fp(f32, RoundingMode::RNE, 1.5)).same_as(tm.mk_real(3, 2)));
  EXPECT_TRUE(fp_to_real(tm.mk_fp(f32, RoundingMode::RNE, -2.5)).same_as(tm.mk_real(-5, 2)));
  EXPECT_TRUE(fp_to_real(tm.mk_fp_pos_zero(f32)).same_as(tm.mk_real(0)));
  EXPECT_TRUE(fp_to_real(tm.mk_fp_neg_zero(f32)).same_as(tm.mk_real(0)));
  // the smallest subnormal and the largest finite value of binary32
  EXPECT_EQ(fp_to_real(tm.mk_fp_from_bits(f32, "0x00000001")).to_rational().str(),
            "1/713623846352979940529142984724747568191373312");
  EXPECT_EQ(fp_to_real(tm.mk_fp_from_bits(f32, "0x7f7fffff")).to_rational().str(),
            "340282346638528859811704183484516925440");
  EXPECT_EQ(fp_to_real(tm.mk_fp_from_bits(f32, "0xff7fffff")).to_rational().str(),
            "-340282346638528859811704183484516925440");
  // every format, from its fields
  for (const Sort& f : {f16, f32, f64, f128, tm.mk_fp_sort(2, 3), tm.mk_fp_sort(3, 2)})
    for (const char* bits : {"1", "10", "11", "101"})
    {
      const std::uint32_t w = f.fp_exp_size() + f.fp_sig_size();
      std::string pattern(w, '0');
      for (std::size_t i = 0; bits[i] != 0; ++i)
        pattern[1 + i] = bits[i]; // just below the sign
      const Term v = tm.mk_fp_from_bits(f, "0b" + pattern);
      const Term c = fp_to_real(v);
      if (!c.is_value())
        continue; // NaN or an infinity in a tiny format
      EXPECT_EQ(c.to_rational().str(), exact(v)) << v;
    }
}

TEST_F(FpToReal, nan_and_the_infinities_are_functions)
{
  // not values, and printed over the special value they convert
  const Term nan = fp_to_real(tm.mk_fp_nan(f32));
  EXPECT_EQ(nan.kind(), Kind::FP_TO_REAL);
  EXPECT_FALSE(nan.is_value());
  EXPECT_TRUE(nan.child(0).same_as(tm.mk_fp_nan(f32)));
  // every NaN is one argument, so one result
  s.add(fp_is_nan(x));
  s.add(fp_is_nan(y));
  s.add(rx != ry);
  EXPECT_TRUE(s.check_sat().is_unsat());
  s.reset_assertions();
  s.add(fp_is_nan(x));
  s.add(rx != nan);
  EXPECT_TRUE(s.check_sat().is_unsat());
  // the same for each infinity
  s.reset_assertions();
  s.add(x == tm.mk_fp_pos_inf(f32));
  s.add(rx != fp_to_real(tm.mk_fp_pos_inf(f32)));
  EXPECT_TRUE(s.check_sat().is_unsat());
  // but nothing ties NaN, +oo and -oo to each other or to a finite value
  s.reset_assertions();
  s.add(fp_is_nan(x));
  s.add(fp_is_inf(y));
  s.add(rx == ry);
  s.add(rx == tm.mk_real(7));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().real_value(ry).str(), "7");
  s.reset_assertions();
  s.add(fp_to_real(tm.mk_fp_pos_inf(f32)) != fp_to_real(tm.mk_fp_neg_inf(f32)));
  EXPECT_TRUE(s.check_sat().is_sat());
  // one format's constants are not another's
  s.reset_assertions();
  s.add(fp_to_real(tm.mk_fp_nan(f32)) != fp_to_real(tm.mk_fp_nan(f64)));
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST_F(FpToReal, exact_solving)
{
  // 1/10 is no binary32 value: only NaN and the infinities reach it
  s.add(rx == tm.mk_real(1, 10));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_NE(s.model().value(x).to_fp().cls, FloatValue::Class::NORMAL);
  s.add(finite(x));
  EXPECT_TRUE(s.check_sat().is_unsat());
  // a range with finite floats in it
  s.reset_assertions();
  s.add(real_gt(rx, 1000));
  s.add(real_lt(rx, tm.mk_real(2001, 2)));
  s.add(finite(x));
  ASSERT_TRUE(s.check_sat().is_sat());
  {
    const Model m = s.model();
    const Term v = m.value(x);
    EXPECT_EQ(m.real_value(rx).str(), exact(v));
    const double d = *v.to_fp().to_double();
    EXPECT_GT(d, 1000.0);
    EXPECT_LT(d, 1000.5);
  }
  // through a Real symbol defined as the conversion
  s.reset_assertions();
  const Term r = tm.declare("r", R);
  s.add(r == rx);
  s.add(real_lt(r, tm.mk_real(-1, 3)));
  s.add(real_gt(r, tm.mk_real(-1, 2)));
  s.add(finite(x));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().real_value(r).str(), exact(s.model().value(x)));
  // zero of either sign converts to 0
  s.reset_assertions();
  s.add(fp_is_zero(x));
  s.add(rx != 0);
  EXPECT_TRUE(s.check_sat().is_unsat());
  // (-oo converts to a Real of the solve's choosing, 0 among them, so only
  // finiteness makes -0 the one answer)
  s.reset_assertions();
  s.add(rx == 0);
  s.add(fp_is_neg(x));
  s.add(finite(x));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.model().value(x).same_as(tm.mk_fp_neg_zero(f32)));
  // the conversion is monotone on finite floats
  s.reset_assertions();
  s.add(fp_lt(x, y));
  s.add(real_ge(rx, ry));
  s.add(finite(x));
  s.add(finite(y));
  EXPECT_TRUE(s.check_sat().is_unsat());
  // and no finite binary32 exceeds the largest one
  s.reset_assertions();
  s.add(real_gt(rx, fp_to_real(tm.mk_fp_from_bits(f32, "0x7f7fffff"))));
  s.add(finite(x));
  EXPECT_TRUE(s.check_sat().is_unsat());
  // the smallest subnormal is reached by exactly one float
  s.reset_assertions();
  s.add(rx == fp_to_real(tm.mk_fp_from_bits(f32, "0x00000001")));
  s.add(finite(x));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.model().value(x).same_as(tm.mk_fp_from_bits(f32, "0x00000001")));
}

TEST_F(FpToReal, other_formats)
{
  for (const Sort& f : {f16, f64, f128})
  {
    SCOPED_TRACE(f.str());
    const Term a = tm.mk_fresh(f, "a");
    const Term ra = fp_to_real(a);
    s.reset_assertions();
    s.add(!fp_is_nan(a) && !fp_is_inf(a));
    s.add(real_gt(ra, tm.mk_real(3, 2)));
    s.add(real_lt(ra, tm.mk_real(7, 4)));
    ASSERT_TRUE(s.check_sat().is_sat());
    const Model m = s.model();
    EXPECT_EQ(m.real_value(ra).str(), exact(m.value(a)));
    s.add(ra == tm.mk_real(1, 3));
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
}

TEST_F(FpToReal, models_of_terms_built_after_the_check)
{
  s.add(x == tm.mk_fp(f32, RoundingMode::RNE, -0.75));
  s.add(fp_is_nan(y));
  s.add(real_lt(ry, 0) && real_gt(ry, -1)); // the solve chooses NaN's value
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(m.real_value(rx).str(), "-3/4");
  EXPECT_EQ(m.real_value(real_mul(tm.mk_real(4), rx)).str(), "-3");
  const RationalValue chosen = m.real_value(ry);
  EXPECT_TRUE(m.try_value(ry).has_value());
  // a conversion the solve never saw, of a float it did
  const Term z = tm.declare("z", f64);
  EXPECT_EQ(m.real_value(fp_to_real(to_fp(f64, RoundingMode::RNE, x))).str(), "-3/4");
  // NaN converts to the solve's choice for its format...
  EXPECT_EQ(m.real_value(fp_to_real(tm.mk_fp_nan(f32))).str(), chosen.str());
  // ...and, where the solve never met the format, to a completion
  EXPECT_EQ(m.real_value(fp_to_real(tm.mk_fp_nan(f64))).str(), "0");
  EXPECT_FALSE(m.try_value(fp_to_real(tm.mk_fp_nan(f64))).has_value());
  EXPECT_EQ(m.real_value(fp_to_real(z)).str(), "0"); // z completes to +0
  EXPECT_FALSE(m.try_value(fp_to_real(z)).has_value());
}

TEST_F(FpToReal, substitute_simplify_and_parse)
{
  // substitution rebuilds the conversion over the new operand
  const Term sub = rx.substitute({{x, y}});
  EXPECT_TRUE(sub.same_as(ry));
  const Term folded = real_add(rx, 1).substitute({{x, tm.mk_fp(f32, RoundingMode::RNE, 0.5)}});
  EXPECT_TRUE(folded.same_as(tm.mk_real(3, 2)));
  // simplification folds a conversion whose operand folds
  TermManager raw = api_test::raw_manager();
  const Sort rf = raw.mk_fp32_sort();
  const Term sum = fp_add(RoundingMode::RNE, raw.mk_fp(rf, RoundingMode::RNE, 1.0),
                          raw.mk_fp(rf, RoundingMode::RNE, 2.0));
  const Term conv = fp_to_real(sum);
  EXPECT_EQ(conv.kind(), Kind::FP_TO_REAL);
  EXPECT_TRUE(raw.simplify(conv).same_as(raw.mk_real(3)));
  // parsing builds the same term
  EXPECT_TRUE(s.parse_term("(fp.to_real x)").same_as(rx));
  EXPECT_TRUE(s.parse_term("(+ (fp.to_real x) 1)").same_as(real_add(rx, 1)));
  // a script, and the script the solver writes back
  s.parse_smt2("(declare-fun r () Real)\n(assert (= r (fp.to_real y)))\n"
               "(assert (> r 2.0))\n(assert (< r 2.5))\n");
  ASSERT_TRUE(s.check_sat().is_sat());
  const std::string script = s.to_smt2();
  EXPECT_NE(script.find("(fp.to_real |y|)"), std::string::npos) << script;
  EXPECT_NE(script.find("(set-logic ALL)"), std::string::npos) << script;
  EXPECT_EQ(script.find('@'), std::string::npos) << script;
  TermManager again;
  Solver s2(again);
  s2.parse_smt2(script);
  EXPECT_TRUE(s2.check_sat().is_sat());
}

TEST_F(FpToReal, formats_beyond_the_exact_arithmetic)
{
  // the constants of a 17-bit exponent need 2^65536, past the number limits
  const Term wide = tm.declare("wide", tm.mk_fp_sort(17, 8));
  auto e = API_ERROR_OF(fp_to_real(wide));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::UNSUPPORTED);
  EXPECT_NE(std::string(e->what()).find("number limits"), std::string::npos) << e->what();
  // the manager is not poisoned: 16 bits still build
  const Term t = fp_to_real(tm.declare("w16", tm.mk_fp_sort(16, 8)));
  EXPECT_EQ(t.kind(), Kind::FP_TO_REAL);
}

// At 16 bits the constants fit, but relating two conversions can need more
// than the number limits allow: a solve that runs into them stops, which is an
// unknown answer with its reason -- it was an engine error (unknown(OTHER),
// "no answer"; SOLVER_ERROR and exit 255 on the command line), and the solver
// goes on. Whether this one does is the search's doing: NaN and the infinities
// convert to Real constants of their own, and a search that tries them answers
// sat without relating two conversions at all.
TEST_F(FpToReal, a_relation_beyond_the_number_limits_is_not_an_error)
{
  const Sort w16 = tm.mk_fp_sort(16, 3);
  const Term a = tm.declare("a", w16), b = tm.declare("b", w16);
  Solver s(tm);
  s.push();
  s.add(real_lt(fp_to_real(a), fp_to_real(b)));
  const Result r = s.check_sat();
  if (!r.is_sat())
  {
    EXPECT_TRUE(r.is_unknown());
    EXPECT_EQ(r.reason(), UnknownReason::INCOMPLETE);
    EXPECT_NE(r.reason_message().find("number limits"), std::string::npos) << r.reason_message();
  }
  s.pop();
  s.add(fp_is_zero(a));
  EXPECT_TRUE(s.check_sat().is_sat());
}

} // namespace

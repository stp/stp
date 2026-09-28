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

// fp-arithmetic.cpp -- floating-point arithmetic built through the API
// and its results read back from a model: every operation, rounding after
// each operation of a chain, the classification and ordering predicates as
// constraints, and the kinds the operations report.
//
// All values are half precision (eb=5, sb=11): 2.0 is 0x4000, 4.0 is 0x4400
// and -2.0 is 0xC000.

#include "api_common.hpp"

#include <cstdint>
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

Term half(TermManager& tm, std::uint64_t bits)
{
  return tm.mk_fp_from_bits(tm.mk_fp_sort(5, 11), tm.mk_bv(16, bits));
}

// The packed interchange bits of a float's value in the model.
std::uint64_t packed(const Model& m, const Term& t)
{
  return std::stoull(m.fp_value(t).bits(), nullptr, 2);
}

} // namespace

TEST(fp_arithmetic, results)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Sort f = tm.mk_fp_sort(5, 11);
  const Term rne = tm.mk_rm(RoundingMode::RNE);

  const Term a = tm.declare("a", f);
  s.add(fp_eq(a, half(tm, 0x4000))); // a = 2.0

  const Term prod = fp_mul(rne, a, a); // 4.0
  const Term sum = fp_add(rne, a, a);  // 4.0
  const Term neg = fp_neg(a);          // -2.0

  // A floating-point operation returns a value of the operands' format.
  EXPECT_EQ(prod.sort().kind(), SortKind::FP);
  EXPECT_EQ(prod.sort().fp_exp_size(), 5u);
  EXPECT_EQ(prod.sort().fp_sig_size(), 11u);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(packed(m, prod), 0x4400u);
  EXPECT_EQ(packed(m, sum), 0x4400u);
  EXPECT_EQ(packed(m, neg), 0xC000u);
}

TEST(fp_arithmetic, more_ops)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Sort f = tm.mk_fp_sort(5, 11);
  const Term rne = tm.mk_rm(RoundingMode::RNE);

  const Term a = tm.declare("a", f);
  s.add(fp_eq(a, half(tm, 0x4400))); // a = 4.0
  const Term two = half(tm, 0x4000);  // 2.0

  const Term rt = fp_sqrt(rne, a);     // 2.0
  const Term dv = fp_div(rne, a, two); // 2.0
  const Term mn = fp_min(a, two);      // 2.0
  const Term mx = fp_max(a, two);      // 4.0

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(packed(m, rt), 0x4000u);
  EXPECT_EQ(packed(m, dv), 0x4000u);
  EXPECT_EQ(packed(m, mn), 0x4000u);
  EXPECT_EQ(packed(m, mx), 0x4400u);
}

// Each source fp.add is rounded before its result feeds the next operation.
// In binary16, 2^-11 is exactly halfway between 1.0 and its successor. RNE
// therefore rounds 1.0 + 2^-11 back to the even 1.0 on both additions. If a
// lowering accidentally carried an unrounded intermediate across the chain,
// the mathematical sum 1.0 + 2^-10 would instead be 0x3C01.
TEST(fp_arithmetic, nested_add_rounds_after_each_operation)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Sort f = tm.mk_fp_sort(5, 11);
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term x = tm.declare("x", f);
  const Term y = tm.declare("y", f);

  s.add(fp_eq(x, half(tm, 0x3C00))); // 1.0
  s.add(fp_eq(y, half(tm, 0x1000))); // 2^-11

  const Term once = fp_add(rne, x, y);
  const Term twice = fp_add(rne, once, y);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(packed(m, once), 0x3C00u);
  EXPECT_EQ(packed(m, twice), 0x3C00u);
}

// The predicates actually constrain the search: nothing is both NaN and zero,
// so this is unsatisfiable.
TEST(fp_arithmetic, predicates_constrain)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term x = tm.declare("x", tm.mk_fp_sort(5, 11));
  s.add(fp_is_nan(x));
  s.add(fp_is_zero(x));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(fp_arithmetic, sub_fma_rem_roundtointegral_abs)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term a = tm.declare("a", tm.mk_fp_sort(5, 11));
  s.add(fp_eq(a, half(tm, 0x4400))); // 4.0
  const Term two = half(tm, 0x4000);

  const Term sub = fp_sub(rne, a, two);           // 2.0
  const Term fma = fp_fma(rne, a, two, two);      // 4*2 + 2 = 10.0
  const Term rem = fp_rem(a, two);                // 0.0
  const Term rti = fp_rti(rne, half(tm, 0x4100)); // rti(2.5) = 2.0
  const Term ab = fp_abs(half(tm, 0xC000));       // |-2.0| = 2.0

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(packed(m, sub), 0x4000u);
  EXPECT_EQ(packed(m, fma), 0x4900u);
  EXPECT_EQ(packed(m, rem), 0x0000u);
  EXPECT_EQ(packed(m, rti), 0x4000u);
  EXPECT_EQ(packed(m, ab), 0x4000u);
}

TEST(fp_arithmetic, ordered_comparisons)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term a = tm.declare("a", tm.mk_fp_sort(5, 11));
  s.add(fp_eq(a, half(tm, 0x4200)));  // 3.0
  s.add(fp_lt(a, half(tm, 0x4400)));  // 3 < 4
  s.add(fp_leq(a, half(tm, 0x4200))); // 3 <= 3
  s.add(fp_gt(a, half(tm, 0x4000)));  // 3 > 2
  s.add(fp_geq(a, half(tm, 0x4200))); // 3 >= 3
  EXPECT_TRUE(s.check_sat().is_sat()); // all hold
}

TEST(fp_arithmetic, ordered_comparison_unsat)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term a = tm.declare("a", tm.mk_fp_sort(5, 11));
  s.add(fp_eq(a, half(tm, 0x4000))); // 2.0
  s.add(fp_gt(a, half(tm, 0x4400))); // 2 > 4
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(fp_arithmetic, is_subnormal_and_normal)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term x = tm.declare("x", tm.mk_fp_sort(5, 11));
  s.add(fp_eq(x, half(tm, 0x0001))); // smallest subnormal
  s.add(fp_is_subnormal(x));

  const Term y = tm.declare("y", tm.mk_fp_sort(5, 11));
  s.add(fp_eq(y, half(tm, 0x3C00))); // 1.0
  s.add(fp_is_normal(y));

  EXPECT_TRUE(s.check_sat().is_sat());
}

// kind() must label floating-point terms correctly: it reports the public
// Kind of the term as the manager built it.
TEST(fp_arithmetic, expr_kinds)
{
  TermManager tm;
  const Sort f = tm.mk_fp_sort(5, 11);
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term x = tm.declare("x", f);
  const Term y = tm.declare("y", f);

  EXPECT_EQ(fp_add(rne, x, y).kind(), Kind::FP_ADD);
  // The simplifying manager mirrors the less-thans onto the greater-thans (as
  // it does bvult onto bvugt), so fp_leq hands back an fp.geq term with the
  // operands swapped -- and kind() must label that term correctly.
  const Term leq = fp_leq(x, y);
  EXPECT_EQ(leq.kind(), Kind::FP_GEQ);
  ASSERT_EQ(leq.num_children(), 2u);
  EXPECT_TRUE(leq.child(0).same_as(y));
  EXPECT_TRUE(leq.child(1).same_as(x));
  EXPECT_EQ(fp_eq(x, y).kind(), Kind::FP_EQ);
  EXPECT_EQ(fp_is_nan(x).kind(), Kind::FP_IS_NAN);
  EXPECT_EQ(fp_to_ieee_bv(x).kind(), Kind::FP_TO_IEEE_BV);
  // The special values are values, not operations.
  EXPECT_EQ(tm.mk_fp_nan(f).kind(), Kind::VALUE);
  EXPECT_EQ(tm.mk_fp_pos_inf(f).kind(), Kind::VALUE);
}

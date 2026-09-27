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

// api3-fp-to-ieee-bv.cpp -- fp_to_ieee_bv, the reinterpretation of a float as
// its packed bits: its fields pulled out with extract and read from a model,
// the fields as real symbolic bit-vectors, and the sort checks that keep a
// float out of a bit-vector position without that conversion.

#include "api3_common.hpp"

#include <cstdint>

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

} // namespace

// fp_to_ieee_bv reinterprets a float as its packed bits, so the exponent and
// significand fields can be pulled out with extract. Half precision: 3.0 is
// 0x4200 (sign 0, exponent 0b10000 = 16, significand 0x200).
TEST(fp_to_ieee_bv, extract_fields)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const std::uint32_t eb = 5, sb = 11;
  const Sort half = tm.mk_fp_sort(eb, sb);
  const Term x = tm.declare("x", half);
  s.add(fp_eq(x, tm.mk_fp_from_bits(half, tm.mk_bv(16, 0x4200))));

  const Term bits = fp_to_ieee_bv(x);
  const Term expo = extract(sb + eb - 2, sb - 1, bits); // exponent
  const Term sig = extract(sb - 2, 0, bits);            // significand

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(m.uint64_value(bits), 0x4200u);
  EXPECT_EQ(m.uint64_value(expo), 16u);
  EXPECT_EQ(m.uint64_value(sig), 0x200u);
}

// The extracted field is a real symbolic bit-vector: constraining a float's
// exponent to all-ones while asserting it is zero is unsatisfiable.
TEST(fp_to_ieee_bv, exponent_constrains_classification)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const std::uint32_t eb = 5, sb = 11;
  const Term y = tm.declare("y", tm.mk_fp_sort(eb, sb));
  const Term expo = extract(sb + eb - 2, sb - 1, fp_to_ieee_bv(y));
  s.add(expo == tm.mk_bv(eb, 0x1F));
  s.add(fp_is_zero(y));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

// 3.x: a mis-sorted operand is a RecoverableError (SORT_MISMATCH) naming the
// argument, where 2.x ended the process; the manager is unchanged by it.
TEST(fp_to_ieee_bv, bitvector_operator_rejects_float_without_conversion)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_fp_sort(8, 24));
  const auto e = API3_ERROR_OF(bvnot(x));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::SORT_MISMATCH) << e->what();
  EXPECT_EQ(e->argument_index(), std::optional<int>(0));
  // the conversion is the way in
  EXPECT_EQ(bvnot(fp_to_ieee_bv(x)).sort().bv_size(), 32u);
}

TEST(fp_to_ieee_bv, ite_rejects_float_and_bitvector_branches)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_fp_sort(8, 24));
  const Term bits = tm.mk_bv(32, 0);
  const auto e = API3_ERROR_OF(ite(tm.mk_true(), x, bits));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::SORT_MISMATCH) << e->what();
  EXPECT_EQ(e->argument_index(), std::optional<int>(2));
}

TEST(fp_to_ieee_bv, equality_rejects_float_and_bitvector_operands)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_fp_sort(8, 24));
  const Term bits = tm.mk_bv(32, 0);
  const auto e = API3_ERROR_OF(eq(x, bits));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::SORT_MISMATCH) << e->what();
  EXPECT_EQ(e->argument_index(), std::optional<int>(1));
}

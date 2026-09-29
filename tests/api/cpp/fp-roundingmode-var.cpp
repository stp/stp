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

// fp-roundingmode-var.cpp -- a RoundingMode symbol made through the API
// is a real variable of the sort: it ranges over exactly the five modes, keeps
// its sort through every public expression shape, and works as the
// rounding-mode operand of the rounding operations. Guards the API-level twin
// of the parser's declaration constraint: the sort is carried in five bits,
// and a bare 5-bit carrier would satisfy the typechecker but denote 32
// "modes".

#include "api_common.hpp"

#include <optional>
#include <type_traits>
#include <vector>

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

const RoundingMode ALL_MODES[] = {RoundingMode::RNE, RoundingMode::RNA, RoundingMode::RTP,
                                  RoundingMode::RTN, RoundingMode::RTZ};

// The call must be refused with `code` by `function`, naming operand `argument`.
template <class F>
void expect_refused(ErrorCode code, const char* function, int argument, F&& call)
{
  const std::optional<RecoverableError> e = api_test::catch_error(call);
  ASSERT_TRUE(e.has_value()) << "no error from " << function;
  EXPECT_EQ(e->code(), code) << e->what();
  EXPECT_EQ(e->function(), function) << e->what();
  EXPECT_EQ(e->argument_index(), std::optional<int>(argument)) << e->what();
}

} // namespace

TEST(fp_roundingmode_var, ranges_over_exactly_five_modes)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Term r = tm.declare("r", tm.mk_rm_sort());

  for (const RoundingMode m : ALL_MODES)
    s.add(!(r == tm.mk_rm(m)));

  // Distinct from all five modes: must be unsatisfiable.
  EXPECT_TRUE(s.check_sat().is_unsat());
}

// Declaring a named symbol of the sort is the one call the case above makes,
// for this sort as for every other. The API's other door for a symbol, an
// anonymous one made from the sort by mk_fresh, builds the same constrained
// variable.
TEST(fp_roundingmode_var, declared_through_the_type)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Sort rmt = tm.mk_rm_sort();
  EXPECT_EQ(rmt.kind(), SortKind::RM);
  EXPECT_TRUE(rmt.is_rm());

  const Term r = tm.mk_fresh(rmt, "r");
  for (const RoundingMode m : ALL_MODES)
    s.add(!(r == tm.mk_rm(m)));

  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(fp_roundingmode_var, source_sort_survives_public_expression_shapes)
{
  TermManager tm;
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term r = tm.declare("r", tm.mk_rm_sort());
  const Term c = tm.declare("c", tm.mk_bool_sort());
  const Term choice = ite(c, rne, r);
  const Term array = tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(1), tm.mk_rm_sort()));
  const Term read = select(array, tm.mk_bv(1, 0));

  EXPECT_TRUE(rne.sort().is_rm());
  EXPECT_TRUE(r.sort().is_rm());
  EXPECT_TRUE(choice.sort().is_rm());
  EXPECT_TRUE(read.sort().is_rm());
  EXPECT_EQ(rne.sort().kind(), SortKind::RM);
}

// The carrier never stands in for the sort, nor the sort for its carrier.
// Each mix is refused -- as a recoverable error naming the call and the
// operand, which leaves the manager as it was, where the 2.x API ended the
// process.
TEST(fp_roundingmode_var, release_api_rejects_carrier_source_mixes)
{
  TermManager tm;
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term bits = tm.mk_bv(5, 1);

  // Equality requires operands of the same sort.
  expect_refused(ErrorCode::SORT_MISMATCH, "eq", 1, [&] { (void)eq(rne, bits); });

  // A bitvector operation requires bitvector operands.
  expect_refused(ErrorCode::SORT_MISMATCH, "bvnot", 0, [&] { (void)bvnot(rne); });

  // A rounding operation expects a rounding mode, not five bits.
  const Term x = tm.declare("x", tm.mk_fp32_sort());
  expect_refused(ErrorCode::SORT_MISMATCH, "fp_add", 0, [&] { (void)fp_add(bits, x, x); });

  // A term is never a sort: that is a compile error here. The one Sort value
  // that names no sort, the null one, is refused.
  static_assert(!std::is_convertible_v<Term, Sort>, "a term must not convert to a sort");
  expect_refused(ErrorCode::NULL_HANDLE, "TermManager::declare", 1,
                 [&] { (void)tm.declare("not_a_type", Sort()); });

  // A name declared as a rounding mode cannot be redeclared as its carrier.
  const Term same = tm.declare("same_name", tm.mk_rm_sort());
  expect_refused(ErrorCode::SORT_MISMATCH, "TermManager::declare", 0,
                 [&] { (void)tm.declare("same_name", tm.mk_bv_sort(5)); });
  EXPECT_TRUE(tm.declare("same_name", tm.mk_rm_sort()).same_as(same));
}

TEST(fp_roundingmode_var, model_completion_after_declaration_scope)
{
  TermManager tm;
  Solver s(tm, sanity_checked());

  // Declare inside a scope that is then popped: the symbol outlives the
  // scope. With no use in the solved formula, the model must complete this
  // RoundingMode value itself.
  s.push();
  const Term r = tm.declare("scoped_r", tm.mk_rm_sort());
  s.pop();
  ASSERT_TRUE(s.check_sat().is_sat());

  EXPECT_EQ(s.value(r).to_rm(), RoundingMode::RNE);
  EXPECT_TRUE(s.value(r).sort().is_rm());

  // A held model, and its batch reader, complete the same way and must
  // preserve the same sort invariant. That the value is a completion shows in
  // try_value, which refuses to complete.
  const Model whole = s.model();
  EXPECT_FALSE(whole.try_value(r).has_value());
  EXPECT_EQ(whole.rm_value(r), RoundingMode::RNE);
  const std::vector<Term> values = whole.values({r});
  ASSERT_EQ(values.size(), 1u);
  EXPECT_EQ(values[0].to_rm(), RoundingMode::RNE);
  EXPECT_TRUE(values[0].sort().is_rm());
}

TEST(fp_roundingmode_var, drives_an_operation_and_reads_back)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const Term r = tm.declare("r", tm.mk_rm_sort());

  // 2.5 in half precision is 0x4100; fp.to_sbv of it under r gives 2 only
  // for the truncating modes -- forcing the result to 3 leaves r one of
  // RNA/RTP (round up), so the model's r must be a legal mode with that
  // behaviour.
  const Term two_and_a_half = tm.mk_fp_from_bits(tm.mk_fp16_sort(), tm.mk_bv(16, 0x4100));
  const Term out = tm.declare("out", tm.mk_bv_sort(8));
  s.add(out == fp_to_sbv(8, r, two_and_a_half));
  s.add(out == tm.mk_bv(8, 3));

  ASSERT_TRUE(s.check_sat().is_sat());

  const RoundingMode rv = s.model().rm_value(r);
  EXPECT_TRUE(rv == RoundingMode::RNA || rv == RoundingMode::RTP) << "r = " << rv;
}

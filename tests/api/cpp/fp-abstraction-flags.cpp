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

// fp-abstraction-flags.cpp -- the floating-point abstraction's options
// and statistics, through the option registry and Solver::statistics().
//
// Twenty entries and eighteen counters is a lot of appliers, and every one of
// them is a line that writes a named field. Nothing about that is hard, which
// is exactly why it wants a test: an applier that writes its neighbour's
// field -- significand bits into the wide significand bits, the restart limit
// into the restart width -- is invisible to review and to every other test in
// the tree, because the two fields have the same type and the wrong one is a
// perfectly ordinary value to hold. api_test::engine_flags(s) reads back the
// fields the solver's next check would consult.
//
// The counters need a different kind of test. They are folded into the
// session totals by a watermark: each FpAbstraction publishes the delta since
// it last published, on destruction and whenever a reader asks. What that has
// to be shown to do is answer MID-SESSION, because the caller these counters
// exist for -- a fuzzing campaign asking whether the abstraction engaged at
// all -- reads them while the solver is still alive. Publishing only from the
// destructor reported zeroes to precisely that caller, which is how the first
// attempt at this was found to be wrong.
//
// Every solver here that checks satisfiability runs with the engine's model
// self-check (check-sanity) on, as every 2.x checker did; it evaluates the
// model and moves none of the counters read below.

#include "api_engine.hpp"

#include "stp/FloatBlaster/FpAbstraction.h"

#include <cstdint>

using namespace stp::api;

namespace
{
// The flags the solver is carrying, which is what a setter has to be shown to
// reach: an applier that writes the wrong field changes nothing here.
const stp::UserDefinedFlags& flags(Solver& s)
{
  return api_test::engine_flags(s);
}

// A query with something to abstract: a product of two normals, asked a
// question it cannot answer by simplification.
void assert_a_product(TermManager& tm, Solver& s)
{
  const Sort f = tm.mk_fp_sort(8, 24);
  const Term x = tm.declare("x", f);
  const Term y = tm.declare("y", f);
  s.add(fp_is_normal(x));
  s.add(fp_is_normal(y));
  (void)s.entails(fp_gt(fp_mul(RoundingMode::RNE, x, y), x));
}
} // namespace

// One assertion per entry, each naming the field it must reach. The values
// are deliberately distinct from each other and from the defaults, so an
// applier that writes a neighbouring field fails rather than coinciding.
TEST(fp_abstraction_flags, EverySetterReachesItsOwnField)
{
  TermManager tm;
  Solver s(tm);
  SolverOptions& o = s.options();

  o.set_bool("fp-abstraction", true);
  EXPECT_TRUE(flags(s).fp_abstraction);
  o.set_bool("fp-abstraction-incremental", true);
  EXPECT_TRUE(flags(s).fp_abstraction_incremental);

  // 2.x passed the two operation sets as bit masks; the registry names the
  // operations.
  o.set_names("fp-abstraction-ops", {"mul", "div"});
  EXPECT_EQ(stp::FP_ABSTRACT_MUL | stp::FP_ABSTRACT_DIV, flags(s).fp_abstraction_ops);
  o.set_names("fp-abstraction-chain-ops", {"mul", "sqrt"});
  EXPECT_EQ(stp::FP_ABSTRACT_MUL | stp::FP_ABSTRACT_SQRT, flags(s).fp_abstraction_chain_ops);

  o.set_uint("fp-abstraction-width", 33);
  EXPECT_EQ(33u, flags(s).fp_abstraction_width);
  o.set_uint("fp-abstraction-tiers", 2);
  EXPECT_EQ(2u, flags(s).fp_abstraction_tiers);
  o.set_uint("fp-abstraction-values", 7);
  EXPECT_EQ(7u, flags(s).fp_abstraction_values);

  o.set_bool("fp-abstraction-shape", false);
  EXPECT_FALSE(flags(s).fp_abstraction_shape);
  o.set_bool("fp-abstraction-relational", false);
  EXPECT_FALSE(flags(s).fp_abstraction_relational);
  o.set_uint("fp-abstraction-relational-last-width", 64);
  EXPECT_EQ(64u, flags(s).fp_abstraction_relational_last_width);

  o.set_bool("fp-abstraction-box-lemmas", true);
  EXPECT_TRUE(flags(s).fp_abstraction_box_lemmas);
  o.set_bool("fp-abstraction-phase-hints", true);
  EXPECT_TRUE(flags(s).fp_abstraction_phase_hints);
  o.set_bool("fp-abstraction-repair", false);
  EXPECT_FALSE(flags(s).fp_abstraction_repair);
  o.set_bool("fp-abstraction-decline-pinned", true);
  EXPECT_TRUE(flags(s).fp_abstraction_decline_pinned);
  using ConstantOperands = stp::UserDefinedFlags::FpConstantOperandMode;
  EXPECT_EQ(ConstantOperands::AUTO, flags(s).fp_abstraction_constant_operands);
  o.set_str("fp-abstraction-constant-operands", "on");
  EXPECT_EQ(ConstantOperands::ON, flags(s).fp_abstraction_constant_operands);
  o.set_str("fp-abstraction-constant-operands", "off");
  EXPECT_EQ(ConstantOperands::OFF, flags(s).fp_abstraction_constant_operands);
  o.set_str("fp-abstraction-constant-operands", "auto");
  EXPECT_EQ(ConstantOperands::AUTO, flags(s).fp_abstraction_constant_operands);

  // The two restart knobs and the two significand ones are the pairs most
  // easily crossed: same type, adjacent lines, names differing by a suffix.
  o.set_uint("fp-abstraction-restart-limit", 9);
  EXPECT_EQ(9u, flags(s).fp_abstraction_restart_limit);
  o.set_uint("fp-abstraction-restart-width", 128);
  EXPECT_EQ(128u, flags(s).fp_abstraction_restart_width);
  EXPECT_EQ(9u, flags(s).fp_abstraction_restart_limit) << "width overwrote limit";

  o.set_uint("fp-abstraction-significand-bits", 6);
  EXPECT_EQ(6u, flags(s).fp_abstraction_significand_bits);
  o.set_uint("fp-abstraction-significand-bits-wide", 24);
  EXPECT_EQ(24u, flags(s).fp_abstraction_significand_bits_wide);
  EXPECT_EQ(6u, flags(s).fp_abstraction_significand_bits)
      << "the wide setting overwrote the narrow one";

  o.set_uint("fp-abstraction-budget", 11);
  EXPECT_EQ(11u, flags(s).fp_abstraction_budget);
}

// Every unsigned knob would wrap to something enormous under a negative --
// for a width, a floor no format can reach; for a budget, no limit at all --
// so a negative is refused with OPTION_VALUE and the option and the field
// left as they were.
TEST(fp_abstraction_flags, NegativesAreRefusedAndChangeNothing)
{
  TermManager tm;
  Solver s(tm);
  SolverOptions& o = s.options();

  o.set_uint("fp-abstraction-width", 33);
  o.set_uint("fp-abstraction-tiers", 2);

  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("fp-abstraction-width", -1));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("fp-abstraction-tiers", -2));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("fp-abstraction-values", "-3"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("fp-abstraction-budget", "-4"));

  EXPECT_EQ(33u, o.get_uint("fp-abstraction-width"));
  EXPECT_EQ(2u, o.get_uint("fp-abstraction-tiers"));
  EXPECT_FALSE(o.is_set("fp-abstraction-values"));
  EXPECT_FALSE(o.is_set("fp-abstraction-budget"));
  EXPECT_EQ(33u, flags(s).fp_abstraction_width);
  EXPECT_EQ(2u, flags(s).fp_abstraction_tiers);
  EXPECT_EQ(4u, flags(s).fp_abstraction_values);
  EXPECT_EQ(0u, flags(s).fp_abstraction_budget);
}

// The point of the watermark: a reader that asks while the solver is alive
// sees what the abstraction has just done. Publishing only on destruction
// answered this reader with zeroes.
TEST(fp_abstraction_flags, CountersAnswerMidSessionAndDoNotDoubleCount)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool("check-sanity", true);
  s.options().set_bool("fp-abstraction", true);
  assert_a_product(tm, s);

  const Statistics first = s.statistics();
  const std::uint64_t candidates = first.uint64("fp.candidates");
  const std::uint64_t abstracted = first.uint64("fp.abstracted");
  EXPECT_GT(candidates, 0u) << "the product was never seen";
  EXPECT_GT(abstracted, 0u) << "the product was seen but not abstracted";

  // Idempotent: the delta since the last publish is zero, so asking again
  // reports the same totals rather than twice them.
  const Statistics second = s.statistics();
  EXPECT_EQ(candidates, second.uint64("fp.candidates"));
  EXPECT_EQ(abstracted, second.uint64("fp.abstracted"));
}

// Zero of both is what a query with no floating-point arithmetic reports,
// and it is a different statement from an abstraction that engaged and did
// nothing -- which is why the pair is published rather than either alone.
TEST(fp_abstraction_flags, NoFloatingPointLeavesTheCountersAtZero)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool("check-sanity", true);
  s.options().set_bool("fp-abstraction", true);

  const Term a = tm.declare("a", tm.mk_bv_sort(32));
  s.add(bvugt(a, 1));
  (void)s.check_sat();

  const Statistics st = s.statistics();
  EXPECT_EQ(0u, st.uint64("fp.candidates"));
  EXPECT_EQ(0u, st.uint64("fp.abstracted"));
}

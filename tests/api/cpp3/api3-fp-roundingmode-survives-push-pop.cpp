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

// api3-fp-roundingmode-survives-push-pop.cpp -- a rounding mode must range
// over exactly the five modes no matter which assertion level the term that
// names it was built at.
//
// Declaring one once pinned its 5-bit carrier to the one-hot encodings by
// asserting the constraint -- and an assertion belongs to the level that was
// current at the time, while the symbol node does not: it is hash-consed and
// global. So a RoundingMode variable built between a push and a pop came out
// of the bracket alive and unconstrained, free to take one of the carrier's
// 27 junk patterns.
//
// Those are not harmless. With every equality in symfpu's roundingDecision
// false nothing rounds up, so the circuit truncates and overflows to max like
// RTZ, but makeRoundingResult's returnZero names RTZ explicitly and is false
// too, so an underflow gives the minimum subnormal where RTZ gives zero.
// Truncating rules out RTP and underflowing to the minimum rules out RTZ: a
// sixth behaviour, in no standard, that a formula can tell from all five --
// and therefore satisfy. STP answered sat to an unsat query.
//
// FpTotalise re-pins every rounding mode the formula names at solve time,
// which is what makes the guarantee independent of the assertion stack.

#include "api3_common.hpp"

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

} // namespace

// The bug at its smallest: nothing floating-point at all, just a mode built
// inside a bracket and asked to be none of the five afterwards.
TEST(fp_roundingmode_push_pop, stays_pinned_when_built_inside_a_bracket)
{
  TermManager tm;
  Solver s(tm, sanity_checked());

  s.push();
  const Term r = tm.declare("r", tm.mk_rm_sort());
  s.pop();

  for (const RoundingMode m : ALL_MODES)
    s.add(!(r == tm.mk_rm(m)));

  EXPECT_TRUE(s.check_sat().is_unsat());
}

// The same, with the check itself in a fresh scope -- the shape the fuzzer
// found, and the one where the constraint's level is furthest from the
// check's.
TEST(fp_roundingmode_push_pop, stays_pinned_across_a_second_scope)
{
  TermManager tm;
  Solver s(tm, sanity_checked());

  s.push();
  const Term r = tm.declare("r", tm.mk_rm_sort());
  s.pop();

  s.push();
  for (const RoundingMode m : ALL_MODES)
    s.add(!(r == tm.mk_rm(m)));
  EXPECT_TRUE(s.check_sat().is_unsat());
  s.pop();
}

namespace
{

// The minimized fuzzer query, whose answer is unsat. `bracket` decides whether
// the floating-point terms are built inside a push/pop pair; the answer must
// not depend on it.
//
// No assertion and no check happen inside the bracket -- ablation pinned the
// trigger to term construction alone.
Result solve_reproducer(bool bracket)
{
  TermManager tm;
  Solver s(tm, sanity_checked());

  const Sort fp = tm.mk_fp32_sort();
  const Term pzero = tm.mk_fp_pos_zero(fp);
  const Term zmin = fp_min(pzero, pzero);

  if (bracket)
    s.push();

  const Term c = tm.mk_fp_from_bits(fp, "0b00000111101011100011111001010010");
  const Term rm = tm.declare("r", tm.mk_rm_sort());
  const Term sub = fp_sub(rm, zmin, fp_sqrt(rm, c));
  const Term eq = fp_rti(rm, sub) == fp_neg(zmin);
  const Term is_sub = fp_is_subnormal(fp_fma(rm, sub, c, zmin));

  if (bracket)
    s.pop();

  s.push();
  s.add(is_sub);
  s.add(eq);
  const Result q = s.check_sat();
  s.pop();

  return q;
}

} // namespace

// The reported query, both ways round. The control matters as much as the
// case: it is what says the bracket is the only difference, so a "fix" that
// made everything unsat would not pass.
TEST(fp_roundingmode_push_pop, reported_query_is_unsat_either_way)
{
  EXPECT_TRUE(solve_reproducer(/* bracket */ false).is_unsat());
  EXPECT_TRUE(solve_reproducer(/* bracket */ true).is_unsat());
}

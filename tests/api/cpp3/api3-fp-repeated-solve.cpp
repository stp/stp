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

// api3-fp-repeated-solve.cpp -- regression tests: a floating-point query may
// be solved more than once.
//
// Solving lowers every floating-point operation to a bitvector circuit, and
// a lowered float *is* its packed bits, with the format stamped onto the node
// that holds them. Nodes are hash-consed, so when the circuit for
// ((_ to_fp e s) bits) folds back to `bits` itself -- which it does whenever
// the exponent and significand fields are already constant, since then there
// is no NaN to canonicalise -- the stamp lands on the input's own node, and
// it reports a floating-point type from then on.
//
// The next solve re-ran the type check over the unchanged to_fp node, found
// its packed-bits child no longer calling itself a bitvector, and aborted:
//
//   Fatal Error: to_fp's argument is not a bitvector of width e + s
//
// on a formula the previous solve had just answered. It is the same e + s
// bits either way, and the check now says so.
//
// Found by fuzzing with murxla (OP_FP_FP over a Float16, OP_FP_LEQ,
// check-sat-assuming then check-sat); delta-minimized.
//
// The engine's type check and the engine flag a solve must leave alone are
// not part of the API, so they are read through api3_engine.hpp.

#include "api3_engine.hpp"

using namespace stp::api;

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

// (fp sign exp sig), as murxla built it over STP: pack the three bitvectors
// and reinterpret the result as a float of (|exp|, |sig| + 1). (mk_fp builds
// fp.fp itself; the reinterpretation is the shape the regression needs.)
Term packed_fp(TermManager& tm, const Term& sign, const Term& exp, const Term& sig)
{
  const std::uint32_t eb = exp.sort().bv_size();
  const std::uint32_t sb = sig.sort().bv_size() + 1;
  return to_fp_from_bits(tm.mk_fp_sort(eb, sb), concat(sign, concat(exp, sig)));
}

// murxla drove STP through an interface with no assumptions, so it emulated
// check-sat-assuming with a scope, and the scope is kept here: it is what
// makes the sequence below two solves of one formula rather than one -- the
// assumptions go away, the assertion does not.
Result check_sat_assuming(Solver& s, const Term& assumption)
{
  s.push();
  s.add(assumption);
  const Result r = s.check_sat();
  s.pop();
  return r;
}

} // namespace

// The fuzzer's case: a Float16 built with fp.fp out of a sign bit and a
// zero exponent and significand, compared with itself.
TEST(fp_repeated_solve, fp_fp_float16_leq_assume_then_solve)
{
  TermManager tm;
  Solver s(tm, sanity_checked());

  const Term sign = tm.declare("_x1", tm.mk_bv_sort(1));
  const Term x2 = tm.declare("_x2", tm.mk_bv_sort(5));
  // x >> x is zero at every width and every value of x, so the exponent and
  // significand below are constant however the solver reaches that -- which
  // is what makes the float's circuit fold back to the bits it was built
  // from.
  const Term zero5 = bvlshr(x2, x2);
  const Term zero10 = sign_extend(5, zero5);

  // (_ FloatingPoint 5 11), a binary16: 1 + 5 + 10 == 16 == 5 + 11.
  const Term f = packed_fp(tm, sign, zero5, zero10);
  ASSERT_TRUE(f.sort().is_fp());
  EXPECT_EQ(f.sort().fp_exp_size(), 5u);
  EXPECT_EQ(f.sort().fp_sig_size(), 11u);

  const Term leq = fp_leq(f, f);
  s.add(leq);

  ASSERT_TRUE(check_sat_assuming(s, leq).is_sat());
  // Solving the same formula again used to abort here.
  ASSERT_TRUE(s.check_sat().is_sat());

  // The to_fp node is still well formed -- the invariant the second solve
  // tripped over. Checked directly as well, so that this bites in a build
  // with assertions disabled, where the solver's own check is compiled out.
  EXPECT_TRUE(stp::BVTypeCheck(api3::engine_node(f)));

  // And the answers are right: an all-zero exponent and significand is a
  // zero, whatever the sign bit is, and a zero is not NaN.
  EXPECT_TRUE(s.entails(fp_is_zero(f)).is_valid());
  EXPECT_TRUE(s.entails(leq).is_valid());
}

// The same bits read two ways in one problem: as a binary16, and as the
// unsigned integer that to_fp_unsigned converts. Blasting the float stamps
// the format onto the shared node; the integer conversion must still take it.
TEST(fp_repeated_solve, to_fp_unsigned_over_the_same_bits)
{
  TermManager tm;
  Solver s(tm, sanity_checked());

  const Term sign = tm.declare("s", tm.mk_bv_sort(1));
  const Term bits = concat(sign, tm.mk_bv(15, 0));

  const Sort f16 = tm.mk_fp16_sort();
  const Term f = to_fp_from_bits(f16, bits);
  const Term g = to_fp_unsigned(f16, RoundingMode::RNE, bits);

  s.add(fp_is_zero(f));
  s.add(fp_leq(g, g));

  ASSERT_TRUE(s.check_sat().is_sat());
  ASSERT_TRUE(s.check_sat().is_sat());

  EXPECT_TRUE(stp::BVTypeCheck(api3::engine_node(g)));

  // Reading the bits as an unsigned integer gives 0 or 2^15, both of which
  // binary16 holds exactly, so the conversion is never negative...
  EXPECT_TRUE(s.entails(fp_is_pos(g)).is_valid());
  // ...and is 32768.0, not a zero, when the top bit is set. Read as a
  // binary16 instead -- which is what the stamp would say the source is --
  // the same bits are a zero either way, so this pins that the format left
  // on them has not changed how the integer conversion reads them.
  EXPECT_TRUE(s.entails(fp_is_zero(g)).is_invalid());
}

// FP activation is determined from the current query DAG. Merely building a
// float in a scope that is later popped must not change a subsequent BV-only
// solve, while retaining and later asserting that node must activate lowering.
// Neither solve may rewrite the user's preprocessing option permanently: the
// option is set through the solver's options, and the engine's flag is read
// as each solve left it (reading it through api3::engine_flags would re-apply
// the option first and hide a rewrite). The counterexample self-check only
// evaluates the model and writes no flag, so it leaves this read alone.
TEST(fp_repeated_solve, floating_point_activation_is_query_local)
{
  TermManager tm;
  Solver s(tm, sanity_checked());
  const stp::UserDefinedFlags& engine = api3::engine_manager(tm).UserFlags;

  const Term bv = tm.declare("live_bv", tm.mk_bv_sort(8));

  s.push();
  const Term fp = tm.declare("scoped_fp", tm.mk_fp16_sort());
  const Term fp_predicate = fp_is_normal(fp);
  s.pop();

  s.add(bv == tm.mk_bv(8, 0x2a));
  s.options().set_bool("difficulty-reversion", true);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(engine.difficulty_reversion);
  EXPECT_EQ(s.model().uint64_value(bv), 0x2au);

  // A term keeps its node alive after the scope it was built in is popped.
  // Reachability from this query, not the old scope, is decisive.
  s.push();
  s.add(fp_predicate);
  s.options().set_bool("difficulty-reversion", true);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(engine.difficulty_reversion);
  s.pop();
}

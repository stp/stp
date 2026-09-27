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

// api3-fp-identity-passthrough.cpp -- regression tests: a floating-point
// operation that simplifies away to one of its own operands.
//
// The node factory folds several floating-point identities as the term is
// built -- (fp.min x x) and (fp.max x x) are x, (fp.mul rm x 1.0) and
// (fp.div rm x 1.0) are x, (fp.neg (fp.neg x)) is x. What comes back is then
// not a fresh node of the operation's own kind: it is whatever the operand
// already was, which may be an ite, an array read, a symbol or a constant.
//
// Term construction once stamped the format on its result unconditionally, on
// the assumption that the result was always a new float-kind node needing one.
// On a passthrough that assumption is wrong twice over: the operand carries
// its format already, and stamping it on a bitvector-kind interior node is
// forbidden -- the format is per-node state and nodes are hash-consed, so it
// would retype every other use of those same bits. SetExpWidth says so:
//
//   Assertion `_ew == 0 || Degree() == 0 || is_FP_kind(GetKind())
//              || GetKind() == FLOATINGPOINT || GetIndexWidth() > 0' failed.
//
// aborting during term construction, before any solving. Found by fuzzing
// with murxla ((fp.min t t) over a Float64 ite); delta-minimized.
//
// The engine's own type check on the node a construction hands back is not
// part of the API, so it is read through api3_engine.hpp.

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

// The fuzzer's trace, term for term. Every step is needed only to arrive at a
// Float64 whose node is an ITE rather than a floating-point operation:
//
//   t47  = ((_ to_fp 15 113) b)        128 bits read as a Float128
//   t114 = ((_ to_fp 11 53) rtn t47)   narrowed to a Float64
//   t168 = (fp.div rm t114 t114)       a Float64
//   t169 = (ite c t168 t114)           a Float64 -- kind ITE, degree 3
//
// and then (fp.min t169 t169), which aborted.
struct Fuzzed
{
  TermManager tm;
  Term narrowed; // t114
  Term ite;      // t169
};

Fuzzed build_fuzzed()
{
  Fuzzed f;
  TermManager& tm = f.tm;

  const Term bits = tm.declare("b", tm.mk_bv_sort(128));
  const Term wide = to_fp_from_bits(tm.mk_fp128_sort(), bits);
  f.narrowed = to_fp(tm.mk_fp64_sort(), RoundingMode::RTN, wide);

  const Term rm = tm.declare("rm", tm.mk_rm_sort());
  const Term quotient = fp_div(rm, f.narrowed, f.narrowed);
  const Term cond = tm.declare("c", tm.mk_bool_sort());
  f.ite = ite(cond, quotient, f.narrowed);

  return f;
}

// A Float64 built here has the format the input asked for, whatever kind of
// node it happens to be, and its node passes the engine's type check.
void is_float64(const Term& e)
{
  ASSERT_TRUE(e.sort().is_fp());
  EXPECT_EQ(e.sort().fp_exp_size(), 11u);
  EXPECT_EQ(e.sort().fp_sig_size(), 53u);
  EXPECT_TRUE(stp::BVTypeCheck(api3::engine_node(e)));
}

} // namespace

// A term is its node, so an identity that hands back its operand hands back a
// term that is the operand: same_as asks exactly that (== would build an
// equality instead).
TEST(fp_identity_passthrough, min_of_an_ite_with_itself)
{
  Fuzzed f = build_fuzzed();
  // What the trace was built to reach. (The engine's headers put their own
  // Kind in the global namespace, so the API's is named in full.)
  ASSERT_EQ(f.ite.kind(), stp::api::Kind::ITE);
  is_float64(f.ite);

  // Used to abort here, in the construction of fp.min, stamping (11, 53) onto
  // the ITE.
  const Term m = fp_min(f.ite, f.ite);

  // The identity fired -- the point of the test is the node it handed back --
  // and the result is the Float64 it should be.
  EXPECT_TRUE(m.same_as(f.ite));
  is_float64(m);
}

TEST(fp_identity_passthrough, max_of_an_ite_with_itself)
{
  Fuzzed f = build_fuzzed();

  const Term m = fp_max(f.ite, f.ite);
  EXPECT_TRUE(m.same_as(f.ite));
  is_float64(m);
}

// The other identities that hand back an operand rather than a fresh node.
// Each is reached the same way and used to abort the same way.
TEST(fp_identity_passthrough, arithmetic_identities_over_an_ite)
{
  Fuzzed f = build_fuzzed();
  const Term rm = f.tm.mk_rm(RoundingMode::RNE);
  const Term one = f.tm.mk_fp(f.tm.mk_fp64_sort(), RoundingMode::RNE, 1.0);

  // x * 1.0 = x and 1.0 * x = x: exact for every value and rounding mode.
  const Term mul = fp_mul(rm, f.ite, one);
  EXPECT_TRUE(mul.same_as(f.ite));
  is_float64(mul);

  const Term mul_flipped = fp_mul(rm, one, f.ite);
  EXPECT_TRUE(mul_flipped.same_as(f.ite));
  is_float64(mul_flipped);

  // x / 1.0 = x.
  const Term div = fp_div(rm, f.ite, one);
  EXPECT_TRUE(div.same_as(f.ite));
  is_float64(div);

  // -(-x) = x, including for NaN payloads and the signed zeros.
  const Term negneg = fp_neg(fp_neg(f.ite));
  EXPECT_TRUE(negneg.same_as(f.ite));
  is_float64(negneg);
}

// An array read is the other float-typed node of a bitvector kind: kind READ,
// degree 2, and (unlike a float-kind node) nothing about the kind says it is
// a float. It reaches the same passthrough.
TEST(fp_identity_passthrough, min_of_an_array_read_with_itself)
{
  TermManager tm;

  const Sort f32 = tm.mk_fp32_sort();
  const Term a = tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(4), f32));
  const Term cell = select(a, tm.declare("i", tm.mk_bv_sort(4)));

  const Term m = fp_min(cell, cell);
  EXPECT_TRUE(m.same_as(cell));
  ASSERT_TRUE(m.sort().is_fp());
  EXPECT_EQ(m.sort().fp_exp_size(), 8u);
  EXPECT_EQ(m.sort().fp_sig_size(), 24u);
  EXPECT_TRUE(stp::BVTypeCheck(api3::engine_node(m)));
}

// A passthrough result must not be merely *reachable*: it has to mean what
// (fp.min x x) means. Over an ite between two ordinary constants there is no
// NaN in play, so fp.eq is ordinary equality and the answers are exact.
TEST(fp_identity_passthrough, min_of_an_ite_still_solves_correctly)
{
  TermManager tm;
  Solver s(tm, sanity_checked());

  const Sort f64 = tm.mk_fp64_sort();
  const Term one = tm.mk_fp(f64, RoundingMode::RNE, 1.0);
  const Term two = tm.mk_fp(f64, RoundingMode::RNE, 2.0);

  const Term cond = tm.declare("c", tm.mk_bool_sort());
  const Term chosen = ite(cond, one, two);
  const Term m = fp_min(chosen, chosen);

  // (fp.min x x) = x, whichever branch the condition takes.
  EXPECT_TRUE(s.entails(fp_eq(m, chosen)).is_valid());

  // And it is one of the two branch values, not some third thing the format
  // stamp could have produced: 1.0 when c holds, 2.0 when it does not.
  s.push();
  s.add(cond);
  EXPECT_TRUE(s.entails(fp_eq(m, one)).is_valid());
  s.pop();

  s.push();
  s.add(!cond);
  EXPECT_TRUE(s.entails(fp_eq(m, two)).is_valid());
  s.pop();
}

// The fuzzer's problem solved, not merely built. This is what catches the
// second half of the bug: the format funnels are also how the manager learns
// that floats are in play at all, so skipping a stamp must not skip the
// notice -- or the floating-point passes stay switched off and the float
// reaches the bit-blaster ("BBForm: FP formulas should not reach the
// bit-blaster"). Nothing here is stamped: every node derives its format.
//
// (fp.min t169 t169) is t169, which is t114/t114 or t114 depending on c, and
// x/x is a NaN exactly when x is a zero, an infinity or itself a NaN.
TEST(fp_identity_passthrough, the_fuzzed_problem_solves)
{
  Fuzzed f = build_fuzzed();
  const Term m = fp_min(f.ite, f.ite);
  Solver s(f.tm, sanity_checked());

  // Not valid: take the ite's else branch with any ordinary finite t114 and
  // the min is that, which is not a NaN.
  EXPECT_TRUE(s.entails(fp_is_nan(m)).is_invalid());

  // Pinning t114 to a NaN makes the min a NaN down either branch, NaN/NaN
  // being a NaN too. Check the assertion is satisfiable first, so that the
  // validity below is real rather than vacuous.
  s.add(fp_is_nan(f.narrowed));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.entails(fp_is_nan(m)).is_valid());
}

// The identity is not confined to the ite: any float-typed operand is handed
// straight back, so check the plain ones too. A symbol has degree zero and a
// float constant is an ASTFPConst, both of which SetExpWidth would have
// accepted -- they are here so that the passthrough is pinned for every shape
// of operand rather than only the one that used to abort.
TEST(fp_identity_passthrough, min_of_a_symbol_or_a_constant_with_itself)
{
  TermManager tm;

  const Sort f64 = tm.mk_fp64_sort();
  const Term x = tm.declare("x", f64);
  const Term mx = fp_min(x, x);
  EXPECT_TRUE(mx.same_as(x));
  EXPECT_TRUE(mx.sort().is_fp());

  const Term one = tm.mk_fp(f64, RoundingMode::RNE, 1.0);
  const Term mone = fp_min(one, one);
  EXPECT_TRUE(mone.same_as(one));
  ASSERT_TRUE(mone.sort().is_fp());
  EXPECT_EQ(mone.sort().fp_exp_size(), 11u);
  EXPECT_EQ(mone.sort().fp_sig_size(), 53u);
}

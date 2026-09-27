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

// api3-fp-lowered-ite-fold.cpp -- regression tests: a floating-point
// if-then-else that the simplifier folds away after the floating-point layer
// has been lowered to bitvectors.
//
// Lowering leaves the formula pure bitvector, but a float symbol keeps the
// format its declaration gave it -- it must, or its value could not be read
// back -- and the structure built over that symbol goes on deriving a format
// from it. So (ite c (fp.abs x) x) over a Float64 x is an ordinary 64-bit
// if-then-else once lowered, and still answers 11/53, because its else branch
// is x (see deriveFPFormat).
//
// The simplifier then finds the condition is a tautology, replaces the
// if-then-else with its then branch -- the bitvector circuit lowering built
// for (fp.abs x), a concatenation, of no floating-point kind -- and carried
// the format across the rebuild onto it. That aborted, in the place that says
// why it must not happen:
//
//   Assertion `_ew == 0 || Degree() == 0 || is_FP_kind(GetKind())
//              || GetKind() == FLOATINGPOINT || GetIndexWidth() > 0' failed.
//
// The format is per-node state and nodes are hash-consed, so the stamp would
// retype every other use of those same bits. Nor is there anything to carry:
// what is left is bits, the blaster is finished with them, and a float symbol
// or a float operation that still needs a format has one of its own.
//
// Found by fuzzing with murxla (fp.abs and fp.neg over a Float64 ite, under
// check-sat-assuming); delta-minimized. The same assertion as
// api3-fp-identity-passthrough.cpp, reached from the other direction: there
// the format was stamped as the term was built, here as it was simplified.

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

// The fuzzer's trace, term for term:
//
//   t3  = _x2                                     a Float64
//   t5  = (fp.gt +zero t3)
//   t16 = (bvult (bvnor _x0 _x0) _x0)
//   t20 = (fp.abs t3)
//   t34 = (=> (and t16 t5) t5)                    true, whatever t16 and t5 are
//   t35 = (not t34)                               and so false
//   t36 = (not t35)
//   t38 = (ite t36 t20 t3)                        a Float64 of kind ITE
//   t48 = (fp.abs t38)
//   t53 = (fp.neg t48)                            which is -(fp.abs t3)
//
// t34 is where the bug turns: a tautology, so the simplifier folds the
// if-then-else to a single branch, but not one the node factory recognises as
// it builds the term, so the if-then-else is really built. Passing a true
// condition instead would fold at construction and there would be no
// if-then-else to lower.
struct Fuzzed
{
  TermManager tm;
  Term x;             // t3
  Term tautology;     // t36
  Term contradiction; // t35
  Term ite;           // t38
  Term neg_abs;       // t53
};

Fuzzed build_fuzzed()
{
  Fuzzed f;
  TermManager& tm = f.tm;

  const Sort f64 = tm.mk_fp64_sort();
  f.x = tm.declare("_x2", f64);

  const Term gt = fp_gt(tm.mk_fp_pos_zero(f64), f.x);
  const Term bits = tm.declare("_x0", tm.mk_bv_sort(1));
  const Term ult = bvult(bvnor(bits, bits), bits);

  const Term conjunction = and_({ult, gt});
  f.contradiction = !implies(conjunction, gt);
  f.tautology = !f.contradiction;

  f.ite = ite(f.tautology, fp_abs(f.x), f.x);
  f.neg_abs = fp_neg(fp_abs(f.ite));

  return f;
}

// -(fp.abs x) is x exactly when x is negative or a zero: for a negative x it
// is x itself, for either zero it is -0 and fp.eq holds between the two zeros,
// and for a NaN both sides are false. The if-then-else cannot change that --
// its branches are x and (fp.abs x), and the enclosing fp.abs makes them the
// same value -- so this holds whichever way the condition is read, and holds
// whether the if-then-else is folded away or left standing.
void is_minus_abs_of(Solver& s, const Term& neg_abs, const Term& x)
{
  const Term equal = fp_eq(x, neg_abs);
  const Term negative_or_zero = fp_is_neg(x) || fp_is_zero(x);
  EXPECT_TRUE(s.entails(equal == negative_or_zero).is_valid());

  // Neither side is a constant the fold could have left behind: there is an x
  // that satisfies the equality and an x that refutes it.
  EXPECT_TRUE(s.entails(equal).is_invalid());
  EXPECT_TRUE(s.entails(!equal).is_invalid());
}

} // namespace

TEST(fp_lowered_ite_fold, the_fuzzed_assumptions_are_unsat)
{
  Fuzzed f = build_fuzzed();
  Solver s(f.tm, sanity_checked());

  // The term that used to be stamped: a Float64 whose kind is ITE, so it has
  // nowhere to store a format and does not need to, deriving one from the
  // float symbol in its else branch.
  ASSERT_EQ(f.ite.kind(), Kind::ITE);
  ASSERT_TRUE(f.ite.sort().is_fp());
  ASSERT_EQ(f.ite.sort().fp_exp_size(), 11u);
  ASSERT_EQ(f.ite.sort().fp_sig_size(), 53u);

  // (check-sat-assuming ((fp.eq t3 t53) (fp.isZero t3) (fp.isNegative t3)
  //                      (fp.isInfinite t3))), which is how murxla drove an
  // assumption through STP: a scope, the assumptions asserted into it, and a
  // check.
  s.push();
  s.add(fp_eq(f.x, f.neg_abs));
  s.add(fp_is_zero(f.x));
  s.add(fp_is_neg(f.x));
  s.add(fp_is_inf(f.x));

  // Used to abort here, in the simplifier, stamping (11, 53) onto the
  // concatenation the if-then-else folded to. Unsatisfiable for a reason that
  // has nothing to do with the if-then-else: no float is both a zero and an
  // infinity.
  EXPECT_TRUE(s.check_sat().is_unsat());
  s.pop();
}

// Reaching an answer is not enough: the term has to still mean what it meant.
// Dropping a format that was needed would show up here, since a float whose
// format is lost blasts at the wrong width or not at all.
TEST(fp_lowered_ite_fold, the_folded_ite_still_means_minus_abs)
{
  Fuzzed f = build_fuzzed();
  Solver s(f.tm, sanity_checked());

  is_minus_abs_of(s, f.neg_abs, f.x);
}

// The same shape with the branches the other way round, under a condition that
// is false rather than true. The format is derived from the then branch now --
// deriveFPFormat takes the first branch that carries one -- and it is the else
// branch, the lowered (fp.abs x), that is left behind. Same abort.
TEST(fp_lowered_ite_fold, folding_to_the_else_branch)
{
  Fuzzed f = build_fuzzed();
  Solver s(f.tm, sanity_checked());

  const Term flipped = ite(f.contradiction, f.x, fp_abs(f.x));
  ASSERT_TRUE(flipped.sort().is_fp());

  const Term neg_abs = fp_neg(fp_abs(flipped));
  is_minus_abs_of(s, neg_abs, f.x);
}

// The other half of the story: an if-then-else whose condition is opaque
// survives simplification, keeps deriving its format, and lowers as a float.
// Nothing here ever aborted -- it is here so that skipping the stamp is pinned
// as skipping only what cannot hold it.
TEST(fp_lowered_ite_fold, an_ite_that_does_not_fold)
{
  TermManager tm;
  Solver s(tm, sanity_checked());

  const Term x = tm.declare("x", tm.mk_fp64_sort());
  const Term chosen = ite(tm.declare("c", tm.mk_bool_sort()), fp_abs(x), x);
  const Term neg_abs = fp_neg(fp_abs(chosen));

  is_minus_abs_of(s, neg_abs, x);
}

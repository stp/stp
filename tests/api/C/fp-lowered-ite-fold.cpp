/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <gtest/gtest.h>
#include <stp/c_interface.h>

// Regression tests: a floating-point if-then-else that the simplifier folds
// away after the floating-point layer has been lowered to bitvectors.
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
// fp-identity-passthrough.cpp, reached from the other direction: there the
// format was stamped as the term was built, here as it was simplified.

namespace
{

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
  VC vc;
  Expr x;             // t3
  Expr tautology;     // t36
  Expr contradiction; // t35
  Expr ite;           // t38
  Expr negAbs;        // t53
};

Fuzzed buildFuzzed()
{
  Fuzzed f;
  f.vc = vc_createValidityChecker();

  Type f64 = vc_fpType(f.vc, 11, 53);
  f.x = vc_varExpr(f.vc, "_x2", f64);

  Expr gt = vc_fpGtExpr(f.vc, vc_fpPlusZero(f.vc, f64), f.x);
  Expr bits = vc_varExpr(f.vc, "_x0", vc_bvType(f.vc, 1));
  Expr ult = vc_bvLtExpr(f.vc, vc_bvNorExpr(f.vc, bits, bits), bits);

  Expr conjuncts[2] = {ult, gt};
  Expr conjunction = vc_andExprN(f.vc, conjuncts, 2);
  f.contradiction = vc_notExpr(f.vc, vc_impliesExpr(f.vc, conjunction, gt));
  f.tautology = vc_notExpr(f.vc, f.contradiction);

  f.ite = vc_iteExpr(f.vc, f.tautology, vc_fpAbsExpr(f.vc, f.x), f.x);
  f.negAbs = vc_fpNegExpr(f.vc, vc_fpAbsExpr(f.vc, f.ite));

  return f;
}

// -(fp.abs x) is x exactly when x is negative or a zero: for a negative x it
// is x itself, for either zero it is -0 and fp.eq holds between the two zeros,
// and for a NaN both sides are false. The if-then-else cannot change that --
// its branches are x and (fp.abs x), and the enclosing fp.abs makes them the
// same value -- so this holds whichever way the condition is read, and holds
// whether the if-then-else is folded away or left standing.
void isMinusAbsOf(VC vc, Expr negAbs, Expr x)
{
  Expr equal = vc_fpEqExpr(vc, x, negAbs);
  Expr negativeOrZero =
      vc_orExpr(vc, vc_fpIsNegativeExpr(vc, x), vc_fpIsZeroExpr(vc, x));
  EXPECT_EQ(1, vc_query(vc, vc_iffExpr(vc, equal, negativeOrZero))); // VALID

  // Neither side is a constant the fold could have left behind: there is an x
  // that satisfies the equality and an x that refutes it.
  EXPECT_EQ(0, vc_query(vc, equal)); // 0 == INVALID
  EXPECT_EQ(0, vc_query(vc, vc_notExpr(vc, equal)));
}

} // namespace

TEST(fp_lowered_ite_fold, the_fuzzed_assumptions_are_unsat)
{
  Fuzzed f = buildFuzzed();

  // The term that used to be stamped: a Float64 whose kind is ITE, so it has
  // nowhere to store a format and does not need to, deriving one from the
  // float symbol in its else branch.
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(f.ite));
  ASSERT_EQ(11, vc_getExpWidth(f.ite));
  ASSERT_EQ(53, vc_getSigWidth(f.ite));

  // (check-sat-assuming ((fp.eq t3 t53) (fp.isZero t3) (fp.isNegative t3)
  //                      (fp.isInfinite t3))), which is how murxla drives an
  // assumption through STP: a scope, the assumptions asserted into it, and a
  // query for false.
  vc_push(f.vc);
  vc_assertFormula(f.vc, vc_fpEqExpr(f.vc, f.x, f.negAbs));
  vc_assertFormula(f.vc, vc_fpIsZeroExpr(f.vc, f.x));
  vc_assertFormula(f.vc, vc_fpIsNegativeExpr(f.vc, f.x));
  vc_assertFormula(f.vc, vc_fpIsInfiniteExpr(f.vc, f.x));

  // Used to abort here, in the simplifier, stamping (11, 53) onto the
  // concatenation the if-then-else folded to. Unsatisfiable for a reason that
  // has nothing to do with the if-then-else: no float is both a zero and an
  // infinity.
  EXPECT_EQ(1, vc_query(f.vc, vc_falseExpr(f.vc))); // 1 == VALID == unsat
  vc_pop(f.vc);

  vc_Destroy(f.vc);
}

// Reaching an answer is not enough: the term has to still mean what it meant.
// Dropping a format that was needed would show up here, since a float whose
// format is lost blasts at the wrong width or not at all.
TEST(fp_lowered_ite_fold, the_folded_ite_still_means_minus_abs)
{
  Fuzzed f = buildFuzzed();

  isMinusAbsOf(f.vc, f.negAbs, f.x);

  vc_Destroy(f.vc);
}

// The same shape with the branches the other way round, under a condition that
// is false rather than true. The format is derived from the then branch now --
// deriveFPFormat takes the first branch that carries one -- and it is the else
// branch, the lowered (fp.abs x), that is left behind. Same abort.
TEST(fp_lowered_ite_fold, folding_to_the_else_branch)
{
  Fuzzed f = buildFuzzed();

  Expr ite = vc_iteExpr(f.vc, f.contradiction, f.x, vc_fpAbsExpr(f.vc, f.x));
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(ite));

  Expr negAbs = vc_fpNegExpr(f.vc, vc_fpAbsExpr(f.vc, ite));
  isMinusAbsOf(f.vc, negAbs, f.x);

  vc_Destroy(f.vc);
}

// The other half of the story: an if-then-else whose condition is opaque
// survives simplification, keeps deriving its format, and lowers as a float.
// Nothing here ever aborted -- it is here so that skipping the stamp is pinned
// as skipping only what cannot hold it.
TEST(fp_lowered_ite_fold, an_ite_that_does_not_fold)
{
  VC vc = vc_createValidityChecker();

  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 11, 53));
  Expr ite = vc_iteExpr(vc, vc_varExpr(vc, "c", vc_boolType(vc)),
                        vc_fpAbsExpr(vc, x), x);
  Expr negAbs = vc_fpNegExpr(vc, vc_fpAbsExpr(vc, ite));

  isMinusAbsOf(vc, negAbs, x);

  vc_Destroy(vc);
}

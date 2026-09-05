/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <gtest/gtest.h>
#include <stp/c_interface.h>

// A rounding mode must range over exactly the five modes no matter which
// assertion level the term that names it was built at.
//
// Declaring one pins its 5-bit carrier to the one-hot encodings by asserting
// the constraint -- and an assertion belongs to the level that was current at
// the time, while the symbol node does not: it is hash-consed and global. So
// a RoundingMode variable built between a vc_push and a vc_pop came out of
// the bracket alive and unconstrained, free to take one of the carrier's 27
// junk patterns.
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

namespace
{

// vc_query: 1 = VALID (the assertions are unsatisfiable), 0 = INVALID (they
// are satisfiable). The queries below are all `false`, so 1 means unsat.
const int UNSAT = 1;

// The five one-hot encodings, as the C API spells them.
const enum VCRoundingMode ALL_MODES[] = {VC_RM_RNE, VC_RM_RNA, VC_RM_RTP,
                                         VC_RM_RTN, VC_RM_RTZ};

} // namespace

// The bug at its smallest: nothing floating-point at all, just a mode built
// inside a bracket and asked to be none of the five afterwards.
TEST(fp_roundingmode_push_pop, stays_pinned_when_built_inside_a_bracket)
{
  VC vc = vc_createValidityChecker();

  vc_push(vc);
  Expr r = vc_fpRoundingModeVar(vc, "r");
  vc_pop(vc);

  for (const enum VCRoundingMode m : ALL_MODES)
    vc_assertFormula(
        vc, vc_notExpr(vc, vc_eqExpr(vc, r, vc_fpRoundingMode(vc, m))));

  EXPECT_EQ(UNSAT, vc_query(vc, vc_falseExpr(vc)));
  vc_Destroy(vc);
}

// The same, with the solve itself in a fresh scope -- the shape the fuzzer
// found, and the one where the constraint's level is furthest from the
// query's.
TEST(fp_roundingmode_push_pop, stays_pinned_across_a_second_scope)
{
  VC vc = vc_createValidityChecker();

  vc_push(vc);
  Expr r = vc_fpRoundingModeVar(vc, "r");
  vc_pop(vc);

  vc_push(vc);
  for (const enum VCRoundingMode m : ALL_MODES)
    vc_assertFormula(
        vc, vc_notExpr(vc, vc_eqExpr(vc, r, vc_fpRoundingMode(vc, m))));
  EXPECT_EQ(UNSAT, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  vc_Destroy(vc);
}

namespace
{

// The minimized fuzzer query, verified unsat by bitwuzla. `bracket` decides
// whether the floating-point terms are built inside a vc_push/vc_pop pair;
// the answer must not depend on it.
//
// No assertion and no solve happen inside the bracket -- ablation pinned the
// trigger to term construction alone.
int solveReproducer(bool bracket)
{
  VC vc = vc_createValidityChecker();

  Type fp = vc_fpType(vc, 8, 24);
  Expr pzero = vc_fpPlusZero(vc, fp);
  Expr zmin = vc_fpMinExpr(vc, pzero, pzero);

  if (bracket)
    vc_push(vc);

  Expr c = vc_fpConstFromBits(
      vc, 8, 24, vc_bvConstExprFromStr(vc, "00000111101011100011111001010010"));
  Expr rm = vc_fpRoundingModeVar(vc, "r");
  Expr sub = vc_fpSubExpr(vc, rm, zmin, vc_fpSqrtExpr(vc, rm, c));
  Expr eq = vc_eqExpr(vc, vc_fpRoundToIntegralExpr(vc, rm, sub),
                      vc_fpNegExpr(vc, zmin));
  Expr is_sub = vc_fpIsSubnormalExpr(vc, vc_fpFMAExpr(vc, rm, sub, c, zmin));

  if (bracket)
    vc_pop(vc);

  vc_push(vc);
  vc_assertFormula(vc, is_sub);
  vc_assertFormula(vc, eq);
  const int q = vc_query(vc, vc_falseExpr(vc));
  vc_pop(vc);

  vc_Destroy(vc);
  return q;
}

} // namespace

// The reported query, both ways round. The control matters as much as the
// case: it is what says the bracket is the only difference, so a "fix" that
// made everything unsat would not pass.
TEST(fp_roundingmode_push_pop, reported_query_is_unsat_either_way)
{
  EXPECT_EQ(UNSAT, solveReproducer(/* bracket */ false));
  EXPECT_EQ(UNSAT, solveReproducer(/* bracket */ true));
}

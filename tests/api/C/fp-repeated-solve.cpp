#include <gtest/gtest.h>
#include <stp/AST/AST.h> // BVTypeCheck, the invariant these pin
#include <stp/STPManager/STP.h>
#include <stp/c_interface.h>

// Regression tests: a floating-point query may be solved more than once.
//
// Solving lowers every floating-point operation to a bitvector circuit, and
// a lowered float *is* its packed bits, with the format stamped onto the node
// that holds them.  Nodes are hash-consed, so when the circuit for
// ((_ to_fp e s) bits) folds back to `bits` itself -- which it does whenever
// the exponent and significand fields are already constant, since then there
// is no NaN to canonicalise -- the stamp lands on the input's own node, and
// it reports FLOATINGPOINT_TYPE from then on.
//
// The next solve re-ran the type check over the unchanged to_fp node, found
// its packed-bits child no longer calling itself a bitvector, and aborted:
//
//   Fatal Error: to_fp's argument is not a bitvector of width e + s
//
// on a formula the previous solve had just answered.  It is the same e + s
// bits either way, and the check now says so.
//
// Found by fuzzing with murxla (OP_FP_FP over a Float16, OP_FP_LEQ,
// check-sat-assuming then check-sat); delta-minimized.

namespace
{

// (fp sign exp sig), as murxla's STP wrapper builds it: pack the three
// bitvectors and reinterpret the result as a float of (|exp|, |sig| + 1).
Expr fpFP(VC vc, Expr sign, Expr exp, Expr sig)
{
  const int eb = vc_getBVLength(vc, exp);
  const int sb = vc_getBVLength(vc, sig) + 1;
  return vc_fpToFPFromIEEEBV(
      vc, eb, sb, vc_bvConcatExpr(vc, sign, vc_bvConcatExpr(vc, exp, sig)));
}

// STP has no assumption interface, so murxla emulates check-sat-assuming with
// a scope. That is what makes the sequence below two solves of one formula
// rather than one: the assumptions go away, the assertion does not.
int checkSatAssuming(VC vc, Expr assumption)
{
  vc_push(vc);
  vc_assertFormula(vc, assumption);
  const int r = vc_query(vc, vc_falseExpr(vc)); // 0 == INVALID == satisfiable
  vc_pop(vc);
  return r;
}

} // namespace

// The fuzzer's case: a Float16 built with fp.fp out of a sign bit and a
// zero exponent and significand, compared with itself.
TEST(fp_repeated_solve, fp_fp_float16_leq_assume_then_solve)
{
  VC vc = vc_createValidityChecker();

  Expr sign = vc_varExpr(vc, "_x1", vc_bvType(vc, 1));
  Expr x2 = vc_varExpr(vc, "_x2", vc_bvType(vc, 5));
  // x >> x is zero at every width and every value of x, so the exponent and
  // significand below are constant however the solver reaches that -- which
  // is what makes the float's circuit fold back to the bits it was built
  // from.
  Expr zero5 = vc_bvRightShiftExprExpr(vc, 5, x2, x2);
  Expr zero10 = vc_bvSignExtend(vc, zero5, 10);

  // (_ FloatingPoint 5 11), a binary16: 1 + 5 + 10 == 16 == 5 + 11.
  Expr f = fpFP(vc, sign, zero5, zero10);
  ASSERT_EQ(FLOATINGPOINT_TYPE, getType(f));
  EXPECT_EQ(5, vc_getExpWidth(f));
  EXPECT_EQ(11, vc_getSigWidth(f));

  Expr leq = vc_fpLeqExpr(vc, f, f);
  vc_assertFormula(vc, leq);

  ASSERT_EQ(0, checkSatAssuming(vc, leq));
  // Solving the same formula again used to abort here.
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // The to_fp node is still well formed -- the invariant the second solve
  // tripped over. Checked directly as well, so that this bites in a build
  // with assertions disabled, where the solver's own check is compiled out.
  EXPECT_TRUE(stp::BVTypeCheck(*(stp::ASTNode*)f));

  // And the answers are right: an all-zero exponent and significand is a
  // zero, whatever the sign bit is, and a zero is not NaN.
  EXPECT_EQ(1, vc_query(vc, vc_fpIsZeroExpr(vc, f)));
  EXPECT_EQ(1, vc_query(vc, leq));

  vc_Destroy(vc);
}

// The same bits read two ways in one problem: as a binary16, and as the
// unsigned integer that to_fp_unsigned converts. Blasting the float stamps
// the format onto the shared node; the integer conversion must still take it.
TEST(fp_repeated_solve, to_fp_unsigned_over_the_same_bits)
{
  VC vc = vc_createValidityChecker();

  Expr sign = vc_varExpr(vc, "s", vc_bvType(vc, 1));
  Expr bits =
      vc_bvConcatExpr(vc, sign, vc_bvConstExprFromLL(vc, 15, 0ULL));

  Expr f = vc_fpToFPFromIEEEBV(vc, 5, 11, bits);
  Expr g = vc_fpToFPFromUnsignedBV(vc, 5, 11,
                                   vc_fpRoundingMode(vc, VC_RM_RNE), bits);

  vc_assertFormula(vc, vc_fpIsZeroExpr(vc, f));
  vc_assertFormula(vc, vc_fpLeqExpr(vc, g, g));

  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  EXPECT_TRUE(stp::BVTypeCheck(*(stp::ASTNode*)g));

  // Reading the bits as an unsigned integer gives 0 or 2^15, both of which
  // binary16 holds exactly, so the conversion is never negative...
  EXPECT_EQ(1, vc_query(vc, vc_fpIsPositiveExpr(vc, g)));
  // ...and is 32768.0, not a zero, when the top bit is set. Read as a
  // binary16 instead -- which is what the stamp would say the source is --
  // the same bits are a zero either way, so this pins that the format left
  // on them has not changed how the integer conversion reads them.
  EXPECT_EQ(0, vc_query(vc, vc_fpIsZeroExpr(vc, g)));

  vc_Destroy(vc);
}

// FP activation is determined from the current query DAG. Merely building a
// float in a scope that is later popped must not change a subsequent BV-only
// solve, while retaining and later asserting that node must activate lowering.
// Neither solve may rewrite the user's preprocessing option permanently.
TEST(fp_repeated_solve, floating_point_activation_is_query_local)
{
  VC vc = vc_createValidityChecker();
  stp::STP* checker = reinterpret_cast<stp::STP*>(vc);

  Expr bv = vc_varExpr(vc, "live_bv", vc_bvType(vc, 8));

  vc_push(vc);
  Expr fp = vc_varExpr(vc, "scoped_fp", vc_fpType(vc, 5, 11));
  Expr fp_predicate = vc_fpIsNormalExpr(vc, fp);
  vc_pop(vc);

  vc_assertFormula(vc,
                   vc_eqExpr(vc, bv, vc_bvConstExprFromLL(vc, 8, 0x2a)));
  checker->bm->UserFlags.difficulty_reversion = true;
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_TRUE(checker->bm->UserFlags.difficulty_reversion);
  EXPECT_EQ(0x2aULL,
            getBVUnsignedLongLong(vc_getCounterExample(vc, bv)));

  // C API expression handles keep the node alive after its parser-like scope
  // is popped. Reachability from this query, not the old scope, is decisive.
  vc_push(vc);
  vc_assertFormula(vc, fp_predicate);
  checker->bm->UserFlags.difficulty_reversion = true;
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_TRUE(checker->bm->UserFlags.difficulty_reversion);
  vc_pop(vc);

  vc_Destroy(vc);
}

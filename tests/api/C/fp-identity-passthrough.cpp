/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <gtest/gtest.h>
#include <stp/AST/AST.h> // BVTypeCheck, the invariant these pin
#include <stp/c_interface.h>

// Regression tests: a floating-point operation that simplifies away to one of
// its own operands.
//
// The node factory folds several floating-point identities as the term is
// built -- (fp.min x x) and (fp.max x x) are x, (fp.mul rm x 1.0) and
// (fp.div rm x 1.0) are x, (fp.neg (fp.neg x)) is x. What comes back is then
// not a fresh node of the operation's own kind: it is whatever the operand
// already was, which may be an ite, an array read, a symbol or a constant.
//
// The C API stamped the format on its result unconditionally, on the
// assumption that the result was always a new float-kind node needing one.
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

namespace
{

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
  VC vc;
  Expr narrowed; // t114
  Expr ite;      // t169
};

Fuzzed buildFuzzed()
{
  Fuzzed f;
  f.vc = vc_createValidityChecker();

  Expr bits = vc_varExpr(f.vc, "b", vc_bvType(f.vc, 128));
  Expr wide = vc_fpToFPFromIEEEBV(f.vc, 15, 113, bits);
  f.narrowed = vc_fpToFPFromFP(f.vc, 11, 53,
                               vc_fpRoundingMode(f.vc, VC_RM_RTN), wide);

  Expr rm = vc_fpRoundingModeVar(f.vc, "rm");
  Expr quotient = vc_fpDivExpr(f.vc, rm, f.narrowed, f.narrowed);
  Expr cond = vc_varExpr(f.vc, "c", vc_boolType(f.vc));
  f.ite = vc_iteExpr(f.vc, cond, quotient, f.narrowed);

  return f;
}

// Expr is a handle onto a node, and the API hands out a fresh handle per
// call, so two Exprs naming one node are not pointer-equal. Compare the nodes.
const stp::ASTNode& node(Expr e)
{
  return *(const stp::ASTNode*)e;
}

// A Float64 built here has the format the input asked for, whatever kind of
// node it happens to be.
void isFloat64(Expr e)
{
  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(e));
  EXPECT_EQ(11, vc_getExpWidth(e));
  EXPECT_EQ(53, vc_getSigWidth(e));
  EXPECT_TRUE(stp::BVTypeCheck(*(stp::ASTNode*)e));
}

} // namespace

TEST(fp_identity_passthrough, min_of_an_ite_with_itself)
{
  Fuzzed f = buildFuzzed();
  isFloat64(f.ite);

  // Used to abort here, in vc_fpMinExpr, stamping (11, 53) onto the ITE.
  Expr m = vc_fpMinExpr(f.vc, f.ite, f.ite);

  // The identity fired -- the point of the test is the node it handed back --
  // and the result is the Float64 it should be.
  EXPECT_EQ(node(f.ite), node(m));
  isFloat64(m);

  vc_Destroy(f.vc);
}

TEST(fp_identity_passthrough, max_of_an_ite_with_itself)
{
  Fuzzed f = buildFuzzed();

  Expr m = vc_fpMaxExpr(f.vc, f.ite, f.ite);
  EXPECT_EQ(node(f.ite), node(m));
  isFloat64(m);

  vc_Destroy(f.vc);
}

// The other identities that hand back an operand rather than a fresh node.
// Each is reached the same way and used to abort the same way.
TEST(fp_identity_passthrough, arithmetic_identities_over_an_ite)
{
  Fuzzed f = buildFuzzed();
  Expr rm = vc_fpRoundingMode(f.vc, VC_RM_RNE);
  Expr one = vc_fpConstFromDouble(f.vc, vc_fpType(f.vc, 11, 53), rm, 1.0);

  // x * 1.0 = x and 1.0 * x = x: exact for every value and rounding mode.
  Expr mul = vc_fpMulExpr(f.vc, rm, f.ite, one);
  EXPECT_EQ(node(f.ite), node(mul));
  isFloat64(mul);

  Expr mulFlipped = vc_fpMulExpr(f.vc, rm, one, f.ite);
  EXPECT_EQ(node(f.ite), node(mulFlipped));
  isFloat64(mulFlipped);

  // x / 1.0 = x.
  Expr div = vc_fpDivExpr(f.vc, rm, f.ite, one);
  EXPECT_EQ(node(f.ite), node(div));
  isFloat64(div);

  // -(-x) = x, including for NaN payloads and the signed zeros.
  Expr negneg = vc_fpNegExpr(f.vc, vc_fpNegExpr(f.vc, f.ite));
  EXPECT_EQ(node(f.ite), node(negneg));
  isFloat64(negneg);

  vc_Destroy(f.vc);
}

// An array read is the other float-typed node of a bitvector kind: kind READ,
// degree 2, and (unlike a float-kind node) nothing about the kind says it is
// a float. It reaches the same passthrough.
TEST(fp_identity_passthrough, min_of_an_array_read_with_itself)
{
  VC vc = vc_createValidityChecker();

  Type f32 = vc_fpType(vc, 8, 24);
  Expr a = vc_varExpr(vc, "a", vc_arrayType(vc, vc_bvType(vc, 4), f32));
  Expr cell = vc_readExpr(vc, a, vc_varExpr(vc, "i", vc_bvType(vc, 4)));

  Expr m = vc_fpMinExpr(vc, cell, cell);
  EXPECT_EQ(node(cell), node(m));
  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(m));
  EXPECT_EQ(8, vc_getExpWidth(m));
  EXPECT_EQ(24, vc_getSigWidth(m));
  EXPECT_TRUE(stp::BVTypeCheck(*(stp::ASTNode*)m));

  vc_Destroy(vc);
}

// A passthrough result must not be merely *reachable*: it has to mean what
// (fp.min x x) means. Over an ite between two ordinary constants there is no
// NaN in play, so fp.eq is ordinary equality and the answers are exact.
TEST(fp_identity_passthrough, min_of_an_ite_still_solves_correctly)
{
  VC vc = vc_createValidityChecker();

  Type f64 = vc_fpType(vc, 11, 53);
  Expr rm = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr one = vc_fpConstFromDouble(vc, f64, rm, 1.0);
  Expr two = vc_fpConstFromDouble(vc, f64, rm, 2.0);

  Expr cond = vc_varExpr(vc, "c", vc_boolType(vc));
  Expr chosen = vc_iteExpr(vc, cond, one, two);
  Expr m = vc_fpMinExpr(vc, chosen, chosen);

  // (fp.min x x) = x, whichever branch the condition takes.
  EXPECT_EQ(1, vc_query(vc, vc_fpEqExpr(vc, m, chosen))); // 1 == VALID

  // And it is one of the two branch values, not some third thing the format
  // stamp could have produced: 1.0 when c holds, 2.0 when it does not.
  vc_push(vc);
  vc_assertFormula(vc, cond);
  EXPECT_EQ(1, vc_query(vc, vc_fpEqExpr(vc, m, one)));
  vc_pop(vc);

  vc_push(vc);
  vc_assertFormula(vc, vc_notExpr(vc, cond));
  EXPECT_EQ(1, vc_query(vc, vc_fpEqExpr(vc, m, two)));
  vc_pop(vc);

  vc_Destroy(vc);
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
  Fuzzed f = buildFuzzed();
  Expr m = vc_fpMinExpr(f.vc, f.ite, f.ite);

  // Not valid: take the ite's else branch with any ordinary finite t114 and
  // the min is that, which is not a NaN.
  EXPECT_EQ(0, vc_query(f.vc, vc_fpIsNaNExpr(f.vc, m))); // 0 == INVALID

  // Pinning t114 to a NaN makes the min a NaN down either branch, NaN/NaN
  // being a NaN too. Check the assertion is satisfiable first, so that the
  // validity below is real rather than vacuous.
  vc_assertFormula(f.vc, vc_fpIsNaNExpr(f.vc, f.narrowed));
  ASSERT_EQ(0, vc_query(f.vc, vc_falseExpr(f.vc)));
  EXPECT_EQ(1, vc_query(f.vc, vc_fpIsNaNExpr(f.vc, m))); // 1 == VALID

  vc_Destroy(f.vc);
}

// The identity is not confined to the ite: any float-typed operand is handed
// straight back, so check the plain ones too. A symbol has degree zero and a
// float constant is an ASTFPConst, both of which SetExpWidth would have
// accepted -- they are here so that the passthrough is pinned for every shape
// of operand rather than only the one that used to abort.
TEST(fp_identity_passthrough, min_of_a_symbol_or_a_constant_with_itself)
{
  VC vc = vc_createValidityChecker();

  Type f64 = vc_fpType(vc, 11, 53);
  Expr x = vc_varExpr(vc, "x", f64);
  Expr mx = vc_fpMinExpr(vc, x, x);
  EXPECT_EQ(node(x), node(mx));
  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(mx));

  Expr one =
      vc_fpConstFromDouble(vc, f64, vc_fpRoundingMode(vc, VC_RM_RNE), 1.0);
  Expr mone = vc_fpMinExpr(vc, one, one);
  EXPECT_EQ(node(one), node(mone));
  EXPECT_EQ(FLOATINGPOINT_TYPE, getType(mone));
  EXPECT_EQ(11, vc_getExpWidth(mone));
  EXPECT_EQ(53, vc_getSigWidth(mone));

  vc_Destroy(vc);
}

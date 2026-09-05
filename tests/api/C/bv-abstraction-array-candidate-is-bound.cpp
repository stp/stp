/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <gtest/gtest.h>
#include <stp/c_interface.h>

#include <string>

// The array-equality consistency checker owns the complete array graph for a
// solve, and ConstructCounterExample refuses to materialize a candidate before
// that graph has been bound -- a model assembled ahead of the checker would be
// read back as if the checker had certified it.
//
// A BV abstraction can reach that point first. It replaces an operation with
// free Booleans and is refined from candidate models, so the driver has to pin
// it before anything else reads the candidate; where it did not, a solve whose
// array equality was still pending had a candidate built underneath it:
//
//   Fatal Error: array-equality: a SAT candidate was materialized before the
//   complete array graph was bound
//
// The shape is a reduced fuzzer trace and every part of it is load-bearing.
// The array disequality is not asserted until after the first solve has fixed
// the abstraction records, and it arrives inside an assumption scope, so the
// graph for it is bound on a later round than the one the abstraction was
// installed on. A hand-written sequence does not get there: with the fix
// reverted, half a dozen other guards on this route fire first, and only this
// ordering reaches the one under test.
//
// Both queries answer for the caller's assertions, so the test pins the
// verdicts as well as the absence of the abort: the first is unsatisfiable
// under its assumptions and the second, with those assumptions retracted, is
// satisfiable.

namespace
{

// vc_query: 1 = VALID (the assertions are unsatisfiable), 0 = INVALID (they
// are satisfiable, and a model is available).
const int SAT = 0;
const int UNSAT = 1;

const int WIDE = 88;  // the width the abstraction engages on here
const int INDEX = 32;

} // namespace

TEST(bv_abstraction_array_candidate_is_bound,
     array_disequality_inside_an_assumption_scope)
{
  VC vc = vc_createValidityChecker();

  vc_setFlag(vc, 'x'); // decide whole-array equality (extensional arrays)
  vc_setFlag(vc, 'u'); // uninterpreted functions
  vc_setInterfaceFlags(vc, BV_EQ_ABSTRACTION, 1);
  vc_setInterfaceFlags(vc, BV_TERM_ABSTRACTION, 1);
  vc_setInterfaceFlags(vc, BV_ABSTRACTION_WIDTH, 1);
  vc_setInterfaceFlags(vc, BV_EQ_REFINE_WIDTH, 1);
  vc_setFlag(vc, 'i'); // incremental driver from the first query

  Type wide = vc_bvType(vc, WIDE);
  Expr x = vc_varExpr(vc, "x", wide);
  Expr y = vc_varExpr(vc, "y", wide);
  Expr z = vc_varExpr(vc, "z", wide);
  Expr w = vc_varExpr(vc, "w", wide);
  Expr v = vc_varExpr(vc, "v", wide);

  Expr maxSigned = vc_bvConstExprFromStr(
      vc, std::string("0" + std::string(WIDE - 1, '1')).c_str());
  Expr minSigned = vc_bvConstExprFromStr(
      vc, std::string("1" + std::string(WIDE - 1, '0')).c_str());
  Expr zero =
      vc_bvConstExprFromStr(vc, std::string(WIDE, '0').c_str());

  // A comparison over abstracted arithmetic: the term abstraction stands in
  // for the remainder, and the comparison is what the refinement pins.
  Expr rem = vc_sbvRemExpr(vc, WIDE, vc_bvUMinusExpr(vc, maxSigned),
                           vc_bvUMinusExpr(vc, minSigned));
  Expr remGtX = vc_bvGtExpr(vc, rem, x);
  Expr quotient = vc_bvDivExpr(vc, WIDE, minSigned, minSigned);

  Type unaryDomain[1] = {wide};
  UFDeclHandle f =
      vc_declareUninterpretedFunction(vc, "f", unaryDomain, 1, wide);
  ASSERT_NE(0u, f);

  Type predicateDomain[4] = {wide, vc_boolType(vc), wide, vc_boolType(vc)};
  UFDeclHandle p = vc_declareUninterpretedFunction(
      vc, "p", predicateDomain, 4, vc_boolType(vc));
  ASSERT_NE(0u, p);

  Expr rm = vc_fpRoundingModeVar(vc, "rm");
  Expr converted = vc_fpToFPFromUnsignedBV(vc, 8, 24, rm, y);
  Expr isNaN = vc_fpIsNaNExpr(vc, converted);

  Expr pArgs0[4] = {v, remGtX, y, remGtX};
  Expr p0 = vc_applyUninterpretedFunction(vc, p, pArgs0, 4);
  ASSERT_NE(nullptr, p0);

  Expr pArgs1[4] = {minSigned, vc_iffExpr(vc, remGtX, p0), y,
                    vc_sbvGeExpr(vc, z, w)};
  Expr p1 = vc_applyUninterpretedFunction(vc, p, pArgs1, 4);
  ASSERT_NE(nullptr, p1);

  Expr fArgs[1] = {y};
  Expr fy = vc_applyUninterpretedFunction(vc, f, fArgs, 1);
  ASSERT_NE(nullptr, fy);

  Expr pArgs2[4] = {fy, isNaN, rem, p0};
  Expr p2 = vc_applyUninterpretedFunction(vc, p, pArgs2, 4);
  ASSERT_NE(nullptr, p2);

  Expr pArgs3[4] = {y, remGtX, vc_varExpr(vc, "u", wide), remGtX};
  Expr p3 = vc_applyUninterpretedFunction(vc, p, pArgs3, 4);
  ASSERT_NE(nullptr, p3);

  Expr pArgs4[4] = {zero, p3, y, p1};
  Expr p4 = vc_applyUninterpretedFunction(vc, p, pArgs4, 4);
  ASSERT_NE(nullptr, p4);

  Expr root[2] = {p4, p2};
  vc_assertFormula(vc, vc_andExprN(vc, root, 2));

  // The array only enters after the abstraction records exist.
  Expr array =
      vc_varExpr(vc, "a", vc_arrayType(vc, vc_bvType(vc, INDEX), wide));
  Expr index = vc_varExpr(vc, "i", vc_bvType(vc, INDEX));
  Expr storeAtIndex = vc_writeExpr(vc, array, index, y);
  Expr storeAtConst = vc_writeExpr(
      vc, array,
      vc_bvConstExprFromStr(vc, "01111011000001100101000100110101"),
      quotient);
  Expr storesDiffer =
      vc_notExpr(vc, vc_eqExpr(vc, storeAtConst, storeAtIndex));

  Expr pArgs5[4] = {x, p0, x, storesDiffer};
  Expr p5 = vc_applyUninterpretedFunction(vc, p, pArgs5, 4);
  ASSERT_NE(nullptr, p5);

  vc_push(vc);
  vc_assertFormula(vc, vc_iffExpr(vc, isNaN, p0));
  vc_assertFormula(vc, p0);
  vc_assertFormula(vc, vc_iffExpr(vc, p5, p0));
  EXPECT_EQ(UNSAT, vc_query(vc, vc_falseExpr(vc)));

  vc_pop(vc);
  EXPECT_EQ(SAT, vc_query(vc, vc_falseExpr(vc)));

  vc_Destroy(vc);
}

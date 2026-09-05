#include <gtest/gtest.h>
#include <stp/AST/AST.h> // BVTypeCheck, the invariant these pin
#include <stp/c_interface.h>

// Regression tests: one bitvector read both as bits and as a float.
//
// Solving lowers every floating-point operation to a bitvector circuit, and
// a lowered float *is* its packed bits, with the format stamped onto the node
// that holds them.  Nodes are hash-consed, so when the circuit for
// ((_ to_fp e s) bits) folds back to `bits` itself -- which it does whenever
// the exponent and significand fields are already constant, since then there
// is no NaN to canonicalise -- the stamp lands on the input's own node, and it
// reports FLOATINGPOINT_TYPE from then on.
//
// A bitvector operation over those same bits then had an operand that no
// longer called itself a bitvector, and the type check aborted:
//
//   Fatal Error: BVTypeCheck: ChildNodes of bitvector-terms must be bitvectors
//   Fatal Error: BVTypeCheck: terms in atomic formulas must be bitvectors
//
// on input every one of whose terms is well sorted. It is the same bits
// either way -- the shift shifts them, the comparison compares them -- and
// the checks now say so, as they already did for to_fp's own operand and for
// every term checkChildrenAreBV covers.
//
// Found by fuzzing with murxla (a bvand of bv-min-signed feeding both
// fp.to_fp_from_bv and bvashr); delta-minimized.

namespace
{

// The fuzzer's trace, term for term, over (_ BitVec 64):
//
//   t8  = (bvand bv-min-signed _x3)      the shared bits
//   t9  = ((_ to_fp 11 53) t8)           those bits read as a Float64
//   t21 = (bvashr t8 _x3)                and the same bits shifted
//
// plus the Booleans that tie the two readings together. Simplifying t9 blasts
// it, which is what leaves the Float64 format on t8's node; simplifying t21
// then built a shift whose first operand was that node.
struct Shared
{
  VC vc;
  Expr x3;   // _x3
  Expr bits; // t8
  Expr f;    // t9
};

Shared buildShared()
{
  Shared s;
  s.vc = vc_createValidityChecker();

  s.x3 = vc_varExpr(s.vc, "_x3", vc_bvType(s.vc, 64));
  // bv-min-signed leaves only the sign bit, so t8's exponent and significand
  // fields are constant zero however the solver reaches that -- which is what
  // makes the float's circuit fold back to the bits it was built from.
  Expr minSigned = vc_bvConstExprFromLL(s.vc, 64, 0x8000000000000000ULL);
  s.bits = vc_bvAndExpr(s.vc, minSigned, s.x3);
  s.f = vc_fpToFPFromIEEEBV(s.vc, 11, 53, s.bits);

  // (not (= (bvsgt t8 _x3) (fp.leq t9 t9))), the two sorts' predicates over
  // the one value. STP spells Boolean '=' as iff.
  Expr sgt = vc_sbvGtExpr(s.vc, s.bits, s.x3);
  Expr leq = vc_fpLeqExpr(s.vc, s.f, s.f);
  vc_assertFormula(s.vc, vc_notExpr(s.vc, vc_iffExpr(s.vc, sgt, leq)));

  // (bvugt t8 (bvnand (bvashr t8 _x3) t8))
  Expr ashr = vc_bvSignedRightShiftExprExpr(s.vc, 64, s.bits, s.x3);
  vc_assertFormula(
      s.vc, vc_bvGtExpr(s.vc, s.bits, vc_bvNandExpr(s.vc, ashr, s.bits)));

  return s;
}

} // namespace

TEST(fp_shared_bv_operand, ashr_over_bits_that_are_also_a_float)
{
  Shared s = buildShared();

  // Used to abort in the simplifier on
  //   (BVSRSHIFT (BVCONCAT _x3[63:63] 0b0...0) _x3)
  // whose first operand the blaster had just stamped as a Float64.
  ASSERT_EQ(0, vc_query(s.vc, vc_falseExpr(s.vc))); // 0 == INVALID == sat

  // The answer is right, not merely reached. t9 is a zero and so never a NaN,
  // so (fp.leq t9 t9) holds and the first assertion is (not (bvsgt t8 _x3)),
  // which every _x3 satisfies. The second forces the sign bit: with it clear
  // t8 is 0, the shift is 0, and (bvugt 0 (bvnand 0 0)) is false.
  Expr cex = vc_getCounterExample(s.vc, s.x3);
  EXPECT_EQ(0x8000000000000000ULL,
            getBVUnsignedLongLong(cex) & 0x8000000000000000ULL);

  // And the float side agrees with the bits: t8's exponent and significand
  // are zero, so t9 is a zero -- a negative one, the sign bit being set.
  EXPECT_EQ(1, vc_query(s.vc, vc_fpIsZeroExpr(s.vc, s.f)));
  EXPECT_EQ(1, vc_query(s.vc, vc_fpIsNegativeExpr(s.vc, s.f)));
  EXPECT_EQ(0, vc_query(s.vc, vc_fpIsNaNExpr(s.vc, s.f)));

  vc_Destroy(s.vc);
}

// The other half of that reasoning, so that "satisfiable" above is a real
// answer rather than a formula the fix made trivially true: clearing the sign
// bit leaves nothing to satisfy.
TEST(fp_shared_bv_operand, unsatisfiable_once_the_sign_bit_is_cleared)
{
  Shared s = buildShared();

  Expr top = vc_bvExtract(s.vc, s.x3, 63, 63);
  vc_assertFormula(s.vc,
                   vc_eqExpr(s.vc, top, vc_bvConstExprFromLL(s.vc, 1, 0ULL)));

  EXPECT_EQ(1, vc_query(s.vc, vc_falseExpr(s.vc))); // 1 == VALID == unsat

  vc_Destroy(s.vc);
}

// The same sharing reached without the solver's own assertions: build the
// bitvector terms *after* a solve has lowered the float over those same bits,
// and type check them here. The C API's checks are asserts too, so a build
// with assertions off would let these through unexamined otherwise.
TEST(fp_shared_bv_operand, bv_terms_over_bits_that_are_also_a_float)
{
  VC vc = vc_createValidityChecker();

  Expr sign = vc_varExpr(vc, "s", vc_bvType(vc, 1));
  Expr bits = vc_bvConcatExpr(vc, sign, vc_bvConstExprFromLL(vc, 15, 0ULL));
  Expr f = vc_fpToFPFromIEEEBV(vc, 5, 11, bits);
  ASSERT_EQ(BITVECTOR_TYPE, getType(bits));

  // Solving builds the float's circuit, which is where the format used to
  // land on the node `bits` names. A binary16 whose exponent and significand
  // are zero is a zero, so asserting it negative pins the sign bit to one,
  // and `bits` to 0x8000.
  vc_assertFormula(vc, vc_fpIsNegativeExpr(vc, f));
  ASSERT_EQ(0, vc_query(vc, vc_falseExpr(vc)));

  // The bits are still bits. Lowering hands the blaster its operand format as
  // an argument now, so nothing is stamped on what it produces, and the node
  // the input built keeps the sort the input gave it.
  EXPECT_EQ(BITVECTOR_TYPE, getType(bits));

  Expr y = vc_varExpr(vc, "y", vc_bvType(vc, 16));
  Expr zero16 = vc_bvConstExprFromLL(vc, 16, 0ULL);

  // A shift, a bitwise operation and an arithmetic one: one check covers the
  // operands of all three.
  Expr shifted = vc_bvSignedRightShiftExprExpr(vc, 16, bits, y);
  Expr anded = vc_bvAndExpr(vc, bits, y);
  Expr summed = vc_bvPlusExpr(vc, 16, bits, y);
  EXPECT_TRUE(stp::BVTypeCheck(*(stp::ASTNode*)shifted));
  EXPECT_TRUE(stp::BVTypeCheck(*(stp::ASTNode*)anded));
  EXPECT_TRUE(stp::BVTypeCheck(*(stp::ASTNode*)summed));

  // The comparison and overflow predicates have a check of their own.
  Expr ugt = vc_bvGtExpr(vc, bits, zero16);
  Expr slt = vc_sbvLtExpr(vc, bits, zero16);
  Expr addo = vc_bvUnsignedAddOverflowExpr(vc, bits, y);
  EXPECT_TRUE(stp::BVTypeCheck(*(stp::ASTNode*)ugt));
  EXPECT_TRUE(stp::BVTypeCheck(*(stp::ASTNode*)slt));
  EXPECT_TRUE(stp::BVTypeCheck(*(stp::ASTNode*)addo));

  // The two readings agree on the one bit they share. 0x8000 is above zero
  // unsigned and below it signed...
  EXPECT_EQ(1, vc_query(vc, ugt));
  EXPECT_EQ(1, vc_query(vc, slt));
  // ...and an arithmetic shift right by one fills with the sign, giving
  // 0xc000 -- the bits still being bits, not the float they also spell.
  EXPECT_EQ(1,
            vc_query(vc, vc_eqExpr(vc,
                                   vc_bvSignedRightShiftExprExpr(
                                       vc, 16, bits,
                                       vc_bvConstExprFromLL(vc, 16, 1ULL)),
                                   vc_bvConstExprFromLL(vc, 16, 0xc000ULL))));

  vc_Destroy(vc);
}

// ((_ to_fp e s) rm bv) over a *signed integer* and ((_ to_fp e s) bv) over
// the same bits, in one problem. Reading the bits as a binary16 makes them a
// zero; reading them as the integer they hold makes them -32768. The two
// answers differ, so which operation is which has to survive lowering.
//
// It did not. A lowered float is its packed bits, so once the reinterpretation
// had been lowered its operand was indistinguishable from the integer, and
// to_fp -- which told the two forms apart by asking the operand's type --
// converted the integer as though it were a float. STP answered that -32768
// converts to a zero. FP_TOFP_SIGNED records which operation was written, at
// the point where the sort is still known.
TEST(fp_shared_bv_operand, signed_to_fp_over_bits_also_read_as_a_float)
{
  VC vc = vc_createValidityChecker();

  Expr s = vc_varExpr(vc, "s", vc_bvType(vc, 1));
  Expr bits = vc_bvConcatExpr(vc, s, vc_bvConstExprFromLL(vc, 15, 0ULL));

  Expr reinterpreted = vc_fpToFPFromIEEEBV(vc, 5, 11, bits);
  Expr converted =
      vc_fpToFPFromSignedBV(vc, 5, 11, vc_fpRoundingMode(vc, VC_RM_RNE), bits);

  // Touch the reinterpretation, so its circuit is built before the conversion
  // is looked at. This ordering is what used to decide the answer.
  vc_assertFormula(vc, vc_fpLeqExpr(vc, reinterpreted, reinterpreted));

  // s = 1 makes the bits 0x8000, which is -32768 as a signed 16-bit integer
  // and is exactly representable in binary16. So the conversion is not always
  // a zero...
  EXPECT_EQ(0, vc_query(vc, vc_fpIsZeroExpr(vc, converted)));
  // ...while the reinterpretation is, for either value of s.
  EXPECT_EQ(1, vc_query(vc, vc_fpIsZeroExpr(vc, reinterpreted)));

  vc_Destroy(vc);
}

// The mirror image: ((_ to_fp e s) rm f) over a float, where the source is an
// *operation* rather than a leaf. Recording "this source is an integer" in the
// kind has to leave the float form alone -- and a float leaf keeps its
// declared format either way, so only an operation, whose lowered form carries
// no format at all, exercises the distinction.
TEST(fp_shared_bv_operand, float_to_float_to_fp_over_an_operation)
{
  VC vc = vc_createValidityChecker();

  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 5, 11));

  // 0.75 + 0.75 = 1.5 in binary16, and widening to binary32 is exact.
  Expr threeQuarters =
      vc_fpConstFromBits(vc, 5, 11, vc_bvConstExprFromLL(vc, 16, 0x3A00ULL));
  vc_assertFormula(vc, vc_fpEqExpr(vc, x, threeQuarters));

  Expr sum = vc_fpAddExpr(vc, rne, x, x);
  Expr widened = vc_fpToFPFromFP(vc, 8, 24, rne, sum);
  Expr oneAndAHalf32 = vc_fpConstFromBits(
      vc, 8, 24, vc_bvConstExprFromLL(vc, 32, 0x3FC00000ULL));

  EXPECT_EQ(1, vc_query(vc, vc_fpEqExpr(vc, widened, oneAndAHalf32)));

  vc_Destroy(vc);
}

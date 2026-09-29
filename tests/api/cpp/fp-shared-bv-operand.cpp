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

// fp-shared-bv-operand.cpp -- regression tests: one bitvector read both
// as bits and as a float.
//
// Solving lowers every floating-point operation to a bitvector circuit, and
// a lowered float *is* its packed bits, with the format stamped onto the node
// that holds them. Nodes are hash-consed, so when the circuit for
// ((_ to_fp e s) bits) folds back to `bits` itself -- which it does whenever
// the exponent and significand fields are already constant, since then there
// is no NaN to canonicalise -- the stamp lands on the input's own node, and it
// reports a floating-point type from then on.
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
//
// The engine's type check is not part of the API, so it is read through
// api_engine.hpp; everything else goes through the public API.

#include "api_engine.hpp"

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
  TermManager tm;
  Solver solver{tm, sanity_checked()};
  Term x3;   // _x3
  Term bits; // t8
  Term f;    // t9

  Shared()
  {
    x3 = tm.declare("_x3", tm.mk_bv_sort(64));
    // bv-min-signed leaves only the sign bit, so t8's exponent and significand
    // fields are constant zero however the solver reaches that -- which is
    // what makes the float's circuit fold back to the bits it was built from.
    bits = bvand(tm.mk_bv_min_signed(64), x3);
    f = to_fp_from_bits(tm.mk_fp64_sort(), bits);

    // (not (= (bvsgt t8 _x3) (fp.leq t9 t9))), the two sorts' predicates over
    // the one value: == between two Booleans is their equality.
    solver.add(!(bvsgt(bits, x3) == fp_leq(f, f)));

    // (bvugt t8 (bvnand (bvashr t8 _x3) t8))
    solver.add(bvugt(bits, bvnand(bvashr(bits, x3), bits)));
  }
};

} // namespace

TEST(fp_shared_bv_operand, ashr_over_bits_that_are_also_a_float)
{
  Shared s;

  // Used to abort in the simplifier on
  //   (BVSRSHIFT (BVCONCAT _x3[63:63] 0b0...0) _x3)
  // whose first operand the blaster had just stamped as a Float64.
  ASSERT_TRUE(s.solver.check_sat().is_sat());

  // The answer is right, not merely reached. t9 is a zero and so never a NaN,
  // so (fp.leq t9 t9) holds and the first assertion is (not (bvsgt t8 _x3)),
  // which every _x3 satisfies. The second forces the sign bit: with it clear
  // t8 is 0, the shift is 0, and (bvugt 0 (bvnand 0 0)) is false.
  EXPECT_EQ(s.solver.model().uint64_value(s.x3) & 0x8000000000000000ULL, 0x8000000000000000ULL);

  // And the float side agrees with the bits: t8's exponent and significand
  // are zero, so t9 is a zero -- a negative one, the sign bit being set.
  EXPECT_TRUE(s.solver.entails(fp_is_zero(s.f)).is_valid());
  EXPECT_TRUE(s.solver.entails(fp_is_neg(s.f)).is_valid());
  EXPECT_TRUE(s.solver.entails(fp_is_nan(s.f)).is_invalid());
}

// The other half of that reasoning, so that "satisfiable" above is a real
// answer rather than a formula the fix made trivially true: clearing the sign
// bit leaves nothing to satisfy.
TEST(fp_shared_bv_operand, unsatisfiable_once_the_sign_bit_is_cleared)
{
  Shared s;

  const Term top = extract(63, 63, s.x3);
  s.solver.add(top == s.tm.mk_bv(1, 0));

  EXPECT_TRUE(s.solver.check_sat().is_unsat());
}

// The same sharing reached without the solver's own assertions: build the
// bitvector terms *after* a solve has lowered the float over those same bits,
// and type check them here. The engine's own type checks are asserts, so a
// build with assertions off would let these through unexamined otherwise.
TEST(fp_shared_bv_operand, bv_terms_over_bits_that_are_also_a_float)
{
  TermManager tm;
  Solver s(tm, sanity_checked());

  const Term sign = tm.declare("s", tm.mk_bv_sort(1));
  const Term bits = concat(sign, tm.mk_bv(15, 0));
  const Term f = to_fp_from_bits(tm.mk_fp16_sort(), bits);
  ASSERT_TRUE(bits.sort().is_bv());

  // Solving builds the float's circuit, which is where the format used to
  // land on the node `bits` names. A binary16 whose exponent and significand
  // are zero is a zero, so asserting it negative pins the sign bit to one,
  // and `bits` to 0x8000.
  s.add(fp_is_neg(f));
  ASSERT_TRUE(s.check_sat().is_sat());

  // The bits are still bits. Lowering hands the blaster its operand format as
  // an argument now, so nothing is stamped on what it produces, and the node
  // the input built keeps the sort the input gave it (a term's sort is read
  // from its node, so a stamp would show here).
  EXPECT_TRUE(bits.sort().is_bv());

  const Term y = tm.declare("y", tm.mk_bv_sort(16));
  const Term zero16 = tm.mk_bv(16, 0);

  // A shift, a bitwise operation and an arithmetic one: one check covers the
  // operands of all three.
  const Term shifted = bvashr(bits, y);
  const Term anded = bvand(bits, y);
  const Term summed = bvadd(bits, y);
  EXPECT_TRUE(stp::BVTypeCheck(api_test::engine_node(shifted)));
  EXPECT_TRUE(stp::BVTypeCheck(api_test::engine_node(anded)));
  EXPECT_TRUE(stp::BVTypeCheck(api_test::engine_node(summed)));

  // The comparison and overflow predicates have a check of their own.
  const Term ugt = bvugt(bits, zero16);
  const Term slt = bvslt(bits, zero16);
  const Term addo = bvuaddo(bits, y);
  EXPECT_TRUE(stp::BVTypeCheck(api_test::engine_node(ugt)));
  EXPECT_TRUE(stp::BVTypeCheck(api_test::engine_node(slt)));
  EXPECT_TRUE(stp::BVTypeCheck(api_test::engine_node(addo)));

  // The two readings agree on the one bit they share. 0x8000 is above zero
  // unsigned and below it signed...
  EXPECT_TRUE(s.entails(ugt).is_valid());
  EXPECT_TRUE(s.entails(slt).is_valid());
  // ...and an arithmetic shift right by one fills with the sign, giving
  // 0xc000 -- the bits still being bits, not the float they also spell.
  EXPECT_TRUE(s.entails(bvashr(bits, tm.mk_bv(16, 1)) == tm.mk_bv(16, 0xc000)).is_valid());
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
  TermManager tm;
  Solver s(tm, sanity_checked());

  const Term sign = tm.declare("s", tm.mk_bv_sort(1));
  const Term bits = concat(sign, tm.mk_bv(15, 0));

  const Sort f16 = tm.mk_fp16_sort();
  const Term reinterpreted = to_fp_from_bits(f16, bits);
  // to_fp over a bitvector is the signed conversion.
  const Term converted = to_fp(f16, RoundingMode::RNE, bits);

  // Touch the reinterpretation, so its circuit is built before the conversion
  // is looked at. This ordering is what used to decide the answer.
  s.add(fp_leq(reinterpreted, reinterpreted));

  // s = 1 makes the bits 0x8000, which is -32768 as a signed 16-bit integer
  // and is exactly representable in binary16. So the conversion is not always
  // a zero...
  EXPECT_TRUE(s.entails(fp_is_zero(converted)).is_invalid());
  // ...while the reinterpretation is, for either value of s.
  EXPECT_TRUE(s.entails(fp_is_zero(reinterpreted)).is_valid());
}

// The mirror image: ((_ to_fp e s) rm f) over a float, where the source is an
// *operation* rather than a leaf. Recording "this source is an integer" in the
// kind has to leave the float form alone -- and a float leaf keeps its
// declared format either way, so only an operation, whose lowered form carries
// no format at all, exercises the distinction.
TEST(fp_shared_bv_operand, float_to_float_to_fp_over_an_operation)
{
  TermManager tm;
  Solver s(tm, sanity_checked());

  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Sort f16 = tm.mk_fp16_sort(), f32 = tm.mk_fp32_sort();
  const Term x = tm.declare("x", f16);

  // 0.75 + 0.75 = 1.5 in binary16, and widening to binary32 is exact.
  const Term three_quarters = tm.mk_fp_from_bits(f16, tm.mk_bv(16, 0x3A00));
  s.add(fp_eq(x, three_quarters));

  const Term sum = fp_add(rne, x, x);
  const Term widened = to_fp(f32, rne, sum);
  const Term one_and_a_half32 = tm.mk_fp_from_bits(f32, tm.mk_bv(32, 0x3FC00000));

  EXPECT_TRUE(s.entails(fp_eq(widened, one_and_a_half32)).is_valid());
}

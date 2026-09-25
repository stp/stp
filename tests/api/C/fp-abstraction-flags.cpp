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

// The floating-point abstraction's knobs and counters, through the C API.
//
// Twenty setters and eighteen counters is a lot of switch arms, and every
// one of them is a line that writes a named field. Nothing about that is
// hard, which is exactly why it wants a test: an arm that writes its
// neighbour's field -- significand bits into the wide significand bits, the
// restart limit into the restart width -- is invisible to review and to
// every other test in the tree, because the two fields have the same type
// and the wrong one is a perfectly ordinary value to hold.
//
// The counters need a different kind of test. They are folded into the
// session totals by a watermark: each FpAbstraction publishes the delta
// since it last published, on destruction and whenever a reader asks. What
// that has to be shown to do is answer MID-SESSION, because the caller these
// counters exist for -- a fuzzing campaign asking whether the abstraction
// engaged at all -- reads them while the checker is still alive. Publishing
// only from the destructor reported zeroes to precisely that caller, which
// is how the first attempt at this was found to be wrong.
#include "stp/STPManager/STP.h"
#include "stp/c_interface.h"
#include <gtest/gtest.h>

namespace
{
// The flags the checker is carrying, which is what a setter has to be shown
// to reach: an arm that writes the wrong field changes nothing here.
const stp::UserDefinedFlags& flags(VC vc)
{
  return ((stp::STP*)vc)->bm->UserFlags;
}

int errors = 0;
void countError(const char*)
{
  errors++;
}

// A query with something to abstract: a product of two normals, asked a
// question it cannot answer by simplification.
void assertAProduct(VC vc)
{
  Type f = vc_fpType(vc, 8, 24);
  Expr rm = vc_fpRoundingMode(vc, VC_RM_RNE);
  Expr x = vc_varExpr(vc, "x", f);
  Expr y = vc_varExpr(vc, "y", f);
  vc_assertFormula(vc, vc_fpIsNormalExpr(vc, x));
  vc_assertFormula(vc, vc_fpIsNormalExpr(vc, y));
  vc_query(vc, vc_fpGtExpr(vc, vc_fpMulExpr(vc, rm, x, y), x));
}
} // namespace

// One assertion per setter, each naming the field it must reach. The values
// are deliberately distinct from each other and from the defaults, so a
// setter that writes a neighbouring field fails rather than coinciding.
TEST(fp_abstraction_flags, EverySetterReachesItsOwnField)
{
  VC vc = vc_createValidityChecker();

  vc_setInterfaceFlags(vc, FP_ABSTRACTION, 1);
  EXPECT_TRUE(flags(vc).fp_abstraction);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_INCREMENTAL, 1);
  EXPECT_TRUE(flags(vc).fp_abstraction_incremental);

  vc_setInterfaceFlags(vc, FP_ABSTRACTION_OPS, 3);
  EXPECT_EQ(3u, flags(vc).fp_abstraction_ops);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_CHAIN_OPS, 5);
  EXPECT_EQ(5u, flags(vc).fp_abstraction_chain_ops);

  vc_setInterfaceFlags(vc, FP_ABSTRACTION_WIDTH, 33);
  EXPECT_EQ(33u, flags(vc).fp_abstraction_width);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_TIERS, 2);
  EXPECT_EQ(2u, flags(vc).fp_abstraction_tiers);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_VALUES, 7);
  EXPECT_EQ(7u, flags(vc).fp_abstraction_values);

  vc_setInterfaceFlags(vc, FP_ABSTRACTION_SHAPE, 0);
  EXPECT_FALSE(flags(vc).fp_abstraction_shape);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_RELATIONAL, 0);
  EXPECT_FALSE(flags(vc).fp_abstraction_relational);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_RELATIONAL_LAST_WIDTH, 64);
  EXPECT_EQ(64u, flags(vc).fp_abstraction_relational_last_width);

  vc_setInterfaceFlags(vc, FP_ABSTRACTION_BOX_LEMMAS, 1);
  EXPECT_TRUE(flags(vc).fp_abstraction_box_lemmas);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_PHASE_HINTS, 1);
  EXPECT_TRUE(flags(vc).fp_abstraction_phase_hints);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_REPAIR, 0);
  EXPECT_FALSE(flags(vc).fp_abstraction_repair);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_DECLINE_PINNED, 1);
  EXPECT_TRUE(flags(vc).fp_abstraction_decline_pinned);
  typedef stp::UserDefinedFlags::FpConstantOperandMode ConstantOperands;
  EXPECT_EQ(ConstantOperands::AUTO, flags(vc).fp_abstraction_constant_operands);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_CONSTANT_OPERANDS, 1);
  EXPECT_EQ(ConstantOperands::ON, flags(vc).fp_abstraction_constant_operands);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_CONSTANT_OPERANDS, 0);
  EXPECT_EQ(ConstantOperands::OFF, flags(vc).fp_abstraction_constant_operands);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_CONSTANT_OPERANDS, 2);
  EXPECT_EQ(ConstantOperands::AUTO, flags(vc).fp_abstraction_constant_operands);

  // The two restart knobs and the two significand ones are the pairs most
  // easily crossed: same type, adjacent lines, names differing by a suffix.
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_RESTART_LIMIT, 9);
  EXPECT_EQ(9u, flags(vc).fp_abstraction_restart_limit);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_RESTART_WIDTH, 128);
  EXPECT_EQ(128u, flags(vc).fp_abstraction_restart_width);
  EXPECT_EQ(9u, flags(vc).fp_abstraction_restart_limit) << "width overwrote limit";

  vc_setInterfaceFlags(vc, FP_ABSTRACTION_SIGNIFICAND_BITS, 6);
  EXPECT_EQ(6u, flags(vc).fp_abstraction_significand_bits);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_SIGNIFICAND_BITS_WIDE, 24);
  EXPECT_EQ(24u, flags(vc).fp_abstraction_significand_bits_wide);
  EXPECT_EQ(6u, flags(vc).fp_abstraction_significand_bits)
      << "the wide setting overwrote the narrow one";

  vc_setInterfaceFlags(vc, FP_ABSTRACTION_BUDGET, 11);
  EXPECT_EQ(11u, flags(vc).fp_abstraction_budget);

  vc_Destroy(vc);
}

// Every unsigned knob would wrap to something enormous under a negative --
// for a width, a floor no format can reach; for a budget, no limit at all --
// so a negative is refused with a nonfatal diagnostic and the field left as
// it was.
TEST(fp_abstraction_flags, NegativesAreRefusedAndChangeNothing)
{
  VC vc = vc_createValidityChecker();
  vc_registerErrorHandler(countError);
  errors = 0;

  vc_setInterfaceFlags(vc, FP_ABSTRACTION_WIDTH, 33);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_TIERS, 2);

  vc_setInterfaceFlags(vc, FP_ABSTRACTION_WIDTH, -1);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_TIERS, -2);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_VALUES, -3);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_BUDGET, -4);

  EXPECT_EQ(4, errors);
  EXPECT_EQ(33u, flags(vc).fp_abstraction_width);
  EXPECT_EQ(2u, flags(vc).fp_abstraction_tiers);

  vc_registerErrorHandler(nullptr);
  vc_Destroy(vc);
}

// The point of the watermark: a reader that asks while the checker is alive
// sees what the abstraction has just done. Publishing only on destruction
// answered this reader with zeroes.
TEST(fp_abstraction_flags, CountersAnswerMidSessionAndDoNotDoubleCount)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, FP_ABSTRACTION, 1);
  assertAProduct(vc);

  const unsigned long long candidates =
      vc_getCounter(vc, STP_COUNTER_FP_CANDIDATES);
  const unsigned long long abstracted =
      vc_getCounter(vc, STP_COUNTER_FP_ABSTRACTED);
  EXPECT_GT(candidates, 0u) << "the product was never seen";
  EXPECT_GT(abstracted, 0u) << "the product was seen but not abstracted";

  // Idempotent: the delta since the last publish is zero, so asking again
  // reports the same totals rather than twice them.
  EXPECT_EQ(candidates, vc_getCounter(vc, STP_COUNTER_FP_CANDIDATES));
  EXPECT_EQ(abstracted, vc_getCounter(vc, STP_COUNTER_FP_ABSTRACTED));

  vc_Destroy(vc);
}

// Zero of both is what a query with no floating-point arithmetic reports,
// and it is a different statement from an abstraction that engaged and did
// nothing -- which is why the pair is published rather than either alone.
TEST(fp_abstraction_flags, NoFloatingPointLeavesTheCountersAtZero)
{
  VC vc = vc_createValidityChecker();
  vc_setInterfaceFlags(vc, FP_ABSTRACTION, 1);

  Type bv = vc_bvType(vc, 32);
  Expr a = vc_varExpr(vc, "a", bv);
  vc_assertFormula(vc, vc_bvGtExpr(vc, a, vc_bvConstExprFromInt(vc, 32, 1)));
  vc_query(vc, vc_falseExpr(vc));

  EXPECT_EQ(0u, vc_getCounter(vc, STP_COUNTER_FP_CANDIDATES));
  EXPECT_EQ(0u, vc_getCounter(vc, STP_COUNTER_FP_ABSTRACTED));

  vc_Destroy(vc);
}

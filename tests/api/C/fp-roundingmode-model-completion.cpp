/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <gtest/gtest.h>
#include <stp/c_interface.h>

// Every RoundingMode value a model hands back names one of the five modes.
//
// The sort is carried in five bits, one-hot, so twenty-seven of the
// thirty-two patterns name nothing. Every mode a formula names is pinned
// to the five -- by its declaration, by FpTotalise at solve time, and by
// the array transform where it mints a cell -- but a pin belongs to the
// assertion level it was made at, while the incremental encoding keeps a
// symbol's SAT variables after that level is popped. The bits behind a
// mode-sorted symbol the last solve never named are therefore free, and
// the backend leaves whatever it likes in them.
//
// Publishing those bits as the symbol's value took the process down:
// vc_getCounterExample lifts a RoundingMode carrier back to a mode, and a
// carrier that is not a mode has nothing to lift into.
//
//   Fatal Error: CreateRMConst requires one of the five rounding modes
//
// Such a symbol is a don't-care, and a don't-care RoundingMode has always
// been completed with RNE -- for the cell no observation covers, for the
// symbol simplified away. This is the same case and takes the same answer.

namespace
{

// vc_query: 1 = VALID (the assertions are unsatisfiable), 0 = INVALID (they
// are satisfiable, so there is a model to read).
const int SAT = 0;

// The bits vc_getCounterExample hands back for a RoundingMode term are the
// VCRoundingMode encoding; see the note on vc_fpRoundingModeType.
unsigned long long modeBits(Expr value)
{
  EXPECT_TRUE(value != NULL);
  return value == NULL ? 0 : getBVUnsignedLongLong(value);
}

bool namesAMode(unsigned long long bits)
{
  return bits == VC_RM_RNE || bits == VC_RM_RTP || bits == VC_RM_RTN ||
         bits == VC_RM_RTZ || bits == VC_RM_RNA;
}

} // namespace

// A rounding mode declared inside a scope, used by one solve, and read back
// after a later solve that never named it. The pin its declaration made went
// with the popped level; the symbol's SAT variables did not, and the last
// solve left them free. Before the fix this aborted the test binary.
TEST(fp_roundingmode_model_completion, symbol_the_last_solve_never_named)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Type rm = vc_fpRoundingModeType(vc);
  Type fp = vc_fpType(vc, 11, 53);
  Expr rtn = vc_fpRoundingMode(vc, VC_RM_RTN);

  vc_push(vc);

  Expr chooser = vc_varExpr(vc, "c", vc_boolType(vc));
  Expr r = vc_varExpr(vc, "r", rm);
  Expr mode = vc_iteExpr(vc, chooser, rtn, r);

  Expr moo = vc_fpMinusInfinity(vc, fp);
  Expr rti = vc_fpRoundToIntegralExpr(vc, r, moo);
  Expr sub = vc_fpSubExpr(vc, mode, rti, rti);

  // The solve that names the mode, and the only one that does.
  vc_assertFormula(vc, vc_fpGtExpr(vc, rti, sub));
  vc_query(vc, vc_falseExpr(vc));

  // The model the read lands on: the level that named the mode -- and that
  // pinned it -- is gone.
  vc_pop(vc);
  ASSERT_EQ(SAT, vc_query(vc, vc_falseExpr(vc)));

  EXPECT_TRUE(namesAMode(modeBits(vc_getCounterExample(vc, mode))));
  EXPECT_TRUE(namesAMode(modeBits(vc_getCounterExample(vc, r))));
  vc_Destroy(vc);
}

// The control, and it carries as much as the case above: completing a free
// carrier must not overwrite one the query decided. A fix that answered RNE
// for every RoundingMode symbol would pass the case and fail this.
TEST(fp_roundingmode_model_completion, a_decided_symbol_keeps_its_mode)
{
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'i');

  Type rm = vc_fpRoundingModeType(vc);
  Expr r = vc_varExpr(vc, "r", rm);
  vc_assertFormula(vc, vc_eqExpr(vc, r, vc_fpRoundingMode(vc, VC_RM_RNA)));

  vc_push(vc);
  ASSERT_EQ(SAT, vc_query(vc, vc_falseExpr(vc)));
  vc_pop(vc);

  ASSERT_EQ(SAT, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)VC_RM_RNA,
            modeBits(vc_getCounterExample(vc, r)));
  vc_Destroy(vc);
}

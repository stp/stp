#include <gtest/gtest.h>
#include <stdio.h>
#include <stp/c_interface.h>

TEST(counter_example_reading, one)
{

  VC vc = vc_createValidityChecker();
  Expr falseExpr = vc_falseExpr(vc);

  Expr A = vc_varExpr(vc, "A", vc_bv32Type(vc));
  Expr B = vc_varExpr(vc, "B", vc_bv32Type(vc));

  vc_push(vc);

  Expr AplusB = vc_bv32PlusExpr(vc, A, B);
  Expr AplusBplus42 =
      vc_bv32PlusExpr(vc, AplusB, vc_bv32ConstExprFromInt(vc, 42));

  assert(0 == vc_query(vc, falseExpr));

// Don't do this,
#if 0
WholeCounterExample wce = vc_getWholeCounterExample(vc);
uint32_t a = getBVUnsigned(vc_getTermFromCounterExample(vc, A, wce));
uint32_t b = getBVUnsigned(vc_getTermFromCounterExample(vc, B, wce));
uint32_t sum = getBVUnsigned(vc_getTermFromCounterExample(vc, AplusBplus42, wce));
vc_deleteWholeCounterExample(wce);
#endif

  // Do this instead.
  vc_getCounterExample(vc, A);
  uint32_t a = getBVUnsigned(vc_getCounterExample(vc, A));
  uint32_t b = getBVUnsigned(vc_getCounterExample(vc, B));
  uint32_t sum = getBVUnsigned(vc_getCounterExample(vc, AplusBplus42));

  ASSERT_TRUE(sum == a + b + 42);

  vc_Destroy(vc);
}

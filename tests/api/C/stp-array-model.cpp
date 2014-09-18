#include <gtest/gtest.h>
#include <stdio.h>
#include <stdlib.h>
#include "stp/c_interface.h"

TEST(stp_array_model,one) {  
  VC vc = vc_createValidityChecker();

  Expr a = vc_bvCreateMemoryArray(vc, "a");

  Expr index_1 = vc_bvConstExprFromInt(vc, 32, 1);
  Expr a_of_1 = vc_readExpr(vc, a, index_1);

  Expr index_2 = vc_bvConstExprFromInt(vc, 32, 2);
  Expr a_of_2 = vc_readExpr(vc, a, index_2);

  Expr ct_42 = vc_bvConstExprFromInt(vc, 8, 42);
  Expr a_of_1_eq_42 = vc_eqExpr(vc, a_of_1, ct_42);

  Expr ct_77 = vc_bvConstExprFromInt(vc, 8, 77);
  Expr a_of_2_eq_77 = vc_eqExpr(vc, a_of_2, ct_77);

  vc_assertFormula(vc, a_of_1_eq_42);
  vc_assertFormula(vc, a_of_2_eq_77);

  /* query(false) */
  ASSERT_TRUE(vc_query(vc, vc_falseExpr(vc)) == 0); // Should be invalid

  ASSERT_FALSE(vc_counterexample_size(vc) == 0);

  Expr *indices;
  Expr *values;
  int size;
  vc_getCounterExampleArray(vc, a, &indices, &values, &size);

  ASSERT_FALSE(size == 0); // No array entries

  int j;
  for (j = 0; j < size; ++j) {
    Expr index = vc_getCounterExample(vc, indices[j]);
    Expr value = vc_getCounterExample(vc, values[j]);
    unsigned long long i = getBVUnsigned(index);
    unsigned long long v = getBVUnsigned(value);

    fprintf(stderr, "a[%llu] = %llu\n", i, v);
  }

  vc_Destroy(vc);

}

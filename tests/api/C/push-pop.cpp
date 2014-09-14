/* g++ -I$(HOME)/stp/c_interface push-pop.c -L$(HOME)/lib -lstp -o cc*/

#include <gtest/gtest.h>
#include <stdio.h>
#include "stp/c_interface.h"

TEST(push_pop, one) {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');
  //vc_setFlags(vc,'v');
  //vc_setFlags(vc,'s');

  Type bv8 = vc_bvType(vc, 8);

  Expr a = vc_varExpr(vc, "a", bv8);
  Expr ct_0 = vc_bvConstExprFromInt(vc, 8, 0);

  Expr a_eq_0 = vc_eqExpr(vc, a, ct_0);

  int query = vc_query(vc, a_eq_0);
  printf("query = %d\n", query);

  vc_push(vc);
  query = vc_query(vc, a_eq_0);
  vc_pop(vc);

  printf("query = %d\n", query);

  vc_DeleteExpr(a_eq_0);
  vc_DeleteExpr(a);

  vc_Destroy(vc);
  // FIXME: Actually test something
  //ASSERT_TRUE(false && "FIXME: Actually test something");
}

TEST(push_pop,two) {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');
  vc_setFlags(vc,'v');
  vc_setFlags(vc,'s');
  vc_setFlags(vc,'c');
  vc_push(vc);

  Type bv8 = vc_bvType(vc, 8);

  Expr a = vc_varExpr(vc, "a", bv8);
  Expr ct_0 = vc_bvConstExprFromInt(vc, 8, 0);

  Expr a_eq_0 = vc_eqExpr(vc, a, ct_0);

  int query;
  //query = vc_query(vc, a_eq_0);
  //printf("query = %d\n", query);

  Expr a_neq_0 = vc_notExpr(vc,a_eq_0);
  vc_assertFormula(vc,a_eq_0);
  vc_printAsserts(vc);
  vc_push(vc);

  Expr queryexp = vc_eqExpr(vc, a, vc_bvConstExprFromInt(vc, 8, 0));
  vc_printExpr(vc, queryexp);
  
  query = vc_query(vc, queryexp);
  vc_printCounterExample(vc);
  vc_pop(vc);
  vc_pop(vc);

  printf("query = %d\n", query);
  // FIXME: Actually test something
  //ASSERT_TRUE(false && "FIXME: Actually test something");
}

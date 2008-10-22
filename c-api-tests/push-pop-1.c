/* g++ -I$(HOME)/stp/c_interface push-pop.c -L$(HOME)/lib -lstp -o cc*/

#include <stdio.h>
#include "c_interface.h"

int main() {
  VC vc = vc_createValidityChecker();
  vc_setFlags('n');
  vc_setFlags('d');
  vc_setFlags('p');
  vc_setFlags('v');
  vc_setFlags('s');
  vc_setFlags('c');
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
}

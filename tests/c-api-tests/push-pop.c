/* g++ -I$(HOME)/stp/c_interface push-pop.c -L$(HOME)/lib -lstp -o cc*/

#include <stdio.h>
#include "c_interface.h"

int main() {
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
}

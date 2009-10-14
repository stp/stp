/* g++ -I$(HOME)/stp/c_interface multiple-queries.c -L$(HOME)/stp/lib -lstp -o cc*/

#include <stdio.h>
#include "c_interface.h"

int main() {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'c');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');

  Type bv8 = vc_bvType(vc, 8);

  Expr a = vc_varExpr(vc, "a", bv8);
  Expr ct_0 = vc_bvConstExprFromInt(vc, 8, 0);

  Expr a_eq_0 = vc_eqExpr(vc, a, ct_0);

  /* Query 1 */
  vc_push(vc);
  int query = vc_query(vc, a_eq_0);
  vc_pop(vc);
  printf("query = %d\n", query);

  /* Query 2 */
  Expr a_neq_0 = vc_notExpr(vc, a_eq_0);
  vc_push(vc);
  query = vc_query(vc, a_neq_0);
  vc_pop(vc);
  printf("query = %d\n", query);

  vc_Destroy(vc);
}


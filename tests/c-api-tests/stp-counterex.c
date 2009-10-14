//g++ -DEXT_HASH_MAP <this-filename> -I/home/vganesh/stp/c_interface -L/home/vganesh/stp/lib -lstp -o cc

#include <stdio.h>
#include <stdlib.h>
#include "c_interface.h"

int main() {  
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  //vc_setFlags(vc,'p');
  
  Type bv8 = vc_bvType(vc, 8);

  Expr a =  vc_bvCreateMemoryArray(vc, "a");  
 
  Expr index_1 = vc_bvConstExprFromInt(vc, 32, 1);
  Expr a_of_1 = vc_readExpr(vc, a, index_1);  
 
  Expr ct_100 = vc_bvConstExprFromInt(vc, 8, 100);
  Expr a_of_1_eq_100 = vc_eqExpr(vc, a_of_1, ct_100);

  /* Query 1 */  
  vc_push(vc);
  int query = vc_query(vc, a_of_1_eq_100);
  vc_pop(vc);
  printf("query = %d\n", query);

  vc_assertFormula(vc, a_of_1_eq_100);
  
  /* query(false) */
  vc_push(vc);
  query = vc_query(vc, vc_falseExpr(vc));
  vc_pop(vc);
  printf("query = %d\n", query);
  
  if (vc_counterexample_size(vc) == 0) {
    printf("Counterexample size is 0\n");
    exit(1);
  }
      
  a_of_1 = vc_simplify(vc, a_of_1);  
  //vc_printExpr(vc, a_of_1);
  Expr ce = vc_getCounterExample(vc, a_of_1);
  unsigned long long v = getBVUnsigned(ce);
  
  fprintf(stderr, "a[1] = %llu\n", v);

  vc_Destroy(vc);
}

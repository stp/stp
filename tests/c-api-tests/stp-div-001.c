/* g++ -I $HOME/stp/c_interface stp-div-001.c -L $HOME/lib -lstp -o cc */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "c_interface.h"

int main() {  
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  //vc_setFlags(vc,'p');
  
  Type bv8 = vc_bvType(vc, 8);

  Expr a =  vc_bvCreateMemoryArray(vc, "a");  
 
  Expr index_3 = vc_bvConstExprFromInt(vc, 32, 3);

  Expr a_of_0 = vc_readExpr(vc, a, index_3);
  int i;
  for (i = 2; i >= 0; i--)
    a_of_0 = vc_bvConcatExpr(vc,
			     a_of_0,
			     vc_readExpr(vc, a, 
					 vc_bvConstExprFromInt(vc, 32, i)));
  
 
  Expr ct_5 = vc_bvConstExprFromInt(vc, 32, 5);
  Expr a_of_0_div_5 = vc_bvDivExpr(vc, 32, a_of_0, ct_5);
  
  Expr a_of_0_div_5_eq_5 = vc_eqExpr(vc, a_of_0_div_5, ct_5);
  vc_printExpr(vc, a_of_0_div_5_eq_5); printf("\n");
  
  /* Query 1 */
  vc_push(vc);
  int query = vc_query(vc, a_of_0_div_5_eq_5);
  vc_pop(vc);
  printf("query = %d\n", query);

  vc_assertFormula(vc, a_of_0_div_5_eq_5);
  vc_printExpr(vc, a_of_0_div_5_eq_5);
  
  /* query(false) */
  vc_push(vc);
  query = vc_query(vc, vc_falseExpr(vc));
  vc_pop(vc);
  printf("query = %d\n", query);
  assert(!query);
  
  assert(vc_counterexample_size(vc));
  
  int* a_val = (int*) malloc(sizeof *a_val);
  char *p = (char*) a_val;
  //a_of_1 = vc_simplify(vc, a_of_1);  // BUG here
  for (i=0; i<=3; i++) {
    Expr elem = vc_readExpr(vc, a, vc_bvConstExprFromInt(vc, 32, i));
    Expr ce = vc_getCounterExample(vc, elem);
    unsigned long long v = getBVUnsigned(ce);
    fprintf(stderr, "a[%d] = %llu\n", i, v);
    *p = v; p++;
  }
  printf("a = %d\n", *a_val);
  assert((*a_val)/5  == 5);

  vc_Destroy(vc);
}

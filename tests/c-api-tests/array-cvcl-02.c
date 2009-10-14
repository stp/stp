/*
g++ -DEXT_HASH_MAP array-cvcl-02.c -I/home/vganesh/stp/c_interface -L/home/vganesh/stp/lib -lstp -o cc
*/


#include <stdio.h>
#include "c_interface.h"
int main() {  
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');

  Expr cvcl_array = vc_varExpr1(vc, "a",32,32);
  Expr i = vc_varExpr1(vc, "i", 0, 8);   
  Expr i32 = vc_bvConcatExpr(vc,
 			     vc_bvConstExprFromStr(vc,
 						   "000000000000000000000000"),
 			     i); 
  Expr no_underflow = vc_bvLeExpr(vc,
				  vc_bvConstExprFromInt(vc, 32, 0),
				  i32);  
  Expr no_overflow = vc_bvLeExpr(vc,
				 i32,
				 vc_bvConstExprFromInt(vc, 32, 9));  
  Expr in_bounds = vc_andExpr(vc, no_underflow, no_overflow);  
  Expr a_of_i = vc_bvSignExtend(vc,
				vc_readExpr(vc,cvcl_array,i32),
				32);  
  Expr a_of_i_eq_11 = vc_eqExpr(vc, 
				vc_bvConcatExpr(vc,i32,a_of_i),
				vc_bvConstExprFromInt(vc, 64, 11));
 
  vc_assertFormula(vc, in_bounds);
  vc_assertFormula(vc, a_of_i_eq_11);  
  vc_query(vc, vc_falseExpr(vc));

  long long v; 
  Expr pre = vc_bvConstExprFromInt(vc,24,0);
  for(int j=0;j<10;j++) {
    Expr exprj = vc_bvConstExprFromInt(vc,8,j);
    Expr index = vc_bvConcatExpr(vc, pre, exprj);
    index = vc_simplify(vc,index);
    Expr a_of_j = vc_readExpr(vc, cvcl_array, index);
    Expr ce = vc_getCounterExample(vc,a_of_j);    
  }
  vc_Destroy(vc);
  //vc_printCounterExample(vc);
}

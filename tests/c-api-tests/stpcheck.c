//g++ -DEXT_HASH_MAP <this-filename> -I/home/vganesh/stp/c_interface -L/home/vganesh/stp/lib -lstp -o cc
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "c_interface.h"
int main() {  
  	
  	VC vc = vc_createValidityChecker();
	vc_setFlags(vc,'n');
	vc_setFlags(vc,'d');
		
	// 8-bit variable 'x'
	Expr x=vc_varExpr(vc,"x",vc_bvType(vc,8));
	
	// 32 bit constant value 1
	Expr one=vc_bvConstExprFromInt(vc,32,1);

	//24 bit constant value 0
	Expr bit24_zero = vc_bvConstExprFromInt(vc,24,0);
	// 32 bit constant value 0
	Expr bit32_zero = vc_bvConstExprFromInt(vc,32,0);

	// Extending 8-bit variable to 32-bit value
	Expr zero_concat_x=vc_bvConcatExpr(vc,bit24_zero,x);
	Expr xp1 = vc_bvPlusExpr(vc,32,zero_concat_x,one);

	//Insteading of concat operation, I also tried with SignExtend
	//Expr signextend_x=vc_bvSignExtend(vc,x,32);
	//Expr xp1=vc_bvPlusExpr(vc,32,signextend_x,one);
	
	//x+1=0
	Expr eq=vc_eqExpr(vc,xp1,bit32_zero);

	// x+1!=0
	eq=vc_notExpr(vc,eq);	

	vc_query(vc,eq);	
	vc_printCounterExample(vc);	
        return 0;
}

 



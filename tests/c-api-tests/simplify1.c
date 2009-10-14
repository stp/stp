/* g++ -I/home/vganesh/stp/c_interface simplify.c -L/home/vganesh/stp/lib -lstp -g */


#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "c_interface.h"

int main() {
  for(int j=0;j < 3; j++) {
    VC vc = vc_createValidityChecker();
    vc_setFlags(vc,'n');
    vc_setFlags(vc,'d');
    vc_setFlags(vc,'p');
    vc_setFlags(vc,'x');
    
    Type bv8 = vc_bvType(vc, 8);
    Expr a =  vc_bvCreateMemoryArray(vc, "a");
    Expr index_3 = vc_bvConstExprFromLL(vc, 32, 3);

    Expr a_of_0 = vc_readExpr(vc, a, index_3);
    int i;
    for (i = 2; i >= 0; i--)
      a_of_0 = vc_bvConcatExpr(vc,
			       a_of_0,
			       vc_readExpr(vc, a,
					   vc_bvConstExprFromInt(vc, 32, i)));
    Expr cast_32_to_8 = vc_bvExtract(vc, a_of_0, 7, 0);
    Expr cast_8_to_32 = vc_bvSignExtend(vc, cast_32_to_8, 32);
    vc_printExpr(vc, cast_8_to_32);
    cast_8_to_32 = vc_simplify(vc, cast_8_to_32);
    vc_Destroy(vc);
  }
}

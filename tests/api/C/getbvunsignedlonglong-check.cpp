/* g++ -I/home/vganesh/stp/c_interface simplify.c -L/home/vganesh/stp/lib -lstp -g */


#include <gtest/gtest.h>
#include <stdio.h>
#include <stdlib.h>
#include "c_interface.h"

TEST(getbvunsignedlonglong_check,one) {
  for(int j=0;j < 3; j++) {
    VC vc = vc_createValidityChecker();
    vc_setFlags(vc,'n');
    vc_setFlags(vc,'d');
    vc_setFlags(vc,'p');
    vc_setFlags(vc,'x');
    
    Type bv8 = vc_bvType(vc, 8);
    Expr a =  vc_bvCreateMemoryArray(vc, "a");    
    Expr index_3 = vc_bvConstExprFromLL(vc, 64, 0xf0000000effff000LL);
    unsigned long long int print_index = getBVUnsignedLongLong(index_3);
    printf("testing getBVUnsignedLongLong function: %llx \n", print_index);
    printf("\n");
    vc_DeleteExpr(a);
    vc_DeleteExpr(index_3);
    vc_Destroy(vc);
  }
  ASSERT_TRUE(false && "FIXME: Actually test something");
}

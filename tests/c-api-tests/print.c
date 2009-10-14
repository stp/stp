//g++ -I$(HOME)/stp/c_interface print.c -L$(HOME)/stp/lib -lstp -o hex

#include <stdio.h>
#include "c_interface.h"

int main() {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');

  Expr ct_3 = vc_bvConstExprFromStr(vc,
"00000000000000000000000000000011");
  vc_printExpr(vc, ct_3);  printf("\n");

  ct_3 = vc_bvConstExprFromInt(vc, 32, 5);
  vc_printExpr(vc, ct_3);  printf("\n");

  vc_Destroy(vc);
}


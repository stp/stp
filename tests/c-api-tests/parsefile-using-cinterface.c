//g++ -I$(HOME)/stp/c_interface print.c -L$(HOME)/stp/lib -lstp -o hex

#include <stdio.h>
#include "c_interface.h"

int main() {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');

  Expr c = vc_parseExpr(vc,"./t.cvc"); 
  
  vc_printExpr(vc, c);
  vc_DeleteExpr(c);
  printf("\n");
  vc_Destroy(vc);
}


//g++ -I$(HOME)/stp/c_interface print.c -L$(HOME)/stp/lib -lstp -o hex

#include <stdio.h>
#include "c_interface.h"

int main() {
  VC vc = vc_createValidityChecker();
  vc_setFlags('n');
  vc_setFlags('d');
  vc_setFlags('p');

  Expr c = vc_parseExpr(vc,"./t.cvc"); 
  
  vc_printExpr(vc, c);
  printf("\n");
  vc_Destroy(vc);
}


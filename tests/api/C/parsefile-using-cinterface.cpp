//g++ -I$(HOME)/stp/c_interface print.c -L$(HOME)/stp/lib -lstp -o hex

#include <gtest/gtest.h>
#include <stdio.h>
#include "c_interface.h"

TEST(parsefile,one) {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');

  // FIXME: Figure out way to get correct path to file
  Expr c = vc_parseExpr(vc,"./t.cvc"); 
  // FIXME: We shouldn't trigger an exit on failure. Libraries DON'T DO THAT!
  
  vc_printExpr(vc, c);
  vc_DeleteExpr(c);
  printf("\n");
  vc_Destroy(vc);
}


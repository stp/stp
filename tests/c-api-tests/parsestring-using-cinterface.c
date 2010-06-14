#include <stdio.h>
#include "c_interface.h"

int main() {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');
  vc_setFlags(vc,'m');

  Expr q;
  Expr asserts;

  
  const char* s =       "(benchmark fg.smt\n"
			":logic QF_AUFBV\n"
			":extrafuns ((x_32 BitVec[32]))\n"
			":extrafuns ((y32 BitVec[32]))\n"
			":assumption true\n)\n";

  vc_parseMemExpr(vc,s,&q,&asserts); 
  
  vc_printExpr(vc, q);
  vc_printExpr(vc, asserts);
  printf("\n");

  vc_Destroy(vc);
}


/*

Take a .cvc file specified by argv[1] and transform to C code

g++ -I$HOME/stp/c_interface cvc-to-c.cpp -L$HOME/stp/lib -lstp -o cvc-to-c

*/

#include "c_interface.h"
#include <iostream>

using namespace std;

int main(int argc, char** argv) {
  VC vc = vc_createValidityChecker();

  //vc_setFlags(vc,'n');
  //vc_setFlags(vc,'d');
  //vc_setFlags(vc,'p');

  Expr c = vc_parseExpr(vc, argv[1]);

  vc_printExprCCode(vc, c);

  vc_Destroy(vc);
  return 0;
}


#include <stdio.h>
#include "c_interface.h"
#include <iostream>
#include <stdlib.h>

int main() {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'m');

  srand(time(NULL));
  Expr c = vc_parseExpr(vc,"./example.smt"); 
  
  for (int i=0; i < 10; i++)
  	{
  		int time = rand() % 7000;
  		std::cout << "Timeout : " << time << " : result " ; 
	  	std::cout << vc_query_with_timeout(vc,vc_falseExpr(vc),time) << std::endl; 
  	}
  vc_DeleteExpr(c);
  vc_Destroy(vc);
  return 0;
}


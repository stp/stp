#include <gtest/gtest.h>
#include <stdio.h>
#include "c_interface.h"
#include <iostream>
#include <stdlib.h>

TEST(timeout,one) {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'m');

  srand(time(NULL)); // FIXME: We should not be introducing non-deterministic behaviour in a test case!

  // SMT_FILE is a macro that expands to a file path
  Expr c = vc_parseExpr(vc, SMT_FILE);
  
  for (int i=0; i < 10; i++)
  	{
  		int time = rand() % 7000; // FIXME: non-determinsitc behaviour in a test case is BAD!!!
  		std::cout << "Timeout : " << time << " : result " ; 
	  	std::cout << vc_query_with_timeout(vc,vc_falseExpr(vc),time) << std::endl; 
  	}
  vc_DeleteExpr(c);
  vc_Destroy(vc);
  // FIXME: Actually test something
  //ASSERT_TRUE(false && "FIXME: Actually test something");
}


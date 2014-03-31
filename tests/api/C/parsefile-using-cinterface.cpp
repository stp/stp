#include <fstream>
#include <gtest/gtest.h>
#include <stdio.h>
#include "c_interface.h"

TEST(parsefile,CVC) {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');

  // CVC_FILE is a macro that expands to a file path
  Expr c = vc_parseExpr(vc, CVC_FILE);
  // FIXME: We shouldn't trigger an exit on failure. Libraries DON'T DO THAT!
  
  vc_printExpr(vc, c);
  vc_DeleteExpr(c);
  printf("\n");
  vc_Destroy(vc);
  // FIXME: Actually test something
  //ASSERT_TRUE(false && "FIXME: We should actually test something!");
}

TEST(parsefile,missing_file) {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');

  const char* nonExistantFile="./iShOuLdNoTExiSt.cvc";
  std::ifstream file(nonExistantFile, std::ifstream::in);
  ASSERT_FALSE( file.good() ); // Check the file does not exist

  Expr c = vc_parseExpr(vc, nonExistantFile);
  // FIXME: We shouldn't trigger an exit on failure. Libraries DON'T DO THAT!
  
  vc_printExpr(vc, c);
  vc_DeleteExpr(c);
  printf("\n");
  vc_Destroy(vc);
  // FIXME: Actually test something
  //ASSERT_TRUE(false && "FIXME: We should actually test something!");
}

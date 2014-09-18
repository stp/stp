#include <fstream>
#include <gtest/gtest.h>
#include <stdio.h>
#include <string>
#include "stp/c_interface.h"

static unsigned int errorCount = 0;
static std::string errorMsg;

TEST(parsefile,CVC) {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');

  // CVC_FILE is a macro that expands to a file path
  Expr c = vc_parseExpr(vc, CVC_FILE);
  
  vc_printExpr(vc, c);
  vc_DeleteExpr(c);
  printf("\n");
  vc_Destroy(vc);
  ASSERT_EQ(errorCount, 0);
}

void errorHandler(const char* err_msg)
{
   errorMsg = std::string(err_msg);
   ++errorCount;
}

TEST(parsefile,missing_file) {
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');
  vc_registerErrorHandler(errorHandler);

  const char* nonExistantFile="./iShOuLdNoTExiSt.cvc";
  std::ifstream file(nonExistantFile, std::ifstream::in);
  ASSERT_FALSE( file.good() ); // Check the file does not exist

  Expr c = vc_parseExpr(vc, nonExistantFile);
  ASSERT_EQ( c, (void*) 0);
  ASSERT_EQ(errorCount, 1);
  ASSERT_STREQ("Cannot open file", errorMsg.c_str());
  
  vc_Destroy(vc);
}

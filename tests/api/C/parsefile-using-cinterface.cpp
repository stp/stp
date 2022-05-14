/***********
AUTHORS:  Michael Katelman, Vijay Ganesh, Trevor Hansen, Dan Liew

BEGIN DATE: Oct, 2008

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
**********************/

#include "stp/c_interface.h"
#include <fstream>
#include <gtest/gtest.h>
#include <stdio.h>
#include <string>

static unsigned int errorCount = 0;
static std::string errorMsg;

TEST(parsefile, CVC)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  vc_setFlags(vc, 'p');

  // CVC_FILE is a macro that expands to a file path
  Expr c = vc_parseExpr(vc, CVC_FILE);

  vc_printExpr(vc, c);
  vc_DeleteExpr(c);
  printf("\n");
  vc_Destroy(vc);
  ASSERT_EQ(errorCount, 0u);
}

void errorHandler(const char* err_msg)
{
  errorMsg = std::string(err_msg);
  ++errorCount;
}

//Disabling test because error handling is horrible and WILL break
//a running system
/*TEST(parsefile, missing_file)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'n');
  vc_setFlags(vc, 'd');
  vc_setFlags(vc, 'p');
  vc_registerErrorHandler(errorHandler);

  const char* nonExistantFile = "./iShOuLdNoTExiSt.cvc";
  std::ifstream file(nonExistantFile, std::ifstream::in);
  ASSERT_FALSE(file.good()); // Check the file does not exist

  Expr c = vc_parseExpr(vc, nonExistantFile);
  ASSERT_EQ(c, (void*)0);
  ASSERT_EQ(errorCount, 1);
  ASSERT_STREQ("Cannot open file", errorMsg.c_str());

  vc_Destroy(vc);
}*/

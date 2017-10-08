/***********
AUTHORS:  Trevor Hansen, Dan Liew

BEGIN DATE: Jan, 2012

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
#include <gtest/gtest.h>
#include <iostream>
#include <stdio.h>
#include <stdlib.h>

TEST(timeout, one)
{
  VC vc = vc_createValidityChecker();
  vc_setFlags(vc, 'm');

  srand(time(NULL)); // FIXME: We should not be introducing non-deterministic
                     // behaviour in a test case!

  // SMT_FILE is a macro that expands to a file path
  Expr c = vc_parseExpr(vc, SMT_FILE);

  for (int i = 0; i < 10; i++)
  {
    int time =
        rand() %
        7000; // FIXME: non-determinsitc behaviour in a test case is BAD!!!
    std::cout << "Timeout : " << time << " : result " << std::flush;
    std::cout << vc_query_with_timeout(vc, vc_falseExpr(vc), time) << std::endl;
  }
  vc_DeleteExpr(c);
  vc_Destroy(vc);
  // FIXME: Actually test something
  // ASSERT_TRUE(false && "FIXME: Actually test something");
}

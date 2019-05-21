/***********
AUTHORS:  Trevor Hansen, Dan Liew, Andrew V. Jones

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

void test_timeout(bool test_with_time, uint32_t max_value, bool use_cms)
{
  srand(time(NULL)); // FIXME: We should not be introducing non-deterministic
                     // behaviour in a test case!

  for (int i = 0; i < 10; i++)
  {
    // need to create VCs for every loop, otherwise the timeouts are not used
    // correctly
    VC vc = vc_createValidityChecker();
    vc_setFlags(vc, 'm');
    if (use_cms)
    {
      vc_useCryptominisat(vc);
    }
    else
    {
      vc_useMinisat(vc);
    }

    // SMT_FILE is a macro that expands to a file path
    Expr c = vc_parseExpr(vc, SMT_FILE);

    int limit = // time is in seconds
        rand() %
        max_value; // FIXME: non-determinsitc behaviour in a test case is BAD!!!
    std::string timeout_type;
    uint32_t max_conflicts = -1;
    uint32_t max_time = -1;
    if (test_with_time)
    {
      timeout_type = "Time ";
      limit = std::max(limit, 1); // we do not want a 0 timeout
      max_time = limit;
    }
    else
    {
      timeout_type = "Conflicts";
      max_conflicts = limit;
    }
    std::cout << timeout_type << " : " << limit << " : result " << std::flush;

    // returns 3 on timeout
    int query = vc_query_with_timeout(vc, vc_falseExpr(vc), max_conflicts, max_time);
    ASSERT_TRUE(query == 3);

    std::cout << query << std::endl;

    // FIXME: Actually test something
    // ASSERT_TRUE(false && "FIXME: Actually test something");

    vc_DeleteExpr(c);
    vc_Destroy(vc);
  }
}

void test_conflicts(bool use_cms)
{
  bool is_time_timeout = false;
  uint32_t max_value = 500;
  test_timeout(is_time_timeout, max_value, use_cms);
}

#ifdef USE_CRYPTOMINISAT
TEST(timeout_conflicts_cms, one)
{
  bool use_cms = true;
  test_conflicts(use_cms);
}
#endif

TEST(timeout_conflicts_minisat, one)
{
  bool use_cms = false;
  test_conflicts(use_cms);
}

#ifdef USE_CRYPTOMINISAT
/*
 * Timeout tests only with with CMS
 */
TEST(timeout_time, one)
{
  /*
   * this test should probably test the instance without a timeout and then
   * choose a value lower than it for the next time
   */
  bool is_time_timeout = true;
  uint32_t max_value = 3; // purposefully very low to ensure we hit a timeout
  bool use_cms = true;
  test_timeout(is_time_timeout, max_value, use_cms);
}
#endif

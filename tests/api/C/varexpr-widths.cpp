/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
 *
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

#include <cstdio>

// A zero-width bit-vector is not a sort, and the sort layer says so with an
// assertion in a header -- which means an abort on an asserting build and a
// zero-width value carried onward on a release one, where the legacy width
// checks read it as a Boolean.
//
// The parser was closed against that, and vc_bvType has refused a zero width
// by the other route for years. This entrance was not: an array-valued
// variable takes its element width here, and nothing looked at it.
TEST(VarExprWidths, ArrayElementWidthMustBePositive)
{
  ::testing::FLAGS_gtest_death_test_style = "threadsafe";

  // A death test because the refusal is a FatalError, like every other refusal
  // in c_interface.cpp: a NULL return would be a new contract for one function
  // and a fault later on for any caller that did not read the header.
  EXPECT_DEATH(
      {
        VC vc = vc_createValidityChecker();
        (void)vc_varExpr1(vc, "bad", 8, 0);
      },
      "number of bits in an array's elements must be a positive integer");
}

namespace
{
void recordError(const char* message)
{
  std::fprintf(stderr, "HANDLER SAW: %s\n", message);
}
} // namespace

// The route the header advertises: a registered handler is told, and is told
// the whole message, prefix and function name included, exactly as the other
// refusals in c_interface.cpp report themselves. The handler runs before the
// abort, so this is still a death test.
TEST(VarExprWidths, TheRefusalReachesARegisteredErrorHandler)
{
  ::testing::FLAGS_gtest_death_test_style = "threadsafe";

  EXPECT_DEATH(
      {
        vc_registerErrorHandler(recordError);
        VC vc = vc_createValidityChecker();
        (void)vc_varExpr1(vc, "bad", 8, 0);
      },
      "HANDLER SAW: CInterface: vc_varExpr1: number of bits in an array's "
      "elements must be a positive integer");
}

// Its own test, so that a regression in the guard above cannot take these with
// it: the widths either side of the refused one still build what they always
// built.
TEST(VarExprWidths, NeighbouringWidthsStillBuild)
{
  VC vc = vc_createValidityChecker();

  // A real array, a plain bit-vector, and the zero/zero spelling that means
  // Bool rather than a zero-width anything.
  EXPECT_NE(nullptr, vc_varExpr1(vc, "arr", 8, 8));
  EXPECT_NE(nullptr, vc_varExpr1(vc, "bv", 0, 8));
  EXPECT_NE(nullptr, vc_varExpr1(vc, "b", 0, 0));

  vc_Destroy(vc);
}

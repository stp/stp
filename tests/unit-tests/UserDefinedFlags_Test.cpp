/***********
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

#include "stp/STPManager/UserDefinedFlags.h"
#include <gtest/gtest.h>

// The sharing-aware flattening stack is on by default.
TEST(UserDefinedFlags_Test, flattening_stack_on_by_default)
{
  stp::UserDefinedFlags uf;
  EXPECT_TRUE(uf.enable_flatten);
  EXPECT_TRUE(uf.enable_common_subsum);
  EXPECT_TRUE(uf.enable_pair_extract);
}

// --disable-simplifications owns the whole stack: the bulk setter must
// switch all of it off.
TEST(UserDefinedFlags_Test, disable_simplifications_clears_flattening_stack)
{
  stp::UserDefinedFlags uf;
  uf.disableSimplifications();
  EXPECT_FALSE(uf.enable_flatten);
  EXPECT_FALSE(uf.enable_common_subsum);
  EXPECT_FALSE(uf.enable_pair_extract);
}

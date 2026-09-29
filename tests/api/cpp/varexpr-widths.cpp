/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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
********************************************************************/

// varexpr-widths.cpp -- a zero-width bit-vector is not a sort, whatever
// the route to it.
//
// In 2.x the sort layer said so with an assertion in a header -- an abort on
// an asserting build and a zero-width value carried onward on a release one,
// where the legacy width checks read it as a Boolean. The parser and
// vc_bvType refused a zero width by other routes; vc_varExpr1, which takes an
// array-valued variable's element width, did not, and its refusal became a
// FatalError, so the 2.x cases were death tests. In 3.x every width goes
// through mk_bv_sort, which refuses zero with a recoverable INVALID_ARGUMENT
// (the manager goes on), and the zero/zero spelling of Bool is mk_bool_sort().

#include "api_common.hpp"

#include <optional>
#include <string>

using namespace stp;

TEST(VarExprWidths, ArrayElementWidthMustBePositive)
{
  TermManager tm;

  // 3.x: refused where the element sort is made, recoverably -- no abort.
  const auto e = API_ERROR_OF(
      tm.declare("bad", tm.mk_array_sort(tm.mk_bv_sort(8), tm.mk_bv_sort(0))));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::INVALID_ARGUMENT);
  EXPECT_NE(std::string(e->what()).find("a bit-vector sort needs a positive width"),
            std::string::npos)
      << e->what();

  // Nothing was declared, and the manager is untouched: the name is still
  // free for a well-formed array.
  EXPECT_FALSE(tm.symbol("bad").has_value());
  const Term good = tm.declare("bad", tm.mk_array_sort(tm.mk_bv_sort(8), tm.mk_bv_sort(8)));
  EXPECT_TRUE(good.sort().is_array());
}

// The route the 2.x header advertised: a registered handler was told the
// whole message, prefix and function name included, before the abort. 3.x
// has no process-global handler: the refusal reaches the caller as the
// exception, which carries the function that refused, the argument and the
// reason.
TEST(VarExprWidths, TheRefusalReachesARegisteredErrorHandler)
{
  TermManager tm;

  const auto e = API_ERROR_OF(tm.mk_bv_sort(0));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::INVALID_ARGUMENT);
  EXPECT_TRUE(e->recoverable());
  EXPECT_EQ(e->function(), "TermManager::mk_bv_sort");
  EXPECT_EQ(e->argument_index(), std::optional<int>(0));
  EXPECT_EQ(std::string(e->what()),
            "invalid call to 'TermManager::mk_bv_sort': a bit-vector sort needs a positive "
            "width (argument 0) [INVALID_ARGUMENT]");
}

// Its own test, so that a regression in the guard above cannot take these with
// it: the widths either side of the refused one still build what they always
// built.
TEST(VarExprWidths, NeighbouringWidthsStillBuild)
{
  TermManager tm;

  // A real array, a plain bit-vector, and Bool (which 2.x spelled as the
  // zero/zero widths rather than a zero-width anything).
  const Term arr = tm.declare("arr", tm.mk_array_sort(tm.mk_bv_sort(8), tm.mk_bv_sort(8)));
  const Term bv = tm.declare("bv", tm.mk_bv_sort(8));
  const Term b = tm.declare("b", tm.mk_bool_sort());

  ASSERT_TRUE(arr.sort().is_array());
  EXPECT_EQ(arr.sort().array_index().bv_size(), 8u);
  EXPECT_EQ(arr.sort().array_element().bv_size(), 8u);
  ASSERT_TRUE(bv.sort().is_bv());
  EXPECT_EQ(bv.sort().bv_size(), 8u);
  EXPECT_TRUE(b.sort().is_bool());
}

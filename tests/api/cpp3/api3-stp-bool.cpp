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

// api3-stp-bool.cpp -- the Boolean sort (2.x's vc_boolType): made by the
// manager, one per manager, what it reports about itself, and a symbol of it
// deciding as a Boolean.

#include "api3_common.hpp"

using namespace stp;

namespace
{

TEST(stp_bool, one)
{
  TermManager tm;
  const Sort b = tm.mk_bool_sort();
  ASSERT_FALSE(b.is_null());
  EXPECT_TRUE(b.is_bool());
  EXPECT_EQ(b.kind(), SortKind::BOOL);
  EXPECT_FALSE(b.is_bv());
  EXPECT_EQ(b.str(), "Bool");
  EXPECT_TRUE(b == tm.mk_bool_sort());
  EXPECT_TRUE(tm.mk_true().sort() == b);
  const Term p = tm.declare("p", b);
  EXPECT_TRUE(p.sort() == b);
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, b.bv_size()); // not a bit-vector

  // and a symbol of it decides as one: p or not p holds, p alone does not
  Solver s(tm);
  EXPECT_TRUE(s.entails(p || !p).is_valid());
  EXPECT_TRUE(s.entails(p).is_invalid());
}

} // namespace

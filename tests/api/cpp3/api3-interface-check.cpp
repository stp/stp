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

// api3-interface-check.cpp -- construction-time folding and simplify(): a
// simplifying manager builds true AND false as the value false, and
// simplify() keeps it so. (2.x read the kind with getExprKind, whose internal
// FALSE kind is the public VALUE kind holding false.) A non-simplifying
// manager keeps the AND as built, and simplify() folds it.

#include "api3_common.hpp"

using namespace stp;

namespace
{

TEST(interface_check, ONE)
{
  TermManager tm;
  const Term b1 = tm.mk_true();
  const Term b2 = tm.mk_false();
  const Term andExpr = b1 && b2;

  ASSERT_EQ(andExpr.kind(), Kind::VALUE);
  EXPECT_FALSE(andExpr.to_bool());

  const Term simplifiedExpr = tm.simplify(andExpr);

  ASSERT_EQ(simplifiedExpr.kind(), Kind::VALUE);
  EXPECT_FALSE(simplifiedExpr.to_bool());
  EXPECT_TRUE(simplifiedExpr.same_as(tm.mk_false()));

  TermManager raw = api3::raw_manager();
  const Term rawAnd = raw.mk_true() && raw.mk_false();
  EXPECT_EQ(rawAnd.kind(), Kind::AND);
  const Term rawSimplified = raw.simplify(rawAnd);
  ASSERT_EQ(rawSimplified.kind(), Kind::VALUE);
  EXPECT_FALSE(rawSimplified.to_bool());
}

} // namespace

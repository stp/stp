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

// api3-counterexample.cpp -- reading the model of a satisfiable check term by
// term (2.x's vc_getCounterExample is Solver::value): a symbol, a sum over
// it, and Boolean terms, constant ones included, each read as a value of its
// sort.

#include "api3_common.hpp"

using namespace stp;

namespace
{

TEST(counterexample, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // every 2.x checker had 'd' on
  const Term falseExpr = tm.mk_false();

  const Term A = tm.declare("A", tm.mk_bv_sort(32));
  const Term c42 = tm.mk_bv(32, 42);
  const Term eq = A == c42;

  s.add(eq);
  ASSERT_TRUE(s.check_sat().is_sat()); // 2.x: vc_query(false) == 0

  Term ce = s.value(A);
  ASSERT_TRUE(ce.is_value());
  ASSERT_EQ(42, ce.to_int64());

  const Term Aplus42 = bvadd(A, c42);
  ce = s.value(Aplus42);
  ASSERT_EQ(84, ce.to_int64());

  ce = s.value(falseExpr);
  ASSERT_TRUE(ce.is_value());
  ASSERT_FALSE(ce.to_bool());

  const Term trueExpr = !falseExpr;
  ce = s.value(trueExpr);
  ASSERT_TRUE(ce.to_bool());

  const Term eq2 = Aplus42 == tm.mk_bv(32, 84);
  ce = s.value(eq2);
  ASSERT_TRUE(ce.to_bool());
}

} // namespace

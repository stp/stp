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

// api3-sbvdiv.cpp -- signed division by a positive symbol: b >s 0 and
// a <=s INT_MAX /s b are satisfiable together, and the checked model
// satisfies both.

#include "api3_common.hpp"

using namespace stp;

namespace
{

TEST(sbdiv, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // 2.x flag 'd'

  const Sort int_type = tm.mk_bv_sort(32);
  const Term zero = tm.mk_bv(32, 0);
  const Term int_max = tm.mk_bv(32, 0x7fffffff);
  const Term a = tm.declare("a", int_type);
  const Term b = tm.declare("b", int_type);
  s.add(bvsgt(b, zero));
  s.add(bvsle(a, bvsdiv(int_max, b)));
  ASSERT_TRUE(s.check_sat().is_sat()); // 2.x: vc_query(false) == 0

  const Model m = s.model();
  EXPECT_TRUE(m.bool_value(bvsgt(b, zero)));
  EXPECT_TRUE(m.bool_value(bvsle(a, bvsdiv(int_max, b))));
}

} // namespace

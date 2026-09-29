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

// failing_solvermap.cpp -- the regression of issue #188
// (https://github.com/stp/stp/issues/188): two satisfiability checks inside
// one push, the second after a further assertion over the same sum A + B.
// (2.x asked whether false was entailed, vc_query(false); the 3.x spelling
// of that question is check_sat().)

#include "api_common.hpp"

using namespace stp;

namespace
{

TEST(failing_solvermap, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // every 2.x checker had 'd' on

  const Term A = tm.declare("A", tm.mk_bv_sort(32));
  const Term B = tm.declare("B", tm.mk_bv_sort(32));

  s.push();

  const Term AplusB = bvadd(A, B);
  const Term AplusBplus42 = bvadd(AplusB, tm.mk_bv(32, 42));

  s.add(bvugt(AplusB, tm.mk_bv(32, 100)));
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.model().bool_value(bvugt(AplusB, tm.mk_bv(32, 100))));
  s.add(bvugt(AplusBplus42, tm.mk_bv(32, 5)));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_TRUE(m.bool_value(bvugt(AplusB, tm.mk_bv(32, 100))));
  EXPECT_TRUE(m.bool_value(bvugt(AplusBplus42, tm.mk_bv(32, 5))));
}

} // namespace

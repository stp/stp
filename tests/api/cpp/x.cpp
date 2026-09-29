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

// x.cpp -- a four-conjunct query mixing unsigned and signed comparisons
// with a multiplication is not entailed. (2.x released every handle with
// vc_DeleteExpr afterwards; terms are values here, released by scope.)

#include "api_common.hpp"

#include <vector>

using namespace stp;

namespace
{

TEST(x, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // 2.x flag 'd'

  const Term nresp1 = tm.declare("nresp1", tm.mk_bv_sort(32));
  const Term packet_get_int0 = tm.declare("packet_get_int0", tm.mk_bv_sort(32));
  const Term sz = tm.declare("sz", tm.mk_bv_sort(32));

  const Term d0 = bvmul(nresp1, tm.mk_bv(32, 4));
  const Term d1 = bvsge(sz, nresp1);
  const Term d2 = bvslt(sz, tm.mk_bv(32, 0));
  const std::vector<Term> exprs = {
      // nresp1 == packet_get_int0
      nresp1 == packet_get_int0,

      // nresp1 > 0
      bvugt(nresp1, tm.mk_bv(32, 0)),

      // sz == nresp1 * 4
      sz == d0,

      // sz > nresp1 || sz < 0
      d1 || d2,
  };

  const Term res = and_(exprs);
  ASSERT_TRUE(s.entails(res).is_invalid());
  EXPECT_FALSE(s.model().bool_value(res));
}

} // namespace

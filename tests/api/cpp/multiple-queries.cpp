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

// multiple-queries.cpp -- a query and its negation, each in its own
// push/pop on one solver: neither a = 0 nor a != 0 is entailed.

#include "api_common.hpp"

using namespace stp;

namespace
{

TEST(multiple_queries, one)
{
  TermManager tm;
  Solver s(tm);
  // 2.x flags 'c' (build a counterexample) and 'd' (build and check it)
  s.options().set_bool(Option::PRODUCE_MODELS, true);
  s.options().set_bool(Option::CHECK_SANITY, true);

  const Sort bv8 = tm.mk_bv_sort(8);

  const Term a = tm.declare("a", bv8);
  const Term ct_0 = tm.mk_bv(8, 0);
  const Term a_eq_0 = a == ct_0;

  /* Query 1 */
  s.push();
  Entailment query = s.entails(a_eq_0);
  ASSERT_TRUE(query.is_invalid());
  EXPECT_NE(s.model().uint64_value(a), 0u);
  s.pop();

  /* Query 2 */
  const Term a_neq_0 = !a_eq_0;
  s.push();
  query = s.entails(a_neq_0);
  s.pop();
  ASSERT_TRUE(query.is_invalid());
  EXPECT_EQ(s.model().uint64_value(a), 0u); // the model outlives the pop
}

} // namespace

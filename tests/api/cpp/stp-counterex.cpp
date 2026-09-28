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

// stp-counterex.cpp -- a cell of a memory array (Array BV32 BV8) read
// from the model of a check made inside a push that was popped at once: the
// model outlives the pop, and the cell, simplified after the check, reads as
// the value it was asserted to have.

#include "api_common.hpp"

#include <cstdint>
#include <iostream>

using namespace stp;

namespace
{

TEST(stp_counterex, one)
{
  TermManager tm;
  Solver s(tm);
  // 2.x flags 'n' (print the verdict, below) and 'd'
  s.options().set_bool(Option::CHECK_SANITY, true);

  const Term a = tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(32), tm.mk_bv_sort(8)));

  const Term index_1 = tm.mk_bv(32, 1);
  Term a_of_1 = a[index_1];

  const Term ct_100 = tm.mk_bv(8, 100);
  const Term a_of_1_eq_100 = a_of_1 == ct_100;

  /* Query 1 */
  s.push();
  const Entailment query = s.entails(a_of_1_eq_100);
  s.pop();
  std::cout << "query = " << query << "\n";
  EXPECT_TRUE(query.is_invalid());

  s.add(a_of_1_eq_100);

  /* the assertions' satisfiability (2.x: query(false)) */
  s.push();
  const Result r = s.check_sat();
  s.pop();
  std::cout << "query = " << r << "\n";
  ASSERT_TRUE(r.is_sat());

  const Model m = s.model();
  ASSERT_FALSE(m.symbols().empty());

  a_of_1 = tm.simplify(a_of_1);
  const std::uint64_t v = m.uint64_value(a_of_1);

  std::cerr << "a[1] = " << v << "\n";
  EXPECT_EQ(v, 100u);
}

} // namespace

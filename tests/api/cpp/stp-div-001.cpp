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

// stp-div-001.cpp -- a 32-bit word assembled from four bytes of a
// memory array (Array BV32 BV8, 2.x's vc_bvCreateMemoryArray) and divided by
// 5. Each check runs inside a push that is popped at once; the model of the
// last one outlives the pop, and its four bytes form a word whose quotient
// is 5.

#include "api_common.hpp"

#include <cstdint>
#include <iostream>

using namespace stp;

namespace
{

TEST(stp_div, one)
{
  TermManager tm;
  Solver s(tm);
  // 2.x flags 'n' (print the verdict, below) and 'd'
  s.options().set_bool(Option::CHECK_SANITY, true);

  const Term a = tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(32), tm.mk_bv_sort(8)));

  const Term index_3 = tm.mk_bv(32, 3);

  Term a_of_0 = a[index_3];
  for (int i = 2; i >= 0; i--)
    a_of_0 = concat(a_of_0, a[tm.mk_bv(32, i)]);

  const Term ct_5 = tm.mk_bv(32, 5);
  const Term a_of_0_div_5 = bvudiv(a_of_0, ct_5);

  const Term a_of_0_div_5_eq_5 = a_of_0_div_5 == ct_5;
  std::cout << a_of_0_div_5_eq_5.to_string(Format::CVC) << "\n";

  /* Query 1 */
  s.push();
  const Entailment query = s.entails(a_of_0_div_5_eq_5);
  s.pop();
  std::cout << "query = " << query << "\n";
  EXPECT_TRUE(query.is_invalid());

  s.add(a_of_0_div_5_eq_5);
  std::cout << a_of_0_div_5_eq_5.to_string(Format::CVC) << "\n";

  /* the assertions' satisfiability (2.x: query(false)) */
  s.push();
  const Result r = s.check_sat();
  s.pop();
  std::cout << "query = " << r << "\n";
  ASSERT_TRUE(r.is_sat());

  const Model m = s.model(); // the model survives the pop
  ASSERT_FALSE(m.symbols().empty());

  std::uint32_t a_val = 0; // the bytes a[0..3], least significant first
  for (int i = 0; i <= 3; i++)
  {
    const Term elem = a[tm.mk_bv(32, i)];
    const std::uint64_t v = m.uint64_value(elem);
    std::cerr << "a[" << i << "] = " << v << "\n";
    a_val |= static_cast<std::uint32_t>(v) << (8 * i);
  }
  std::cout << "a = " << a_val << "\n";
  EXPECT_EQ(a_val / 5, 5u);
  EXPECT_EQ(m.uint64_value(a_of_0), a_val);
}

} // namespace

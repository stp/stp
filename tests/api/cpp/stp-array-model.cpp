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

// stp-array-model.cpp -- the model of a memory array (Array BV32 BV8)
// with two constrained cells: the array's value lists explicit entries
// (2.x's vc_getCounterExampleArray), each an index and an element value,
// among them a[1] = 42 and a[2] = 77.

#include "api_common.hpp"

#include <cstdint>
#include <iostream>

using namespace stp;

namespace
{

TEST(stp_array_model, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // every 2.x checker had 'd' on

  const Term a = tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(32), tm.mk_bv_sort(8)));

  const Term index_1 = tm.mk_bv(32, 1);
  const Term a_of_1 = a[index_1];

  const Term index_2 = tm.mk_bv(32, 2);
  const Term a_of_2 = a[index_2];

  const Term ct_42 = tm.mk_bv(8, 42);
  const Term a_of_1_eq_42 = a_of_1 == ct_42;

  const Term ct_77 = tm.mk_bv(8, 77);
  const Term a_of_2_eq_77 = a_of_2 == ct_77;

  s.add(a_of_1_eq_42);
  s.add(a_of_2_eq_77);

  /* the assertions' satisfiability (2.x: query(false), which should be invalid) */
  ASSERT_TRUE(s.check_sat().is_sat());

  const Model m = s.model();
  ASSERT_FALSE(m.symbols().empty());

  const ArrayValue value = m.array_value(a);

  ASSERT_NE(value.size(), 0u); // No array entries

  for (const ArrayValue::Entry& entry : value.entries())
  {
    ASSERT_TRUE(entry.index.is_value());
    ASSERT_TRUE(entry.element.is_value());
    const std::uint64_t i = entry.index.to_uint64();
    const std::uint64_t v = entry.element.to_uint64();

    std::cerr << "a[" << i << "] = " << v << "\n";
  }
  EXPECT_EQ(value.at(index_1).to_uint64(), 42u);
  EXPECT_EQ(value.at(index_2).to_uint64(), 77u);
}

} // namespace

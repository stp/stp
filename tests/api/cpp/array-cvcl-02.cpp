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

// array-cvcl-02.cpp -- an array read at a bounded, zero-extended 8-bit
// index (0 <= i <= 9), concatenated with the index and compared with the
// 64-bit constant 11, which forces i = 0 and a[0] = 11; then the model is
// read at each of the ten cells the bound allows, through indices that are
// simplified first. The 2.x suite built its symbols with vc_varExpr1(name,
// index width, value width): an array for a positive index width, a
// bit-vector for index width 0.

#include "api_common.hpp"

#include <iostream>

using namespace stp;

namespace
{

TEST(array_cvcl02, one)
{
  TermManager tm;
  Solver s(tm);
  // 2.x flags 'n' (print the verdict), 'd' and 'p' (print the counterexample)
  s.options().set_bool(Option::CHECK_SANITY, true);

  const Term cvcl_array =
      tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(32), tm.mk_bv_sort(32)));
  const Term i = tm.declare("i", tm.mk_bv_sort(8));
  const Term i32 = concat(tm.mk_bv(24, "000000000000000000000000", 2), i);
  const Term no_underflow = bvule(tm.mk_bv(32, 0), i32);
  const Term no_overflow = bvule(i32, tm.mk_bv(32, 9));
  const Term in_bounds = no_underflow && no_overflow;
  // 2.x's vc_bvSignExtend(e, 32) of a 32-bit e built the full-width extract
  const Term a_of_i = extract(31, 0, cvcl_array[i32]);
  const Term a_of_i_eq_11 = concat(i32, a_of_i) == tm.mk_bv(64, 11);

  s.add(in_bounds);
  s.add(a_of_i_eq_11);
  const Result r = s.check_sat(); // 2.x: vc_query(false) == 0
  std::cout << r << "\n";
  ASSERT_TRUE(r.is_sat());
  const Model m = s.model();
  std::cout << m.to_smt2();
  EXPECT_EQ(m.uint64_value(i), 0u);

  const Term pre = tm.mk_bv(24, 0);
  for (unsigned j = 0; j < 10; j++)
  {
    const Term exprj = tm.mk_bv(8, j);
    Term index = concat(pre, exprj);
    index = tm.simplify(index);
    const Term a_of_j = cvcl_array[index];
    const Term value = m.value(a_of_j);
    ASSERT_TRUE(value.is_value());
    ASSERT_EQ(value.sort().bv_size(), 32u);
    if (j == 0)
    {
      EXPECT_EQ(value.to_uint64(), 11u);
    }
  }
}

} // namespace

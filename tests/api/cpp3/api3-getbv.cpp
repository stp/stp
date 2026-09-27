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

// api3-getbv.cpp -- bit-vector constants read back exactly: every value
// 2^k - 1 at 64 bits and at 32 bits, each built in a fresh manager and solver
// (2.x: a fresh validity checker) that also declares a memory array. 2.x
// allowed deleting such a constant before destroying its checker; here a term
// outlives its manager's handle and the solver, since destruction order is
// free.

#include "api3_common.hpp"

#include <cstdint>

using namespace stp;

namespace
{

TEST(getbv, INT64)
{
  ASSERT_EQ(64ul, sizeof(uint64_t) * 8);

  for (uint64_t j = 1; j < UINT64_MAX; j |= (j << 1))
  {
    Term index_3;
    {
      TermManager tm;
      Solver s(tm);
      // 2.x flags 'n', 'd' and 'p': 'd' is check-sanity; 'n' and 'p' printed
      // a check's verdict and counterexample, and this suite runs no check
      s.options().set_bool(Option::CHECK_SANITY, true);

      const Sort bv8 = tm.mk_bv_sort(8);
      ASSERT_FALSE(bv8.is_null());

      const Term a = tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(32), bv8));
      ASSERT_FALSE(a.is_null());
      index_3 = tm.mk_bv(64, j);
      ASSERT_FALSE(index_3.is_null());

      const uint64_t print_index = index_3.to_uint64();
      ASSERT_EQ(print_index, j);
    }
    // the constant outlives the manager handle and the solver it came from
    EXPECT_EQ(index_3.to_uint64(), j);
  }
}

TEST(getbv, INT32)
{
  ASSERT_EQ(32ul, sizeof(int32_t) * 8);

  for (uint32_t j = 1; j < UINT32_MAX; j |= (j << 1))
  {
    Term index_3;
    {
      TermManager tm;
      Solver s(tm);
      s.options().set_bool(Option::CHECK_SANITY, true); // 2.x flags 'n', 'd', 'p'

      const Sort bv8 = tm.mk_bv_sort(8);
      ASSERT_FALSE(bv8.is_null());

      const Term a = tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(32), bv8));
      ASSERT_FALSE(a.is_null());

      index_3 = tm.mk_bv(32, j);
      ASSERT_FALSE(index_3.is_null());

      const uint32_t print_index = static_cast<uint32_t>(index_3.to_uint64());
      ASSERT_EQ(print_index, j);
    }
    // the constant outlives the manager handle and the solver it came from
    EXPECT_EQ(index_3.to_uint64(), j);
    EXPECT_EQ(index_3.sort().bv_size(), 32u);
  }
}

} // namespace

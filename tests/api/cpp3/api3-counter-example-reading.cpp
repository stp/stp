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

// api3-counter-example-reading.cpp -- reading a model: the values of A, B
// and of the term A + B + 42 agree with each other. 2.x had two readers, one
// term at a time (vc_getCounterExample) and a whole-counterexample snapshot
// (vc_getWholeCounterExample), and steered clients to the first; in 3.x the
// Model is the snapshot, and reading it never changes it.

#include "api3_common.hpp"

#include <cstdint>

using namespace stp;

namespace
{

TEST(counter_example_reading, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // every 2.x checker had 'd' on

  const Term A = tm.declare("A", tm.mk_bv_sort(32));
  const Term B = tm.declare("B", tm.mk_bv_sort(32));

  s.push();

  const Term AplusB = bvadd(A, B);
  const Term AplusBplus42 = bvadd(AplusB, tm.mk_bv(32, 42));

  ASSERT_TRUE(s.check_sat().is_sat()); // 2.x: vc_query(false) == 0

  const Model m = s.model();
  (void)m.value(A);
  const auto a = static_cast<std::uint32_t>(m.uint64_value(A));
  const auto b = static_cast<std::uint32_t>(m.uint64_value(B));
  const auto sum = static_cast<std::uint32_t>(m.uint64_value(AplusBplus42));

  EXPECT_EQ(sum, static_cast<std::uint32_t>(a + b + 42));
  // the solver's model and a copy of it are one snapshot
  EXPECT_EQ(s.model().uint64_value(A), a);
  EXPECT_EQ(s.model().uint64_value(AplusBplus42), sum);
}

} // namespace

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

// deep-terms.cpp -- terms a hundred thousand levels deep through the API's
// own walks: the model's evaluator, TermManager::simplify and substitute.
// Each walk keeps its stack on the heap; the evaluator overflowed the C++
// stack from about 40 000 levels and simplify from 80 000.

#include "api_common.hpp"

#include <string>

using namespace stp;

namespace
{

constexpr int depth = 100000;

// x0 or/and x1 or/and ... : every symbol a level of its own.
Term boolean_chain(TermManager& tm)
{
  Term chain = tm.declare("p0", tm.mk_bool_sort());
  for (int i = 1; i < depth; ++i)
  {
    const Term v = tm.declare("p" + std::to_string(i), tm.mk_bool_sort());
    chain = (i % 2) ? (v || chain) : (v && chain);
  }
  return chain;
}

} // namespace

TEST(DeepTerms, a_boolean_chain_is_simplified_and_valued)
{
  TermManager tm;
  const Term chain = boolean_chain(tm);
  EXPECT_EQ(tm.simplify(chain).kind(), Kind::OR);
  const Term p0 = *tm.symbol("p0");
  EXPECT_EQ(chain.substitute({{p0, tm.mk_true()}}).kind(), Kind::OR);
  Solver s(tm);
  s.add(chain);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_TRUE(m.bool_value(chain));
  EXPECT_TRUE(m.value(chain).to_bool());
  // every symbol is in the core, so nothing completes
  ASSERT_TRUE(m.try_value(chain).has_value());
  EXPECT_TRUE(m.try_value(chain)->to_bool());
}

TEST(DeepTerms, a_bit_vector_chain_is_simplified_and_valued)
{
  TermManager::Config cfg;
  cfg.simplify = false; // keep every level
  TermManager tm(cfg);
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8);
  Term chain = x;
  for (int i = 1; i < depth; ++i)
    chain = (i % 2) ? bvadd(chain, tm.mk_bv(8, 1)) : bvxor(chain, tm.mk_bv(8, 0x55));
  // folded all the way down to x and one constant, whatever the shape
  EXPECT_NE(tm.simplify(chain).kind(), Kind::VALUE);
  Solver s(tm);
  s.add(x == tm.mk_bv(8, 7));
  ASSERT_TRUE(s.check_sat().is_sat());
  // the value by folding one level at a time, from the bottom
  std::uint64_t expected = 7;
  for (int i = 1; i < depth; ++i)
    expected = (i % 2) ? (expected + 1) & 0xff : expected ^ 0x55;
  EXPECT_EQ(s.model().uint64_value(chain), expected);
  EXPECT_EQ(tm.simplify(chain.substitute({{x, tm.mk_bv(8, 7)}})).to_uint64(), expected);
}

TEST(DeepTerms, a_long_store_chain_is_valued)
{
  TermManager::Config cfg;
  cfg.simplify = false;
  TermManager tm(cfg);
  const Sort idx = tm.mk_bv_sort(32), bv8 = tm.mk_bv_sort(8);
  const Term a = tm.declare("a", tm.mk_array_sort(idx, bv8));
  Term cells = a;
  for (int i = 0; i < depth; ++i)
    cells = store(cells, tm.mk_bv(32, static_cast<std::uint64_t>(i)), tm.mk_bv(8, i & 0xff));
  Solver s(tm);
  s.add(select(a, tm.mk_bv(32, 7)) == tm.mk_bv(8, 1));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  // a read at the bottom of the chain, and the chain's whole value
  EXPECT_EQ(m.uint64_value(select(cells, tm.mk_bv(32, 0))), 0u);
  EXPECT_EQ(m.uint64_value(select(cells, tm.mk_bv(32, depth - 1))), (depth - 1) & 0xffu);
  EXPECT_EQ(m.array_value(cells).size(), static_cast<std::size_t>(depth));
  EXPECT_EQ(m.value(cells).kind(), Kind::STORE);
}

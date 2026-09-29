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

// y.cpp -- a two-conjunct query over two 32-bit symbols is not entailed:
// the query is printed, and so is the counterexample (the model), which
// names both symbols and falsifies the query.

#include "api_common.hpp"

#include <iostream>
#include <string>

using namespace stp;

namespace
{

TEST(y, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // 2.x flag 'd'

  const Term nresp1 = tm.declare("nresp1", tm.mk_bv_sort(32));
  const Term packet_get_int0 = tm.declare("packet_get_int0", tm.mk_bv_sort(32));
  const Term res = and_({// nresp1 == packet_get_int0
                         nresp1 == packet_get_int0,
                         // nresp1 > 0
                         bvugt(nresp1, tm.mk_bv(32, 0))});
  const std::string query = res.to_string(Format::SMTLIB2);
  std::cout << query << "\n";
  EXPECT_NE(query.find("nresp1"), std::string::npos) << query;
  EXPECT_NE(query.find("packet_get_int0"), std::string::npos) << query;

  ASSERT_TRUE(s.entails(res).is_invalid());
  // vc_printCounterExample
  const Model m = s.model();
  const std::string counterexample = m.to_smt2();
  std::cout << counterexample;
  EXPECT_NE(counterexample.find("nresp1"), std::string::npos) << counterexample;
  EXPECT_NE(counterexample.find("packet_get_int0"), std::string::npos) << counterexample;
  EXPECT_FALSE(m.bool_value(res));
}

} // namespace

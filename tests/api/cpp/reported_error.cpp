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

// reported_error.cpp -- the regression of issue #120
// (https://github.com/stp/stp/issues/120, reported by
// https://github.com/quark17): v + 4 = n, v + 4 >= v and 4 = n asserted
// inside a push are satisfiable, by v = 0 and n = 4. The assertions are
// printed in the presentation language as they are made.

#include "api_common.hpp"

#include <iostream>
#include <string>

using namespace stp;

namespace
{

TEST(reported_issue_120, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // every 2.x checker had 'd' on

  // Numbers will be non-negatives integers bounded at 2^32
  const Sort bv32 = tm.mk_bv_sort(32);

  // Determine whether the following equations are satisfiable:
  //   v + 4 = n
  //   4 = n

  // Construct variable n
  const Term n = tm.declare("n", bv32);

  // Construct v + 4
  const Term v = tm.declare("v", bv32);
  const Term ct_4 = tm.mk_bv(32, 4);
  const Term add_v_4 = bvadd(v, ct_4);

  // Because numbers are represented as bit vectors,
  // addition can roll over.  So construct a constraint
  // expresses that v+4 does not overflow the bounds:
  //   v + 4 >= v
  //
  const Term ge = bvuge(add_v_4, v);

  // Push a new context
  std::cout << "Push\n";
  s.push();

  // Assert v + 4 = n
  std::cout << "Assert v + 4 = n\n";
  const Term f_add = add_v_4 == n;
  s.add(f_add);
  std::cout << f_add.to_string(Format::CVC) << "\n------\n";

  // Assert the bounds constraint
  std::cout << "Assert v + 4 >= v\n";
  s.add(ge);
  std::cout << ge.to_string(Format::CVC) << "\n------\n";

  // Assert 4 = n
  std::cout << "Assert 4 = n\n";
  const Term f_numeq = ct_4 == n;
  s.add(f_numeq);
  std::cout << f_numeq.to_string(Format::CVC) << "\n------\n";

  // Check for satisfiability
  std::cout << "Check\n";
  const std::string asserts = s.to_string(Format::CVC);
  std::cout << asserts << "\n------\n";
  std::size_t count = 0;
  for (std::size_t at = asserts.find("ASSERT("); at != std::string::npos;
       at = asserts.find("ASSERT(", at + 1))
    ++count;
  EXPECT_EQ(count, 3u) << asserts;
  EXPECT_NE(asserts.find("n : BITVECTOR(32);"), std::string::npos) << asserts;
  EXPECT_NE(asserts.find("v : BITVECTOR(32);"), std::string::npos) << asserts;
  const Result query = s.check_sat(); // 2.x: vc_query(false) == 0
  ASSERT_TRUE(query.is_sat());
  EXPECT_EQ(s.model().uint64_value(v), 0u);
  EXPECT_EQ(s.model().uint64_value(n), 4u);

  // Pop context
  std::cout << "Pop\n";
  s.pop();

  std::cout << "query = " << query << "\n";
}

} // namespace

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

// push-pop.cpp -- entailment queries around push and pop: the same
// question asked at the base level and inside a pushed level, and a query
// entailed by an assertion made two levels down. 2.x's vc_query(e) decided
// the assertions and not e; 3.x's Solver::entails(e) answers the same question
// as valid, invalid or unknown.

#include "api_common.hpp"

#include <string>

using namespace stp;

TEST(push_pop, one)
{
  TermManager tm;
  Options o;
  o.set_bool("check-sanity", true); // 'd'
  Solver s(tm, o);

  const Sort bv8 = tm.mk_bv_sort(8);

  const Term a = tm.declare("a", bv8);
  const Term ct_0 = tm.mk_bv(8, 0);

  const Term a_eq_0 = a == ct_0;

  // nothing constrains a, so a = 0 is not entailed
  EXPECT_TRUE(s.entails(a_eq_0).is_invalid());

  s.push();
  EXPECT_TRUE(s.entails(a_eq_0).is_invalid());
  s.pop();
  EXPECT_EQ(s.level(), 0u);
}

TEST(push_pop, two)
{
  TermManager tm;
  Options o;
  o.set_bool("check-sanity", true);   // 'd'
  o.set_bool("produce-models", true); // 'c'
  Solver s(tm, o);
  s.push();

  const Sort bv8 = tm.mk_bv_sort(8);

  const Term a = tm.declare("a", bv8);
  const Term ct_0 = tm.mk_bv(8, 0);

  const Term a_eq_0 = a == ct_0;

  s.add(a_eq_0);
  // vc_printAsserts: the assertions in the presentation language
  const std::string asserts = s.to_string(Format::CVC);
  EXPECT_NE(asserts.find("a : BITVECTOR(8);"), std::string::npos) << asserts;
  EXPECT_NE(asserts.find("(a = 0x00"), std::string::npos) << asserts;
  s.push();

  const Term queryexp = a == tm.mk_bv(8, 0);

  const Entailment query = s.entails(queryexp);
  // vc_printCounterExample: 3.x has no model after an entailment holds (2.x
  // printed an empty counterexample)
  API_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
  s.pop();
  s.pop();
  EXPECT_EQ(s.level(), 0u);

  ASSERT_TRUE(query.is_valid());
}

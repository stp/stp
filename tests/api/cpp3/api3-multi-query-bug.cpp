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

// api3-multi-query-bug.cpp -- a sequence of queries over the same two
// symbols, each in its own push/pop on one solver: none is entailed, and
// each counterexample falsifies its own query. 2.x printed each query, each
// verdict ('n') and each counterexample ('p'); the test prints them.

#include "api3_common.hpp"

#include <iostream>
#include <string>

using namespace stp;

namespace
{

// What 2.x's 'p' printed after a query that does not hold: the
// counterexample, which names both symbols and falsifies the query.
void print_counterexample(const Solver& s, const Term& query)
{
  const Model m = s.model();
  const std::string text = m.to_smt2();
  std::cout << text;
  EXPECT_NE(text.find("(define-fun a "), std::string::npos) << text;
  EXPECT_NE(text.find("(define-fun b "), std::string::npos) << text;
  EXPECT_FALSE(m.bool_value(query));
}

TEST(multi_query_bug, one)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // 2.x flags 'n', 'd', 'p'

  const Term a = tm.declare("a", tm.mk_bv_sort(32));
  const Term b = tm.declare("b", tm.mk_bv_sort(32));
  // a == b
  const Term expr = a == b;
  std::cout << expr.to_string(Format::CVC);

  s.push();
  const Entailment res = s.entails(expr);
  std::cout << "vc_query result = " << res << "\n";
  ASSERT_TRUE(res.is_invalid());
  print_counterexample(s, expr);
  s.pop();

  const Term expr2 = bvugt(a, b);
  std::cout << expr2.to_string(Format::CVC);

  s.push();
  const Entailment res2 = s.entails(expr2);
  std::cout << "vc_query result = " << res2 << "\n";
  ASSERT_TRUE(res2.is_invalid());
  print_counterexample(s, expr2);
  s.pop();
}

TEST(multi_query_bug, many)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // 2.x flags 'n', 'd', 'p'

  const Term a = tm.declare("a", tm.mk_bv_sort(32));
  const Term b = tm.declare("b", tm.mk_bv_sort(32));

  // a == b
  Term expr = a == b;
  std::cout << expr.to_string(Format::CVC);
  s.push();
  Entailment res = s.entails(expr);
  std::cout << "vc_query result = " << res << "\n";
  ASSERT_TRUE(res.is_invalid());
  print_counterexample(s, expr);
  s.pop();

  // a >= b
  expr = bvuge(a, b);
  std::cout << expr.to_string(Format::CVC);
  s.push();
  res = s.entails(expr);
  std::cout << "vc_query result = " << res << "\n";
  ASSERT_TRUE(res.is_invalid());
  print_counterexample(s, expr);
  s.pop();

  // a > b
  expr = bvugt(a, b);
  std::cout << expr.to_string(Format::CVC);
  s.push();
  res = s.entails(expr);
  std::cout << "vc_query result = " << res << "\n";
  ASSERT_TRUE(res.is_invalid());
  print_counterexample(s, expr);
  s.pop();

  // a < b
  expr = bvugt(b, a);
  std::cout << expr.to_string(Format::CVC);
  s.push();
  res = s.entails(expr);
  std::cout << "vc_query result = " << res << "\n";
  ASSERT_TRUE(res.is_invalid());
  print_counterexample(s, expr);
  s.pop();
}

} // namespace

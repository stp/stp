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

// api3-example_broken.cpp -- a small example program showing how to use a
// few bits of the API (after https://gist.github.com/delcypher/13fdf881fdde69eca95d):
// x + x = 2*x is entailed and x + x = 2 is not. Each query is printed with
// the assertions before it, its verdict and, when it is not entailed, the
// counterexample. (2.x's fourth verdict, "could not answer" for an error, is
// an exception here.)

#include "api3_common.hpp"

#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>

using namespace stp;

namespace
{

Entailment handleQuery(Solver& s, const Term& queryExpr, std::ostream& out)
{
  // Print the assertions
  out << "Assertions:\n" << s.to_string(Format::CVC);

  const Entailment result = s.entails(queryExpr);
  out << "Query:\nQUERY(" << queryExpr.to_string(Format::CVC) << ");\n";
  if (result.is_invalid())
  {
    out << "Query is INVALID\n";

    // print counter example
    out << "Counter example:\n" << s.model().to_smt2();
  }
  else if (result.is_valid())
    out << "Query is VALID\n";
  else
    out << "Could not answer query (" << result << ").\n";
  out << "\n\n";
  return result;
}

TEST(examplebroken, one)
{
  const std::uint32_t width = 8;
  TermManager tm;
  Solver s(tm);
  s.options().set_bool(Option::CHECK_SANITY, true); // every 2.x checker had 'd' on

  // Create variable "x"
  const Term x = tm.declare("x", tm.mk_bv_sort(width));

  // Create bitvector x + x
  const Term xPlusx = bvadd(x, x);

  // Create bitvector constant 2
  const Term two = tm.mk_bv(width, 2);

  // Create bitvector 2*x
  const Term xTimes2 = bvmul(two, x);

  // Create bool expression x + x = 2*x
  const Term equality = xPlusx == xTimes2;

  s.add(tm.mk_true());

  // We are asking STP: forall x. true -> ( x + x = 2*x )
  // This should be VALID.
  std::ostringstream first;
  first << "######First Query\n";
  const Entailment r1 = handleQuery(s, equality, first);
  std::cout << first.str();
  EXPECT_TRUE(r1.is_valid());
  EXPECT_NE(first.str().find("ASSERT("), std::string::npos) << first.str();
  EXPECT_NE(first.str().find("Query is VALID"), std::string::npos) << first.str();

  // We are asking STP: forall x. true -> ( x + x = 2 )
  // This should be INVALID.
  std::ostringstream second;
  second << "######Second Query\n";
  // Create bool expression x + x = 2
  const Term badEquality = xPlusx == two;
  const Entailment r2 = handleQuery(s, badEquality, second);
  std::cout << second.str();
  EXPECT_TRUE(r2.is_invalid());
  EXPECT_NE(second.str().find("Query is INVALID"), std::string::npos) << second.str();
  EXPECT_NE(second.str().find("(define-fun x () (_ BitVec 8)"), std::string::npos)
      << second.str();
  EXPECT_FALSE(s.model().bool_value(badEquality));
}

} // namespace

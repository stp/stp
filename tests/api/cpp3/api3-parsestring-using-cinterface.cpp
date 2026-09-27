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

// api3-parsestring-using-cinterface.cpp -- parsing CVC and SMT-LIB 1 text held
// in a string.
//
// 2.x's vc_parseMemExpr handed back the text's query and its assertions as two
// expressions, and the cases printed them. 3.x's Solver::parse asserts the
// assertions, and the query as the assertion of its negation, so that
// check_sat answers the text's question: unsat when the query is valid.

#include "api3_common.hpp"

#include <vector>

using namespace stp;

TEST(parse_string, CVC)
{
  TermManager tm;
  Options o;
  o.set_bool("check-sanity", true); // 'd'
  Solver s(tm, o);

  const char* text = "QUERY BVMOD(2,0bin10,0bin10) = 0bin00;\n";

  s.parse(text, Format::CVC);
  EXPECT_EQ(s.level(), 0u);

  // 2.x printed the query and the assertions: TRUE and TRUE, since 2 mod 2 = 0
  // folds. The query is valid, so its negation -- false -- is the one
  // assertion, and check_sat answers unsat (stp --CVC says Valid.).
  const std::vector<Term> asserted = s.assertions();
  ASSERT_EQ(asserted.size(), 1u);
  EXPECT_TRUE(asserted[0].same_as(tm.mk_false()));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(parse_string, SMT)
{
  TermManager tm;
  Options o;
  o.set_bool("check-sanity", true);   // 'd'
  o.set_bool("print-counterex", true); // 'p'
  Solver s(tm, o);

  const char* text = "(benchmark fg.smt\n"
                     ":logic QF_AUFBV\n"
                     ":extrafuns ((x_32 BitVec[32]))\n"
                     ":extrafuns ((y32 BitVec[32]))\n"
                     ":assumption true\n)\n";

  // 2.x selected the SMT-LIB 1 parser with 'm'; 3.x takes the format as an
  // argument.
  s.parse(text, Format::SMTLIB1);

  // 2.x printed the query and the assertions: FALSE (there is no :formula)
  // and TRUE. 3.x asserts the assumption, and the query adds nothing: the
  // assertions are satisfiable.
  const std::vector<Term> asserted = s.assertions();
  ASSERT_EQ(asserted.size(), 1u);
  EXPECT_TRUE(asserted[0].same_as(tm.mk_true()));
  EXPECT_TRUE(s.check_sat().is_sat());

  // The benchmark declares x_32 and y32 as 32-bit vectors: they are the
  // manager's symbols, which a later parse or parse_term can use.
  const std::optional<Term> x = tm.symbol("x_32"), y = tm.symbol("y32");
  ASSERT_TRUE(x.has_value());
  ASSERT_TRUE(y.has_value());
  EXPECT_EQ(x->sort().bv_size(), 32u);
  s.parse_smt2("(assert (= x_32 (bvadd y32 #x00000001)))\n");
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.parse_term("x_32").same_as(*x));
}

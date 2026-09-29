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

// parsestring-using-cinterface.cpp -- parsing SMT-LIB 2 text held in a
// string.
//
// 2.x's vc_parseMemExpr handed back a CVC or SMT-LIB 1 text's query and its
// assertions as two expressions, and the cases printed them. 3.x's
// Solver::parse reads SMT-LIB 2 and asserts the assertions, so that
// check_sat answers the text's question. The two texts 2.x parsed here are
// kept, in SMT-LIB 2.

#include "api_common.hpp"

#include <vector>

using namespace stp;

TEST(parse_string, AQueryThatFolds)
{
  TermManager tm;
  Options o;
  o.set_bool("check-sanity", true); // 'd'
  Solver s(tm, o);

  // 2.x's text was the CVC query BVMOD(2,0bin10,0bin10) = 0bin00, whose
  // negation is asserted here.
  const char* text = "(assert (not (= (bvurem #b10 #b10) #b00)))\n";

  s.parse(text, Format::SMTLIB2);
  EXPECT_EQ(s.level(), 0u);

  // 2 mod 2 = 0 folds, so the negation -- false -- is the one assertion, and
  // check_sat answers unsat.
  const std::vector<Term> asserted = s.assertions();
  ASSERT_EQ(asserted.size(), 1u);
  EXPECT_TRUE(asserted[0].same_as(tm.mk_false()));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(parse_string, Declarations)
{
  TermManager tm;
  Options o;
  o.set_bool("check-sanity", true);   // 'd'
  o.set_bool("print-counterex", true); // 'p'
  Solver s(tm, o);

  // 2.x's text was an SMT-LIB 1 benchmark with these two declarations and
  // the one assumption.
  const char* text = "(set-logic QF_AUFBV)\n"
                     "(declare-fun x_32 () (_ BitVec 32))\n"
                     "(declare-fun y32 () (_ BitVec 32))\n"
                     "(assert true)\n";

  s.parse(text, Format::SMTLIB2);

  // The assumption is the one assertion: the assertions are satisfiable.
  const std::vector<Term> asserted = s.assertions();
  ASSERT_EQ(asserted.size(), 1u);
  EXPECT_TRUE(asserted[0].same_as(tm.mk_true()));
  EXPECT_TRUE(s.check_sat().is_sat());

  // The text declares x_32 and y32 as 32-bit vectors: they are the
  // manager's symbols, which a later parse or parse_term can use.
  const std::optional<Term> x = tm.symbol("x_32"), y = tm.symbol("y32");
  ASSERT_TRUE(x.has_value());
  ASSERT_TRUE(y.has_value());
  EXPECT_EQ(x->sort().bv_size(), 32u);
  s.parse_smt2("(assert (= x_32 (bvadd y32 #x00000001)))\n");
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.parse_term("x_32").same_as(*x));
}

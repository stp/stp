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

// parsing.cpp -- scripts in and text out: parse_smt2 in both modes,
// the SMT-LIB 1 and CVC parsers, parse_file by extension, parse_term, parse
// errors that leave the solver as it was, and the printers.

#include "api_common.hpp"

#include <cstdio>
#include <fstream>
#include <functional>
#include <future>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <streambuf>
#include <thread>

using namespace stp;

namespace
{

// A file in the working directory that is removed with the test.
struct TempFile
{
  std::string path;
  TempFile(const std::string& name, const std::string& text) : path(name)
  {
    std::ofstream(path) << text;
  }
  ~TempFile() { std::remove(path.c_str()); }
};

TEST(Parsing, smt2_declare_and_assert)
{
  TermManager tm;
  Solver s(tm);
  const Term c = tm.declare("c", tm.mk_bv_sort(8)); // declared through the API first
  testing::internal::CaptureStdout();
  s.parse_smt2("(set-logic QF_BV)\n"
               "(declare-fun px () (_ BitVec 8))\n"
               "(declare-const py (_ BitVec 8))\n"
               "(assert (= px #x2a))\n"
               "(assert (bvult py px))\n"
               "(assert (= c (bvadd px #x01)))\n");
  EXPECT_TRUE(testing::internal::GetCapturedStdout().empty());
  // the script's symbols are the manager's, and it saw the API's
  ASSERT_TRUE(tm.symbol("px").has_value());
  ASSERT_TRUE(tm.symbol("py").has_value());
  EXPECT_TRUE(tm.symbol("px")->sort() == tm.mk_bv_sort(8));
  EXPECT_TRUE(tm.symbol("px")->is_const());
  EXPECT_TRUE(s.symbol("py")->same_as(*tm.symbol("py")));
  EXPECT_TRUE(tm.declare("px", tm.mk_bv_sort(8)).same_as(*tm.symbol("px")));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.declare("px", tm.mk_bv_sort(16)));
  EXPECT_EQ(tm.symbols().size(), 3u);
  EXPECT_EQ(s.assertions().size(), 3u);
  EXPECT_EQ(s.level(), 0u);
  API_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model()); // nothing was checked
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(m.uint64_value(*tm.symbol("px")), 42u);
  EXPECT_LT(m.uint64_value(*tm.symbol("py")), 42u);
  EXPECT_EQ(m.uint64_value(c), 43u);
  // API terms and script terms mix
  s.add(*tm.symbol("py") == c - 40);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(*tm.symbol("py")), 3u);
  // a second script continues in the same table, and define-fun is expanded
  s.parse_smt2("(define-fun d () (_ BitVec 8) (bvadd px #x01))\n(assert (= d #x2b))\n");
  EXPECT_EQ(s.assertions().size(), 5u);
  EXPECT_TRUE(s.check_sat().is_sat());
  // a script cannot redeclare a name (SMT-LIB); the API's declare is the
  // idempotent door
  testing::internal::CaptureStdout();
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_smt2("(declare-fun px () (_ BitVec 8))\n"));
  (void)testing::internal::GetCapturedStdout();
  EXPECT_EQ(tm.symbols().size(), 3u);
  EXPECT_EQ(s.assertions().size(), 5u);
  // a script's check-sat is ignored in this mode, but the frontend conjoins
  // the level's assertions on the way (a limit docs/api.rst lists)
  testing::internal::CaptureStdout();
  s.parse_smt2("(check-sat)\n");
  EXPECT_TRUE(testing::internal::GetCapturedStdout().empty());
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_EQ(s.assertions()[0].kind(), Kind::AND);
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(*tm.symbol("py")), 3u);
}

TEST(Parsing, push_and_pop_inside_scripts)
{
  TermManager tm;
  Solver s(tm);
  s.parse_smt2("(declare-fun a () (_ BitVec 8))\n(assert (= a #x2a))\n");
  s.parse_smt2("(push 1)\n(assert (= a #x2b))\n(check-sat)\n(pop 1)\n(check-sat)\n");
  EXPECT_EQ(s.level(), 0u);
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_TRUE(s.check_sat().is_sat());
  s.parse_smt2("(push 1)\n(assert (= a #x2b))\n");
  EXPECT_EQ(s.level(), 1u);
  EXPECT_EQ(s.assertions().size(), 2u);
  EXPECT_TRUE(s.check_sat().is_unsat());
  s.pop(); // the API and the script share one stack
  EXPECT_EQ(s.level(), 0u);
  EXPECT_TRUE(s.check_sat().is_sat());
  s.push();
  s.parse_smt2("(assert (= a #x2c))\n(pop 1)\n");
  EXPECT_EQ(s.level(), 0u);
  EXPECT_EQ(s.assertions().size(), 1u);
  s.parse_smt2("(push 2)\n(assert (bvugt a #x00))\n(pop 1)\n");
  EXPECT_EQ(s.level(), 1u);
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(*tm.symbol("a")), 42u);
}

TEST(Parsing, execute_mode_runs_the_script)
{
  TermManager tm;
  Solver s(tm);
  // the answers go to the output sink, and nothing to the process's stdout
  std::string out;
  s.set_output_sink([&out](std::string_view chunk) { out.append(chunk); });
  testing::internal::CaptureStdout();
  s.parse_smt2("(declare-fun a () (_ BitVec 8))\n"
               "(assert (= a #x2a))\n"
               "(check-sat)\n"
               "(get-value (a))\n"
               "(get-model)\n",
               ParseMode::EXECUTE);
  EXPECT_TRUE(testing::internal::GetCapturedStdout().empty());
  EXPECT_EQ(out.rfind("sat\n", 0), 0u) << out; // check-sat answered first
  EXPECT_NE(out.find("#x2A"), std::string::npos) << out; // get-value answered
  EXPECT_NE(out.find("define-fun"), std::string::npos) << out; // get-model printed
  EXPECT_EQ(s.assertions().size(), 1u);
  // the script's check is the frontend's, and leaves the API no model (a
  // limit docs/api.rst lists); the API's own check starts afresh and agrees
  API_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(*tm.symbol("a")), 42u);
  // the same script in DECLARE_AND_ASSERT mode neither checks nor prints a model
  TermManager t2;
  Solver s2(t2);
  testing::internal::CaptureStdout();
  s2.parse_smt2("(declare-fun a () (_ BitVec 8))\n(assert (= a #x2a))\n(check-sat)\n");
  EXPECT_TRUE(testing::internal::GetCapturedStdout().empty());
  EXPECT_EQ(s2.statistics().uint64("checks.total"), 0u);
  // an unsat script under EXECUTE, then a sat API check after a pop
  TermManager t3;
  Solver s3(t3);
  testing::internal::CaptureStdout();
  s3.parse_smt2("(declare-fun a () (_ BitVec 8))\n(assert (= a #x2a))\n(push 1)\n(assert (= a #x2b))\n(check-sat)\n(pop 1)\n",
                ParseMode::EXECUTE);
  (void)testing::internal::GetCapturedStdout();
  EXPECT_EQ(s3.level(), 0u);
  EXPECT_TRUE(s3.check_sat().is_sat());
}

TEST(Parsing, smtlib1_and_cvc)
{
  TermManager tm;
  Solver s(tm);
  s.parse("(benchmark b\n :logic QF_BV\n :extrafuns ((sx BitVec[8]) (sy BitVec[8]))\n"
          " :assumption (= sx bv5[8])\n :formula (= sy bv6[8]))\n",
          Format::SMTLIB1);
  ASSERT_TRUE(tm.symbol("sx").has_value());
  ASSERT_TRUE(tm.symbol("sy").has_value());
  // SMT-LIB 1: the assumption and the formula are both asserted (a benchmark
  // asks whether their conjunction is satisfiable)
  EXPECT_GE(s.assertions().size(), 2u);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(*tm.symbol("sx")), 5u);
  EXPECT_EQ(s.model().uint64_value(*tm.symbol("sy")), 6u);
  s.add(*tm.symbol("sy") == 7);
  EXPECT_TRUE(s.check_sat().is_unsat());
  // CVC: ASSERT is asserted, QUERY becomes the assertion of its negation
  TermManager t2;
  Solver s2(t2);
  s2.parse("cx : BITVECTOR(8);\ncy : BITVECTOR(8);\nASSERT(cx = 0hex2a);\nQUERY(cy = 0hex2b);\n", Format::CVC);
  ASSERT_TRUE(t2.symbol("cx").has_value());
  EXPECT_EQ(s2.assertions().size(), 2u);
  EXPECT_EQ(s2.assertions()[1].kind(), Kind::NOT);
  ASSERT_TRUE(s2.check_sat().is_sat()); // the query is not entailed: a counterexample
  EXPECT_EQ(s2.model().uint64_value(*t2.symbol("cx")), 42u);
  EXPECT_NE(s2.model().uint64_value(*t2.symbol("cy")), 43u);
  // a valid query gives unsat
  TermManager t3;
  Solver s3(t3);
  s3.parse("cx : BITVECTOR(8);\nASSERT(cx = 0hex2a);\nQUERY(cx = 0hex2a);\n", Format::CVC);
  EXPECT_TRUE(s3.check_sat().is_unsat());
  // QUERY(FALSE) is the CVC spelling of "only assertions" (the grammar
  // requires a QUERY; a text without one is a syntax error, a PARSE error)
  TermManager t4;
  Solver s4(t4);
  s4.parse("cx : BITVECTOR(8);\nASSERT(cx = 0hex2a);\nQUERY(FALSE);\n", Format::CVC);
  EXPECT_EQ(s4.assertions().size(), 1u);
  EXPECT_TRUE(s4.check_sat().is_sat());
  // parse() takes SMTLIB2 too, and nothing else
  s4.parse("(assert (= cx #x2a))", Format::SMTLIB2);
  EXPECT_EQ(s4.assertions().size(), 2u);
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s4.parse("(assert true)", Format::DOT));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s4.parse("(assert true)", Format::GDL));
  // a malformed CVC or SMT-LIB 1 text is a PARSE error, the solver as it was
  API_EXPECT_ERROR(ErrorCode::PARSE, s4.parse("cy : BITVECTOR(8);\nASSERT(cy = ;\n", Format::CVC));
  API_EXPECT_ERROR(ErrorCode::PARSE,
                   s4.parse("(benchmark b :extrafuns ((z BitVec[8])) :formula (= z", Format::SMTLIB1));
  EXPECT_EQ(s4.assertions().size(), 2u);
}

TEST(Parsing, parse_file_by_extension)
{
  const TempFile smt2("api_parse_test.smt2", "(declare-fun fa () (_ BitVec 8))\n(assert (= fa #x11))\n");
  const TempFile smt("api_parse_test.smt", "(benchmark b :logic QF_BV :extrafuns ((fb BitVec[8])) :formula (= fb bv6[8]))\n");
  const TempFile cvc("api_parse_test.cvc", "fc : BITVECTOR(8);\nASSERT(fc = 0hex22);\nQUERY(fc = 0hex23);\n");
  const TempFile stp("api_parse_test.stp", "fd : BITVECTOR(8);\nASSERT(fd = 0hex33);\nQUERY(FALSE);\n");
  const TempFile other("api_parse_test.txt", "(declare-fun fe () (_ BitVec 8))\n(assert (= fe #x44))\n");
  TermManager tm;
  Solver s(tm);
  s.parse_file(smt2.path);
  s.parse_file(smt.path);
  s.parse_file(cvc.path);
  s.parse_file(stp.path);
  s.parse_file(other.path); // an unknown extension reads as SMT-LIB 2
  for (const char* name : {"fa", "fb", "fc", "fd", "fe"})
    EXPECT_TRUE(tm.symbol(name).has_value()) << name;
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(m.uint64_value(*tm.symbol("fa")), 0x11u);
  EXPECT_EQ(m.uint64_value(*tm.symbol("fb")), 6u); // SMT-LIB 1: the formula is asserted
  EXPECT_EQ(m.uint64_value(*tm.symbol("fc")), 0x22u);
  EXPECT_EQ(m.uint64_value(*tm.symbol("fd")), 0x33u);
  EXPECT_EQ(m.uint64_value(*tm.symbol("fe")), 0x44u);
  // an explicit format overrides the extension
  TermManager t2;
  Solver s2(t2);
  const TempFile cvc_as_txt("api_parse_test2.txt", "fg : BITVECTOR(8);\nASSERT(fg = 0hex55);\nQUERY(FALSE);\n");
  s2.parse_file(cvc_as_txt.path, Format::CVC);
  ASSERT_TRUE(s2.check_sat().is_sat());
  EXPECT_EQ(s2.model().uint64_value(*t2.symbol("fg")), 0x55u);
  API_EXPECT_ERROR(ErrorCode::PARSE, s2.parse_file(cvc_as_txt.path, Format::SMTLIB2));
  // a missing file is an IO error
  auto e = API_ERROR_OF(s2.parse_file("api_no_such_file.smt2"));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::IO);
  EXPECT_EQ(e->function(), "Solver::parse_file");
  EXPECT_EQ(s2.assertions().size(), 1u);
}

// parse_term puts the text inside a command of its own, and a ')' in it used
// to close that command and run what followed against the solver: "true)
// (reset-assertions) (assert true" emptied an unsat solver, and "true) (pop 1)
// (assert false" left false on the base level of an empty one. The text must
// be exactly one term, and the solver is as it was whatever it holds.
TEST(Parsing, parse_term_parses_one_term_and_runs_nothing)
{
  TermManager tm;
  const Term px = tm.declare("px", tm.mk_bv_sort(8));
  Solver s(tm);
  s.add(tm.mk_false());
  ASSERT_TRUE(s.check_sat().is_unsat());
  for (const char* text : {"true) (reset-assertions) (assert true", "true) (pop 1) (assert false",
                           "true (assert false)", "(bvadd px #x01) px", ")", "(bvadd px",
                           "|px", "\"a)b", "; nothing but a comment"})
    API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_term(text));
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_EQ(s.level(), 0u);
  EXPECT_TRUE(s.check_sat().is_unsat());

  Solver empty(tm);
  API_EXPECT_ERROR(ErrorCode::PARSE, empty.parse_term("true) (pop 1) (assert false"));
  EXPECT_TRUE(empty.assertions().empty());
  EXPECT_TRUE(empty.check_sat().is_sat());

  // what one term may hold: comments, a trailing one included, and a quoted
  // symbol with a parenthesis in its name
  const Term odd = tm.declare("a)b", tm.mk_bv_sort(8));
  EXPECT_TRUE(s.parse_term("|a)b|").same_as(odd));
  EXPECT_TRUE(s.parse_term("(bvadd px ; an operand\n #x01) ; the end")
                  .same_as(bvadd(px, tm.mk_bv(8, 1))));
  EXPECT_TRUE(s.parse_term("  px\n").same_as(px));
  EXPECT_EQ(s.assertions().size(), 1u);
}

// A declared sort is the manager's, as a declared symbol is. A later script
// names it whichever door declared it -- a script or the API -- and a script
// that declares only the sort still leaves it to the manager. The second
// parse below once failed with "unknown sort".
TEST(Parsing, declared_sorts_carry_across_parses)
{
  TermManager tm;
  Solver s(tm);
  s.parse_smt2("(declare-sort S 0) (declare-fun a () S)");
  s.parse_smt2("(declare-fun b () S) (assert (distinct a b))");
  ASSERT_TRUE(s.check_sat().is_sat());
  const std::optional<Term> a = tm.symbol("a"), b = tm.symbol("b");
  ASSERT_TRUE(a.has_value() && b.has_value());
  EXPECT_TRUE(a->sort() == b->sort());
  EXPECT_TRUE(s.parse_term("(= a b)").same_as(*a == *b));

  const Sort T = tm.declare_sort("T");
  s.parse_smt2("(declare-fun c () T)");
  ASSERT_TRUE(tm.symbol("c").has_value());
  EXPECT_TRUE(tm.symbol("c")->sort() == T);

  Solver s2(tm);
  s2.parse_smt2("(declare-sort U 0)");
  std::vector<std::string> names;
  for (const Sort& d : tm.declared_sorts())
    names.push_back(d.name());
  EXPECT_EQ(names, (std::vector<std::string>{"S", "T", "U"}));
  s2.parse_smt2("(declare-fun u () U)");
  ASSERT_TRUE(tm.symbol("u").has_value());
  EXPECT_EQ(tm.symbol("u")->sort().name(), "U");

  // a known sort declared again is a PARSE error, as SMT-LIB has it
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_smt2("(declare-sort S 0)"));
}

TEST(Parsing, parse_term)
{
  TermManager tm;
  Solver s(tm);
  const Term px = tm.declare("px", tm.mk_bv_sort(8)), py = tm.declare("py", tm.mk_bv_sort(8));
  const Term t = s.parse_term("(bvadd px #x01)");
  EXPECT_EQ(t.kind(), Kind::BV_ADD);
  EXPECT_TRUE(t.sort() == tm.mk_bv_sort(8));
  EXPECT_TRUE(t.same_as(bvadd(px, tm.mk_bv(8, 1))));
  EXPECT_TRUE(s.parse_term("px").same_as(px));
  EXPECT_TRUE(s.parse_term("#x0a").same_as(tm.mk_bv(8, 10)));
  EXPECT_TRUE(s.parse_term("(_ bv10 8)").same_as(tm.mk_bv(8, 10)));
  // a parsed term is built like a constructed one: under this simplifying
  // manager both spell bvult as bvugt, and they are the same node
  const Term lt = s.parse_term("(bvult px py)");
  EXPECT_EQ(lt.kind(), bvult(px, py).kind());
  EXPECT_TRUE(lt.same_as(bvult(px, py)));
  EXPECT_TRUE(s.parse_term("(and (bvult px py) (= px #x01))").kind() == Kind::AND);
  EXPECT_TRUE(s.parse_term("true").same_as(tm.mk_true()));
  EXPECT_TRUE(s.parse_term("((_ extract 3 0) py)").same_as(extract(3, 0, py)));
  EXPECT_EQ(s.assertions().size(), 0u); // parse_term asserts nothing
  EXPECT_EQ(s.level(), 0u);
  // an application of a declared function, and an equality between arrays
  // (both need no set-logic: the API's construction admits them)
  const Term g = tm.declare("g", tm.mk_fun_sort({tm.mk_bv_sort(8)}, tm.mk_bv_sort(8)));
  EXPECT_TRUE(s.parse_term("(g px)").same_as(g(px)));
  const Sort as = tm.mk_array_sort(tm.mk_bv_sort(8), tm.mk_bv_sort(8));
  const Term a1 = tm.declare("a1", as), a2 = tm.declare("a2", as);
  const Term aeq = s.parse_term("(= a1 a2)");
  EXPECT_EQ(aeq.kind(), Kind::EQUAL);
  EXPECT_TRUE(aeq.same_as(a1 == a2));
  s.push();
  s.add(aeq);
  s.add(a1[px] != a2[px]);
  EXPECT_TRUE(s.check_sat().is_unsat());
  s.pop();
  // a script-declared symbol is visible, and the term evaluates in a model
  s.parse_smt2("(declare-fun pz () (_ BitVec 8))\n(assert (= pz #x05))\n");
  const Term u = s.parse_term("(bvmul pz #x03)");
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(u), 15u);
  // errors
  auto e = API_ERROR_OF(s.parse_term("(bvadd px"));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::PARSE);
  EXPECT_EQ(e->function(), "Solver::parse_term");
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_term("(bvadd px nope)"));
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_term(""));
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_EQ(s.level(), 0u);
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST(Parsing, errors_keep_the_solver_unchanged)
{
  TermManager tm;
  Solver s(tm);
  s.parse_smt2("(declare-fun a () (_ BitVec 8))\n(assert (= a #x01))\n");
  const std::size_t symbols = tm.symbols().size();
  ASSERT_TRUE(s.check_sat().is_sat());
  testing::internal::CaptureStdout();
  auto e = API_ERROR_OF(s.parse_smt2("(set-logic QF_BV)\n(declare-fun b () (_ BitVec 8))\n(assert (= b #x0q))\n"));
  (void)testing::internal::GetCapturedStdout();
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::PARSE);
  EXPECT_EQ(e->line(), 3); // relative to this script
  EXPECT_EQ(e->column(), 0);
  EXPECT_EQ(e->function(), "Solver::parse_smt2");
  EXPECT_NE(std::string(e->what()).find("parse error at 3:0"), std::string::npos);
  EXPECT_NE(std::string(e->what()).find("[PARSE]"), std::string::npos);
  EXPECT_TRUE(e->recoverable());
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_EQ(s.level(), 0u);
  EXPECT_EQ(tm.symbols().size(), symbols);
  EXPECT_EQ(s.model().uint64_value(*tm.symbol("a")), 1u); // the last answer survives
  // the next script's numbering starts again at 1
  testing::internal::CaptureStdout();
  e = API_ERROR_OF(s.parse_smt2("(assert (= a #x0q))"));
  (void)testing::internal::GetCapturedStdout();
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->line(), 1);
  testing::internal::CaptureStdout();
  e = API_ERROR_OF(s.parse_smt2("\n\n\n(assert (= zz #x00))\n"));
  (void)testing::internal::GetCapturedStdout();
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->line(), 4);
  testing::internal::CaptureStdout();
  e = API_ERROR_OF(s.parse_smt2("(assert (= a #x01)"));
  (void)testing::internal::GetCapturedStdout();
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::PARSE);
  EXPECT_EQ(s.assertions().size(), 1u);
  // and the solver goes on
  s.parse_smt2("(assert (bvult a #x02))\n");
  EXPECT_EQ(s.assertions().size(), 2u);
  EXPECT_TRUE(s.check_sat().is_sat());
  // a non-parse error is not a PARSE error
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s.pop());
}

TEST(Parsing, smt2_text_round_trips_through_a_fresh_solver)
{
  // bit-vectors, arrays and a function
  TermManager tm;
  Solver s(tm);
  const Sort bv8 = tm.mk_bv_sort(8), bv32 = tm.mk_bv_sort(32);
  const Term x = tm.declare("x", bv8), y = tm.declare("y", bv8);
  const Term arr = tm.declare("arr", tm.mk_array_sort(bv32, bv8));
  const Term f = tm.declare("f", tm.mk_fun_sort({bv8}, bv8));
  const Term odd = tm.declare("odd name", bv8);
  s.add(bvmul(x, y) == 6);
  s.add(bvult(x, y));
  s.add(arr[tm.mk_bv(32, 1)] == x);
  s.add(f(x) == bvadd(y, 1));
  s.push();
  s.add(odd == extract(7, 0, zero_extend(8, x)));
  s.add(bvugt(x, 1));
  const std::string text = s.to_smt2(true);
  EXPECT_EQ(text.rfind("(check-sat)\n"), text.size() - 12);
  EXPECT_NE(text.find("(set-logic QF_AUFBV)"), std::string::npos);
  EXPECT_NE(text.find("(declare-fun |odd name| () (_ BitVec 8))"), std::string::npos);
  EXPECT_NE(text.find("(declare-fun f ((_ BitVec 8)) (_ BitVec 8))"), std::string::npos);
  EXPECT_NE(text.find("(push 1)"), std::string::npos);
  EXPECT_EQ(s.to_smt2(false).find("(check-sat)"), std::string::npos);
  EXPECT_EQ(s.to_string(Format::SMTLIB2), s.to_smt2(false));
  EXPECT_EQ(s.to_string(Format::AUTO), s.to_smt2(false));
  const Result r = s.check_sat();
  ASSERT_TRUE(r.is_sat());
  TermManager t2;
  Solver s2(t2);
  s2.parse_smt2(s.to_smt2(false)); // without the check-sat, which would conjoin each level
  EXPECT_EQ(s2.level(), 1u);
  EXPECT_EQ(s2.assertions().size(), s.assertions().size());
  EXPECT_TRUE(t2.symbol("odd name").has_value());
  EXPECT_TRUE(t2.symbol("f")->sort().is_fun());
  EXPECT_TRUE(s2.check_sat().is_sat());
  TermManager t2b;
  Solver s2b(t2b);
  s2b.parse_smt2(text); // with the check-sat: the same verdict
  EXPECT_EQ(s2b.level(), 1u);
  EXPECT_TRUE(s2b.check_sat().is_sat());
  const std::uint64_t xv = s2.model().uint64_value(*t2.symbol("x"));
  const std::uint64_t yv = s2.model().uint64_value(*t2.symbol("y"));
  EXPECT_EQ((xv * yv) & 0xff, 6u);
  EXPECT_LT(xv, yv);
  // an unsat stack round trips to unsat: x * y = 6 (mod 256) has no solution
  // with x in {254, 255} and x < y
  s.add(bvugt(x, 253));
  ASSERT_TRUE(s.check_sat().is_unsat());
  TermManager t3;
  Solver s3(t3);
  s3.parse_smt2(s.to_smt2(true));
  EXPECT_TRUE(s3.check_sat().is_unsat());
  // options that differ from their defaults are written as set-option
  s.options().set_bool("produce-models", false);
  s.options().set_int("max-num-confl", 5);
  const std::string with_options = s.to_smt2();
  EXPECT_NE(with_options.find("(set-option :produce-models false)"), std::string::npos);
  EXPECT_NE(with_options.find("(set-option :stp.max-num-confl 5)"), std::string::npos);
  // floating point and a declared sort
  TermManager t4;
  Solver s4(t4);
  const Sort f32 = t4.mk_fp32_sort();
  const Term fx = t4.declare("fx", f32);
  const Term rm = t4.declare("rm", t4.mk_rm_sort());
  const Sort S = t4.declare_sort("S");
  const Term p = t4.declare("p", S), q = t4.declare("q", S);
  // (a literal beside a symbolic rounding mode is UNSUPPORTED: the value is spelled out)
  s4.add(fp_eq(fp_add(rm, fx, t4.mk_fp(f32, RoundingMode::RNE, 1.5)), 3.0));
  s4.add(fp_is_normal(fx));
  s4.add(distinct(p, q));
  const std::string fp_text = s4.to_smt2(true);
  EXPECT_NE(fp_text.find("(set-logic QF_UFBVFP)"), std::string::npos); // the declared sort is UF's
  EXPECT_NE(fp_text.find("(declare-sort S 0)"), std::string::npos);
  EXPECT_NE(fp_text.find("(declare-fun fx () (_ FloatingPoint 8 24))"), std::string::npos);
  EXPECT_NE(fp_text.find("(declare-fun rm () RoundingMode)"), std::string::npos);
  ASSERT_TRUE(s4.check_sat().is_sat());
  TermManager t5;
  Solver s5(t5);
  s5.parse_smt2(fp_text);
  ASSERT_TRUE(s5.check_sat().is_sat());
  EXPECT_NEAR(*s5.model().fp_value(*t5.symbol("fx")).to_double(), 1.5, 1e-6);
  EXPECT_NE(s5.model().uninterpreted_index(*t5.symbol("p")), s5.model().uninterpreted_index(*t5.symbol("q")));
  // reals
  TermManager t6;
  Solver s6(t6);
  const Term rx = t6.declare("rx", t6.mk_real_sort()), ry = t6.declare("ry", t6.mk_real_sort());
  s6.add(rx + ry == t6.mk_real(3));
  s6.add(real_lt(rx, ry));
  s6.add(rx * 2 == ry);
  const std::string real_text = s6.to_smt2(true);
  EXPECT_NE(real_text.find("(set-logic QF_LRA)"), std::string::npos);
  ASSERT_TRUE(s6.check_sat().is_sat());
  TermManager t7;
  Solver s7(t7);
  s7.parse_smt2(real_text);
  ASSERT_TRUE(s7.check_sat().is_sat());
  EXPECT_EQ(s7.model().real_value(*t7.symbol("rx")).str(), "1");
  EXPECT_EQ(s7.model().real_value(*t7.symbol("ry")).str(), "2");
}

TEST(Parsing, functions_declared_by_scripts)
{
  // a function a script declares is the manager's afterwards, whatever the
  // logic line says (the CLI wants a set-logic naming UF), and applies from
  // the API
  TermManager tm;
  Solver s(tm);
  s.parse_smt2("(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\n"
               "(declare-fun x () (_ BitVec 8))\n(declare-fun y () (_ BitVec 8))\n"
               "(assert (not (= (f x) (f y))))\n");
  ASSERT_TRUE(tm.symbol("f").has_value());
  const Term f = *tm.symbol("f");
  EXPECT_TRUE(f.sort().is_fun());
  ASSERT_EQ(f.sort().fun_domain().size(), 1u);
  EXPECT_TRUE(f.sort().fun_domain()[0] == tm.mk_bv_sort(8));
  EXPECT_TRUE(f.sort().fun_codomain() == tm.mk_bv_sort(8));
  EXPECT_TRUE(tm.declare("f", tm.mk_fun_sort({tm.mk_bv_sort(8)}, tm.mk_bv_sort(8))).same_as(f));
  const Term x = *tm.symbol("x"), y = *tm.symbol("y");
  EXPECT_TRUE(s.check_sat().is_sat());
  s.push();
  s.add(x == y); // congruence refutes the script's assertion
  EXPECT_TRUE(s.check_sat().is_unsat());
  s.pop();
  s.add(f(x) == 3); // applied from the API
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(f(x)), 3u);
  // a later script sees it
  s.parse_smt2("(assert (= (f y) #x07))\n");
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.assertions().size(), 3u);
  // declared inside a level the script itself pops: gone with the level
  s.parse_smt2("(push 1)\n(declare-fun g ((_ BitVec 8)) (_ BitVec 8))\n"
               "(assert (= (g x) x))\n(pop 1)\n");
  EXPECT_FALSE(tm.symbol("g").has_value());
  // declared inside a level the API pops: the manager's name table is
  // unscoped, so it stays, as a declared constant does
  s.parse_smt2("(push 1)\n(declare-fun h ((_ BitVec 8)) (_ BitVec 8))\n"
               "(declare-fun hx () (_ BitVec 8))\n(assert (= (h x) hx))\n");
  ASSERT_TRUE(tm.symbol("h").has_value());
  s.pop();
  EXPECT_TRUE(tm.symbol("h").has_value());
  EXPECT_TRUE(tm.symbol("hx").has_value());
  s.add((*tm.symbol("h"))(x) == 9);
  EXPECT_TRUE(s.check_sat().is_sat());
  // a failed script leaves no function behind
  API_EXPECT_ERROR(ErrorCode::PARSE,
                   s.parse_smt2("(declare-fun k ((_ BitVec 8)) Bool)\n(assert (k x)\n"));
  EXPECT_FALSE(tm.symbol("k").has_value());
  s.parse_smt2("(declare-fun k ((_ BitVec 8)) Bool)\n(assert (k x))\n");
  EXPECT_TRUE(tm.symbol("k").has_value());
  EXPECT_TRUE(s.check_sat().is_sat());
}

// The frontend refuses these commands by ending the parse as a whole
// (Cpp_interface::refuseCurrentCommand unwinds to SMT2Parse, which answers
// failure), and the API reports PARSE with the solver as it was.
TEST(Parsing, function_misuse_in_a_script_is_a_parse_error)
{
  TermManager tm;
  Solver s(tm);
  s.parse_smt2("(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\n(declare-fun x () (_ BitVec 8))\n"
               "(assert (= (f x) x))\n");
  // redeclared with another signature
  API_EXPECT_ERROR(ErrorCode::PARSE,
                   s.parse_smt2("(declare-fun f ((_ BitVec 4)) (_ BitVec 8))\n"));
  // applied to the wrong number, or sort, of arguments
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_smt2("(assert (= (f x x) x))\n"));
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_smt2("(assert (= (f #b1) x))\n"));
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_TRUE(s.check_sat().is_sat());
}

// Every one of these once ended the process (the grammar's fatal_yyerror, the
// frontend's refusals, a constant the engine's constructor would not take).
// Each is PARSE now, with the solver as it was -- its level, its assertions --
// and usable afterwards.
TEST(Parsing, frontend_refusals_are_parse_errors)
{
  TermManager tm;
  Solver s(tm);
  s.parse_smt2("(declare-fun x () (_ BitVec 8))\n(declare-fun y () (_ FloatingPoint 8 24))\n"
               "(assert (= x #x01))\n");
  s.push();
  const char* const scripts[] = {
      "(assert (= x #b1))",                                         // width mismatch
      "(assert (= x (bvadd x true)))",                              // Bool where BitVec
      "(assert (and x true))",                                      // BitVec where Bool
      "(declare-fun x () (_ BitVec 4))",                            // redeclaration
      "(declare-fun g ((Array (_ BitVec 8) (_ BitVec 8))) (_ BitVec 8))", // an unsupported UF sort
      "(declare-fun bvadd () (_ BitVec 8))",                        // a theory name
      "(assert (= (fp.to_real x) (fp.to_real y)))",                 // fp.to_real of a bit-vector
      "(declare-fun rr () Real)\n(assert (= y ((_ to_fp 8 24) RNE rr)))", // to_fp of a symbolic Real
      "(assert (= y ((_ to_fp 8 24) 1.5)))",                        // one-argument to_fp of a literal
      "(set-option :produce-models maybe)",                         // a Boolean option's value
      "(set-option :global-declarations true)",                     // an option that must come first
      "(assert (= x (bvadd x)))",                                   // too few operands
      "(declare-fun z () (_ BitVec 0))",                            // a zero width
      "(assert (= x (_ bv300 8)))",                                 // a constant that does not fit
      "(assert (= x (_ bv0 0)))",                                   // a constant of width zero
      "(assert (= x ((_ extract 9 2) x)))",                         // an extract the frontend rejects and skips
      "(declare-fun r () Real)\n(assert (= r (/ 1 0)))",            // Real division by zero
      "(declare-fun @x () (_ BitVec 8))",                           // a reserved name
      "(define-sort F () (_ FloatingPoint 8 24))\n(define-sort F () (_ FloatingPoint 11 53))", // a sort alias defined twice
      "(declare-sort T 0)\n(declare-sort T 0)",                     // a sort declared twice
      "(declare-sort T 0)\n(declare-fun t () T)\n(assert (= t t))\n(assert (= x (bvadd t x)))", // a declared sort where a bit-vector is expected
      "(set-logic ALL)",                                            // a logic STP does not decide
  };
  for (const char* script : scripts)
  {
    const std::optional<RecoverableError> err = API_ERROR_OF(s.parse_smt2(script));
    ASSERT_TRUE(err.has_value()) << script;
    EXPECT_EQ(err->code(), ErrorCode::PARSE) << script << "\n" << err->what();
    EXPECT_EQ(s.level(), 1u) << script;
    EXPECT_EQ(s.assertions().size(), 1u) << script;
  }
  s.pop();
  EXPECT_EQ(s.level(), 0u);
  // a (pop) with nothing pushed at all
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_smt2("(pop 1)"));
  EXPECT_EQ(s.level(), 0u);
  EXPECT_EQ(s.assertions().size(), 1u);
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_FALSE(tm.symbol("z").has_value());
  EXPECT_FALSE(tm.symbol("g").has_value());
  // the same refusals through parse_term
  API_EXPECT_ERROR(ErrorCode::PARSE, (void)s.parse_term("(bvadd x)"));
  API_EXPECT_ERROR(ErrorCode::PARSE, (void)s.parse_term("(_ bv300 8)"));
  API_EXPECT_ERROR(ErrorCode::PARSE, (void)s.parse_term("((_ extract 9 2) x)"));
  EXPECT_EQ(s.assertions().size(), 1u);
}

TEST(Parsing, content_a_switched_off_theory_cannot_decide)
{
  // array-equality = off: the script's array equality is refused, with the
  // solver as it was
  {
    TermManager tm;
    Options o;
    o.set("array-equality", "off");
    Solver s(tm, o);
    s.parse_smt2("(declare-fun x () (_ BitVec 4))\n(assert (= x #x1))\n");
    API_EXPECT_ERROR(ErrorCode::UNSUPPORTED,
                     s.parse_smt2("(declare-fun a () (Array (_ BitVec 4) (_ BitVec 4)))\n"
                                   "(declare-fun b () (Array (_ BitVec 4) (_ BitVec 4)))\n"
                                   "(declare-fun f ((_ BitVec 4)) (_ BitVec 4))\n"
                                   "(push 1)\n(assert (= a b))\n(assert (= (f x) x))\n"));
    EXPECT_EQ(s.level(), 0u);
    EXPECT_EQ(s.assertions().size(), 1u);
    EXPECT_FALSE(tm.symbol("f").has_value());
    EXPECT_TRUE(s.check_sat().is_sat());
    // the same name is free for the next script
    s.parse_smt2("(declare-fun f ((_ BitVec 4)) (_ BitVec 4))\n(assert (= (f x) x))\n");
    EXPECT_TRUE(s.check_sat().is_sat());
  }
  // uninterpreted-functions = off: the script parses (the syntax is always
  // accepted) and the check is refused; no check has happened, so the mode
  // can still be changed
  {
    TermManager tm;
    Options o;
    o.set("uninterpreted-functions", "off");
    Solver s(tm, o);
    s.parse_smt2("(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\n(declare-fun x () (_ BitVec 8))\n"
                 "(declare-fun y () (_ BitVec 8))\n(assert (not (= (f x) (f y))))\n"
                 "(assert (= x y))\n");
    API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, s.check_sat());
    EXPECT_EQ(s.assertions().size(), 2u);
    s.options().set("uninterpreted-functions", "auto");
    EXPECT_TRUE(s.check_sat().is_unsat());
  }
}

TEST(Parsing, other_printers)
{
  TermManager tm;
  Solver s(tm);
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8), y = tm.declare("y", bv8);
  const Term arr = tm.declare("arr", tm.mk_array_sort(bv8, bv8));
  const Term b = tm.declare("b", tm.mk_bool_sort());
  s.add(bvadd(x, y) == 3);
  s.add(arr[x] == y);
  s.add(b);
  const std::string cvc = s.to_string(Format::CVC);
  EXPECT_NE(cvc.find("x : BITVECTOR(8);"), std::string::npos);
  EXPECT_NE(cvc.find("arr : ARRAY BITVECTOR(8) OF BITVECTOR(8);"), std::string::npos);
  EXPECT_NE(cvc.find("b : BOOLEAN;"), std::string::npos);
  EXPECT_NE(cvc.find("ASSERT("), std::string::npos);
  EXPECT_NE(cvc.find("QUERY(FALSE);"), std::string::npos);
  // the CVC text parses back to the same verdict
  TermManager t2;
  Solver s2(t2);
  s2.parse(cvc, Format::CVC);
  EXPECT_TRUE(s2.check_sat().is_sat());
  EXPECT_EQ((s2.model().uint64_value(*t2.symbol("x")) + s2.model().uint64_value(*t2.symbol("y"))) & 0xff, 3u);
  const std::string dot = s.to_string(Format::DOT);
  EXPECT_EQ(dot.rfind("digraph G{", 0), 0u);
  EXPECT_NE(dot.find("BVPLUS"), std::string::npos);
  const std::string gdl = s.to_string(Format::GDL);
  EXPECT_EQ(gdl.rfind("graph: {", 0), 0u);
  EXPECT_NE(gdl.find("BVPLUS"), std::string::npos);
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, s.to_string(Format::SMTLIB1));
  // an empty solver prints too
  TermManager t3;
  Solver s3(t3);
  EXPECT_EQ(s3.to_string(Format::CVC), "QUERY(FALSE);\n");
  EXPECT_EQ(s3.to_string(Format::DOT).rfind("digraph G{", 0), 0u);
  EXPECT_NE(s3.to_smt2().find("(set-logic QF_BV)"), std::string::npos);
  // the CVC language has no floating-point or Real syntax
  s.add(fp_is_nan(tm.declare("fx", tm.mk_fp32_sort())));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, s.to_string(Format::CVC));
  EXPECT_NE(s.to_smt2().find("(set-logic QF_ABVFP)"), std::string::npos);
  TermManager t4;
  Solver s4(t4);
  s4.add(real_gt(t4.declare("r", t4.mk_real_sort()), 1));
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, s4.to_string(Format::CVC));
}

TEST(Parsing, term_printing)
{
  TermManager tm = api_test::raw_manager(); // x + ~x would fold to all ones otherwise
  Solver s(tm);
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8), y = tm.declare("y", bv8);
  const Term prod = bvmul(x, y);
  const Term t = bvadd(prod, bvnot(prod));
  EXPECT_EQ(x.str(), "x");
  EXPECT_EQ(prod.str(), "(bvmul x y)");
  EXPECT_EQ(t.str(), "(bvadd (bvmul x y) (bvnot (bvmul x y)))");
  EXPECT_EQ(t.to_string(Format::SMTLIB2, false), t.str());
  EXPECT_EQ(t.to_string(Format::AUTO, false), t.str());
  const std::string shared = t.to_string(Format::SMTLIB2, true);
  EXPECT_FALSE(shared.empty());
  // both spellings parse back to the term
  EXPECT_TRUE(s.parse_term(t.str()).same_as(t));
  EXPECT_TRUE(s.parse_term(shared).same_as(t));
  EXPECT_TRUE(s.parse_term(t.to_string(Format::SMTLIB2)).same_as(t));
  std::ostringstream os;
  os << prod << " " << Term();
  EXPECT_EQ(os.str(), "(bvmul x y) <null term>");
  EXPECT_EQ(prod.to_string(Format::CVC).rfind("BVMULT(8,", 0), 0u);
  EXPECT_EQ(prod.to_string(Format::DOT).rfind("digraph G{", 0), 0u);
  EXPECT_EQ(prod.to_string(Format::GDL).rfind("graph: {", 0), 0u);
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, prod.to_string(Format::SMTLIB1));
  const Term fx = tm.declare("fx", tm.mk_fp32_sort());
  EXPECT_EQ(fp_is_nan(fx).str(), "(fp.isNaN fx)");
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, fp_is_nan(fx).to_string(Format::CVC));
  EXPECT_EQ(tm.mk_fp(fx.sort(), RoundingMode::RNE, 1.0).str(), "(fp #b0 #b01111111 #b00000000000000000000000)");
  EXPECT_EQ(to_fp(tm.mk_fp64_sort(), RoundingMode::RTZ, fx).str(), "((_ to_fp 11 53) RTZ fx)");
  EXPECT_EQ(fp_to_ubv(8, RoundingMode::RNE, fx).str(), "((_ fp.to_ubv 8) RNE fx)");
  EXPECT_EQ(extract(3, 0, x).str(), "((_ extract 3 0) x)");
  EXPECT_EQ(tm.mk_real(1, 2).str(), "(/ 1 2)");
  EXPECT_EQ((tm.declare("r", tm.mk_real_sort()) + 1).str(), "(+ r 1)");
  EXPECT_EQ(tm.declare("weird name", bv8).str(), "|weird name|");
  EXPECT_EQ(tm.mk_const_array(tm.mk_array_sort(bv8, bv8), tm.mk_bv(8, 0)).sort().str(), "(Array (_ BitVec 8) (_ BitVec 8))");
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, Term().str());
}

// A CVC or SMT-LIB 1 query is a validity question: a query that is, or folds
// to, TRUE is valid, so the solver it was parsed into is unsatisfiable.
TEST(Parsing, a_true_query_is_valid)
{
  for (const char* text :
       {"QUERY(TRUE);\n", "x : BITVECTOR(2);\nQUERY(BVMOD(2, 0bin10, 0bin10) = 0bin00);\n"})
  {
    TermManager tm;
    Solver s(tm);
    s.parse(text, Format::CVC);
    EXPECT_TRUE(s.check_sat().is_unsat()) << text;
  }
  TermManager tm;
  Solver s(tm);
  s.parse("QUERY(FALSE);\n", Format::CVC); // just the assertions, of which there are none
  EXPECT_TRUE(s.check_sat().is_sat());
}

// A declaration no assertion mentions is still the script's, for a later script
// or term to use; one made under a push that the script popped is not.
TEST(Parsing, unused_declarations_are_kept)
{
  TermManager tm;
  Solver s(tm);
  s.parse_smt2("(declare-fun x () (_ BitVec 8))\n(push 1)\n(declare-fun gone () Bool)\n(pop 1)\n");
  ASSERT_TRUE(s.symbol("x").has_value());
  EXPECT_FALSE(s.symbol("gone").has_value());
  s.parse_smt2("(assert (= x #x01))\n");
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(*s.symbol("x")), 1u);
  EXPECT_TRUE(s.parse_term("x").same_as(*s.symbol("x")));
  s.parse("y : BITVECTOR(4);\nQUERY(FALSE);\n", Format::CVC);
  EXPECT_TRUE(s.symbol("y").has_value());
  s.parse("(benchmark b :logic QF_BV :extrafuns ((z BitVec[4])) :formula true)\n", Format::SMTLIB1);
  EXPECT_TRUE(s.symbol("z").has_value());
}

// A failed parse leaves the stack as it found it, whatever the script did to
// it first: popped a level, pushed one, conjoined the levels on a check-sat,
// or popped past the base.
TEST(Parsing, a_failed_script_leaves_the_stack_as_it_was)
{
  TermManager tm;
  Solver s(tm);
  const Term a = tm.declare("a", tm.mk_bool_sort());
  tm.declare("b", tm.mk_bool_sort());
  s.add(a);
  s.push();
  s.add(tm.mk_false());
  ASSERT_TRUE(s.check_sat().is_unsat());
  for (const char* script : {"(pop 1) (assert missing)", "(push 1) (assert b) (assert missing)",
                             "(assert b) (check-sat) (assert missing)", "(pop 1) (pop 1)"})
  {
    API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_smt2(script));
    EXPECT_EQ(s.level(), 1u) << script;
    ASSERT_EQ(s.assertions().size(), 2u) << script;
    EXPECT_TRUE(s.assertions()[0].same_as(a)) << script;
    EXPECT_TRUE(s.check_sat().is_unsat()) << script;
  }
  s.pop();
  EXPECT_TRUE(s.check_sat().is_sat());
}

// A CVC or SMT-LIB 1 input that a grammar action rejects ends the parse. The
// actions reported the error and went on building from what they had just
// rejected: an unresolved name crashed the process, and a width mismatch
// asserted a formula no one wrote. Each is PARSE, with the solver as it was.
TEST(Parsing, a_rejected_cvc_or_smtlib1_input_ends_the_parse)
{
  const std::vector<std::pair<Format, const char*>> inputs{
      {Format::CVC, "x : BITVECTOR(8);\nASSERT(y = 0hex01);\nQUERY(x = x);\n"},
      {Format::CVC, "x : BITVECTOR(8);\nASSERT(x = y);\nQUERY(FALSE);\n"},
      {Format::CVC, "x : BITVECTOR(8);\nASSERT((x & 0hex001) = 0hex01);\nQUERY(FALSE);\n"},
      {Format::CVC, "x : BITVECTOR(8);\nASSERT((x | 0hex001) = 0hex000);\nQUERY(FALSE);\n"},
      {Format::CVC, "x : BITVECTOR(8);\ny : BITVECTOR(4);\n"
                    "ASSERT((IF x = 0hex00 THEN x ELSE y ENDIF) = 0hex05);\nQUERY(FALSE);\n"},
      {Format::CVC, "x : BITVECTOR(8);\nASSERT(x[2:5] = 0bin0);\nQUERY(FALSE);\n"},
      {Format::SMTLIB1, "(benchmark b :logic QF_BV :extrafuns ((x BitVec[8]))\n"
                        " :formula (= (rotate_left[9] x) bv1[8]))\n"},
      {Format::SMTLIB1, "(benchmark b :logic QF_LIA :extrafuns ((x BitVec[8]))\n"
                        " :formula (= x bv1[8]))\n"},
  };
  for (const auto& input : inputs)
  {
    TermManager tm;
    Solver s(tm);
    const Term p = tm.declare("p", tm.mk_bool_sort());
    s.add(p);
    API_EXPECT_ERROR(ErrorCode::PARSE, s.parse(input.second, input.first));
    ASSERT_EQ(s.assertions().size(), 1u) << input.second;
    EXPECT_TRUE(s.assertions()[0].same_as(p)) << input.second;
    EXPECT_TRUE(s.check_sat().is_sat()) << input.second;
    EXPECT_NO_THROW(tm.mk_bv(8, 1)) << input.second;
  }
}

// A run reads a script as the command line does: an equality between whole
// arrays is decided with array-equality = on, and refused otherwise -- as
// the UNSUPPORTED the API's own reading gives under off, where the refusal
// used to poison the manager as an engine failure.
TEST(Parsing, a_run_decides_whole_array_equality_only_when_switched_on)
{
  const char* script = "(set-logic QF_ABV)(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))"
                       "(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))"
                       "(assert (= a b))(check-sat)";
  {
    TermManager tm;
    Solver s(tm);
    API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, s.parse_smt2(script, ParseMode::EXECUTE));
    EXPECT_TRUE(s.assertions().empty());
    EXPECT_NO_THROW(tm.mk_bv(8, 1));
    EXPECT_TRUE(s.check_sat().is_sat());
  }
  TermManager tm;
  Options options;
  options.set("array-equality", "on");
  Solver s(tm, options);
  std::string out;
  s.set_output_sink([&](std::string_view text) { out.append(text); });
  s.parse_smt2(script, ParseMode::EXECUTE);
  EXPECT_EQ(out, "sat\n");
}

// parse_term reads its term as a script's terms are read, over the type
// checker and the grammar's width checks: an ill-sorted term used to be
// handed out, and deciding one could abort the process.
TEST(Parsing, parse_term_refuses_an_ill_sorted_term)
{
  TermManager tm;
  Solver s(tm);
  tm.declare("x", tm.mk_bv_sort(8));
  tm.declare("y", tm.mk_bv_sort(16));
  for (const char* text : {"(bvadd x y)", "(bvult x y)", "(bvcomp x y)", "(bvnand x y)",
                           "(concat x (bvsub y x))", "(let ((q x) (q x)) q)"})
  {
    SCOPED_TRACE(text);
    API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_term(text));
  }
  EXPECT_TRUE(s.assertions().empty());
  EXPECT_TRUE(s.parse_term("(concat x (bvadd y y))").sort() == tm.mk_bv_sort(24));
  EXPECT_TRUE(s.check_sat().is_sat());
}

// A stream the caller set to throw: reaching its end ends the input, and a
// failing buffer is IO. Its exception used to leave the parse as an engine
// failure, INTERNAL, poisoning the manager.
TEST(Parsing, a_stream_that_throws)
{
  {
    TermManager tm;
    Solver s(tm);
    std::istringstream in("(declare-fun x () (_ BitVec 8))(assert (= x #x01))");
    in.exceptions(std::ios_base::eofbit | std::ios_base::failbit | std::ios_base::badbit);
    s.parse(in, Format::SMTLIB2);
    ASSERT_EQ(s.assertions().size(), 1u);
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_EQ(s.model().uint64_value(*s.symbol("x")), 1u);
  }
  struct Failing : std::streambuf
  {
    int_type underflow() override { throw std::runtime_error("the device went away"); }
  };
  for (const bool mask : {true, false})
  {
    TermManager tm;
    Solver s(tm);
    const Term p = tm.declare("p", tm.mk_bool_sort());
    s.add(p);
    Failing buffer;
    std::istream in(&buffer);
    if (mask)
      in.exceptions(std::ios_base::badbit);
    API_EXPECT_ERROR(ErrorCode::IO, s.parse(in, Format::SMTLIB2));
    ASSERT_EQ(s.assertions().size(), 1u) << mask;
    EXPECT_TRUE(s.check_sat().is_sat()) << mask;
    EXPECT_NO_THROW(tm.mk_bv(8, 1)) << mask;
  }
}

// A script's (reset) begins a new session for the script, but the manager's
// symbols outlive it: a Real the API declared, or made with mk_fresh, is
// still one afterwards and a model reads its value, not 0 -- in this solver,
// in another one of the manager, and after a script that resets and then
// fails. (reset-assertions) is the control.
TEST(Parsing, a_script_reset_leaves_the_managers_reals_alone)
{
  for (const char* script : {"(reset)", "(reset) (assert (bogus))", "(reset-assertions)"})
  {
    TermManager tm;
    const Term r = tm.declare("r", tm.mk_real_sort());
    const Term t = tm.mk_fresh(tm.mk_real_sort(), "t");
    const std::vector<Term> cs{real_gt(r, tm.mk_real(1)), real_lt(r, tm.mk_real(3)),
                               t == real_add(r, tm.mk_real(1))};
    Solver s(tm);
    for (const Term& c : cs)
      s.add(c);
    ASSERT_TRUE(s.check_sat().is_sat());
    if (std::string(script).find("bogus") != std::string::npos)
      API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_smt2(script));
    else
      s.parse_smt2(script);
    if (s.assertions().empty())
      for (const Term& c : cs)
        s.add(c);
    ASSERT_TRUE(s.check_sat().is_sat()) << script;
    const Model m = s.model();
    for (const Term& c : cs)
      EXPECT_TRUE(m.bool_value(c)) << script << ": " << c;
    Solver other(tm);
    for (const Term& c : cs)
      other.add(c);
    ASSERT_TRUE(other.check_sat().is_sat()) << script;
    const Model n = other.model();
    for (const Term& c : cs)
      EXPECT_TRUE(n.bool_value(c)) << script << ": " << c;
  }
}

// A printed script names a logic that admits what it declares: a declared
// sort needs a UF logic as much as a function does, and an array beside a
// Real needs QF_AUFLRA, since QF_UFLRA has no arrays. STP reads the script
// back whatever logic it names; another reader need not.
TEST(Parsing, a_printed_script_names_a_logic_that_admits_it)
{
  const auto printed = [](const std::function<void(TermManager&, Solver&)>& build) {
    TermManager tm;
    Solver s(tm);
    build(tm, s);
    const std::string text = s.to_smt2(true);
    TermManager again;
    Solver back(again);
    back.parse_smt2(text);
    EXPECT_TRUE(back.check_sat().is_sat()) << text;
    return text.substr(0, text.find('\n'));
  };
  const auto half = [](TermManager& tm) { return tm.mk_real("1/2"); };
  EXPECT_EQ(printed([&](TermManager& tm, Solver& s) {
              const Sort u = tm.declare_sort("U");
              const Term a = tm.declare("a", tm.mk_array_sort(u, u));
              s.add(select(a, tm.declare("i", u)) != select(a, tm.declare("j", u)));
              s.add(real_gt(tm.declare("x", tm.mk_real_sort()), half(tm)));
            }),
            "(set-logic QF_AUFLRA)");
  EXPECT_EQ(printed([&](TermManager& tm, Solver& s) {
              const Sort bv8 = tm.mk_bv_sort(8);
              s.add(select(tm.declare("a", tm.mk_array_sort(bv8, bv8)), tm.mk_bv(8, 1)) == tm.mk_bv(8, 3));
              s.add(real_gt(tm.declare("x", tm.mk_real_sort()), half(tm)));
            }),
            "(set-logic QF_AUFLRA)");
  EXPECT_EQ(printed([&](TermManager& tm, Solver& s) {
              const Sort u = tm.declare_sort("U");
              s.add(tm.declare("u", u) != tm.declare("v", u));
              s.add(real_gt(tm.declare("x", tm.mk_real_sort()), half(tm)));
            }),
            "(set-logic QF_UFLRA)");
  EXPECT_EQ(printed([&](TermManager& tm, Solver& s) {
              const Sort u = tm.declare_sort("U");
              s.add(tm.declare("u", u) != tm.declare("v", u));
              s.add(bvugt(tm.declare("y", tm.mk_bv_sort(8)), tm.mk_bv(8, 3)));
            }),
            "(set-logic QF_UFBV)");
  EXPECT_EQ(printed([&](TermManager& tm, Solver& s) {
              s.add(real_gt(tm.declare("x", tm.mk_real_sort()), half(tm)));
            }),
            "(set-logic QF_LRA)");
}

// The logic admits the declarations as well as the assertions: a symbol no
// assertion mentions still names its sort. An unused Real printed as
// "(set-logic QF_BV) (declare-fun x () Real)", which STP's own EXECUTE mode
// refuses, and so did an unused float, function or declared sort.
TEST(Parsing, a_printed_logic_admits_the_unused_declarations)
{
  const auto logic_of = [](const std::function<void(TermManager&)>& declare) {
    TermManager tm;
    Solver s(tm);
    declare(tm);
    const std::string text = s.to_smt2(false);
    TermManager again;
    Solver back(again);
    back.parse_smt2(text, ParseMode::EXECUTE); // which enforces the logic
    return text.substr(0, text.find('\n'));
  };
  EXPECT_EQ(logic_of([](TermManager& tm) { tm.declare("x", tm.mk_real_sort()); }),
            "(set-logic QF_LRA)");
  EXPECT_EQ(logic_of([](TermManager& tm) { tm.declare("f", tm.mk_fp32_sort()); }),
            "(set-logic QF_BVFP)");
  EXPECT_EQ(logic_of([](TermManager& tm) {
              tm.declare("g", tm.mk_fun_sort({tm.mk_bv_sort(8)}, tm.mk_bv_sort(8)));
            }),
            "(set-logic QF_UFBV)");
  EXPECT_EQ(logic_of([](TermManager& tm) { tm.declare_sort("U"); }), "(set-logic QF_UFBV)");
  EXPECT_EQ(logic_of([](TermManager& tm) {
              tm.declare("a", tm.mk_array_sort(tm.mk_bv_sort(8), tm.mk_fp32_sort()));
            }),
            "(set-logic QF_ABVFP)");
}

// A parse keeps the frontends' answers for its diagnostics by routing the
// calling thread's output, not by taking std::cout from the process: what
// another thread prints while a parse is under way reaches stdout.
TEST(Parsing, a_parse_leaves_other_threads_output_alone)
{
  // input that holds the parse inside the frontend until released
  struct Held : std::streambuf
  {
    std::promise<void> entered, released;
    std::future<void> go = released.get_future();
    bool done = false;
    char script[19] = "(set-logic QF_BV)\n";
    int_type underflow() override
    {
      if (done)
        return traits_type::eof();
      done = true;
      entered.set_value();
      go.wait();
      setg(script, script, script + 18);
      return traits_type::to_int_type(*gptr());
    }
  } held;
  std::future<void> inside = held.entered.get_future();
  TermManager tm;
  Solver s(tm);
  testing::internal::CaptureStdout();
  std::thread parser([&] {
    std::istream in(&held);
    s.parse(in, Format::SMTLIB2);
  });
  inside.wait();
  std::cout << "printed during the parse" << std::endl;
  held.released.set_value();
  parser.join();
  const std::string out = testing::internal::GetCapturedStdout();
  EXPECT_NE(std::string::npos, out.find("printed during the parse")) << out;
}

} // namespace

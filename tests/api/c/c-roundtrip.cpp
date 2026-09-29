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

// Parse and print round trips through the C API: a script parsed, printed
// and parsed again answers the same; a term printed and parsed back is the
// same node; the CVC and DOT printers produce what their parsers and readers
// expect.

#include <stp/stp.h>

#include <gtest/gtest.h>

#include <cstring>
#include <string>

namespace
{
std::string take(char* s)
{
  std::string out = s ? s : "<null>";
  stp_free(s);
  return out;
}

std::string pending(stp_tm tm)
{
  const stp_error* e = stp_tm_error(tm);
  std::string out = e ? e->message : "(no error)";
  stp_tm_clear_error(tm);
  return out;
}

struct Session
{
  stp_tm tm;
  stp_solver s;
  Session()
  {
    tm = stp_tm_new(nullptr);
    stp_tm_scope_push(tm);
    s = stp_solver_new(tm, nullptr);
  }
  ~Session()
  {
    stp_solver_delete(s);
    stp_tm_scope_pop(tm);
    stp_tm_release(tm);
  }
  stp_result_kind check()
  {
    stp_result r;
    if (stp_solver_check_sat(s, &r) != STP_OK)
      return static_cast<stp_result_kind>(0);
    return r.kind;
  }
};
} // namespace

TEST(c_roundtrip, smt2_script_prints_and_parses_again)
{
  Session a;
  const char* script = "(set-logic QF_ABV)\n"
                       "(declare-fun x () (_ BitVec 8))\n"
                       "(declare-fun y () (_ BitVec 8))\n"
                       "(declare-fun m () (Array (_ BitVec 8) (_ BitVec 8)))\n"
                       "(assert (= (bvadd x y) #x2a))\n"
                       "(assert (bvult x #x10))\n"
                       "(assert (= (select m x) y))\n";
  ASSERT_EQ(STP_OK, stp_solver_parse_smt2(a.s, script, STP_PARSE_DECLARE_AND_ASSERT)) << pending(a.tm);
  // a script without a (check-sat) leaves its assertions apart
  EXPECT_EQ(3u, stp_solver_num_assertions(a.s));
  stp_term x = stp_tm_symbol(a.tm, "x");
  ASSERT_NE(nullptr, x);
  EXPECT_EQ(x, stp_solver_symbol(a.s, "x"));
  EXPECT_EQ(nullptr, stp_tm_symbol(a.tm, "nope"));
  EXPECT_EQ(nullptr, stp_tm_error(a.tm));
  ASSERT_EQ(STP_SAT, a.check());
  EXPECT_EQ(3u, stp_solver_num_assertions(a.s)); // and so does a check
  uint64_t xv = 0, yv = 0;
  stp_model m = stp_solver_model(a.s);
  ASSERT_NE(nullptr, m);
  ASSERT_EQ(STP_OK, stp_model_uint64(m, x, &xv));
  ASSERT_EQ(STP_OK, stp_model_uint64(m, stp_tm_symbol(a.tm, "y"), &yv));
  EXPECT_EQ(0x2au, (xv + yv) & 0xff);
  EXPECT_LT(xv, 0x10u);
  stp_model_release(m);

  const std::string with_check = take(stp_solver_to_smt2(a.s, true));
  EXPECT_NE(std::string::npos, with_check.find("(declare-fun x () (_ BitVec 8))"));
  EXPECT_NE(std::string::npos, with_check.find("(check-sat)"));
  const std::string printed = take(stp_solver_to_smt2(a.s, false));
  EXPECT_EQ(std::string::npos, printed.find("(check-sat)"));

  Session b;
  ASSERT_EQ(STP_OK, stp_solver_parse_smt2(b.s, printed.c_str(), STP_PARSE_DECLARE_AND_ASSERT))
      << pending(b.tm) << "\n" << printed;
  EXPECT_GE(stp_solver_num_assertions(b.s), 1u);
  EXPECT_EQ(STP_SAT, b.check());
  // the same question with a contradiction is unsat in both
  ASSERT_EQ(STP_OK, stp_solver_assert(b.s, stp_eq(b.tm, stp_tm_symbol(b.tm, "x"), stp_mk_bv_uint64(b.tm, 8, 0x20))));
  EXPECT_EQ(STP_UNSAT, b.check());
  EXPECT_EQ(nullptr, stp_tm_error(b.tm)) << pending(b.tm);
}

TEST(c_roundtrip, fresh_sort_declarations_round_trip)
{
  Session original;
  stp_sort sort = stp_mk_fresh_sort(original.tm, "fresh sort");
  stp_term x = stp_declare(original.tm, "x", sort), y = stp_declare(original.tm, "y", sort);
  ASSERT_EQ(STP_OK, stp_solver_assert(original.s, stp_not(original.tm, stp_eq(original.tm, x, y))));
  ASSERT_EQ(STP_SAT, original.check());
  const std::string text = take(stp_solver_to_smt2(original.s, true));
  const std::string declaration = "(declare-sort " + take(stp_sort_str(sort)) + " 0)";
  ASSERT_NE(text.find(declaration), std::string::npos) << text;
  EXPECT_EQ(0u, stp_tm_num_declared_sorts(original.tm));
  Session copy;
  ASSERT_EQ(STP_OK, stp_solver_parse_smt2(copy.s, text.c_str(), STP_PARSE_EXECUTE))
      << pending(copy.tm) << "\n" << text;
  ASSERT_EQ(STP_SAT, copy.check());
  EXPECT_EQ(1u, stp_tm_num_declared_sorts(copy.tm));
  stp_term px = stp_tm_symbol(copy.tm, "x"), py = stp_tm_symbol(copy.tm, "y");
  ASSERT_NE(nullptr, px);
  ASSERT_NE(nullptr, py);
  ASSERT_EQ(STP_OK, stp_solver_assert(copy.s, stp_eq(copy.tm, px, py)));
  EXPECT_EQ(STP_UNSAT, copy.check());
}

TEST(c_roundtrip, function_aliases_are_visible_to_parsing)
{
  Session a;
  stp_sort bv4 = stp_mk_bv_sort(a.tm, 4);
  stp_term f = stp_declare(a.tm, "f", stp_mk_fun_sort(a.tm, 1, &bv4, bv4));
  ASSERT_NE(nullptr, f);
  ASSERT_EQ(STP_OK, stp_tm_bind_symbol(a.tm, "g", f));
  stp_term application = stp_apply(a.tm, f, stp_mk_bv_uint64(a.tm, 4, 0));
  ASSERT_NE(nullptr, application);
  EXPECT_EQ(application, stp_solver_parse_term(a.s, "(g #x0)")) << pending(a.tm);
  ASSERT_EQ(STP_OK, stp_solver_parse_smt2(
      a.s, "(assert (= (g #x0) #x1))", STP_PARSE_DECLARE_AND_ASSERT)) << pending(a.tm);
  ASSERT_EQ(STP_SAT, a.check());
  EXPECT_EQ(f, stp_tm_symbol(a.tm, "g"));
  EXPECT_EQ(application, stp_solver_parse_term(a.s, "(g #x0)")) << pending(a.tm);
  ASSERT_EQ(STP_OK, stp_solver_parse_smt2(
      a.s, "(assert (= (f #x0) #x2))", STP_PARSE_DECLARE_AND_ASSERT)) << pending(a.tm);
  EXPECT_EQ(STP_UNSAT, a.check());
}

TEST(c_roundtrip, a_term_prints_and_parses_to_the_same_node)
{
  Session a;
  stp_sort bv8 = stp_mk_bv_sort(a.tm, 8);
  stp_term x = stp_declare(a.tm, "x", bv8);
  stp_term y = stp_declare(a.tm, "y", bv8);
  stp_term t = stp_bvadd(a.tm, stp_bvmul(a.tm, x, y), stp_mk_bv_uint64(a.tm, 8, 1));
  ASSERT_NE(nullptr, t);
  const std::string text = take(stp_term_str(t));
  // the printer quotes symbols and may reorder commutative operands, so the exact
  // spelling is not fixed; what must hold is that it parses back to the same node
  EXPECT_NE(std::string::npos, text.find("bvadd"));
  EXPECT_NE(std::string::npos, text.find("bvmul"));
  stp_term back = stp_solver_parse_term(a.s, text.c_str());
  ASSERT_NE(nullptr, back) << pending(a.tm) << "\nprinted: " << text;
  EXPECT_EQ(t, back);
  EXPECT_EQ(text, take(stp_term_str(back)));
  // the shared form
  const std::string shared = take(stp_term_to_string(t, STP_FORMAT_SMTLIB2, true));
  EXPECT_FALSE(shared.empty());
  // a symbol with a name that needs quoting survives too
  stp_term odd = stp_declare(a.tm, "odd name", bv8);
  ASSERT_NE(nullptr, odd);
  EXPECT_EQ("|odd name|", take(stp_term_str(odd)));
  EXPECT_EQ(odd, stp_solver_parse_term(a.s, "|odd name|"));
  // a parse error is recorded and does not fail the solver (parse_term builds, it does not
  // assert), an operator given too few operands among them
  for (const char* bad : {"(bvadd x x x", "(bvadd x)"})
  {
    EXPECT_EQ(nullptr, stp_solver_parse_term(a.s, bad)) << bad;
    ASSERT_NE(nullptr, stp_tm_error(a.tm)) << bad;
    EXPECT_EQ(STP_ERR_PARSE, stp_tm_error(a.tm)->code) << bad;
    stp_tm_clear_error(a.tm);
  }
  EXPECT_EQ(nullptr, stp_solver_failed(a.s));
}

TEST(c_roundtrip, a_failed_parse_fails_the_solver_and_keeps_the_stack)
{
  Session a;
  ASSERT_EQ(STP_OK, stp_solver_parse_smt2(a.s, "(declare-fun x () (_ BitVec 8))(assert (= x #x01))",
                                          STP_PARSE_DECLARE_AND_ASSERT));
  EXPECT_EQ(STP_ERROR, stp_solver_parse_smt2(a.s, "(assert (= x", STP_PARSE_DECLARE_AND_ASSERT));
  ASSERT_NE(nullptr, stp_solver_failed(a.s));
  EXPECT_EQ(STP_ERR_PARSE, stp_solver_failed(a.s)->code);
  EXPECT_EQ(STP_ERR_PARSE, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  stp_result r;
  EXPECT_EQ(STP_ERROR, stp_solver_check_sat(a.s, &r));
  EXPECT_EQ(STP_ERR_STATE, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  stp_solver_clear_error(a.s);
  EXPECT_EQ(1u, stp_solver_num_assertions(a.s));
  EXPECT_EQ(STP_SAT, a.check());
  EXPECT_EQ(STP_ERROR, stp_solver_parse_file(a.s, "/nonexistent/file.smt2", STP_FORMAT_AUTO));
  EXPECT_EQ(STP_ERR_IO, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  stp_solver_clear_error(a.s);
}

TEST(c_roundtrip, a_refused_command_is_a_parse_error)
{
  // The frontend's own refusals (a wrong arity here, a sort error, a
  // constant that does not fit) end the parse, not the process: PARSE, the
  // stack as it was, the solver usable once its failed state is cleared.
  Session a;
  ASSERT_EQ(STP_OK, stp_solver_parse_smt2(a.s,
                                          "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))"
                                          "(declare-fun x () (_ BitVec 8))(assert (= (f x) x))",
                                          STP_PARSE_DECLARE_AND_ASSERT))
      << pending(a.tm);
  for (const char* script : {"(assert (= (f x x) x))", "(assert (= x #b1))", "(assert (= x (_ bv300 8)))",
                             "(declare-fun z () (_ BitVec 0))"})
  {
    EXPECT_EQ(STP_ERROR, stp_solver_parse_smt2(a.s, script, STP_PARSE_DECLARE_AND_ASSERT)) << script;
    ASSERT_NE(nullptr, stp_tm_error(a.tm)) << script;
    EXPECT_EQ(STP_ERR_PARSE, stp_tm_error(a.tm)->code) << script;
    stp_tm_clear_error(a.tm);
    stp_solver_clear_error(a.s);
    EXPECT_EQ(1u, stp_solver_num_assertions(a.s)) << script;
  }
  EXPECT_EQ(STP_SAT, a.check());
}

TEST(c_roundtrip, smtlib2_and_dot_and_model_printing)
{
  Session a;
  ASSERT_EQ(STP_OK, stp_solver_parse(a.s,
                                     "(declare-fun cx () (_ BitVec 8))\n(assert (= cx #x2a))\n"
                                     "(assert (not (= cx #x2b)))\n",
                                     STP_FORMAT_SMTLIB2))
      << pending(a.tm);
  EXPECT_EQ(STP_SAT, a.check());
  stp_term cx = stp_tm_symbol(a.tm, "cx");
  ASSERT_NE(nullptr, cx);
  uint64_t v = 0;
  stp_model m = stp_solver_model(a.s);
  ASSERT_EQ(STP_OK, stp_model_uint64(m, cx, &v));
  EXPECT_EQ(42u, v);
  const std::string model = take(stp_model_to_smt2(m));
  // the printer spells the value uppercase (#x2A) and may pad with a space before it
  EXPECT_NE(std::string::npos, model.find("(define-fun cx () (_ BitVec 8)")) << model;
  EXPECT_TRUE(model.find("#x2a") != std::string::npos || model.find("#x2A") != std::string::npos)
      << model;
  stp_model_release(m);

  const std::string smt2 = take(stp_solver_to_string(a.s, STP_FORMAT_SMTLIB2));
  Session b;
  ASSERT_EQ(STP_OK, stp_solver_parse(b.s, smt2.c_str(), STP_FORMAT_SMTLIB2)) << pending(b.tm) << "\n" << smt2;
  EXPECT_EQ(STP_SAT, b.check());
  stp_model mb = stp_solver_model(b.s);
  ASSERT_EQ(STP_OK, stp_model_uint64(mb, stp_tm_symbol(b.tm, "cx"), &v));
  stp_model_release(mb);
  EXPECT_EQ(42u, v);

  const std::string dot = take(stp_solver_to_string(a.s, STP_FORMAT_DOT));
  EXPECT_NE(std::string::npos, dot.find("digraph")) << dot;
  EXPECT_FALSE(take(stp_solver_to_string(a.s, STP_FORMAT_GDL)).empty());
  EXPECT_EQ(nullptr, stp_solver_to_string(a.s, static_cast<stp_format>(42)));
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
}

TEST(c_roundtrip, binding_and_fresh_symbols)
{
  Session a;
  stp_sort bv8 = stp_mk_bv_sort(a.tm, 8);
  stp_term x = stp_declare(a.tm, "x", bv8);
  stp_term fresh = stp_mk_fresh(a.tm, bv8, "tmp");
  ASSERT_NE(nullptr, fresh);
  EXPECT_EQ("x", take(stp_term_symbol(x)));
  EXPECT_EQ(1u, stp_tm_num_symbols(a.tm)); // fresh symbols never enter the table
  EXPECT_EQ(x, stp_tm_symbol_at(a.tm, 0));
  EXPECT_EQ(nullptr, stp_tm_symbol_at(a.tm, 1));
  EXPECT_EQ(STP_ERR_INDEX_OUT_OF_RANGE, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  const std::string fname = take(stp_term_str(fresh)); // the printer quotes it: |tmp!0|
  EXPECT_NE(std::string::npos, fname.find("tmp!")) << fname;
  // bind_symbol enters an existing symbol under a second name (an alias)
  ASSERT_EQ(STP_OK, stp_tm_bind_symbol(a.tm, "x_alias", x));
  EXPECT_EQ(x, stp_tm_symbol(a.tm, "x_alias"));
  EXPECT_EQ(STP_OK, stp_tm_bind_symbol(a.tm, "x_alias", x)); // idempotent for the same term
  EXPECT_EQ(STP_ERROR, stp_tm_bind_symbol(a.tm, "x_alias", fresh)); // the name means something else
  EXPECT_EQ(STP_ERR_SORT_MISMATCH, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  // a name SMT-LIB predefines cannot be told apart from the predefined symbol
  EXPECT_EQ(nullptr, stp_declare(a.tm, "select", bv8));
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  EXPECT_EQ(STP_ERROR, stp_tm_bind_symbol(a.tm, "true", x));
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  EXPECT_EQ(nullptr, stp_tm_declare_sort(a.tm, "Bool"));
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  // a compound term has no place in the table, and the parse below still sees the table whole
  EXPECT_EQ(STP_ERROR, stp_tm_bind_symbol(a.tm, "x_sum", stp_bvadd(a.tm, x, x)));
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, stp_tm_error(a.tm)->code);
  stp_tm_clear_error(a.tm);
  EXPECT_EQ(nullptr, stp_tm_symbol(a.tm, "x_sum"));
  // a script can refer to a symbol the API declared
  ASSERT_EQ(STP_OK, stp_solver_parse_smt2(a.s, "(assert (= x #x07))", STP_PARSE_DECLARE_AND_ASSERT)) << pending(a.tm);
  EXPECT_EQ(STP_SAT, a.check());
  uint64_t v = 0;
  stp_model m = stp_solver_model(a.s);
  ASSERT_EQ(STP_OK, stp_model_uint64(m, x, &v));
  stp_model_release(m);
  EXPECT_EQ(7u, v);
}

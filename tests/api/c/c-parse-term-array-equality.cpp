/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: October, 2026
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

// c-parse-term-array-equality.cpp -- an array equality read by
// stp_solver_parse_term is decided as the one stp_eq builds.
//
// The parse turned the engine's array-equality switch on for itself and put
// it back afterwards, and a check does not apply array-equality = auto again
// while the entry is unset; so nothing left the switch on for the term, and
// the solve never lowered its equality. The check failed inside the engine
// ("TransformFormula: Illegal kind", "SimplifyAtomicFormula: NO atomic
// formula" when incremental) and poisoned the term manager, and a distinct
// over arrays failed already in parse_term's fold. Every formula here is
// read by parse_term, on solvers that leave array-equality unset, under
// both managers and both incremental modes.

#include <stp/stp.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <functional>
#include <initializer_list>
#include <string>
#include <vector>

namespace
{
const char* const kDeclarations = "(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))\n"
                                   "(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))\n"
                                   "(declare-fun c () (Array (_ BitVec 4) (_ BitVec 8)))\n"
                                   "(declare-fun i () (_ BitVec 4))\n"
                                   "(declare-fun p () Bool)\n";

struct Session
{
  stp_tm tm;
  stp_solver s;
  Session(bool simplify, const char* incremental, const char* declarations)
  {
    tm = stp_tm_new_with(simplify, STP_RM_RNE, 16);
    stp_options o = stp_options_new();
    EXPECT_EQ(STP_OK, stp_options_set_str(o, "incremental", incremental));
    s = stp_solver_new(tm, o);
    stp_options_delete(o);
    EXPECT_EQ(STP_OK, stp_solver_parse_smt2(s, declarations, STP_PARSE_DECLARE_AND_ASSERT));
  }
  ~Session()
  {
    stp_solver_delete(s);
    stp_tm_release_all(tm);
    stp_tm_release(tm);
  }

  stp_term term(const char* text)
  {
    const stp_term t = stp_solver_parse_term(s, text);
    EXPECT_NE(nullptr, t) << text << ": " << error();
    return t;
  }

  // the engine's complaint, when a call failed
  std::string error() const
  {
    const stp_error* e = stp_solver_failed(s);
    if (e == nullptr)
      e = stp_tm_error(tm);
    return e != nullptr ? e->message : "(no error)";
  }

  stp_result_kind assuming(std::initializer_list<const char*> texts)
  {
    std::vector<stp_term> terms;
    for (const char* text : texts)
      terms.push_back(term(text));
    stp_result r{};
    EXPECT_EQ(STP_OK, stp_solver_check_sat_assuming(s, terms.size(), terms.data(), &r))
        << error();
    return r.kind;
  }

  std::uint64_t value(const char* text)
  {
    const stp_term v = stp_solver_value(s, term(text));
    std::uint64_t out = 0;
    EXPECT_NE(nullptr, v) << text;
    if (v != nullptr)
    {
      EXPECT_EQ(STP_OK, stp_term_to_uint64(v, &out));
    }
    return out;
  }
};

// Each test under the default and the non-simplifying manager, batch and
// incremental (the engine failed differently in the two). The bodies assert
// each answer: a failed check poisons the manager, and every call after it
// fails the same way.
void each_configuration(const char* declarations, const std::function<void(Session&)>& body)
{
  for (bool simplify : {true, false})
    for (const char* incremental : {"off", "on"})
    {
      SCOPED_TRACE(std::string("simplify ") + (simplify ? "on" : "off") + ", incremental " +
                   incremental);
      Session x(simplify, incremental, declarations);
      body(x);
      EXPECT_EQ(nullptr, stp_tm_error(x.tm)) << x.error();
    }
}
} // namespace

TEST(c_parse_term_array_equality, an_assumption)
{
  each_configuration(kDeclarations, [](Session& x) {
    ASSERT_EQ(STP_SAT, x.assuming({"(= a b)", "(= (select b i) #x07)"}));
    EXPECT_EQ(7u, x.value("(select a i)"));
    ASSERT_EQ(STP_UNSAT,
              x.assuming({"(= a b)", "(= (select b i) #x07)", "(= (select a i) #x06)"}));
  });
}

TEST(c_parse_term_array_equality, a_distinct)
{
  each_configuration(kDeclarations, [](Session& x) {
    ASSERT_EQ(STP_SAT, x.assuming({"(distinct a b)", "(= (select a i) (select b i))"}));
    ASSERT_EQ(STP_UNSAT, x.assuming({"(distinct a b c)", "(= a c)"}));
  });
}

TEST(c_parse_term_array_equality, under_an_ite_and_a_connective)
{
  each_configuration(kDeclarations, [](Session& x) {
    ASSERT_EQ(STP_SAT, x.assuming({"(= (ite p a b) c)", "p", "(= (select a i) #x07)"}));
    EXPECT_EQ(7u, x.value("(select c i)"));
    ASSERT_EQ(STP_SAT, x.assuming({"(or p (= a b))", "(not p)", "(= (select b i) #x07)"}));
    EXPECT_EQ(7u, x.value("(select a i)"));
    ASSERT_EQ(STP_UNSAT, x.assuming({"(and (= a b) (not (= (select a i) (select b i))))"}));
  });
}

TEST(c_parse_term_array_equality, asserted_in_a_scope)
{
  each_configuration(kDeclarations, [](Session& x) {
    ASSERT_EQ(STP_OK, stp_solver_push(x.s, 1));
    ASSERT_EQ(STP_OK, stp_solver_assert(x.s, x.term("(= a b)")));
    ASSERT_EQ(STP_SAT, x.assuming({"(= (select b i) #x07)"}));
    EXPECT_EQ(7u, x.value("(select a i)"));
    ASSERT_EQ(STP_UNSAT, x.assuming({"(= (select b i) #x07)", "(= (select a i) #x06)"}));
    ASSERT_EQ(STP_OK, stp_solver_pop(x.s, 1));
    ASSERT_EQ(STP_SAT, x.assuming({"(= (select b i) #x07)", "(= (select a i) #x06)"}));
  });
}

// The campaign's query: float-indexed arrays, beside an uninterpreted
// function.
TEST(c_parse_term_array_equality, the_campaign_query)
{
  const char* declarations =
      "(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))\n"
      "(declare-fun b () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))\n"
      "(declare-fun x () (_ BitVec 8))\n"
      "(declare-fun g ((_ BitVec 8)) (_ BitVec 8))\n"
      "(define-fun c () (_ FloatingPoint 8 24) (fp #b0 #b01111111 #b00000000000000000000000))\n"
      "(assert (= (g x) #x01))\n";
  each_configuration(declarations, [](Session& x) {
    ASSERT_EQ(STP_SAT, x.assuming({"(= a b)", "(= (select b c) #x07)"}));
    EXPECT_EQ(7u, x.value("(select a c)"));
    EXPECT_EQ(7u, x.value("(select b c)"));
  });
}

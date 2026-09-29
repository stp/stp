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

// Constant arrays through the C API: equality decided, models completed
// with the default, store chains, distinct, and the as-const spelling
// through the printer and the parser.

#include <stp/stp.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

namespace
{
std::string take(char* s)
{
  std::string out = s ? s : "<null>";
  stp_free(s);
  return out;
}

struct Fixture
{
  stp_tm tm = stp_tm_new(nullptr);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_sort A = stp_mk_array_sort(tm, bv8, bv8);
  stp_term c7 = stp_mk_const_array(tm, A, stp_mk_bv_uint64(tm, 8, 7));
  stp_term c1 = stp_mk_const_array(tm, A, stp_mk_bv_uint64(tm, 8, 1));
  stp_term c2 = stp_mk_const_array(tm, A, stp_mk_bv_uint64(tm, 8, 2));
  ~Fixture()
  {
    stp_tm_release_all(tm);
    stp_tm_release(tm);
  }
  stp_term idx(std::uint64_t i) { return stp_mk_bv_uint64(tm, 8, i); }
};

stp_result_kind check(stp_solver s)
{
  stp_result r;
  EXPECT_EQ(STP_OK, stp_solver_check_sat(s, &r));
  return r.kind;
}

std::uint64_t u64(stp_model m, stp_term t)
{
  std::uint64_t v = 0;
  EXPECT_EQ(STP_OK, stp_model_uint64(m, t, &v));
  return v;
}
} // namespace

TEST(c_const_arrays, equality_and_the_completed_model)
{
  Fixture f;
  stp_term a = stp_declare(f.tm, "a", f.A);
  stp_solver s = stp_solver_new(f.tm, nullptr);
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(f.tm, a, f.c7)));
  ASSERT_EQ(STP_SAT, check(s));
  stp_model m = stp_solver_model(s);
  ASSERT_NE(nullptr, m);
  bool b = false;
  EXPECT_EQ(STP_OK, stp_model_bool(m, stp_eq(f.tm, a, f.c7), &b));
  EXPECT_TRUE(b);
  EXPECT_EQ(7u, u64(m, stp_select(f.tm, a, f.idx(200))));
  stp_array_value v = stp_model_array_value(m, a);
  ASSERT_NE(nullptr, v);
  std::uint64_t d = 0;
  EXPECT_EQ(STP_OK, stp_term_to_uint64(stp_array_value_default(v), &d));
  EXPECT_EQ(7u, d);
  stp_array_value_release(v);
  const std::string text = take(stp_model_to_smt2(m));
  EXPECT_NE(std::string::npos, text.find("((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07)"));
  stp_model_release(m);
  // a read disagreeing with the default is unsat
  stp_term i = stp_declare(f.tm, "i", f.bv8);
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_not(f.tm, stp_eq(f.tm, stp_select(f.tm, a, i), f.idx(7)))));
  EXPECT_EQ(STP_UNSAT, check(s));
  stp_solver_delete(s);
  EXPECT_EQ(nullptr, stp_tm_error(f.tm));
}

TEST(c_const_arrays, store_chain_distinct_and_two_constants)
{
  Fixture f;
  stp_term a = stp_declare(f.tm, "a", f.A);
  stp_term chain = stp_store(f.tm, f.c7, f.idx(5), f.idx(42));
  {
    stp_solver s = stp_solver_new(f.tm, nullptr);
    ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(f.tm, a, chain)));
    ASSERT_EQ(STP_SAT, check(s));
    stp_model m = stp_solver_model(s);
    EXPECT_EQ(42u, u64(m, stp_select(f.tm, a, f.idx(5))));
    EXPECT_EQ(7u, u64(m, stp_select(f.tm, a, f.idx(9))));
    stp_array_value v = stp_model_array_value(m, a);
    std::uint64_t d = 0;
    EXPECT_EQ(STP_OK, stp_term_to_uint64(stp_array_value_default(v), &d));
    EXPECT_EQ(7u, d);
    stp_array_value_release(v);
    stp_model_release(m);
    stp_solver_delete(s);
  }
  {
    stp_solver s = stp_solver_new(f.tm, nullptr);
    stp_term args[2] = {f.c1, f.c2};
    ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_distinct(f.tm, 2, args)));
    EXPECT_EQ(STP_SAT, check(s));
    stp_solver_delete(s);
  }
  {
    stp_solver s = stp_solver_new(f.tm, nullptr);
    ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(f.tm, a, f.c1)));
    ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(f.tm, a, f.c2)));
    EXPECT_EQ(STP_UNSAT, check(s));
    stp_solver_delete(s);
  }
  EXPECT_EQ(nullptr, stp_tm_error(f.tm));
}

TEST(c_const_arrays, spelling_and_parsing)
{
  Fixture f;
  const std::string spelled = "((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07)";
  EXPECT_EQ(spelled, take(stp_term_str(f.c7)));
  EXPECT_EQ(spelled, take(stp_term_to_string(f.c7, STP_FORMAT_SMTLIB2, true)));
  stp_kind kind;
  ASSERT_EQ(STP_OK, stp_term_get_kind(f.c7, &kind));
  EXPECT_EQ(STP_KIND_CONST_ARRAY, kind);
  stp_solver s = stp_solver_new(f.tm, nullptr);
  EXPECT_EQ(f.c7, stp_solver_parse_term(s, spelled.c_str()));
  ASSERT_EQ(STP_OK,
            stp_solver_parse_smt2(s,
                                  "(declare-fun z () (Array (_ BitVec 8) (_ BitVec 8)))"
                                  "(assert (= z ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07)))",
                                  STP_PARSE_DECLARE_AND_ASSERT));
  ASSERT_EQ(STP_SAT, check(s));
  stp_model m = stp_solver_model(s);
  stp_term z = stp_tm_symbol(f.tm, "z");
  ASSERT_NE(nullptr, z);
  EXPECT_EQ(7u, u64(m, stp_select(f.tm, z, f.idx(100))));
  stp_model_release(m);
  // the wrong element sort is a PARSE error, recorded on the manager
  EXPECT_EQ(nullptr, stp_solver_parse_term(s, "((as const (Array (_ BitVec 8) (_ BitVec 8))) #b1)"));
  const stp_error* e = stp_tm_error(f.tm);
  ASSERT_NE(nullptr, e);
  EXPECT_EQ(STP_ERR_PARSE, e->code);
  stp_tm_clear_error(f.tm);
  stp_solver_delete(s);
}

TEST(c_const_arrays, symbolic_defaults_survive_solving)
{
  Fixture f;
  stp_term z = stp_declare(f.tm, "z", f.bv8);
  stp_term symbolic = stp_mk_const_array(f.tm, f.A, z);
  ASSERT_NE(nullptr, symbolic);
  EXPECT_EQ(nullptr, stp_tm_error(f.tm));
  stp_term a = stp_declare(f.tm, "a", f.A);
  stp_solver s = stp_solver_new(f.tm, nullptr);
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(f.tm, a, symbolic)));
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(f.tm, z, f.idx(3))));
  ASSERT_EQ(STP_SAT, check(s));
  stp_model m = stp_solver_model(s);
  ASSERT_NE(nullptr, m);
  EXPECT_EQ(3u, u64(m, stp_select(f.tm, a, f.idx(200))));
  stp_array_value v = stp_model_array_value(m, a);
  ASSERT_NE(nullptr, v);
  std::uint64_t d = 0;
  EXPECT_EQ(STP_OK, stp_term_to_uint64(stp_array_value_default(v), &d));
  EXPECT_EQ(3u, d);
  stp_array_value_release(v);
  stp_model_release(m);
  stp_solver_delete(s);
  EXPECT_EQ(nullptr, stp_tm_error(f.tm));
}

TEST(c_const_arrays, unsupported_defaults_are_recoverable)
{
  Fixture f;
  stp_term a = stp_declare(f.tm, "a", f.A);
  stp_term b = stp_declare(f.tm, "b", f.A);
  stp_term condition = stp_eq(f.tm, a, b);
  stp_term value = stp_mk_term3(f.tm, STP_KIND_ITE, condition, f.idx(1), f.idx(2));
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(nullptr, stp_mk_const_array(f.tm, f.A, value));
  const stp_error* e = stp_tm_error(f.tm);
  ASSERT_NE(nullptr, e);
  EXPECT_EQ(STP_ERR_UNSUPPORTED, e->code);
  EXPECT_TRUE(e->recoverable);
  stp_tm_clear_error(f.tm);
  stp_term k3 = stp_mk_const_array(f.tm, f.A, f.idx(3));
  ASSERT_NE(nullptr, k3);
  EXPECT_EQ(nullptr, stp_tm_error(f.tm));
}

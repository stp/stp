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

// The hand-written runtime, one guarantee per test: the four reclamation
// rules, the manager outliving every release order, NULL propagation without
// a record, the failed state confined to the solver, foreign handles, and
// the batch readers.

#include <stp/stp.h>

#include <gtest/gtest.h>

#include <atomic>
#include <climits>
#include <cstring>
#include <initializer_list>
#include <string>
#include <thread>
#include <vector>

namespace
{
std::string take(char* s)
{
  std::string out = s ? s : "<null>";
  stp_free(s);
  return out;
}

// the printer may |quote| a symbol; strip the bars so both spellings compare
std::string symbol_text(stp_term t)
{
  std::string s = take(stp_term_str(t));
  if (s.size() >= 2 && s.front() == '|' && s.back() == '|')
    s = s.substr(1, s.size() - 2);
  return s;
}

stp_error_code code_of(stp_tm tm)
{
  const stp_error* e = stp_tm_error(tm);
  const stp_error_code c = e ? e->code : static_cast<stp_error_code>(0);
  stp_tm_clear_error(tm);
  return c;
}
} // namespace

TEST(c_runtime, scope_rules)
{
  stp_tm tm = stp_tm_new(nullptr);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  // rule 1: with no scope open a returned handle is unscoped and releasable
  stp_term x = stp_declare(tm, "x", bv8);
  EXPECT_EQ(STP_OK, stp_term_release(x));
  x = stp_declare(tm, "x", bv8);
  stp_tm_scope_push(tm);
  EXPECT_EQ(1u, stp_tm_scope_depth(tm));
  stp_term y = stp_declare(tm, "y", bv8);
  // rule 3: a scoped handle refuses release, and nothing happens
  EXPECT_EQ(STP_ERROR, stp_term_release(y));
  EXPECT_EQ(STP_ERR_STATE, code_of(tm));
  // an unscoped reference on the same node is still releasable inside a scope
  EXPECT_EQ(STP_OK, stp_term_release(x));
  // rule 2: a copy is unscoped
  stp_term keep = stp_term_copy(y);
  EXPECT_EQ(y, keep);
  stp_tm_scope_push(tm);
  stp_term inner = stp_bvadd(tm, y, keep);
  EXPECT_EQ(2u, stp_tm_scope_depth(tm));
  stp_tm_scope_pop(tm); // releases inner
  EXPECT_EQ(1u, stp_tm_scope_depth(tm));
  (void)inner;
  stp_tm_scope_pop(tm); // rule 4: releases y's scoped reference
  EXPECT_EQ(0u, stp_tm_scope_depth(tm));
  stp_tm_scope_pop(tm); // nothing open: nothing happens
  EXPECT_EQ("y", symbol_text(keep));
  EXPECT_EQ(STP_OK, stp_term_release(keep));
  EXPECT_EQ(STP_ERROR, stp_term_release(keep));
  EXPECT_EQ(STP_ERR_STATE, code_of(tm));
  // release_all empties the journals and the unscoped counts, the scopes stay open
  stp_term a = stp_declare(tm, "a", bv8);
  stp_term b = stp_term_copy(a);
  stp_tm_scope_push(tm);
  stp_term c = stp_declare(tm, "c", bv8);
  stp_tm_release_all(tm);
  EXPECT_EQ(1u, stp_tm_scope_depth(tm));
  EXPECT_EQ(STP_ERROR, stp_term_release(a));
  EXPECT_EQ(STP_ERR_STATE, code_of(tm));
  (void)b;
  (void)c;
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

TEST(c_runtime, the_manager_outlives_every_release_order)
{
  // (a) the manager handle goes first; terms, solver and model keep working
  stp_tm tm = stp_tm_new(nullptr);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_term x = stp_declare(tm, "x", bv8);
  stp_solver s = stp_solver_new(tm, nullptr);
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(tm, x, stp_mk_bv_uint64(tm, 8, 5)))); // leaks two handles on purpose: released by release_all below
  stp_tm_release(tm);
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s, &r));
  EXPECT_EQ(STP_SAT, r.kind);
  stp_model m = stp_solver_model(s);
  ASSERT_NE(nullptr, m);
  stp_tm again = stp_model_manager(m); // +1: the same manager
  stp_tm via_term = stp_term_manager(x);
  EXPECT_EQ(again, via_term);
  stp_tm_release(via_term);
  stp_solver_delete(s);
  uint64_t v = 0;
  ASSERT_EQ(STP_OK, stp_model_uint64(m, x, &v)); // the model outlives its solver
  EXPECT_EQ(5u, v);
  EXPECT_EQ("x", symbol_text(x));
  stp_model_release(m);
  EXPECT_EQ("x", symbol_text(x)); // the term outlives the model
  stp_tm_release_all(again);              // the leaked handles and x
  stp_tm_release(again);                  // the last reference: the manager dies here
  // (b) the term goes last through a copy of the manager handle
  tm = stp_tm_new_with(true, STP_RM_RTZ, 8);
  EXPECT_EQ(STP_RM_RTZ, stp_tm_default_rounding_mode(tm));
  EXPECT_EQ(8u, stp_tm_uf_sort_width(tm));
  stp_tm copy = stp_tm_copy(tm);
  EXPECT_EQ(stp_tm_id(tm), stp_tm_id(copy));
  stp_term y = stp_declare(tm, "y", stp_mk_bv_sort(tm, 8));
  stp_tm_release(tm);
  stp_tm_release(copy);
  EXPECT_EQ("y", symbol_text(y));
  EXPECT_EQ(STP_OK, stp_term_release(y)); // the manager dies here
  // (c) two managers are independent and their ids differ
  stp_tm t1 = stp_tm_new(nullptr);
  stp_tm t2 = stp_tm_new(nullptr);
  EXPECT_NE(stp_tm_id(t1), stp_tm_id(t2));
  stp_term p = stp_declare(t1, "p", stp_mk_bv_sort(t1, 8));
  stp_term q = stp_declare(t2, "p", stp_mk_bv_sort(t2, 8));
  EXPECT_NE(p, q);
  EXPECT_NE(stp_term_hash(p), stp_term_hash(q));
  // a foreign term is refused at its argument, and the record keeps none of
  // the other manager's terms
  EXPECT_EQ(nullptr, stp_bvadd(t1, p, q));
  const stp_error* e = stp_tm_error(t1);
  ASSERT_NE(nullptr, e);
  EXPECT_EQ(STP_ERR_FOREIGN_MANAGER, e->code);
  EXPECT_STREQ("stp_bvadd", e->function); // the constructor called, at its operand
  EXPECT_EQ(1, e->argument_index);
  EXPECT_EQ(0u, stp_tm_error_num_terms(t1));
  stp_tm_clear_error(t1);
  EXPECT_EQ(nullptr, stp_tm_error(t2)); // the other manager saw nothing
  stp_solver s1 = stp_solver_new(t1, nullptr);
  EXPECT_EQ(STP_ERROR, stp_solver_assert(s1, stp_eq(t2, q, q)));
  EXPECT_EQ(STP_ERR_FOREIGN_MANAGER, code_of(t1));
  EXPECT_NE(nullptr, stp_solver_failed(s1));
  stp_solver_delete(s1);
  stp_tm_release_all(t1);
  stp_tm_release_all(t2);
  stp_tm_release(t1);
  stp_tm_release(t2);
}

// Refusing a term of another manager touches nothing of that manager's: the
// check read the term's owner through a counted reference, and the record kept
// the term, so the refusal and every later clearing of the record changed the
// other manager's plain reference counts from this thread while its own thread
// used them (a crash, or a node freed under it).
TEST(c_runtime, refusing_a_foreign_term_leaves_its_manager_alone)
{
  stp_tm a = stp_tm_new(nullptr);
  stp_tm b = stp_tm_new(nullptr);
  stp_term y = stp_declare(b, "y", stp_mk_bv_sort(b, 8));
  std::atomic<bool> stop{false};
  std::thread builder([&] {
    stp_tm_scope_push(b);
    stp_sort bv8 = stp_mk_bv_sort(b, 8);
    for (unsigned i = 0; !stop.load(); ++i)
    {
      stp_term t = stp_bvadd(b, y, stp_mk_bv_uint64(b, 8, i & 0xff));
      (void)stp_bvmul(b, t, stp_declare(b, "z", bv8));
      if (i % 256 == 255)
      {
        stp_tm_scope_pop(b);
        stp_tm_scope_push(b);
      }
    }
    stp_tm_scope_pop(b);
  });
  for (int i = 0; i < 200000; ++i)
  {
    EXPECT_EQ(nullptr, stp_tm_simplify(a, y));
    EXPECT_EQ(STP_ERR_FOREIGN_MANAGER, code_of(a));
    EXPECT_EQ(0u, stp_tm_error_num_terms(a));
    stp_tm_clear_error(a);
  }
  stop.store(true);
  builder.join();
  EXPECT_EQ(nullptr, stp_tm_error(b)); // the other manager saw nothing
  EXPECT_EQ(STP_OK, stp_term_release(y));
  stp_tm_release(b);
  stp_tm_release(a);
}

TEST(c_runtime, null_propagation_records_nothing)
{
  stp_tm tm = stp_tm_new(nullptr);
  int calls = 0;
  stp_tm_set_error_callback(
      tm, [](const stp_error*, void* user) { ++*static_cast<int*>(user); }, &calls);
  stp_tm_scope_push(tm);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_term x = stp_declare(tm, "x", bv8);
  EXPECT_EQ(nullptr, stp_bvadd(tm, x, nullptr));
  EXPECT_EQ(nullptr, stp_extract(tm, 3, 0, nullptr));
  EXPECT_EQ(nullptr, stp_mk_array_sort(tm, nullptr, bv8));
  EXPECT_EQ(nullptr, stp_declare(tm, "z", nullptr));
  EXPECT_EQ(nullptr, stp_term_sort(nullptr));
  EXPECT_EQ(nullptr, stp_term_child(nullptr, 0));
  EXPECT_EQ(0u, stp_term_id(nullptr));
  EXPECT_EQ(0u, stp_term_hash(nullptr));
  EXPECT_FALSE(stp_term_is_const(nullptr));
  EXPECT_FALSE(stp_term_fits_uint64(nullptr));
  EXPECT_EQ(nullptr, stp_term_copy(nullptr));
  EXPECT_EQ(STP_ERROR, stp_term_release(nullptr));
  stp_kind k;
  EXPECT_EQ(STP_ERROR, stp_term_get_kind(nullptr, &k));
  uint32_t w;
  EXPECT_EQ(STP_ERROR, stp_sort_bv_size(nullptr, &w));
  EXPECT_EQ(0u, stp_sort_id(nullptr));
  EXPECT_EQ(nullptr, stp_tm_error(tm));
  EXPECT_EQ(0, calls);
  // a non-term NULL is an error, recorded where there is an object, thread-locally otherwise
  EXPECT_EQ(nullptr, stp_declare(tm, nullptr, bv8));
  EXPECT_EQ(STP_ERR_NULL_HANDLE, code_of(tm));
  EXPECT_EQ(1, calls);
  EXPECT_EQ(nullptr, stp_mk_bv_sort(nullptr, 8));
  ASSERT_NE(nullptr, stp_last_error());
  EXPECT_EQ(STP_ERR_NULL_HANDLE, stp_last_error()->code);
  EXPECT_STREQ("stp_mk_bv_sort", stp_last_error()->function);
  EXPECT_EQ(nullptr, stp_tm_error(tm));
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

TEST(c_runtime, the_failed_state_is_the_solvers_alone)
{
  stp_tm tm = stp_tm_new(nullptr);
  stp_tm_scope_push(tm);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_term x = stp_declare(tm, "x", bv8);
  stp_solver s = stp_solver_new(tm, nullptr);
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(tm, x, stp_mk_bv_uint64(tm, 8, 1))));
  EXPECT_EQ(STP_ERROR, stp_solver_assert(s, x)); // not Boolean
  ASSERT_NE(nullptr, stp_solver_failed(s));
  EXPECT_EQ(STP_ERR_SORT_MISMATCH, stp_solver_failed(s)->code);
  EXPECT_STREQ("stp_solver_assert", stp_solver_failed(s)->function);
  EXPECT_EQ(STP_ERR_SORT_MISMATCH, code_of(tm));
  // a second failure does not replace the original one
  EXPECT_EQ(STP_ERROR, stp_solver_pop(s, 1));
  EXPECT_EQ(STP_ERR_SORT_MISMATCH, stp_solver_failed(s)->code);
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, code_of(tm));
  // every check refuses with STATE naming the original failure
  stp_result r;
  EXPECT_EQ(STP_ERROR, stp_solver_check_sat(s, &r));
  const stp_error* e = stp_tm_error(tm);
  ASSERT_NE(nullptr, e);
  EXPECT_EQ(STP_ERR_STATE, e->code);
  EXPECT_NE(nullptr, strstr(e->message, "failed state"));
  EXPECT_NE(nullptr, strstr(e->message, "SORT_MISMATCH"));
  stp_tm_clear_error(tm);
  stp_entailment en;
  EXPECT_EQ(STP_ERROR, stp_solver_entails(s, stp_eq(tm, x, x), nullptr, &en));
  EXPECT_EQ(STP_ERR_STATE, code_of(tm));
  EXPECT_EQ(nullptr, stp_solver_model(s));
  EXPECT_EQ(STP_ERR_STATE, code_of(tm));
  EXPECT_EQ(nullptr, stp_solver_candidate_model(s));
  EXPECT_EQ(STP_ERR_STATE, code_of(tm));
  EXPECT_EQ(nullptr, stp_solver_value(s, x));
  EXPECT_EQ(STP_ERR_STATE, code_of(tm));
  // while the manager, the readers and the printers are untouched
  EXPECT_NE(nullptr, stp_bvadd(tm, x, x));
  EXPECT_EQ(1u, stp_solver_num_assertions(s));
  EXPECT_FALSE(take(stp_solver_to_smt2(s, false)).empty());
  EXPECT_NE(nullptr, stp_solver_statistics(s));
  EXPECT_EQ(nullptr, stp_tm_error(tm));
  // successful mutations do not clear it either; only clear_error does
  EXPECT_EQ(STP_OK, stp_solver_push(s, 1));
  EXPECT_NE(nullptr, stp_solver_failed(s));
  stp_solver_clear_error(s);
  EXPECT_EQ(nullptr, stp_solver_failed(s));
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s, &r));
  EXPECT_EQ(STP_SAT, r.kind);
  EXPECT_NE(nullptr, stp_solver_value(s, x));
  // a reset keeps the options and drops the assertions
  EXPECT_EQ(STP_OK, stp_solver_reset(s));
  EXPECT_EQ(0u, stp_solver_num_assertions(s));
  EXPECT_EQ(0u, stp_solver_level(s));
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s, &r));
  EXPECT_EQ(STP_SAT, r.kind);
  stp_solver_delete(s);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

TEST(c_runtime, several_solvers_per_manager)
{
  stp_tm tm = stp_tm_new(nullptr);
  stp_tm_scope_push(tm);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_term x = stp_declare(tm, "x", bv8);
  stp_solver s1 = stp_solver_new(tm, nullptr);
  stp_solver s2 = stp_solver_new(tm, nullptr);
  ASSERT_NE(nullptr, s1);
  ASSERT_NE(nullptr, s2);
  EXPECT_EQ(nullptr, stp_tm_error(tm));
  EXPECT_EQ(STP_OK, stp_solver_assert(s1, stp_eq(tm, x, stp_mk_bv_uint64(tm, 8, 1))));
  EXPECT_EQ(STP_OK, stp_solver_assert(s2, stp_eq(tm, x, stp_mk_bv_uint64(tm, 8, 2))));
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s1, &r));
  EXPECT_EQ(STP_SAT, r.kind);
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s2, &r));
  EXPECT_EQ(STP_SAT, r.kind);
  stp_model m1 = stp_solver_model(s1);
  stp_model m2 = stp_solver_model(s2);
  ASSERT_NE(nullptr, m1);
  ASSERT_NE(nullptr, m2);
  uint64_t v = 0;
  EXPECT_EQ(STP_OK, stp_model_uint64(m1, x, &v));
  EXPECT_EQ(1u, v);
  EXPECT_EQ(STP_OK, stp_model_uint64(m2, x, &v));
  EXPECT_EQ(2u, v);
  stp_model_release(m1);
  stp_model_release(m2);
  stp_solver_delete(s1); // the first goes first: the second stays usable
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s2, &r));
  EXPECT_EQ(STP_SAT, r.kind);
  EXPECT_EQ(1u, stp_solver_num_assertions(s2));
  stp_solver_delete(s2);
  stp_solver s3 = stp_solver_new(tm, nullptr);
  ASSERT_NE(nullptr, s3);
  EXPECT_EQ(0u, stp_solver_num_assertions(s3));
  stp_solver_delete(s3);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

// A manager may be used from any thread, one call at a time: declare on this
// thread, assert, check and read the model on another.
TEST(c_runtime, a_manager_may_be_used_from_another_thread)
{
  stp_tm tm = stp_tm_new(nullptr);
  stp_tm_scope_push(tm);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_term x = stp_declare(tm, "x", bv8);
  stp_solver s = stp_solver_new(tm, nullptr);
  ASSERT_NE(nullptr, s);
  uint64_t seen = 0;
  bool ok = false;
  std::thread worker([&] {
    stp_tm_scope_push(tm);
    stp_term y = stp_declare(tm, "y", bv8);
    ok = stp_solver_assert(s, stp_eq(tm, x, stp_mk_bv_uint64(tm, 8, 5))) == STP_OK &&
         stp_solver_assert(s, stp_eq(tm, y, stp_bvadd(tm, x, stp_mk_bv_uint64(tm, 8, 1)))) == STP_OK;
    stp_result r;
    ok = ok && stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT;
    stp_model m = stp_solver_model(s);
    ok = ok && m != nullptr && stp_model_uint64(m, y, &seen) == STP_OK;
    stp_model_release(m);
    stp_tm_scope_pop(tm);
  });
  worker.join();
  EXPECT_TRUE(ok);
  EXPECT_EQ(6u, seen);
  EXPECT_EQ(nullptr, stp_tm_error(tm));
  // and back here
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s, &r));
  EXPECT_EQ(STP_SAT, r.kind);
  stp_solver_delete(s);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

TEST(c_runtime, batch_values_substitution_and_children)
{
  stp_tm tm = stp_tm_new(nullptr);
  stp_tm_scope_push(tm);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_term x = stp_declare(tm, "x", bv8), y = stp_declare(tm, "y", bv8), z = stp_declare(tm, "z", bv8);
  stp_term sum = stp_bvadd(tm, x, y);
  size_t n = 0;
  ASSERT_EQ(STP_OK, stp_term_num_children(sum, &n));
  EXPECT_EQ(2u, n);
  EXPECT_EQ(x, stp_term_child(sum, 0));
  EXPECT_EQ(y, stp_term_child(sum, 1));
  // substitution
  const stp_term from[1] = {y};
  const stp_term to[1] = {z};
  stp_term subst = stp_term_substitute(sum, 1, from, to);
  EXPECT_EQ(stp_bvadd(tm, x, z), subst);
  EXPECT_EQ(sum, stp_term_substitute(sum, 0, nullptr, nullptr));
  // batch model values, all or nothing
  stp_solver s = stp_solver_new(tm, nullptr);
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(tm, x, stp_mk_bv_uint64(tm, 8, 1))));
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(tm, y, stp_mk_bv_uint64(tm, 8, 2))));
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s, &r));
  stp_model m = stp_solver_model(s);
  const stp_term in[3] = {x, y, sum};
  stp_term out[3] = {nullptr, nullptr, nullptr};
  ASSERT_EQ(STP_OK, stp_model_values(m, 3, in, out));
  uint64_t v = 0;
  ASSERT_EQ(STP_OK, stp_term_to_uint64(out[2], &v));
  EXPECT_EQ(3u, v);
  // z is not in the core: value completes it, try_value does not
  EXPECT_FALSE(stp_model_in_core(m, z));
  EXPECT_NE(nullptr, stp_model_value(m, z));
  EXPECT_EQ(nullptr, stp_model_try_value(m, z));
  EXPECT_EQ(nullptr, stp_tm_error(tm));
  EXPECT_NE(nullptr, stp_model_try_value(m, x));
  // a model copy shares the snapshot
  stp_model m2 = stp_model_copy(m);
  stp_model_release(m);
  ASSERT_EQ(STP_OK, stp_model_uint64(m2, sum, &v));
  EXPECT_EQ(3u, v);
  EXPECT_EQ(2u, stp_model_num_symbols(m2));
  EXPECT_NE(nullptr, stp_model_symbol(m2, 0));
  stp_model_release(m2);
  // simplify is local
  EXPECT_EQ(x, stp_tm_simplify(tm, stp_bvadd(tm, x, stp_mk_bv_uint64(tm, 8, 0))));
  stp_solver_delete(s);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

// An array's value is its array value's term; a function has none.
TEST(c_runtime, the_value_of_an_array_or_a_function)
{
  stp_tm tm = stp_tm_new(nullptr);
  stp_tm_scope_push(tm);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_sort as = stp_mk_array_sort(tm, bv8, bv8);
  stp_term a = stp_declare(tm, "a", as), b = stp_declare(tm, "b", as);
  stp_term f = stp_declare(tm, "f", stp_mk_fun_sort(tm, 1, &bv8, bv8));
  stp_term one = stp_mk_bv_uint64(tm, 8, 1), two = stp_mk_bv_uint64(tm, 8, 2);
  stp_solver s = stp_solver_new(tm, nullptr);
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(tm, stp_select(tm, a, one), two)));
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(tm, stp_apply(tm, f, one), two)));
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s, &r));
  stp_model m = stp_solver_model(s);
  stp_array_value av = stp_model_array_value(m, a);
  ASSERT_NE(nullptr, av);
  stp_term va = stp_model_value(m, a);
  ASSERT_NE(nullptr, va);
  EXPECT_EQ(stp_array_value_as_term(av), va);
  EXPECT_EQ(va, stp_model_try_value(m, a));
  EXPECT_FALSE(stp_term_is_const(va));
  // b is outside the core: value completes it, try_value does not
  EXPECT_NE(nullptr, stp_model_value(m, b));
  EXPECT_EQ(nullptr, stp_model_try_value(m, b));
  EXPECT_EQ(nullptr, stp_tm_error(tm));
  // a function: SORT_MISMATCH
  EXPECT_EQ(nullptr, stp_model_value(m, f));
  ASSERT_NE(nullptr, stp_tm_error(tm));
  EXPECT_EQ(STP_ERR_SORT_MISMATCH, stp_tm_error(tm)->code);
  stp_tm_clear_error(tm);
  EXPECT_EQ(nullptr, stp_model_try_value(m, f));
  ASSERT_NE(nullptr, stp_tm_error(tm));
  EXPECT_EQ(STP_ERR_SORT_MISMATCH, stp_tm_error(tm)->code);
  stp_tm_clear_error(tm);
  stp_array_value_release(av);
  stp_model_release(m);
  stp_solver_delete(s);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

TEST(c_runtime, error_callback_sees_every_error_and_the_record_keeps_the_first)
{
  stp_tm tm = stp_tm_new(nullptr);
  std::vector<stp_error_code> seen;
  stp_tm_set_error_callback(
      tm,
      [](const stp_error* e, void* user) {
        static_cast<std::vector<stp_error_code>*>(user)->push_back(e->code);
      },
      &seen);
  stp_tm_scope_push(tm);
  EXPECT_EQ(nullptr, stp_mk_bv_sort(tm, 0));
  EXPECT_EQ(nullptr, stp_mk_bv_uint64(tm, 4, 16));
  EXPECT_EQ(nullptr, stp_mk_fp_sort(tm, 1, 1));
  ASSERT_EQ(3u, seen.size());
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, seen[0]);
  EXPECT_EQ(STP_ERR_VALUE_OUT_OF_RANGE, seen[1]);
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, seen[2]);
  const stp_error* e = stp_tm_error(tm);
  ASSERT_NE(nullptr, e);
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, e->code);
  EXPECT_STREQ("stp_mk_bv_sort", e->function);
  EXPECT_TRUE(e->recoverable);
  EXPECT_EQ(nullptr, e->option);
  stp_tm_clear_error(tm);
  stp_tm_set_error_callback(tm, nullptr, nullptr);
  EXPECT_EQ(nullptr, stp_mk_bv_sort(tm, 0));
  EXPECT_EQ(3u, seen.size());
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

// The thread-local record can be cleared, which is what lets a registry query
// whose every answer is also a valid one report failure: an unknown name's tier
// is STABLE like a real one's, and an error from any earlier call stayed in the
// record for good. The message lives until the next object-less error or clear.
TEST(c_runtime, the_thread_record_is_cleared_to_ask_a_registry_query)
{
  EXPECT_EQ(nullptr, stp_tm_new_with(true, STP_RM_RNE, 0)); // leaves an error behind
  ASSERT_NE(nullptr, stp_last_error());
  stp_clear_last_error();
  EXPECT_EQ(nullptr, stp_last_error());
  EXPECT_EQ(STP_TIER_STABLE, stp_statistics_tier("checks.total"));
  EXPECT_EQ(nullptr, stp_last_error()); // a real name: no error
  EXPECT_EQ(STP_TIER_STABLE, stp_statistics_tier("no.such.statistic"));
  const stp_error* e = stp_last_error();
  ASSERT_NE(nullptr, e);
  EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, e->code);
  const std::string message = e->message;
  EXPECT_NE(std::string::npos, message.find("no.such.statistic")) << message;
  stp_clear_last_error();
  EXPECT_EQ(nullptr, stp_last_error());
}

TEST(c_runtime, no_limit_round_trips_through_the_duration_functions)
{
  // max-time's default, read and copied the way a C client copies a setting
  stp_options o = stp_options_new();
  uint64_t ms = 0;
  ASSERT_EQ(STP_OK, stp_options_get_duration_ms(o, "max-time", &ms));
  EXPECT_EQ(STP_DURATION_NONE, ms);
  stp_options o2 = stp_options_new();
  ASSERT_EQ(STP_OK, stp_options_set_duration_ms(o2, "max-time", 1000));
  ASSERT_EQ(STP_OK, stp_options_set_duration_ms(o2, "max-time", ms));
  EXPECT_EQ("none", take(stp_options_get_str(o2, "max-time")));
  EXPECT_EQ(STP_ERROR, stp_options_set_duration_ms(o2, "max-time", STP_DURATION_NONE - 1));
  ASSERT_NE(nullptr, stp_options_error(o2));
  EXPECT_EQ(STP_ERR_VALUE_OUT_OF_RANGE, stp_options_error(o2)->code);
  stp_options_clear_error(o2);

  stp_tm tm = stp_tm_new(nullptr);
  stp_term x = stp_declare(tm, "x", stp_mk_bv_sort(tm, 8));
  stp_solver s = stp_solver_new(tm, o2);
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(tm, x, stp_mk_bv_uint64(tm, 8, 3))));
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s, &r));
  EXPECT_EQ(STP_SAT, r.kind); // not the "give up at once" of a 0 ms budget
  ms = 0;
  ASSERT_EQ(STP_OK, stp_solver_get_duration_ms(s, "max-time", &ms));
  EXPECT_EQ(STP_DURATION_NONE, ms);
  ASSERT_EQ(STP_OK, stp_solver_set_duration_ms(s, "max-time", 5000));
  ASSERT_EQ(STP_OK, stp_solver_get_duration_ms(s, "max-time", &ms));
  EXPECT_EQ(5000u, ms);
  ASSERT_EQ(STP_OK, stp_solver_set_duration_ms(s, "max-time", STP_DURATION_NONE));
  EXPECT_EQ("none", take(stp_solver_get_str(s, "max-time")));
  stp_solver_delete(s);
  stp_options_delete(o);
  stp_options_delete(o2);
  stp_tm_release_all(tm);
  stp_tm_release(tm);
}

TEST(c_runtime, a_budget_past_the_clocks_range_is_no_limit)
{
  stp_tm tm = stp_tm_new(nullptr);
  stp_term x = stp_declare(tm, "x", stp_mk_bv_sort(tm, 8));
  stp_solver s = stp_solver_new(tm, nullptr);
  ASSERT_EQ(STP_OK, stp_solver_assert(s, stp_eq(tm, x, stp_mk_bv_uint64(tm, 8, 3))));
  for (const uint64_t ms : std::initializer_list<uint64_t>{9223372036854ull, 9223372036854775807ull, STP_DURATION_NONE})
  {
    stp_budget b = {true, ms, false, 0};
    stp_result r;
    ASSERT_EQ(STP_OK, stp_solver_check_sat_budget(s, 0, nullptr, &b, &r));
    EXPECT_EQ(STP_SAT, r.kind) << ms;
  }
  ASSERT_EQ(STP_OK, stp_solver_set_duration_ms(s, "max-time", 9223372036854775807ull));
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat(s, &r));
  EXPECT_EQ(STP_SAT, r.kind);
  stp_solver_delete(s);
  stp_tm_release_all(tm);
  stp_tm_release(tm);
}

// The error codes are sixteen bits wide: stp_error_code_name wrapped a wider
// value onto a code, naming 65637 "INTERNAL" and 65553 "PARSE". Every name
// function answers "?" for a value no enumerator names.
TEST(c_runtime, an_error_code_past_sixteen_bits_names_nothing)
{
  EXPECT_STREQ("PARSE", stp_error_code_name(STP_ERR_PARSE));
  EXPECT_STREQ("INTERNAL", stp_error_code_name(STP_ERR_INTERNAL));
  for (const int wide : {65536 + STP_ERR_INTERNAL, 65536 + STP_ERR_PARSE, 0x7fffffff})
    EXPECT_STREQ("?", stp_error_code_name(static_cast<stp_error_code>(wide))) << wide;
}

// Every enum spans all of int, from its *_MIN_ENUM to its *_MAX_ENUM, so a C
// caller's negative value is a value of the type for the implementation
// rather than undefined behaviour there, and is refused like any other value
// no enumerator names.
TEST(c_runtime, a_negative_enum_value_is_refused)
{
  static_assert(STP_RM_MIN_ENUM == INT_MIN && STP_KIND_MIN_ENUM == INT_MIN &&
                    STP_ERR_MIN_ENUM == INT_MIN && STP_OPT_MIN_ENUM == INT_MIN &&
                    STP_STATUS_MIN_ENUM == INT_MIN && STP_POLICY_MIN_ENUM == INT_MIN,
                "every enum reaches INT_MIN");
  stp_tm tm = stp_tm_new(nullptr);
  for (const int v : {-1, INT_MIN})
  {
    SCOPED_TRACE(v);
    EXPECT_EQ(nullptr, stp_mk_rm(tm, static_cast<stp_rm>(v)));
    EXPECT_EQ(STP_ERR_INVALID_ARGUMENT, code_of(tm));
    EXPECT_STREQ("?", stp_rm_name(static_cast<stp_rm>(v)));
    EXPECT_STREQ("?", stp_kind_name(static_cast<stp_kind>(v)));
    EXPECT_STREQ("?", stp_error_code_name(static_cast<stp_error_code>(v)));
    EXPECT_STREQ("?", stp_unknown_reason_name(static_cast<stp_unknown_reason>(v)));
    EXPECT_STREQ("?", stp_result_kind_name(static_cast<stp_result_kind>(v)));
    EXPECT_STREQ("?", stp_validity_name(static_cast<stp_validity>(v)));
    EXPECT_EQ(nullptr, stp_option_name(static_cast<stp_option>(v)));
    ASSERT_NE(nullptr, stp_last_error());
    EXPECT_EQ(STP_ERR_OPTION_UNKNOWN, stp_last_error()->code);
    stp_clear_last_error();
  }
  stp_tm_release_all(tm);
  stp_tm_release(tm);
}

// A NULL assumption -- most often a lookup that found nothing, which
// stp_tm_symbol answers with NULL and no record -- failed the check with no
// error recorded anywhere. It is recorded as the NULL formula of
// stp_solver_assert and stp_solver_entails is, and the solver is not failed.
TEST(c_runtime, a_null_assumption_is_an_error_of_the_check)
{
  stp_tm tm = stp_tm_new(nullptr);
  stp_term x = stp_declare(tm, "x", stp_mk_bool_sort(tm));
  stp_solver s = stp_solver_new(tm, nullptr);
  const stp_term assumptions[] = {x, stp_tm_symbol(tm, "no_such_name")};
  ASSERT_EQ(nullptr, assumptions[1]);
  EXPECT_EQ(nullptr, stp_tm_error(tm));
  stp_result r;
  EXPECT_EQ(STP_ERROR, stp_solver_check_sat_assuming(s, 2, assumptions, &r));
  const stp_error* e = stp_tm_error(tm);
  ASSERT_NE(nullptr, e);
  EXPECT_EQ(STP_ERR_NULL_HANDLE, e->code);
  EXPECT_EQ(2, e->argument_index);
  EXPECT_NE(std::string::npos, std::string(e->message).find("assumption 1")) << e->message;
  stp_tm_clear_error(tm);
  stp_budget b = {false, 0, false, 0};
  EXPECT_EQ(STP_ERROR, stp_solver_check_sat_budget(s, 2, assumptions, &b, &r));
  EXPECT_EQ(STP_ERR_NULL_HANDLE, code_of(tm));
  EXPECT_EQ(nullptr, stp_solver_failed(s));
  ASSERT_EQ(STP_OK, stp_solver_check_sat_assuming(s, 1, assumptions, &r));
  EXPECT_EQ(STP_SAT, r.kind);
  stp_solver_delete(s);
  stp_tm_release_all(tm);
  stp_tm_release(tm);
}

// The indexed reads answer for the object as it is now: a solver's
// assertions after each assert, push, pop, parse and reset, its unsat
// assumptions after each check, a manager's symbols and declared sorts after
// each declaration (a bind_symbol alias of a listed symbol adds none), a
// model's symbols. They used to rebuild the whole collection for every call,
// so an enumeration of n took time n^2 (16,000 symbols, 16.8 s); they now
// read the manager's own lists, or a view built once per change.
TEST(c_runtime, indexed_reads_follow_every_change)
{
  stp_tm tm = stp_tm_new(nullptr);
  stp_sort b = stp_mk_bool_sort(tm);
  stp_term x = stp_declare(tm, "x", b);
  stp_term y = stp_declare(tm, "y", b);
  ASSERT_EQ(2u, stp_tm_num_symbols(tm));
  EXPECT_EQ(stp_term_id(y), stp_term_id(stp_tm_symbol_at(tm, 1)));
  ASSERT_EQ(STP_OK, stp_tm_bind_symbol(tm, "also_x", x));
  EXPECT_EQ(2u, stp_tm_num_symbols(tm));
  stp_term z = stp_declare(tm, "z", b);
  ASSERT_EQ(3u, stp_tm_num_symbols(tm));
  EXPECT_EQ(stp_term_id(z), stp_term_id(stp_tm_symbol_at(tm, 2)));
  EXPECT_EQ(nullptr, stp_tm_symbol_at(tm, 3));
  EXPECT_EQ(STP_ERR_INDEX_OUT_OF_RANGE, code_of(tm));
  EXPECT_EQ(0u, stp_tm_num_declared_sorts(tm));
  stp_sort u = stp_tm_declare_sort(tm, "U");
  ASSERT_EQ(1u, stp_tm_num_declared_sorts(tm));
  EXPECT_EQ(stp_sort_id(u), stp_sort_id(stp_tm_declared_sort_at(tm, 0)));

  stp_solver s = stp_solver_new(tm, nullptr);
  ASSERT_EQ(STP_OK, stp_solver_assert(s, x));
  ASSERT_EQ(1u, stp_solver_num_assertions(s));
  EXPECT_EQ(stp_term_id(x), stp_term_id(stp_solver_assertion(s, 0)));
  ASSERT_EQ(STP_OK, stp_solver_push(s, 1));
  ASSERT_EQ(STP_OK, stp_solver_assert(s, y));
  ASSERT_EQ(2u, stp_solver_num_assertions(s));
  EXPECT_EQ(stp_term_id(y), stp_term_id(stp_solver_assertion(s, 1)));
  ASSERT_EQ(STP_OK, stp_solver_pop(s, 1));
  ASSERT_EQ(1u, stp_solver_num_assertions(s));
  ASSERT_EQ(STP_OK, stp_solver_parse_smt2(s, "(assert z)", STP_PARSE_DECLARE_AND_ASSERT));
  ASSERT_EQ(2u, stp_solver_num_assertions(s));
  EXPECT_EQ(stp_term_id(z), stp_term_id(stp_solver_assertion(s, 1)));
  ASSERT_EQ(STP_OK, stp_solver_reset_assertions(s));
  EXPECT_EQ(0u, stp_solver_num_assertions(s));

  const stp_term contradiction[] = {x, stp_not(tm, x)};
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat_assuming(s, 2, contradiction, &r));
  ASSERT_EQ(STP_UNSAT, r.kind);
  EXPECT_GE(stp_solver_num_unsat_assumptions(s), 1u);
  ASSERT_EQ(STP_OK, stp_solver_check_sat_assuming(s, 1, contradiction, &r));
  ASSERT_EQ(STP_SAT, r.kind);
  EXPECT_EQ(0u, stp_solver_num_unsat_assumptions(s)); // no longer the last answer's
  EXPECT_EQ(STP_ERR_STATE, code_of(tm));
  stp_model m = stp_solver_model(s);
  ASSERT_NE(nullptr, m);
  const size_t n = stp_model_num_symbols(m);
  EXPECT_GE(n, 1u);
  for (size_t i = 0; i < n; ++i)
    EXPECT_NE(nullptr, stp_model_symbol(m, i));
  EXPECT_EQ(nullptr, stp_model_symbol(m, n));
  EXPECT_EQ(STP_ERR_INDEX_OUT_OF_RANGE, code_of(tm));
  stp_model_release(m);
  stp_solver_delete(s);
  stp_tm_release_all(tm);
  stp_tm_release(tm);
}

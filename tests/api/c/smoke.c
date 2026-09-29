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

/* A pure-C (C99) end-to-end exercise of <stp/stp.h>: the header must compile
 * as C, and every theory, the options, the checks, the model readers, the
 * error record with its callback, the scopes and the failed state must work
 * from C. Mirrors tests/api/cpp/smoke.cpp. */

#include <stp/stp.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;
#define CHECK(cond)                                                            \
  do                                                                           \
  {                                                                            \
    if (!(cond))                                                               \
    {                                                                          \
      printf("FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);                   \
      ++failures;                                                              \
    }                                                                          \
  } while (0)

/* the pending error must carry `code`; then it is cleared */
static void expect_error(stp_tm tm, stp_error_code code)
{
  const stp_error* e = stp_tm_error(tm);
  CHECK(e != NULL);
  if (e != NULL)
  {
    CHECK(e->code == code);
    CHECK(e->message != NULL && strlen(e->message) > 0);
    CHECK(e->function != NULL && strncmp(e->function, "stp_", 4) == 0);
  }
  stp_tm_clear_error(tm);
}

static void on_error(const stp_error* e, void* user)
{
  int* calls = (int*)user;
  ++*calls;
  CHECK(e != NULL && e->message != NULL);
}

static void free_string(char* s)
{
  stp_free(s);
}

/* the printer may |quote| a symbol; both spellings name the same symbol */
static int same_symbol(const char* printed, const char* name)
{
  size_t n = strlen(name);
  if (strcmp(printed, name) == 0)
    return 1;
  return printed[0] == '|' && strncmp(printed + 1, name, n) == 0 && printed[n + 1] == '|' &&
         printed[n + 2] == '\0';
}

/* ------------------------------------------------------------------ */

static void bitvectors_and_errors(void)
{
  stp_tm tm = stp_tm_new(NULL);
  int calls = 0;
  stp_sort bv32, boolean;
  stp_term x, y, three, seven, ten, c, big, neg, keep, bad;
  stp_solver s;
  stp_model m;
  stp_result r;
  stp_entailment en;
  const stp_error* e;
  uint64_t v = 0, xv = 0, yv = 100, limb = 0, limbs[2], id;
  uint8_t bytes[4], bb[16];
  int64_t sv = 0;
  size_t nl = 0;
  stp_kind k;
  stp_sort_kind sk;
  uint32_t w = 0;
  char* text;

  CHECK(tm != NULL);
  CHECK(stp_tm_simplify_enabled(tm));
  CHECK(stp_tm_default_rounding_mode(tm) == STP_RM_RNE);
  stp_tm_set_error_callback(tm, on_error, &calls);
  stp_tm_scope_push(tm);
  CHECK(stp_tm_scope_depth(tm) == 1);

  bv32 = stp_mk_bv_sort(tm, 32);
  boolean = stp_mk_bool_sort(tm);
  x = stp_declare(tm, "x", bv32);
  y = stp_declare(tm, "y", bv32);
  CHECK(x != NULL && y != NULL && x != y);
  CHECK(stp_declare(tm, "x", bv32) == x); /* interned by name */
  text = stp_term_symbol(x);
  CHECK(text != NULL && strcmp(text, "x") == 0);
  free_string(text);
  CHECK(stp_term_get_kind(x, &k) == STP_OK && k == STP_KIND_CONSTANT);
  CHECK(stp_term_is_const(x) && !stp_term_is_value(x));
  CHECK(stp_sort_get_kind(stp_term_sort(x), &sk) == STP_OK && sk == STP_SORT_BV);
  CHECK(stp_sort_bv_size(bv32, &w) == STP_OK && w == 32);
  CHECK(stp_sort_fp_exp_size(bv32, &w) == STP_ERROR);
  expect_error(tm, STP_ERR_INVALID_ARGUMENT);
  id = stp_term_id(x);
  CHECK(id != 0 && stp_tm_term_from_id(tm, id) == x);
  CHECK(stp_term_hash(x) != 0 && stp_term_hash(x) != stp_term_hash(y));
  CHECK(stp_term_same(x, x) && !stp_term_same(x, y));

  three = stp_mk_bv_uint64(tm, 32, 3);
  seven = stp_mk_bv_uint64(tm, 32, 7);
  ten = stp_mk_bv_uint64(tm, 32, 10);
  CHECK(stp_term_is_value(three));
  CHECK(stp_term_to_uint64(three, &v) == STP_OK && v == 3);
  c = stp_eq(tm, stp_bvmul(tm, x, three), seven);
  CHECK(c != NULL);
  CHECK(stp_term_get_kind(c, &k) == STP_OK && k == STP_KIND_EQUAL);
  text = stp_term_str(c);
  CHECK(text != NULL && strstr(text, "bvmul") != NULL);
  free_string(text);

  s = stp_solver_new(tm, NULL);
  CHECK(s != NULL);
  CHECK(stp_solver_assert(s, c) == STP_OK);
  CHECK(stp_solver_assert(s, stp_bvult(tm, y, ten)) == STP_OK);
  CHECK(stp_solver_num_assertions(s) == 2);
  CHECK(stp_solver_assertion(s, 0) == c);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK);
  CHECK(r.kind == STP_SAT && r.reason == STP_REASON_NONE);
  m = stp_solver_model(s);
  CHECK(m != NULL);
  CHECK(stp_model_uint64(m, x, &xv) == STP_OK);
  CHECK(((xv * 3) & 0xffffffffu) == 7);
  CHECK(stp_model_uint64(m, y, &yv) == STP_OK && yv < 10);
  CHECK(stp_model_bv_limbs(m, x, 1, &limb) == STP_OK && limb == xv);
  CHECK(stp_model_bv_bytes(m, x, 4, bytes, true) == STP_OK && bytes[0] == (uint8_t)xv);
  CHECK(stp_model_in_core(m, x));
  CHECK(stp_model_num_symbols(m) >= 1);
  text = stp_model_to_smt2(m);
  CHECK(text != NULL && strstr(text, "define-fun") != NULL);
  free_string(text);
  text = stp_model_bv_string(m, x, 16, true);
  CHECK(text != NULL && strlen(text) == 8);
  free_string(text);
  /* a term built after the check is evaluated over the snapshot */
  CHECK(stp_term_to_uint64(stp_model_value(m, stp_bvmul(tm, x, three)), &v) == STP_OK && v == 7);
  CHECK(stp_term_to_uint64(stp_solver_value(s, stp_bvmul(tm, x, three)), &v) == STP_OK && v == 7);

  /* push / pop */
  CHECK(stp_solver_push(s, 1) == STP_OK);
  CHECK(stp_solver_level(s) == 1);
  CHECK(stp_solver_assert(s, stp_eq(tm, x, stp_mk_bv_uint64(tm, 32, 0))) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_UNSAT);
  CHECK(stp_solver_model(s) == NULL);
  expect_error(tm, STP_ERR_NO_MODEL);
  CHECK(stp_solver_pop(s, 1) == STP_OK);
  CHECK(stp_solver_level(s) == 0);
  CHECK(stp_solver_pop(s, 1) == STP_ERROR); /* below zero: INVALID_ARGUMENT, and the failed state */
  expect_error(tm, STP_ERR_INVALID_ARGUMENT);
  CHECK(stp_solver_failed(s) != NULL && stp_solver_failed(s)->code == STP_ERR_INVALID_ARGUMENT);
  stp_solver_clear_error(s);
  CHECK(stp_solver_failed(s) == NULL);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);

  /* entailment */
  CHECK(stp_solver_entails(s, stp_bvult(tm, y, stp_mk_bv_uint64(tm, 32, 11)), NULL, &en) == STP_OK);
  CHECK(en.kind == STP_VALID);
  CHECK(stp_solver_entails(s, stp_bvult(tm, y, three), NULL, &en) == STP_OK);
  CHECK(en.kind == STP_INVALID);

  /* wide and signed values */
  big = stp_mk_bv_str(tm, 128, "0x0123456789abcdef0123456789abcdef", 16);
  CHECK(big != NULL);
  text = stp_term_to_bv_string(big, 16, true);
  CHECK(text != NULL && strcmp(text, "0123456789abcdef0123456789abcdef") == 0);
  free_string(text);
  CHECK(!stp_term_fits_uint64(big));
  CHECK(stp_term_bv_num_limbs(big, &nl) == STP_OK && nl == 2);
  CHECK(stp_term_to_bv_limbs(big, 2, limbs) == STP_OK);
  CHECK(limbs[0] == 0x0123456789abcdefull && limbs[1] == 0x0123456789abcdefull);
  CHECK(stp_term_to_bv_bytes(big, 16, bb, true) == STP_OK && bb[0] == 0xef && bb[15] == 0x01);
  CHECK(stp_term_to_bv_limbs(big, 1, limbs) == STP_ERROR);
  expect_error(tm, STP_ERR_INVALID_ARGUMENT);
  CHECK(stp_term_to_uint64(big, &v) == STP_ERROR);
  expect_error(tm, STP_ERR_DOES_NOT_FIT);
  CHECK(stp_term_to_uint64(x, &v) == STP_ERROR); /* not a value */
  expect_error(tm, STP_ERR_NOT_A_VALUE);
  neg = stp_mk_bv_int64(tm, 8, -2);
  CHECK(stp_term_to_int64(neg, &sv) == STP_OK && sv == -2);
  CHECK(stp_term_to_uint64(neg, &v) == STP_OK && v == 254);
  text = stp_term_to_bv_string(neg, 2, true);
  CHECK(text != NULL && strcmp(text, "11111110") == 0);
  free_string(text);
  CHECK(stp_mk_bv_limbs(tm, 128, 2, limbs) == big);
  CHECK(stp_mk_bv_bytes(tm, 128, 16, bb, true) == big);

  /* the error record: the first error is kept, the callback sees every one */
  calls = 0;
  bad = stp_bvadd(tm, x, stp_declare(tm, "b", boolean));
  CHECK(bad == NULL);
  e = stp_tm_error(tm);
  CHECK(e != NULL && e->code == STP_ERR_SORT_MISMATCH && e->recoverable);
  CHECK(calls == 1);
  CHECK(stp_tm_error_num_terms(tm) >= 1);
  CHECK(stp_tm_error_term(tm, 0) != NULL);
  CHECK(stp_mk_bv_uint64(tm, 8, 256) == NULL);
  CHECK(calls == 2);
  e = stp_tm_error(tm);
  CHECK(e != NULL && e->code == STP_ERR_SORT_MISMATCH); /* still the first */
  stp_tm_clear_error(tm);
  CHECK(stp_tm_error(tm) == NULL);
  CHECK(stp_mk_bv_uint64(tm, 8, 256) == NULL);
  e = stp_tm_error(tm);
  CHECK(e != NULL && e->code == STP_ERR_VALUE_OUT_OF_RANGE);
  CHECK(e != NULL && strcmp(e->function, "stp_mk_bv_uint64") == 0);
  stp_tm_clear_error(tm);
  CHECK(stp_declare(tm, "x", stp_mk_bv_sort(tm, 8)) == NULL); /* the name is taken at another sort */
  expect_error(tm, STP_ERR_SORT_MISMATCH);

  /* NULL propagation: no record, no callback */
  calls = 0;
  CHECK(stp_bvadd(tm, NULL, x) == NULL);
  CHECK(stp_eq(tm, stp_bvadd(tm, NULL, x), x) == NULL);
  CHECK(stp_term_to_uint64(NULL, &v) == STP_ERROR);
  CHECK(stp_term_str(NULL) == NULL);
  CHECK(!stp_term_is_value(NULL));
  CHECK(stp_tm_error(tm) == NULL && calls == 0);
  /* a NULL out-pointer is NULL_HANDLE */
  CHECK(stp_term_to_uint64(three, NULL) == STP_ERROR);
  expect_error(tm, STP_ERR_NULL_HANDLE);

  /* the failed state: a dropped assertion can never be silent */
  CHECK(stp_solver_assert(s, NULL) == STP_ERROR);
  expect_error(tm, STP_ERR_NULL_HANDLE);
  CHECK(stp_solver_failed(s) != NULL && stp_solver_failed(s)->code == STP_ERR_NULL_HANDLE);
  CHECK(stp_solver_check_sat(s, &r) == STP_ERROR);
  expect_error(tm, STP_ERR_STATE);
  CHECK(stp_solver_model(s) == NULL);
  expect_error(tm, STP_ERR_STATE);
  CHECK(stp_solver_value(s, x) == NULL);
  expect_error(tm, STP_ERR_STATE);
  /* readers, constructors and printers keep working in the failed state */
  CHECK(stp_bvadd(tm, x, y) != NULL);
  text = stp_solver_to_smt2(s, true);
  CHECK(text != NULL && strstr(text, "(check-sat)") != NULL);
  free_string(text);
  CHECK(stp_solver_num_assertions(s) >= 1); /* the engine may have conjoined the level by now */
  CHECK(stp_tm_error(tm) == NULL);
  stp_solver_clear_error(s);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);
  /* a sort mismatch in an assert fails the solver too */
  CHECK(stp_solver_assert(s, x) == STP_ERROR);
  expect_error(tm, STP_ERR_SORT_MISMATCH);
  CHECK(stp_solver_failed(s) != NULL && stp_solver_failed(s)->code == STP_ERR_SORT_MISMATCH);
  stp_solver_clear_error(s);

  /* scopes: a scoped handle cannot be released; a copy survives the scope */
  CHECK(stp_term_release(x) == STP_ERROR);
  expect_error(tm, STP_ERR_STATE);
  keep = stp_term_copy(x);
  CHECK(keep == x);
  stp_tm_scope_pop(tm);
  CHECK(stp_tm_scope_depth(tm) == 0);
  text = stp_term_str(keep);
  CHECK(text != NULL && same_symbol(text, "x"));
  free_string(text);
  CHECK(stp_term_release(keep) == STP_OK);
  CHECK(stp_term_release(keep) == STP_ERROR); /* no unscoped reference left */
  expect_error(tm, STP_ERR_STATE);

  stp_model_release(m);
  stp_solver_delete(s);
  stp_tm_release(tm);
}

static void arrays(void)
{
  stp_tm tm = stp_tm_new(NULL);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8), bv32 = stp_mk_bv_sort(tm, 32);
  stp_sort arr = stp_mk_array_sort(tm, bv32, bv8);
  stp_term a, i, kk, ks, fb, b;
  stp_solver s;
  stp_model m;
  stp_result r;
  stp_array_value av;
  uint64_t v = 0;
  uint8_t bytes[4] = {0, 0, 0, 0};
  const uint8_t data[3] = {1, 2, 3};
  stp_term index, element;

  stp_tm_scope_push(tm);
  CHECK(arr != NULL && stp_sort_array_index(arr) == bv32 && stp_sort_array_element(arr) == bv8);
  a = stp_declare(tm, "a", arr);
  i = stp_declare(tm, "i", bv32);
  s = stp_solver_new(tm, NULL);
  CHECK(stp_solver_assert(s, stp_eq(tm, stp_select(tm, a, i), stp_mk_bv_uint64(tm, 8, 42))) == STP_OK);
  CHECK(stp_solver_assert(
            s, stp_eq(tm,
                      stp_select(tm,
                                 stp_store(tm, a, stp_bvadd(tm, i, stp_mk_bv_uint64(tm, 32, 1)),
                                           stp_mk_bv_uint64(tm, 8, 7)),
                                 i),
                      stp_mk_bv_uint64(tm, 8, 42))) == STP_OK);
  CHECK(stp_solver_assert(s, stp_eq(tm, i, stp_mk_bv_uint64(tm, 32, 5))) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);
  m = stp_solver_model(s);
  CHECK(m != NULL);
  CHECK(stp_model_uint64(m, stp_select(tm, a, stp_mk_bv_uint64(tm, 32, 5)), &v) == STP_OK && v == 42);
  av = stp_model_array_value(m, a);
  CHECK(av != NULL && stp_array_value_size(av) >= 1);
  CHECK(stp_array_value_entry(av, 0, &index, &element) == STP_OK);
  CHECK(index != NULL && element != NULL && stp_term_is_value(index) && stp_term_is_value(element));
  CHECK(stp_array_value_default(av) != NULL);
  CHECK(stp_array_value_as_term(av) != NULL);
  CHECK(stp_array_value_sort(av) == arr);
  CHECK(stp_model_array_bytes(m, a, 4, 4, bytes) == STP_OK && bytes[1] == 42);
  stp_array_value_release(av);

  /* constant arrays */
  kk = stp_mk_const_array(tm, arr, stp_mk_bv_uint64(tm, 8, 9));
  CHECK(kk != NULL);
  CHECK(stp_term_to_uint64(stp_select(tm, kk, i), &v) == STP_OK && v == 9);
  ks = stp_store(tm, kk, stp_mk_bv_uint64(tm, 32, 1), stp_mk_bv_uint64(tm, 8, 3));
  CHECK(stp_term_to_uint64(stp_select(tm, ks, stp_mk_bv_uint64(tm, 32, 1)), &v) == STP_OK && v == 3);
  CHECK(stp_term_to_uint64(stp_select(tm, ks, stp_mk_bv_uint64(tm, 32, 2)), &v) == STP_OK && v == 9);
  fb = stp_array_from_bytes(tm, 3, data, 32);
  CHECK(fb != NULL);
  CHECK(stp_term_to_uint64(stp_select(tm, fb, stp_mk_bv_uint64(tm, 32, 2)), &v) == STP_OK && v == 3);

  /* extensional equality */
  b = stp_declare(tm, "b", arr);
  CHECK(stp_solver_reset_assertions(s) == STP_OK);
  CHECK(stp_solver_assert(s, stp_eq(tm, a, stp_store(tm, b, i, stp_mk_bv_uint64(tm, 8, 1)))) == STP_OK);
  CHECK(stp_solver_assert(s, stp_eq(tm, stp_select(tm, b, i), stp_mk_bv_uint64(tm, 8, 2))) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);
  CHECK(stp_term_to_uint64(stp_solver_value(s, stp_select(tm, a, i)), &v) == STP_OK && v == 1);
  CHECK(stp_solver_assert(s, stp_eq(tm, stp_select(tm, a, i), stp_mk_bv_uint64(tm, 8, 2))) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_UNSAT);

  stp_model_release(m);
  stp_solver_delete(s);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

static void floats(void)
{
  stp_tm tm = stp_tm_new(NULL);
  stp_sort f32 = stp_mk_fp32_sort(tm);
  stp_term x, one, tenth, third, three, rm, bits, back, i, conv, ub, fpfp, r2fp, nan;
  stp_solver s;
  stp_model m;
  stp_result r;
  stp_float_value fv;
  double d = 0;
  uint64_t sl = 0, v = 0;
  uint32_t e = 0, sg = 0, idx = 0;
  size_t n = 0;
  bool bt = false;
  stp_rm rmv = STP_RM_RTP;
  stp_kind k;
  char *text, *num, *den;

  stp_tm_scope_push(tm);
  CHECK(stp_sort_fp_exp_size(f32, &e) == STP_OK && e == 8);
  CHECK(stp_sort_fp_sig_size(f32, &sg) == STP_OK && sg == 24);
  x = stp_declare(tm, "fx", f32);
  one = stp_mk_fp_double(tm, f32, STP_RM_RNE, 1.0);
  CHECK(one != NULL && stp_term_is_value(one));
  CHECK(stp_term_to_fp(one, &fv) == STP_OK);
  CHECK(fv.exp_size == 8 && fv.sig_size == 24 && !fv.sign && fv.biased_exponent == 127 && fv.cls == STP_FP_NORMAL);
  CHECK(stp_term_fp_significand_limbs(one, 1, &sl) == STP_OK && sl == 0);
  CHECK(stp_term_fp_to_double(one, &d) == STP_OK && d == 1.0);
  text = stp_term_fp_bits(one);
  CHECK(text != NULL && strcmp(text, "00111111100000000000000000000000") == 0);
  free_string(text);
  CHECK(stp_term_fp_to_rational(one, &num, &den) == STP_OK);
  CHECK(strcmp(num, "1") == 0 && strcmp(den, "1") == 0);
  free_string(num);
  free_string(den);
  tenth = stp_mk_fp_decimal(tm, f32, STP_RM_RNE, "0.1");
  CHECK(stp_term_fp_to_double(tenth, &d) == STP_OK && (float)d == 0.1f);
  third = stp_mk_fp_decimal(tm, f32, STP_RM_RTZ, "1/3");
  CHECK(stp_term_to_fp(third, &fv) == STP_OK && fv.cls == STP_FP_NORMAL);
  three = stp_mk_fp_double(tm, f32, STP_RM_RNE, 3.0);

  s = stp_solver_new(tm, NULL);
  CHECK(stp_solver_assert(s, stp_eq(tm, stp_fp_add_rm(tm, STP_RM_RNE, x, one), three)) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);
  m = stp_solver_model(s);
  CHECK(m != NULL);
  CHECK(stp_model_fp(m, x, &fv) == STP_OK && fv.cls == STP_FP_NORMAL);
  CHECK(stp_model_fp_to_double(m, x, &d) == STP_OK);
  {
    /* through a volatile float: x87 keeps the sum in extended precision otherwise */
    volatile float sum = (float)d + 1.0f;
    CHECK(sum == 3.0f);
  }
  CHECK(stp_model_fp_significand_limbs(m, x, 1, &sl) == STP_OK);
  CHECK(stp_term_fp_to_double(stp_model_value(m, stp_fp_add_rm(tm, STP_RM_RNE, x, one)), &d) == STP_OK && d == 3.0);
  stp_model_release(m);

  nan = stp_mk_fp_nan(tm, f32);
  CHECK(stp_term_to_bool(stp_fp_is_nan(tm, nan), &bt) == STP_OK && bt);
  CHECK(stp_term_to_fp(stp_mk_fp_neg_zero(tm, f32), &fv) == STP_OK && fv.sign && fv.cls == STP_FP_ZERO);
  CHECK(stp_term_to_fp(stp_mk_fp_pos_inf(tm, f32), &fv) == STP_OK && fv.cls == STP_FP_INFINITY);
  CHECK(stp_term_fp_to_rational(nan, &num, &den) == STP_ERROR);
  stp_tm_clear_error(tm);

  rm = stp_declare(tm, "rm", stp_mk_rm_sort(tm));
  CHECK(stp_solver_reset_assertions(s) == STP_OK);
  CHECK(stp_solver_assert(s, stp_eq(tm, stp_fp_add(tm, rm, one, tenth), stp_fp_add_rm(tm, STP_RM_RTP, one, tenth))) == STP_OK);
  CHECK(stp_solver_assert(s, stp_not(tm, stp_eq(tm, rm, stp_mk_rm(tm, STP_RM_RTP)))) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);
  m = stp_solver_model(s);
  CHECK(stp_model_rm(m, rm, &rmv) == STP_OK && rmv != STP_RM_RTP);
  CHECK(stp_term_to_rm(stp_mk_rm(tm, STP_RM_RTN), &rmv) == STP_OK && rmv == STP_RM_RTN);
  stp_model_release(m);

  bits = stp_fp_to_ieee_bv(tm, one);
  CHECK(bits != NULL && stp_term_to_uint64(bits, &v) == STP_OK && v == 0x3f800000u);
  back = stp_to_fp_from_bits(tm, f32, bits);
  CHECK(back == one);
  CHECK(stp_mk_fp_from_bits(tm, f32, bits) == one);
  CHECK(stp_mk_fp_from_bits_str(tm, f32, "0x3f800000") == one);
  i = stp_declare(tm, "fi", stp_mk_bv_sort(tm, 32));
  conv = stp_to_fp_rm(tm, f32, STP_RM_RNE, i);
  CHECK(conv != NULL);
  CHECK(stp_term_get_kind(conv, &k) == STP_OK && k == STP_KIND_FP_TO_FP_FROM_SBV);
  CHECK(stp_term_num_indices(conv, &n) == STP_OK && n == 2);
  CHECK(stp_term_index(conv, 1, &idx) == STP_OK && idx == 24);
  CHECK(stp_term_index(conv, 2, &idx) == STP_ERROR);
  stp_tm_clear_error(tm);
  ub = stp_fp_to_ubv_rm(tm, 8, STP_RM_RTZ, x);
  CHECK(ub != NULL && stp_sort_bv_size(stp_term_sort(ub), &e) == STP_OK && e == 8);
  fpfp = stp_mk_fp(tm, stp_mk_bv_uint64(tm, 1, 0), stp_mk_bv_uint64(tm, 8, 127), stp_mk_bv_uint64(tm, 23, 0));
  CHECK(fpfp == one);
  r2fp = stp_to_fp_rm(tm, f32, STP_RM_RNE, stp_mk_real_str(tm, "1/4"));
  CHECK(r2fp != NULL && stp_term_fp_to_double(r2fp, &d) == STP_OK && d == 0.25);
  {
    /* a float value converts exactly to a Real value; a symbolic float
       converts to a Real term the solver decides */
    stp_term r1 = stp_fp_to_real(tm, one);
    stp_term rx = stp_fp_to_real(tm, x);
    stp_term child = NULL;
    stp_sort_kind sk;
    stp_kind rk;
    size_t nk = 0;
    char* num;
    char* text;
    CHECK(r1 != NULL && stp_sort_get_kind(stp_term_sort(r1), &sk) == STP_OK && sk == STP_SORT_REAL);
    num = stp_term_real_numerator(r1);
    CHECK(num != NULL && strcmp(num, "1") == 0);
    stp_free(num);
    CHECK(rx != NULL && stp_term_get_kind(rx, &rk) == STP_OK && rk == STP_KIND_FP_TO_REAL);
    CHECK(stp_term_num_children(rx, &nk) == STP_OK && nk == 1);
    child = stp_term_child(rx, 0);
    CHECK(child == x);
    text = stp_term_str(rx);
    CHECK(text != NULL && strcmp(text, "(fp.to_real fx)") == 0);
    stp_free(text);
    /* the conversion is exact: -5/2 is -2.5 and nothing else that is normal
       (NaN and the infinities convert to values of their own choosing) */
    CHECK(stp_solver_reset_assertions(s) == STP_OK);
    CHECK(stp_solver_assert(s, stp_eq(tm, rx, stp_mk_real_str(tm, "-5/2"))) == STP_OK);
    CHECK(stp_solver_assert(s, stp_fp_is_normal(tm, x)) == STP_OK);
    CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);
    m = stp_solver_model(s);
    CHECK(stp_model_fp_to_double(m, x, &d) == STP_OK && d == -2.5);
    num = stp_term_real_numerator(stp_model_value(m, rx));
    CHECK(num != NULL && strcmp(num, "-5") == 0);
    stp_free(num);
    stp_model_release(m);
    CHECK(stp_solver_assert(s, stp_not(tm, stp_fp_eq(tm, x, stp_mk_fp_double(tm, f32, STP_RM_RNE, -2.5)))) == STP_OK);
    CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_UNSAT);
  }

  stp_solver_delete(s);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

static void uninterpreted(void)
{
  stp_tm tm = stp_tm_new(NULL);
  stp_sort bv8 = stp_mk_bv_sort(tm, 8);
  stp_sort dom[2];
  stp_sort fs, S;
  stp_term f, a, b, fa, fba, args[3], vals[2], p, q, else_value;
  stp_solver s;
  stp_model m;
  stp_result r;
  stp_fun_value fv;
  uint64_t v = 0, pi = 0, qi = 0;
  uint32_t arity = 0;
  char* text;

  stp_tm_scope_push(tm);
  dom[0] = bv8;
  dom[1] = bv8;
  fs = stp_mk_fun_sort(tm, 2, dom, bv8);
  CHECK(fs != NULL);
  CHECK(stp_sort_fun_arity(fs, &arity) == STP_OK && arity == 2);
  CHECK(stp_sort_fun_domain(fs, 1) == bv8 && stp_sort_fun_codomain(fs) == bv8);
  CHECK(stp_sort_fun_domain(fs, 2) == NULL);
  expect_error(tm, STP_ERR_INDEX_OUT_OF_RANGE);
  f = stp_declare(tm, "f", fs);
  a = stp_declare(tm, "ua", bv8);
  b = stp_declare(tm, "ub", bv8);
  args[0] = f;
  args[1] = a;
  args[2] = b;
  fa = stp_apply_n(tm, 3, args);
  CHECK(fa != NULL);
  args[1] = b;
  args[2] = a;
  fba = stp_apply_n(tm, 3, args);
  CHECK(fba != NULL && fba != fa);
  s = stp_solver_new(tm, NULL);
  CHECK(stp_solver_assert(s, stp_eq(tm, fa, stp_mk_bv_uint64(tm, 8, 3))) == STP_OK);
  CHECK(stp_solver_assert(s, stp_eq(tm, fba, stp_mk_bv_uint64(tm, 8, 4))) == STP_OK);
  CHECK(stp_solver_assert(s, stp_eq(tm, a, b)) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_UNSAT);
  CHECK(stp_solver_reset_assertions(s) == STP_OK);
  CHECK(stp_solver_assert(s, stp_eq(tm, fa, stp_mk_bv_uint64(tm, 8, 3))) == STP_OK);
  CHECK(stp_solver_assert(s, stp_eq(tm, fba, stp_mk_bv_uint64(tm, 8, 4))) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);
  m = stp_solver_model(s);
  CHECK(stp_model_uint64(m, fa, &v) == STP_OK && v == 3);
  fv = stp_model_fun_value(m, f);
  CHECK(fv != NULL);
  CHECK(stp_fun_value_arity(fv) == 2);
  CHECK(stp_fun_value_sort(fv) == fs);
  else_value = stp_fun_value_else(fv);
  CHECK(else_value != NULL && stp_term_is_value(else_value));
  vals[0] = stp_model_value(m, a);
  vals[1] = stp_model_value(m, b);
  CHECK(stp_term_to_uint64(stp_fun_value_apply(fv, 2, vals), &v) == STP_OK && v == 3);
  text = stp_model_to_smt2(m);
  CHECK(text != NULL && strstr(text, "f") != NULL);
  free_string(text);
  stp_fun_value_release(fv);
  stp_model_release(m);

  /* declared sorts */
  S = stp_tm_declare_sort(tm, "S");
  CHECK(S != NULL && stp_tm_num_declared_sorts(tm) == 1 && stp_tm_declared_sort_at(tm, 0) == S);
  text = stp_sort_name(S);
  CHECK(text != NULL && strcmp(text, "S") == 0);
  free_string(text);
  p = stp_declare(tm, "p", S);
  q = stp_declare(tm, "q", S);
  CHECK(stp_solver_reset_assertions(s) == STP_OK);
  CHECK(stp_solver_assert(s, stp_distinct2(tm, p, q)) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);
  m = stp_solver_model(s);
  CHECK(stp_model_uninterpreted_index(m, p, &pi) == STP_OK);
  CHECK(stp_model_uninterpreted_index(m, q, &qi) == STP_OK);
  CHECK(pi != qi);
  stp_model_release(m);

  stp_solver_delete(s);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

static void reals(void)
{
  stp_tm tm = stp_tm_new(NULL);
  stp_sort R = stp_mk_real_sort(tm);
  stp_term x, y, half, one;
  stp_solver s;
  stp_model m;
  stp_result r;
  char* text;
  int64_t num = 0, den = 0;
  double d = 0;

  stp_tm_scope_push(tm);
  x = stp_declare(tm, "rx", R);
  y = stp_declare(tm, "ry", R);
  s = stp_solver_new(tm, NULL);
  CHECK(stp_solver_assert(s, stp_eq(tm, stp_real_add(tm, x, y), stp_mk_real_int64(tm, 3))) == STP_OK);
  CHECK(stp_solver_assert(s, stp_real_lt(tm, x, y)) == STP_OK);
  CHECK(stp_solver_assert(s, stp_eq(tm, stp_real_mul(tm, x, stp_mk_real_int64(tm, 2)), y)) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);
  m = stp_solver_model(s);
  text = stp_model_real_numerator(m, x);
  CHECK(text != NULL && strcmp(text, "1") == 0);
  free_string(text);
  text = stp_model_real_denominator(m, x);
  CHECK(text != NULL && strcmp(text, "1") == 0);
  free_string(text);
  text = stp_model_real_numerator(m, y);
  CHECK(text != NULL && strcmp(text, "2") == 0);
  free_string(text);
  stp_model_release(m);
  CHECK(stp_solver_assert(s, stp_real_gt(tm, x, stp_mk_real_int64(tm, 5))) == STP_OK);
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_UNSAT);

  half = stp_mk_real_fraction(tm, 1, 2);
  CHECK(half != NULL && stp_term_real_fits_int64(half));
  CHECK(stp_term_real_to_int64(half, &num, &den) == STP_OK && num == 1 && den == 2);
  CHECK(stp_term_real_to_double(half, &d) == STP_OK && d == 0.5);
  one = stp_mk_real_str(tm, "0.25");
  CHECK(one != NULL && stp_term_real_to_double(one, &d) == STP_OK && d == 0.25);
  CHECK(stp_mk_real_fraction(tm, 1, 0) == NULL);
  expect_error(tm, STP_ERR_INVALID_ARGUMENT);

  stp_solver_delete(s);
  stp_tm_scope_pop(tm);
  stp_tm_release(tm);
}

static void cnf_sink(const char* text, size_t len, void* user)
{
  int* seen = (int*)user;
  if (len > 0 && strstr(text, "p cnf") != NULL)
    *seen = 1;
}

static void options_and_limits(void)
{
  stp_tm tm = stp_tm_new(NULL);
  stp_options o = stp_options_new();
  stp_options copy;
  stp_solver s;
  stp_term x;
  stp_result r;
  stp_budget budget;
  stp_statistics st;
  const stp_error* e;
  const char* argv[2];
  uint64_t ms = 0;
  bool b = false, has_min = false, has_max = false;
  int64_t lo = 0, hi = 0;
  int seen = 0;
  stp_option opt;
  char* text;
  /* a backend this build has (CI builds each backend on its own) */
  const char* backend = stp_sat_backend_name(0);

  CHECK(o != NULL);
  CHECK(stp_options_set_bool(o, "produce-models", true) == STP_OK);
  CHECK(stp_options_set_str(o, "max-time", "2s") == STP_OK);
  CHECK(stp_options_get_duration_ms(o, "max-time", &ms) == STP_OK && ms == 2000);
  CHECK(stp_options_set_uint64(o, "max-num-confl", 1000000) == STP_OK);
  CHECK(backend != NULL);
  CHECK(stp_options_set_str_e(o, STP_OPT_SAT_BACKEND, backend) == STP_OK);
  text = stp_options_get_str(o, "sat-backend");
  CHECK(text != NULL && strcmp(text, backend) == 0);
  free_string(text);
  CHECK(stp_options_is_set(o, "sat-backend") && !stp_options_is_set(o, "logic"));
  argv[0] = "--fp-abstraction";
  argv[1] = "--bb.div-v3=false";
  CHECK(stp_options_set_args(o, 2, argv) == STP_OK);
  CHECK(stp_options_get_bool(o, "fp-abstraction", &b) == STP_OK && b);
  CHECK(stp_options_get_bool(o, "bb.div-v3", &b) == STP_OK && !b);
  CHECK(stp_options_set_str(o, "no-such-option", "1") == STP_ERROR);
  e = stp_options_error(o);
  CHECK(e != NULL && e->code == STP_ERR_OPTION_UNKNOWN);
  CHECK(stp_options_set_bool(o, "max-time", true) == STP_ERROR);
  CHECK(stp_options_error(o)->code == STP_ERR_OPTION_UNKNOWN); /* the first is kept */
  stp_options_clear_error(o);
  CHECK(stp_options_error(o) == NULL);
  CHECK(stp_options_set_bool(o, "max-time", true) == STP_ERROR);
  e = stp_options_error(o);
  CHECK(e != NULL && e->code == STP_ERR_OPTION_VALUE && e->option != NULL && strcmp(e->option, "max-time") == 0);
  stp_options_clear_error(o);
  copy = stp_options_copy(o);
  CHECK(copy != NULL && stp_options_error(copy) == NULL);
  text = stp_options_get_str(copy, "sat-backend");
  CHECK(text != NULL && strcmp(text, backend) == 0);
  free_string(text);
  stp_options_delete(copy);
  CHECK(stp_options_resolve(o) == STP_OK);
  text = stp_options_resolved_str(o, "produce-models");
  CHECK(text != NULL);
  free_string(text);

  /* the registry */
  CHECK(stp_options_num_names(STP_TIER_STABLE) == STP_NUM_STABLE_OPTIONS);
  CHECK(stp_options_num_names(-1) > stp_options_num_names(STP_TIER_STABLE));
  CHECK(stp_options_name(STP_TIER_STABLE, 0) != NULL);
  CHECK(stp_options_name(STP_TIER_STABLE, 100000) == NULL);
  CHECK(strcmp(stp_option_name(STP_OPT_SAT_BACKEND), "sat-backend") == 0);
  CHECK(stp_option_name((stp_option)999) == NULL);
  CHECK(stp_option_from_name("sat-backend", &opt) == STP_OK && opt == STP_OPT_SAT_BACKEND);
  CHECK(strcmp(stp_option_info_type("max-time"), "duration") == 0);
  CHECK(stp_option_info_tier("incremental") == STP_TIER_STABLE);
  CHECK(stp_option_info_scope("simplify") == STP_SCOPE_MANAGER);
  CHECK(stp_option_info_settable("sat-backend") == STP_SETTABLE_CONSTRUCTION);
  CHECK(stp_option_info_num_values("sat-backend") >= 3);
  CHECK(strcmp(stp_option_info_value("sat-backend", 0), "auto") == 0);
  CHECK(stp_option_info_help("max-time") != NULL);
  CHECK(stp_option_info_category("max-time") != NULL);
  CHECK(stp_option_info_python_key("max-time") != NULL);
  CHECK(stp_option_info_short("max-time") != NULL);
  CHECK(stp_option_info_negation("max-time") != NULL);
  CHECK(stp_option_info_range("uf-sort-width", &has_min, &lo, &has_max, &hi) == STP_OK);
  text = stp_option_info_default("sat-backend");
  CHECK(text != NULL && strcmp(text, "auto") == 0);
  free_string(text);
  CHECK(stp_option_info_type("no-such-option") == NULL);
  CHECK(stp_last_error() != NULL && stp_last_error()->code == STP_ERR_OPTION_UNKNOWN);
  text = stp_options_help(STP_TIER_STABLE);
  CHECK(text != NULL && strstr(text, "sat-backend") != NULL);
  free_string(text);

  /* the live options of a solver */
  s = stp_solver_new(tm, o);
  CHECK(s != NULL);
  CHECK(stp_solver_set_str(s, "logic", "QF_BV") == STP_OK); /* before the first check: allowed */
  text = stp_solver_get_str(s, "logic");
  CHECK(text != NULL && strcmp(text, "QF_BV") == 0);
  free_string(text);
  CHECK(stp_solver_option_is_set(s, "logic"));
  CHECK(stp_solver_set_str(s, "sat-backend", backend) == STP_ERROR); /* construction-only */
  e = stp_tm_error(tm);
  CHECK(e != NULL && e->code == STP_ERR_OPTION_TIMING);
  stp_tm_clear_error(tm);
  /* an option write that failed put the solver into the failed state */
  CHECK(stp_solver_failed(s) != NULL && stp_solver_failed(s)->code == STP_ERR_OPTION_TIMING);
  CHECK(stp_solver_check_sat(s, &r) == STP_ERROR);
  expect_error(tm, STP_ERR_STATE);
  stp_solver_clear_error(s);
  CHECK(stp_solver_get_duration_ms(s, "max-time", &ms) == STP_OK && ms == 2000);
  copy = stp_solver_options_copy(s);
  CHECK(copy != NULL);
  CHECK(stp_options_get_duration_ms(copy, "max-time", &ms) == STP_OK && ms == 2000);
  stp_options_delete(copy);

  x = stp_declare(tm, "ox", stp_mk_bv_sort(tm, 64));
  CHECK(stp_solver_assert(s, stp_eq(tm, stp_bvmul(tm, x, x), stp_mk_bv_uint64(tm, 64, 1))) == STP_OK);
  budget.has_time = true;
  budget.time_ms = 0;
  budget.has_conflicts = false;
  budget.conflicts = 0;
  CHECK(stp_solver_check_sat_budget(s, 0, NULL, &budget, &r) == STP_OK);
  CHECK(r.kind == STP_UNKNOWN && r.reason == STP_REASON_TIMEOUT);
  text = stp_solver_last_reason_message(s);
  CHECK(text != NULL && strlen(text) > 0);
  free_string(text);
  CHECK(stp_solver_set_str(s, "logic", "QF_ABV") == STP_ERROR); /* after a check: refused, unchanged */
  expect_error(tm, STP_ERR_OPTION_TIMING);
  stp_solver_clear_error(s);
  text = stp_solver_get_str(s, "logic");
  CHECK(text != NULL && strcmp(text, "QF_BV") == 0);
  free_string(text);
  CHECK(stp_solver_set_duration_ms(s, "max-time", 30000) == STP_OK); /* anytime */
  stp_solver_interrupt(s);
  CHECK(stp_solver_interrupt_pending(s));
  CHECK(stp_solver_check_sat(s, &r) == STP_OK);
  CHECK(r.kind == STP_UNKNOWN && r.reason == STP_REASON_INTERRUPTED);
  CHECK(!stp_solver_interrupt_pending(s));
  CHECK(stp_solver_check_sat(s, &r) == STP_OK && r.kind == STP_SAT);
  st = stp_solver_statistics(s);
  CHECK(st != NULL && stp_statistics_size(st) > 0);
  text = stp_statistics_str(st, "sat.backend");
  CHECK(text != NULL && strcmp(text, backend) == 0);
  free_string(text);
  CHECK(stp_statistics_is_uint64(st, "checks.total") && !stp_statistics_is_uint64(st, "sat.backend"));
  CHECK(stp_statistics_uint64(st, "checks.total", &ms) == STP_OK && ms >= 3);
  CHECK(stp_statistics_name(st, 0) != NULL);
  CHECK(stp_statistics_tier("checks.total") == STP_TIER_STABLE);
  stp_statistics_release(st);
  stp_cnf_scope scope = STP_CNF_PARTIAL;
  CHECK(stp_solver_write_cnf(s, cnf_sink, &seen, &scope) == STP_OK && seen == 1 && scope == STP_CNF_WHOLE);
  seen = 0;
  CHECK(stp_solver_write_cnf(s, cnf_sink, &seen, NULL) == STP_OK && seen == 1);

  /* the thread-local record for calls with no object */
  CHECK(stp_tm_new_with(true, (stp_rm)99, 16) == NULL);
  CHECK(stp_last_error() != NULL && stp_last_error()->code == STP_ERR_INVALID_ARGUMENT);
  CHECK(stp_tm_new_with(true, STP_RM_RNE, 0) == NULL);
  CHECK(stp_last_error() != NULL && stp_last_error()->code == STP_ERR_INVALID_ARGUMENT);
  CHECK(stp_tm_new_with(true, STP_RM_RNE, 1025) == NULL);
  CHECK(stp_last_error() != NULL && stp_last_error()->code == STP_ERR_INVALID_ARGUMENT &&
        stp_last_error()->argument_index == 2);
  CHECK(stp_options_set_str(NULL, "logic", "QF_BV") == STP_ERROR);
  CHECK(stp_last_error() != NULL && stp_last_error()->code == STP_ERR_NULL_HANDLE);
  CHECK(stp_solver_check_sat(NULL, &r) == STP_ERROR);
  CHECK(stp_last_error()->code == STP_ERR_NULL_HANDLE);

  stp_solver_delete(s);
  stp_options_delete(o);
  stp_tm_release(tm);
}

static void library(void)
{
  stp_version v = stp_get_version();
  char* text;
  size_t n, i;
  CHECK(v.string != NULL && strlen(v.string) > 0);
  CHECK(v.git_sha != NULL && v.build_info != NULL);
  text = stp_capability("api.version");
  CHECK(text != NULL && strcmp(text, "3.0.0-alpha") == 0);
  free_string(text);
  CHECK(stp_capability("no.such.key") == NULL);
  text = stp_capabilities();
  CHECK(text != NULL && strstr(text, "sat.backends=") != NULL);
  free_string(text);
  n = stp_num_sat_backends();
  CHECK(n >= 1);
  for (i = 0; i < n; ++i)
    CHECK(stp_sat_backend_name(i) != NULL && stp_has_sat_backend(stp_sat_backend_name(i)));
  CHECK(stp_sat_backend_name(n) == NULL);
  CHECK(!stp_has_sat_backend("no-such-backend"));
  CHECK(strcmp(stp_kind_name(STP_KIND_BV_ADD), "BV_ADD") == 0);
  CHECK(strcmp(stp_kind_smtlib(STP_KIND_BV_ADD), "bvadd") == 0);
  CHECK(strcmp(stp_kind_name((stp_kind)999), "?") == 0);
  CHECK(strcmp(stp_rm_name(STP_RM_RTZ), "RTZ") == 0);
  CHECK(strcmp(stp_error_code_name(STP_ERR_SORT_MISMATCH), "SORT_MISMATCH") == 0);
  CHECK(strcmp(stp_result_kind_name(STP_UNSAT), "unsat") == 0);
  CHECK(strcmp(stp_validity_name(STP_VALID), "valid") == 0);
  CHECK(strcmp(stp_unknown_reason_name(STP_REASON_TIMEOUT), "timeout") == 0);
  CHECK(stp_get_internal_error_policy() == STP_POISON);
  stp_free(NULL); /* harmless */
}

int main(void)
{
  printf("STP %s (C API)\n", stp_get_version().string);
  printf("[library]\n");
  library();
  printf("[bv]\n");
  bitvectors_and_errors();
  printf("[arrays]\n");
  arrays();
  printf("[floats]\n");
  floats();
  printf("[uf]\n");
  uninterpreted();
  printf("[reals]\n");
  reals();
  printf("[options]\n");
  options_and_limits();
  printf("%s%d\n", failures ? "FAILURES: " : "all passed: ", failures);
  return failures ? 1 : 0;
}

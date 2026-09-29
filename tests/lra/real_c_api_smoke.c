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

/* real_c_api_smoke.c -- exact Real arithmetic through the 3.x C API, in
 * C99: the Real constructors with their sorts and kinds, the exact SMT-LIB 2
 * spelling of a script, an exact model read across the ABI (numerator,
 * denominator, the value's SMT-LIB spelling and the whole model), the model's
 * lifetime across declarations, assertions, push and pop, and the misuses
 * that ended the process in 2.x -- a null or foreign operand, a wrong sort,
 * an invalid literal, a width query on a Real, an ite whose branches
 * disagree -- each now a refusal the caller can inspect.
 *
 * With no argument every case runs; "emit" also prints the SMT-LIB 2 script;
 * naming one misuse (null-operand, cross-manager, ...) runs only that one,
 * which exits 0 when the misuse is refused as it should be. */

#include <stp/stp.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int require(int condition, const char* message)
{
  if (condition)
    return 1;
  fprintf(stderr, "FAIL %s\n", message);
  return 0;
}

/* The manager's recorded error must carry `code` and be recoverable; the
 * record is cleared either way. */
static int refused_with(stp_tm tm, stp_error_code code)
{
  const stp_error* error = stp_tm_error(tm);
  const int ok = error != NULL && error->code == code && error->recoverable;
  if (!ok)
    fprintf(stderr, "expected a %s refusal, the manager recorded %s\n",
            stp_error_code_name(code),
            error != NULL ? stp_error_code_name(error->code) : "nothing");
  stp_tm_clear_error(tm);
  return ok;
}

static int check_sat_is(stp_solver s, stp_result_kind expected)
{
  stp_result result;
  return stp_solver_check_sat(s, &result) == STP_OK && result.kind == expected;
}

static stp_sort_kind sort_kind_of(stp_term term)
{
  stp_sort_kind kind = STP_SORT_MAX_ENUM;
  return stp_sort_get_kind(stp_term_sort(term), &kind) == STP_OK ? kind : STP_SORT_MAX_ENUM;
}

static stp_kind kind_of(stp_term term)
{
  stp_kind kind = STP_KIND_MAX_ENUM;
  return stp_term_get_kind(term, &kind) == STP_OK ? kind : STP_KIND_MAX_ENUM;
}

/* Whether the solver's model gives `term` the exact value num/den. */
static int model_reads(stp_solver s, stp_term term, const char* num, const char* den)
{
  stp_model model = stp_solver_model(s);
  char* numerator = model != NULL ? stp_model_real_numerator(model, term) : NULL;
  char* denominator = model != NULL ? stp_model_real_denominator(model, term) : NULL;
  const int ok = numerator != NULL && denominator != NULL && strcmp(numerator, num) == 0 &&
                 strcmp(denominator, den) == 0;
  stp_free(numerator);
  stp_free(denominator);
  if (model != NULL)
    stp_model_release(model);
  return ok;
}

/* A NULL operand propagates: the construction returns NULL and records
 * nothing, so a chain of constructions is checked once, where it is
 * asserted. The assert refuses it (NULL_HANDLE) and puts the solver into its
 * failed state, in which no check runs, so the NULL can never be a silently
 * dropped assertion. */
static int null_propagates(stp_tm tm, stp_term built)
{
  stp_solver s;
  stp_result result;
  int ok;
  if (built != NULL || stp_tm_error(tm) != NULL)
    return 0;
  s = stp_solver_new(tm, NULL);
  ok = s != NULL && stp_solver_assert(s, built) == STP_ERROR &&
       refused_with(tm, STP_ERR_NULL_HANDLE) && stp_solver_failed(s) != NULL &&
       stp_solver_check_sat(s, &result) == STP_ERROR && refused_with(tm, STP_ERR_STATE);
  stp_solver_delete(s);
  return ok;
}

/* A refusal is no wound: the manager still builds and decides. */
static int still_usable(stp_tm tm, stp_term x)
{
  stp_solver s = stp_solver_new(tm, NULL);
  const int ok = s != NULL &&
                 stp_solver_assert(s, stp_eq(tm, x, stp_mk_real_fraction(tm, 1, 2))) == STP_OK &&
                 check_sat_is(s, STP_SAT) && model_reads(s, x, "1", "2");
  stp_solver_delete(s);
  return ok && stp_tm_error(tm) == NULL;
}

static const char* const negative_modes[] = {
    "null-operand",
    "cross-manager",
    "cross-manager-equality",
    "null-equality",
    "wrong-sort",
    "invalid-exact-text",
    "value-width",
    "index-width",
    "exponent-width",
    "significand-width",
    "real-ite-mixed-branches",
};

/* The misuses 2.x made fatal. In 3.x each is refused -- the call returns NULL
 * or STP_ERROR and the manager records the error -- and leaves the manager as
 * it was. Returns 0 when the misuse was refused as it should be, 1 when not,
 * 2 for an unknown mode. */
static int negative_mode(const char* mode)
{
  stp_tm first = stp_tm_new(NULL);
  stp_tm second = NULL;
  stp_sort real_sort = stp_mk_real_sort(first);
  stp_term x = stp_declare(first, "x", real_sort);
  uint32_t width = 0;
  int ok = 0;

  if (strcmp(mode, "null-operand") == 0)
    ok = null_propagates(first, stp_real_add(first, x, NULL));
  else if (strcmp(mode, "cross-manager") == 0)
  {
    second = stp_tm_new(NULL);
    stp_term foreign = stp_declare(second, "foreign", stp_mk_real_sort(second));
    ok = stp_real_add(first, x, foreign) == NULL &&
         refused_with(first, STP_ERR_FOREIGN_MANAGER);
  }
  else if (strcmp(mode, "cross-manager-equality") == 0)
  {
    second = stp_tm_new(NULL);
    stp_term foreign = stp_declare(second, "foreign", stp_mk_real_sort(second));
    ok = stp_eq(first, x, foreign) == NULL && refused_with(first, STP_ERR_FOREIGN_MANAGER);
  }
  else if (strcmp(mode, "null-equality") == 0)
    ok = null_propagates(first, stp_eq(first, x, NULL));
  else if (strcmp(mode, "wrong-sort") == 0)
  {
    stp_term bv = stp_declare(first, "bv", stp_mk_bv_sort(first, 8));
    ok = stp_real_add(first, x, bv) == NULL && refused_with(first, STP_ERR_SORT_MISMATCH);
  }
  else if (strcmp(mode, "invalid-exact-text") == 0)
    ok = stp_mk_real_str(first, "1/0") == NULL &&
         refused_with(first, STP_ERR_INVALID_ARGUMENT);
  /* The width queries are questions about a sort: a Real sort has none of
     the four widths. */
  else if (strcmp(mode, "value-width") == 0)
    ok = stp_sort_bv_size(real_sort, &width) == STP_ERROR &&
         refused_with(first, STP_ERR_INVALID_ARGUMENT);
  else if (strcmp(mode, "index-width") == 0)
    ok = stp_sort_array_index(real_sort) == NULL &&
         refused_with(first, STP_ERR_INVALID_ARGUMENT);
  else if (strcmp(mode, "exponent-width") == 0)
    ok = stp_sort_fp_exp_size(real_sort, &width) == STP_ERROR &&
         refused_with(first, STP_ERR_INVALID_ARGUMENT);
  else if (strcmp(mode, "significand-width") == 0)
    ok = stp_sort_fp_sig_size(real_sort, &width) == STP_ERROR &&
         refused_with(first, STP_ERR_INVALID_ARGUMENT);
  /* A Real-branch ite is buildable; what is refused is a branch pair that
     does not agree on the sort, which is what this case pins. The else
     branch is a bit-vector, so the refusal names it: argument 2. */
  else if (strcmp(mode, "real-ite-mixed-branches") == 0)
  {
    stp_term bv = stp_declare(first, "ite_bv", stp_mk_bv_sort(first, 8));
    stp_term condition = stp_mk_true(first);
    const stp_error* error;
    ok = stp_ite(first, condition, x, bv) == NULL;
    error = stp_tm_error(first);
    ok = ok && error != NULL && error->argument_index == 2 &&
         refused_with(first, STP_ERR_SORT_MISMATCH);
  }
  else
  {
    fprintf(stderr, "unknown negative mode: %s\n", mode);
    stp_tm_release_all(first);
    stp_tm_release(first);
    return 2;
  }

  ok = ok && still_usable(first, x);
  stp_tm_release_all(first);
  stp_tm_release(first);
  if (second != NULL)
  {
    stp_tm_release_all(second);
    stp_tm_release(second);
  }
  if (!ok)
    fprintf(stderr, "FAIL negative C API mode was not refused as it should be: %s\n", mode);
  return ok ? 0 : 1;
}

int main(int argc, char** argv)
{
  const int emit = argc == 2 && strcmp(argv[1], "emit") == 0;
  size_t i;
  if (argc == 2 && !emit)
    return negative_mode(argv[1]);
  if (argc != 1 && !emit)
    return 2;

  /* Every misuse 2.x made fatal is a refusal in 3.x, so all of them run in
     this process rather than one per process. */
  for (i = 0; i != sizeof negative_modes / sizeof negative_modes[0]; ++i)
    if (negative_mode(negative_modes[i]) != 0)
      return 1;

  stp_tm tm = stp_tm_new(NULL);
  if (!require(tm != NULL, "manager creation"))
    return 1;
  /* 2.x reported Real construction and QF_LRA as two capabilities; 3.x
     reports the one, lra, and the Real sort is part of every manager. */
  char* lra = stp_capability("lra");
  const int lra_ok = lra != NULL && strcmp(lra, "true") == 0;
  stp_free(lra);
  stp_sort real_sort = stp_mk_real_sort(tm);
  if (!require(real_sort != NULL, "Real construction capability") ||
      !require(lra_ok, "QF_LRA semantic capability"))
    return 1;

  stp_term x = stp_declare(tm, "x", real_sort);
  stp_term half = stp_mk_real_fraction(tm, 2, 4);
  stp_term two = stp_mk_real_str(tm, "2.0");
  stp_term scaled = stp_real_mul(tm, two, x);
  stp_term sum = stp_real_add(tm, scaled, half);
  stp_term nine_halves = stp_mk_real_str(tm, "9/2");
  stp_term upper = stp_real_le(tm, sum, nine_halves);
  stp_term negative_fraction = stp_mk_real_str(tm, "-7/3");
  stp_term negative_integer = stp_mk_real_str(tm, "-9");
  stp_term lower_fraction = stp_real_gt(tm, x, negative_fraction);
  stp_term lower_integer = stp_real_ge(tm, x, negative_integer);
  stp_term lower = stp_and2(tm, lower_fraction, lower_integer);
  stp_term predicate = stp_and2(tm, upper, lower);
  stp_term equality = stp_eq(tm, x, sum);

  /* A NULL anywhere above would have propagated into these two. 3.x has one
     kind for every constant, VALUE (2.x: REAL_CONST), and calls equality
     EQUAL on every sort (2.x: EQ). */
  if (!require(predicate != NULL && equality != NULL && stp_tm_error(tm) == NULL,
               "Real construction") ||
      !require(sort_kind_of(x) == STP_SORT_REAL, "Real source-sort exposure") ||
      !require(kind_of(half) == STP_KIND_VALUE && stp_term_is_value(half),
               "Real constant kind") ||
      !require(sort_kind_of(predicate) == STP_SORT_BOOL, "Real comparison result sort") ||
      !require(kind_of(equality) == STP_KIND_EQUAL, "polymorphic Real equality kind"))
    return 1;

  /* A script is the solver's: its assertions with the set-logic and the
     declarations. The assertions are printed by the engine's printer, which
     quotes every symbol. */
  stp_solver s = stp_solver_new(tm, NULL);
  if (!require(s != NULL && stp_solver_assert(s, predicate) == STP_OK,
               "asserting the Real predicate"))
    return 1;
  char* printed = stp_solver_to_smt2(s, false);
  const int print_ok =
      printed != NULL && strstr(printed, "(set-logic QF_LRA)") != NULL &&
      strstr(printed, "() Real") != NULL && strstr(printed, "(/ 1 2)") != NULL &&
      strstr(printed, "(* |x| 2)") != NULL && strstr(printed, "(- (/ 7 3))") != NULL &&
      strstr(printed, "(- 9)") != NULL;
  if (!require(print_ok, "exact legal SMT-LIB2 output"))
  {
    if (printed != NULL)
      fprintf(stderr, "%s\n", printed);
    stp_free(printed);
    return 1;
  }
  if (emit)
    fputs(printed, stdout);
  stp_free(printed);

  /* Solve an exact public C model and copy every DTO across the ABI. */
  stp_term four_thirds = stp_mk_real_str(tm, "4/3");
  stp_term fixed_x = stp_eq(tm, x, four_thirds);
  if (!require(stp_solver_assert(s, fixed_x) == STP_OK, "asserting the fixed value") ||
      !require(check_sat_is(s, STP_SAT), "QF_LRA C solve"))
    return 1;
  stp_model model = stp_solver_model(s);
  stp_term x_value = model != NULL ? stp_model_value(model, x) : NULL;
  stp_term sum_value = model != NULL ? stp_model_value(model, sum) : NULL;
  if (!require(model != NULL, "current exact Real model") ||
      !require(x_value != NULL && stp_model_in_core(model, x), "symbol model value") ||
      !require(sum_value != NULL, "normalized-expression model value"))
    return 1;

  /* The C API reads a rational as its two parts (as strings, or as int64s
     when they fit) rather than as one "19/6" string. */
  char* numerator = stp_model_real_numerator(model, sum);
  char* denominator = stp_model_real_denominator(model, sum);
  int64_t num64 = 0;
  int64_t den64 = 0;
  const int fits = stp_term_real_to_int64(sum_value, &num64, &den64) == STP_OK;
  char* smt_value = stp_term_str(sum_value);
  char* smt_model = stp_model_to_smt2(model);
  /* The model's own printer quotes a symbol only where SMT-LIB requires. */
  const int model_ok = numerator != NULL && strcmp(numerator, "19") == 0 &&
                       denominator != NULL && strcmp(denominator, "6") == 0 && fits &&
                       num64 == 19 && den64 == 6 && smt_value != NULL &&
                       strcmp(smt_value, "(/ 19 6)") == 0 && smt_model != NULL &&
                       strstr(smt_model, "(define-fun x () Real") != NULL &&
                       strstr(smt_model, "(/ 4 3)") != NULL;
  if (!require(model_ok, "exact C model DTO and SMT-LIB output"))
    return 1;
  stp_free(numerator);
  stp_free(denominator);
  stp_free(smt_value);
  stp_free(smt_model);
  stp_term_release(x_value);
  stp_term_release(sum_value);
  stp_model_release(model);

  /* 3.x: a model is a snapshot of the last check that answered sat, and it
     stays readable across declarations, assertions, push and pop (2.x
     invalidated the exact Real model at each) until the next check. */
  stp_sort bv_sort = stp_mk_bv_sort(tm, 8);
  stp_term newly_declared_bv = stp_declare(tm, "newly_declared_bv", bv_sort);
  if (!require(model_reads(s, x, "4", "3"),
               "disjoint declaration keeps the combined model") ||
      !require(check_sat_is(s, STP_SAT), "post-disjoint-declaration QF_LRA C solve"))
    return 1;

  stp_term unconstrained = stp_declare(tm, "unconstrained", real_sort);
  if (!require(model_reads(s, x, "4", "3"), "Real declaration keeps the exact model") ||
      !require(check_sat_is(s, STP_SAT), "post-declaration QF_LRA C solve") ||
      !require(model_reads(s, unconstrained, "0", "1"),
               "unconstrained declared Real model value"))
    return 1;

  stp_term true_assertion = stp_mk_true(tm);
  if (!require(stp_solver_assert(s, true_assertion) == STP_OK, "asserting true") ||
      !require(model_reads(s, x, "4", "3"), "assertion mutation keeps the exact model") ||
      !require(check_sat_is(s, STP_SAT), "post-mutation QF_LRA C solve") ||
      !require(model_reads(s, x, "4", "3"),
               "post-mutation solve did not republish exact model"))
    return 1;

  if (!require(stp_solver_push(s, 1) == STP_OK, "push") ||
      !require(model_reads(s, x, "4", "3"), "push keeps the Real model"))
    return 1;
  if (!require(check_sat_is(s, STP_SAT), "C solve inside pushed context") ||
      !require(model_reads(s, x, "4", "3"), "pushed-context solve published exact model"))
    return 1;
  if (!require(stp_solver_pop(s, 1) == STP_OK, "pop") ||
      !require(model_reads(s, x, "4", "3"), "pop keeps the Real model"))
    return 1;

  /* Every returned term handle carries one reference the caller owns, given
     back here (the 2.x deletes). Sorts are the manager's; stp_sort_release
     would be a no-op. */
  const stp_term owned[] = {predicate, equality, lower, lower_integer, lower_fraction,
                            negative_integer, negative_fraction, upper, sum, scaled, two,
                            half, nine_halves, fixed_x, four_thirds, true_assertion,
                            newly_declared_bv, unconstrained, x};
  int released = 1;
  for (i = 0; i != sizeof owned / sizeof owned[0]; ++i)
    released = stp_term_release(owned[i]) == STP_OK && released;
  stp_solver_delete(s);
  if (!require(released && stp_tm_error(tm) == NULL, "term handles released"))
    return 1;
  stp_tm_release(tm);
  if (!emit)
    puts("PASS real-c-api-smoke");
  return 0;
}

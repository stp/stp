#include "imrat.h"
#include "ImathAllocHooks.h"

#include <stdio.h>
#include <string.h>

static int expect_ok(mp_result result, const char* operation) {
  if (result == MP_OK) return 1;
  fprintf(stderr, "%s failed: %s\n", operation, mp_error_string(result));
  return 0;
}

int main(void) {
  imath_rat_value left;
  imath_rat_value right;
  imath_rat_value sum;
  char output[32];
  int ok = 1;
  stp_lra_imath_budget_state budget;

  stp_lra_imath_budget_init(&budget, UINT64_MAX);
  if (stp_lra_imath_exchange_active_budget(&budget) != NULL) {
    fprintf(stderr, "unexpected existing IMath allocation scope\n");
    return 1;
  }

  ok &= expect_ok(mp_rat_init(&left), "init left");
  ok &= expect_ok(mp_rat_init(&right), "init right");
  ok &= expect_ok(mp_rat_init(&sum), "init sum");
  if (!ok) {
    stp_lra_imath_exchange_active_budget(NULL);
    return 1;
  }

  ok &= expect_ok(mp_rat_set_value(&left, 1, 3), "set 1/3");
  ok &= expect_ok(mp_rat_set_value(&right, 1, 6), "set 1/6");
  ok &= expect_ok(mp_rat_add(&left, &right, &sum), "add");
  ok &= expect_ok(mp_rat_to_string(&sum, 10, output, (int)sizeof(output)),
                  "format");
  ok &= strcmp(output, "1/2") == 0;

  stp_lra_imath_exchange_active_budget(NULL);
  mp_rat_clear(&sum);
  mp_rat_clear(&right);
  mp_rat_clear(&left);

  if (budget.live_bytes != 0) {
    fprintf(stderr, "IMath allocation accounting did not return to zero\n");
    return 1;
  }

  if (!ok) {
    fprintf(stderr, "unexpected rational result: %s\n", output);
    return 1;
  }
  return 0;
}

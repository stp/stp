#include "stp/c_interface.h"

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

static int negative_mode(const char* mode)
{
  VC first = vc_createValidityChecker();
  Type real_type = vc_realType(first);
  Expr x = vc_varExpr(first, "x", real_type);

  if (strcmp(mode, "null-operand") == 0)
    (void)vc_realPlusExpr(first, x, NULL);
  else if (strcmp(mode, "cross-manager") == 0)
  {
    VC second = vc_createValidityChecker();
    Type second_real_type = vc_realType(second);
    Expr foreign = vc_varExpr(second, "foreign", second_real_type);
    (void)vc_realPlusExpr(first, x, foreign);
  }
  else if (strcmp(mode, "cross-manager-equality") == 0)
  {
    VC second = vc_createValidityChecker();
    Type second_real_type = vc_realType(second);
    Expr foreign = vc_varExpr(second, "foreign", second_real_type);
    (void)vc_eqExpr(first, x, foreign);
  }
  else if (strcmp(mode, "null-equality") == 0)
    (void)vc_eqExpr(first, x, NULL);
  else if (strcmp(mode, "wrong-sort") == 0)
  {
    Type bv_type = vc_bvType(first, 8);
    Expr bv = vc_varExpr(first, "bv", bv_type);
    (void)vc_realPlusExpr(first, x, bv);
  }
  else if (strcmp(mode, "invalid-exact-text") == 0)
    (void)vc_realConstExprFromStr(first, "1/0");
  else if (strcmp(mode, "value-width") == 0)
    (void)getVWidth(x);
  else if (strcmp(mode, "index-width") == 0)
    (void)getIWidth(x);
  else if (strcmp(mode, "exponent-width") == 0)
    (void)vc_getExpWidth(x);
  else if (strcmp(mode, "significand-width") == 0)
    (void)vc_getSigWidth(x);
  /* A Real-branch ite is buildable (see vc_hasRealIte); what stays fatal is
     a branch pair that does not agree on the sort, which is what this case
     now pins.  The else branch is a bit-vector, so requireOwnedRealExpr
     refuses it and names the branch it refused. */
  else if (strcmp(mode, "real-ite-mixed-branches") == 0)
  {
    Type bv_type = vc_bvType(first, 8);
    Expr bv = vc_varExpr(first, "ite_bv", bv_type);
    (void)vc_iteExpr(first, vc_trueExpr(first), x, bv);
  }
  else
  {
    fprintf(stderr, "unknown negative mode: %s\n", mode);
    return 2;
  }

  fprintf(stderr, "negative C API mode returned unexpectedly: %s\n", mode);
  return 0;
}

int main(int argc, char** argv)
{
  const int emit = argc == 2 && strcmp(argv[1], "emit") == 0;
  if (argc == 2 && !emit)
    return negative_mode(argv[1]);
  if (argc != 1 && !emit)
    return 2;

  VC vc = vc_createValidityChecker();
  if (!require(vc != NULL, "vc creation") ||
      !require(vc_hasRealConstruction() == 1, "Real construction capability") ||
      !require(vc_hasQFLRA() == 1, "QF_LRA semantic capability"))
    return 1;

  Type real_type = vc_realType(vc);
  Expr x = vc_varExpr(vc, "x", real_type);
  Expr half = vc_realConstExpr(vc, "2", "4");
  Expr two = vc_realConstExprFromStr(vc, "2.0");
  Expr scaled = vc_realMultExpr(vc, two, x);
  Expr sum = vc_realPlusExpr(vc, scaled, half);
  Expr nine_halves = vc_realConstExprFromStr(vc, "9/2");
  Expr upper = vc_realLeExpr(vc, sum, nine_halves);
  Expr negative_fraction = vc_realConstExprFromStr(vc, "-7/3");
  Expr negative_integer = vc_realConstExprFromStr(vc, "-9");
  Expr lower_fraction = vc_realGtExpr(vc, x, negative_fraction);
  Expr lower_integer = vc_realGeExpr(vc, x, negative_integer);
  Expr lower = vc_andExpr(vc, lower_fraction, lower_integer);
  Expr predicate = vc_andExpr(vc, upper, lower);
  Expr equality = vc_eqExpr(vc, x, sum);

  if (!require(getType(x) == REAL_TYPE, "Real source-sort exposure") ||
      !require(getExprKind(half) == REAL_CONST, "Real constant kind") ||
      !require(getType(predicate) == BOOLEAN_TYPE, "Real comparison result sort") ||
      !require(getExprKind(equality) == EQ,
               "polymorphic Real equality kind"))
    return 1;

  char* printed = vc_printSMTLIB2(vc, predicate);
  const int print_ok =
      printed != NULL && strstr(printed, "(set-logic QF_LRA)") != NULL &&
      strstr(printed, "() Real") != NULL &&
      strstr(printed, "(/ 1 2)") != NULL &&
      strstr(printed, "(* |x| 2)") != NULL &&
      strstr(printed, "(- (/ 7 3))") != NULL &&
      strstr(printed, "(- 9)") != NULL;
  if (!require(print_ok, "exact legal SMT-LIB2 output"))
  {
    if (printed != NULL)
      fprintf(stderr, "%s\n", printed);
    free(printed);
    return 1;
  }
  if (emit)
    fputs(printed, stdout);
  free(printed);

  /* Solve an exact public C model and copy every DTO across the ABI. */
  Expr four_thirds = vc_realConstExprFromStr(vc, "4/3");
  Expr fixed_x = vc_eqExpr(vc, x, four_thirds);
  Expr false_query = vc_falseExpr(vc);
  vc_assertFormula(vc, predicate);
  vc_assertFormula(vc, fixed_x);
  if (!require(vc_query(vc, false_query) == 0, "QF_LRA C solve") ||
      !require(vc_hasRealModel(vc) == 1, "current exact Real model") ||
      !require(vc_hasRealModelValue(vc, x) == 1, "symbol model value") ||
      !require(vc_hasRealModelValue(vc, sum) == 1,
               "normalized-expression model value"))
    return 1;

  char* fraction = vc_getRealModelValue(vc, sum);
  char* numerator = vc_getRealModelNumerator(vc, sum);
  char* denominator = vc_getRealModelDenominator(vc, sum);
  char* smt_value = vc_getRealModelSMTLIBValue(vc, sum);
  char* smt_model = vc_getRealModelSMTLIB2(vc);
  const int model_ok =
      fraction != NULL && strcmp(fraction, "19/6") == 0 &&
      numerator != NULL && strcmp(numerator, "19") == 0 &&
      denominator != NULL && strcmp(denominator, "6") == 0 &&
      smt_value != NULL && strcmp(smt_value, "(/ 19 6)") == 0 &&
      smt_model != NULL && strstr(smt_model, "(define-fun |x| () Real") &&
      strstr(smt_model, "(/ 4 3)");
  if (!require(model_ok, "exact C model DTO and SMT-LIB output"))
    return 1;
  vc_deleteString(fraction);
  vc_deleteString(numerator);
  vc_deleteString(denominator);
  vc_deleteString(smt_value);
  vc_deleteString(smt_model);

  Type bv_type = vc_bvType(vc, 8);
  Expr newly_declared_bv = vc_varExpr(vc, "newly_declared_bv", bv_type);
  if (!require(vc_hasRealModel(vc) == 0,
               "disjoint declaration invalidates combined model") ||
      !require(vc_query(vc, false_query) == 0,
               "post-disjoint-declaration QF_LRA C solve"))
    return 1;

  Expr unconstrained = vc_varExpr(vc, "unconstrained", real_type);
  if (!require(vc_hasRealModel(vc) == 0,
               "Real declaration invalidates exact model") ||
      !require(vc_query(vc, false_query) == 0,
               "post-declaration QF_LRA C solve"))
    return 1;
  char* unconstrained_value = vc_getRealModelValue(vc, unconstrained);
  if (!require(unconstrained_value != NULL &&
                   strcmp(unconstrained_value, "0") == 0,
               "unconstrained declared Real model value"))
    return 1;
  vc_deleteString(unconstrained_value);

  Expr true_assertion = vc_trueExpr(vc);
  vc_assertFormula(vc, true_assertion);
  if (!require(vc_hasRealModel(vc) == 0,
               "assertion mutation invalidates exact model") ||
      !require(vc_query(vc, false_query) == 0,
               "post-mutation QF_LRA C solve") ||
      !require(vc_hasRealModel(vc) == 1,
               "post-mutation solve did not republish exact model"))
    return 1;

  vc_push(vc);
  if (!require(vc_hasRealModel(vc) == 0, "push invalidates Real model"))
    return 1;
  if (!require(vc_query(vc, false_query) == 0,
               "C solve inside pushed context") ||
      !require(vc_hasRealModel(vc) == 1,
               "pushed-context solve published exact model"))
    return 1;
  vc_pop(vc);
  if (!require(vc_hasRealModel(vc) == 0, "pop invalidates Real model"))
    return 1;

  vc_DeleteExpr(predicate);
  vc_DeleteExpr(equality);
  vc_DeleteExpr(lower);
  vc_DeleteExpr(lower_integer);
  vc_DeleteExpr(lower_fraction);
  vc_DeleteExpr(negative_integer);
  vc_DeleteExpr(negative_fraction);
  vc_DeleteExpr(upper);
  vc_DeleteExpr(sum);
  vc_DeleteExpr(scaled);
  vc_DeleteExpr(two);
  vc_DeleteExpr(half);
  vc_DeleteExpr(nine_halves);
  vc_DeleteExpr(false_query);
  vc_DeleteExpr(fixed_x);
  vc_DeleteExpr(four_thirds);
  vc_DeleteExpr(true_assertion);
  vc_DeleteExpr(newly_declared_bv);
  vc_DeleteExpr(unconstrained);
  vc_DeleteExpr(x);
  /* Type constructors are checker-owned, as documented by vc_DeleteExpr. */
  vc_Destroy(vc);
  if (!emit)
    puts("PASS real-c-api-smoke");
  return 0;
}

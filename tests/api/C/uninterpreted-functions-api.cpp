/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <initializer_list>
#include <vector>

namespace
{
int errors = 0;
void countError(const char*) { ++errors; }

UFDeclHandle declareFunction(VC vc, const char* name,
                             std::initializer_list<unsigned> domainWidths,
                             unsigned codomainWidth)
{
  std::vector<Type> domain;
  domain.reserve(domainWidths.size());
  for (const unsigned width : domainWidths)
    domain.push_back(width == 0 ? vc_boolType(vc) : vc_bvType(vc, width));
  Type codomain = codomainWidth == 0 ? vc_boolType(vc)
                                     : vc_bvType(vc, codomainWidth);
  const UFDeclHandle declaration = vc_declareUninterpretedFunction(
      vc, name, domain.data(), domain.size(), codomain);
  for (const Type type : domain)
    vc_DeleteExpr(type);
  vc_DeleteExpr(codomain);
  return declaration;
}
}

TEST(UninterpretedFunctionsCAPI, OwnershipTypingAndNonfatalRejection)
{
  vc_registerErrorHandler(countError);
  errors = 0;

  VC first = vc_createValidityChecker();
  VC second = vc_createValidityChecker();
  vc_setFlag(first, 'u');
  vc_setFlag(second, 'u');

  UFDeclHandle f = declareFunction(first, "f", {8, 0}, 16);
  ASSERT_NE(0u, f);
  EXPECT_EQ(0u, declareFunction(first, "f", {8, 0}, 16));
  EXPECT_EQ(nullptr, vc_varExpr(first, "f", vc_bvType(first, 8)));

  Expr bv8 = vc_varExpr(first, "x", vc_bvType(first, 8));
  Expr boolean = vc_varExpr(first, "b", vc_boolType(first));
  const Expr actuals[] = {bv8, boolean};
  Expr application = vc_applyUninterpretedFunction(first, f, actuals, 2);
  ASSERT_NE(nullptr, application);
  EXPECT_EQ(UF_APPLY, getExprKind(application));
  EXPECT_EQ(16, vc_getBVLength(first, application));

  EXPECT_EQ(nullptr,
            vc_applyUninterpretedFunction(first, f, actuals, 1));
  const Expr wrong[] = {boolean, boolean};
  EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(first, f, wrong, 2));
  EXPECT_EQ(nullptr, vc_applyUninterpretedFunction(second, f, actuals, 2));
  EXPECT_GE(errors, 5);

  vc_DeleteExpr(application);
  vc_DeleteExpr(bv8);
  vc_DeleteExpr(boolean);
  vc_Destroy(second);
  vc_Destroy(first);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsCAPI, DefaultOffAndZeroArityAreRejected)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC vc = vc_createValidityChecker();
  Type bv8 = vc_bvType(vc, 8);
  EXPECT_EQ(0u,
            vc_declareUninterpretedFunction(vc, "off", &bv8, 1, bv8));
  vc_setFlag(vc, 'u');
  EXPECT_EQ(0u,
            vc_declareUninterpretedFunction(vc, "zero", &bv8, 0, bv8));
  EXPECT_EQ(2, errors);
  vc_DeleteExpr(bv8);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsCAPI, CertifiedDurableValuesBatchAndRejection)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC first = vc_createValidityChecker();
  VC second = vc_createValidityChecker();
  vc_setFlag(first, 'u');
  vc_setFlag(second, 'u');

  UFDeclHandle f = declareFunction(first, "f", {8}, 8);
  ASSERT_NE(0u, f);
  Expr x = vc_varExpr(first, "x", vc_bvType(first, 8));
  const Expr actuals[] = {x};
  Expr application = vc_applyUninterpretedFunction(first, f, actuals, 1);
  ASSERT_NE(nullptr, application);
  Expr expected = vc_bvConstExprFromInt(first, 8, 42);
  Expr equation = vc_eqExpr(first, application, expected);
  vc_assertFormula(first, equation);

  Expr falseQuery = vc_falseExpr(first);
  ASSERT_EQ(0, vc_query(first, falseQuery));
  vc_DeleteExpr(falseQuery);
  Expr value = vc_getUninterpretedFunctionValue(first, application);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(42u, getBVUnsigned(value));
  vc_DeleteExpr(value);
  value = vc_getCounterExample(first, application);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(42u, getBVUnsigned(value));
  vc_DeleteExpr(value);

  // A newly registered but unreachable handle was not active in this solve,
  // and a foreign context cannot read the first context's handle.
  Expr y = vc_varExpr(first, "y", vc_bvType(first, 8));
  const Expr otherActuals[] = {y};
  Expr inactive =
      vc_applyUninterpretedFunction(first, f, otherActuals, 1);
  ASSERT_NE(nullptr, inactive);
  EXPECT_EQ(nullptr, vc_getUninterpretedFunctionValue(first, inactive));
  EXPECT_EQ(nullptr,
            vc_getUninterpretedFunctionValue(second, application));

  // Mutating the asserted root invalidates the certified map immediately.
  Expr tautology = vc_trueExpr(first);
  vc_assertFormula(first, tautology);
  vc_DeleteExpr(tautology);
  EXPECT_EQ(nullptr,
            vc_getUninterpretedFunctionValue(first, application));
  EXPECT_GE(errors, 3);

  vc_DeleteExpr(inactive);
  vc_DeleteExpr(y);
  vc_DeleteExpr(equation);
  vc_DeleteExpr(application);
  vc_DeleteExpr(x);
  vc_Destroy(second);
  vc_Destroy(first);
  vc_registerErrorHandler(nullptr);
}

TEST(UninterpretedFunctionsCAPI, CertifiedDurableValuePersistentMode)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  vc_setFlag(vc, 'i');

  UFDeclHandle p = declareFunction(vc, "p", {0, 9}, 0);
  ASSERT_NE(0u, p);
  Expr b = vc_varExpr(vc, "b", vc_boolType(vc));
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 9));
  const Expr actuals[] = {b, x};
  Expr application = vc_applyUninterpretedFunction(vc, p, actuals, 2);
  ASSERT_NE(nullptr, application);
  vc_assertFormula(vc, application);

  Expr falseQuery = vc_falseExpr(vc);
  ASSERT_EQ(0, vc_query(vc, falseQuery));
  vc_DeleteExpr(falseQuery);
  Expr value = vc_getUninterpretedFunctionValue(vc, application);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(1, vc_isBool(value));
  vc_DeleteExpr(value);

  // A real stack mutation clears the block-owned certified lookup map.
  vc_push(vc);
  EXPECT_EQ(nullptr, vc_getUninterpretedFunctionValue(vc, application));
  EXPECT_GE(errors, 1);

  // Re-certify the pushed block, then prove that the matching pop itself
  // invalidates the block-owned durable-handle map.
  falseQuery = vc_falseExpr(vc);
  ASSERT_EQ(0, vc_query(vc, falseQuery));
  vc_DeleteExpr(falseQuery);
  value = vc_getUninterpretedFunctionValue(vc, application);
  ASSERT_NE(nullptr, value);
  vc_DeleteExpr(value);
  vc_pop(vc);
  EXPECT_EQ(nullptr, vc_getUninterpretedFunctionValue(vc, application));

  vc_DeleteExpr(application);
  vc_DeleteExpr(x);
  vc_DeleteExpr(b);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// Reading the model value of a term that *contains* an application, rather
// than an application itself. The enclosing operator needs a constant
// operand, so refusing is not an option here as it is at the root: an
// application the certified solve never reached is completed through the
// certified function seed. Before this was handled, every case below aborted
// the process from the counterexample walk.
TEST(UninterpretedFunctionsCAPI, ValuesOfTermsContainingApplications)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');

  UFDeclHandle f = declareFunction(vc, "f", {8}, 8);
  ASSERT_NE(0u, f);
  Expr x = vc_varExpr(vc, "x", vc_bvType(vc, 8));
  Expr seven = vc_bvConstExprFromInt(vc, 8, 7);
  const Expr atX[] = {x};
  const Expr atSeven[] = {seven};
  Expr fx = vc_applyUninterpretedFunction(vc, f, atX, 1);
  ASSERT_NE(nullptr, fx);
  // Same argument tuple as fx once x is pinned to 7, but a distinct durable
  // node that the solve never reaches.
  Expr fSeven = vc_applyUninterpretedFunction(vc, f, atSeven, 1);
  ASSERT_NE(nullptr, fSeven);

  vc_assertFormula(vc, vc_eqExpr(vc, x, seven));
  vc_assertFormula(vc, vc_eqExpr(vc, fx, vc_bvConstExprFromInt(vc, 8, 3)));
  Expr falseQuery = vc_falseExpr(vc);
  ASSERT_EQ(0, vc_query(vc, falseQuery));
  vc_DeleteExpr(falseQuery);

  Expr one = vc_bvConstExprFromInt(vc, 8, 1);

  // A bit-vector operator over a certified application.
  Expr sum = vc_bvPlusExpr(vc, 8, fx, one);
  Expr value = vc_getCounterExample(vc, sum);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(4u, getBVUnsigned(value));
  vc_DeleteExpr(value);

  // A predicate over a certified application reaches the formula walk.
  Expr predicate = vc_eqExpr(vc, fx, vc_bvConstExprFromInt(vc, 8, 3));
  value = vc_getCounterExample(vc, predicate);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(1, vc_isBool(value));
  vc_DeleteExpr(value);

  // Congruence across the certified/uncertified boundary: f(7) was never
  // reached, but it shares f(x)'s argument tuple and must share its value.
  // Completing with an arbitrary constant instead would break this.
  Expr uncertifiedSum = vc_bvPlusExpr(vc, 8, fSeven, one);
  value = vc_getCounterExample(vc, uncertifiedSum);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(4u, getBVUnsigned(value));
  vc_DeleteExpr(value);

  // The root accessor keeps its strict contract: an application the solve
  // never reached still has no public value of its own.
  EXPECT_EQ(nullptr, vc_getUninterpretedFunctionValue(vc, fSeven));

  vc_DeleteExpr(uncertifiedSum);
  vc_DeleteExpr(predicate);
  vc_DeleteExpr(sum);
  vc_DeleteExpr(one);
  vc_DeleteExpr(fSeven);
  vc_DeleteExpr(fx);
  vc_DeleteExpr(seven);
  vc_DeleteExpr(x);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// A Bool-codomain application nested in a formula reaches the formula walk
// rather than the term walk, and used to abort there with a different
// diagnostic than the bit-vector case.
TEST(UninterpretedFunctionsCAPI, ValuesOfFormulasContainingBoolApplications)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');

  UFDeclHandle g = declareFunction(vc, "g", {0}, 0);
  ASSERT_NE(0u, g);
  Expr p = vc_varExpr(vc, "p", vc_boolType(vc));
  Expr q = vc_varExpr(vc, "q", vc_boolType(vc));
  const Expr atP[] = {p};
  Expr gp = vc_applyUninterpretedFunction(vc, g, atP, 1);
  ASSERT_NE(nullptr, gp);

  vc_assertFormula(vc, gp);
  Expr falseQuery = vc_falseExpr(vc);
  ASSERT_EQ(0, vc_query(vc, falseQuery));
  vc_DeleteExpr(falseQuery);

  // g(p) is asserted, so it holds; its negation must therefore be false.
  // vc_isBool answers 1 for true, 0 for false and -1 for "not a Boolean".
  Expr value = vc_getCounterExample(vc, gp);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(1, vc_isBool(value));
  vc_DeleteExpr(value);

  Expr negated = vc_notExpr(vc, gp);
  value = vc_getCounterExample(vc, negated);
  ASSERT_NE(nullptr, value);
  EXPECT_EQ(0, vc_isBool(value));
  vc_DeleteExpr(value);
  vc_DeleteExpr(negated);

  // With g(p) true, both of these reduce to q's own model value.
  Expr qValue = vc_getCounterExample(vc, q);
  ASSERT_NE(nullptr, qValue);
  const int expected = vc_isBool(qValue);
  ASSERT_NE(-1, expected);
  vc_DeleteExpr(qValue);

  for (Expr nested : {vc_andExpr(vc, gp, q), vc_iffExpr(vc, gp, q)})
  {
    Expr nestedValue = vc_getCounterExample(vc, nested);
    ASSERT_NE(nullptr, nestedValue);
    EXPECT_EQ(expected, vc_isBool(nestedValue));
    vc_DeleteExpr(nestedValue);
    vc_DeleteExpr(nested);
  }

  vc_DeleteExpr(gp);
  vc_DeleteExpr(q);
  vc_DeleteExpr(p);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// The sorts the C API used to refuse. Its converter had its own hand-rolled
// list, strictly narrower than the one an .smt2 file gets, so a signature the
// parser accepted could not be built here at all.
TEST(UninterpretedFunctionsCAPI, FloatingPointAndRoundingModeSignatures)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');

  Type single = vc_fpType(vc, 8, 24);
  Type mode = vc_fpRoundingModeType(vc);
  Type bv4 = vc_bvType(vc, 4);

  const Type toBits[] = {single};
  UFDeclHandle f = vc_declareUninterpretedFunction(vc, "f", toBits, 1, bv4);
  EXPECT_NE(0u, f);
  const Type fromBits[] = {bv4};
  UFDeclHandle k = vc_declareUninterpretedFunction(vc, "k", fromBits, 1, mode);
  EXPECT_NE(0u, k);
  const Type fromMode[] = {mode};
  UFDeclHandle q =
      vc_declareUninterpretedFunction(vc, "q", fromMode, 1, single);
  EXPECT_NE(0u, q);
  EXPECT_EQ(0, errors);

  // An application at a float codomain is a float of the declared format,
  // not its packed carrier: it has to be usable as a floating-point operand.
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  const Expr atRne[] = {rne};
  Expr qRne = vc_applyUninterpretedFunction(vc, q, atRne, 1);
  ASSERT_NE(nullptr, qRne);
  EXPECT_EQ(8, vc_getExpWidth(qRne));
  EXPECT_EQ(24, vc_getSigWidth(qRne));
  Expr isNaNOfResult = vc_fpIsNaNExpr(vc, qRne);
  ASSERT_NE(nullptr, isNaNOfResult);

  // Congruence over a float argument is congruence over its *value*. x and y
  // are both NaN, which is one value however each was built, so f(x) and f(y)
  // must agree -- the query below is valid.
  Expr x = vc_varExpr(vc, "x", single);
  Expr y = vc_varExpr(vc, "y", single);
  const Expr atX[] = {x};
  const Expr atY[] = {y};
  Expr fx = vc_applyUninterpretedFunction(vc, f, atX, 1);
  Expr fy = vc_applyUninterpretedFunction(vc, f, atY, 1);
  ASSERT_NE(nullptr, fx);
  ASSERT_NE(nullptr, fy);
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, x));
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, y));
  Expr congruent = vc_eqExpr(vc, fx, fy);
  EXPECT_EQ(1, vc_query(vc, congruent)); // 1: valid
  vc_DeleteExpr(congruent);

  vc_DeleteExpr(isNaNOfResult);
  vc_DeleteExpr(qRne);
  vc_DeleteExpr(rne);
  vc_DeleteExpr(fy);
  vc_DeleteExpr(fx);
  vc_DeleteExpr(y);
  vc_DeleteExpr(x);
  vc_DeleteExpr(bv4);
  vc_DeleteExpr(mode);
  vc_DeleteExpr(single);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// Reading a float and a rounding mode back out of a certified model, at the
// declared sort rather than as the packed carrier the checker solved them as.
TEST(UninterpretedFunctionsCAPI, FloatingPointAndRoundingModeModelValues)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');
  vc_setFlag(vc, 'c');

  Type single = vc_fpType(vc, 8, 24);
  Type mode = vc_fpRoundingModeType(vc);
  Type bv4 = vc_bvType(vc, 4);
  const Type fromBits[] = {bv4};
  UFDeclHandle k = vc_declareUninterpretedFunction(vc, "k", fromBits, 1, mode);
  UFDeclHandle q =
      vc_declareUninterpretedFunction(vc, "q", fromBits, 1, single);
  ASSERT_NE(0u, k);
  ASSERT_NE(0u, q);

  Expr index = vc_bvConstExprFromInt(vc, 4, 3);
  const Expr at[] = {index};
  Expr kAt = vc_applyUninterpretedFunction(vc, k, at, 1);
  Expr qAt = vc_applyUninterpretedFunction(vc, q, at, 1);
  ASSERT_NE(nullptr, kAt);
  ASSERT_NE(nullptr, qAt);

  Expr rtz = vc_fpRoundingMode(vc, VC_RM_RTZ);
  Expr nan = vc_fpNaN(vc, single);
  vc_assertFormula(vc, vc_eqExpr(vc, kAt, rtz));
  vc_assertFormula(vc, vc_fpIsNaNExpr(vc, qAt));
  Expr falseQuery = vc_falseExpr(vc);
  ASSERT_EQ(0, vc_query(vc, falseQuery)); // 0: invalid, i.e. satisfiable
  vc_DeleteExpr(falseQuery);

  // A rounding mode comes back as one of the five, never as a bare 5-bit
  // vector: all-zeros and the twenty-six other patterns denote no mode.
  Expr modeValue = vc_getUninterpretedFunctionValue(vc, kAt);
  ASSERT_NE(nullptr, modeValue);
  EXPECT_EQ((unsigned)VC_RM_RTZ, getBVUnsigned(modeValue));
  vc_DeleteExpr(modeValue);

  // A float comes back at the declared format.
  Expr floatValue = vc_getUninterpretedFunctionValue(vc, qAt);
  ASSERT_NE(nullptr, floatValue);
  EXPECT_EQ(8, vc_getExpWidth(floatValue));
  EXPECT_EQ(24, vc_getSigWidth(floatValue));
  vc_DeleteExpr(floatValue);

  vc_DeleteExpr(nan);
  vc_DeleteExpr(rtz);
  vc_DeleteExpr(qAt);
  vc_DeleteExpr(kAt);
  vc_DeleteExpr(index);
  vc_DeleteExpr(bv4);
  vc_DeleteExpr(mode);
  vc_DeleteExpr(single);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

// Array stays refused, and so does anything that is not a sort at all: a
// value expression of the right sort is not a Type.
TEST(UninterpretedFunctionsCAPI, ArraysAndNonSortsAreStillRejected)
{
  vc_registerErrorHandler(countError);
  errors = 0;
  VC vc = vc_createValidityChecker();
  vc_setFlag(vc, 'u');

  Type bv8 = vc_bvType(vc, 8);
  Type array = vc_arrayType(vc, bv8, bv8);
  EXPECT_EQ(0u, vc_declareUninterpretedFunction(vc, "a", &array, 1, bv8));
  EXPECT_EQ(0u, vc_declareUninterpretedFunction(vc, "r", &bv8, 1, array));

  Expr notAType = vc_varExpr(vc, "v", bv8);
  Type disguised = (Type)notAType;
  EXPECT_EQ(0u, vc_declareUninterpretedFunction(vc, "d", &disguised, 1, bv8));
  EXPECT_EQ(3, errors);

  vc_DeleteExpr(notAType);
  vc_DeleteExpr(array);
  vc_DeleteExpr(bv8);
  vc_Destroy(vc);
  vc_registerErrorHandler(nullptr);
}

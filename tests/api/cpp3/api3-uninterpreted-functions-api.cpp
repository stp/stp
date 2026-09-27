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

// api3-uninterpreted-functions-api.cpp -- uninterpreted functions through the
// API: declaration, application and their refusals, the values a model gives
// applications and the terms containing them, floating-point and
// rounding-mode signatures, and the sorts a function cannot take.
//
// 2.x declared a function with vc_declareUninterpretedFunction (after the 'u'
// flag), which returned a UFDeclHandle, applied it with
// vc_applyUninterpretedFunction, and read an application's value with
// vc_getUninterpretedFunctionValue, which answered only for an application
// the last satisfiable query had reached (a "certified" value) and only until
// the next assertion, push or pop. In 3.x a function is a term of a function
// sort, declared and applied whatever the uninterpreted-functions option
// says. A Model evaluates any term, applications included, and survives every
// later assertion, push and pop; its strict reader is try_value, which
// refuses what the check never assigned instead of completing it.

#include "api3_common.hpp"

#include <initializer_list>
#include <type_traits>
#include <vector>

using namespace stp;

namespace
{

// A function over Bool (width 0) and bit-vector sorts, as the 2.x helper
// declared them.
Term declareFunction(TermManager& tm, const char* name,
                     std::initializer_list<unsigned> domainWidths, unsigned codomainWidth)
{
  std::vector<Sort> domain;
  domain.reserve(domainWidths.size());
  for (const unsigned width : domainWidths)
    domain.push_back(width == 0 ? tm.mk_bool_sort() : tm.mk_bv_sort(width));
  const Sort codomain = codomainWidth == 0 ? tm.mk_bool_sort() : tm.mk_bv_sort(codomainWidth);
  return tm.declare(name, tm.mk_fun_sort(domain, codomain));
}

// The options of a 2.x checker: vc_createValidityChecker set 'd', so every
// 2.x case ran with the counterexample self-check on, and every solver here
// runs with check-sanity.
Options checkerOptions()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

} // namespace

TEST(UninterpretedFunctionsCAPI, OwnershipTypingAndNonfatalRejection)
{
  // 2.x set 'u' on both checkers; 3.x needs no switch to declare or apply.
  TermManager first;
  TermManager second;

  const Term f = declareFunction(first, "f", {8, 0}, 16);
  ASSERT_FALSE(f.is_null());
  // 3.x: declare is keyed by name and sort, so the same declaration again is
  // the same function (2.x refused it); the name at another sort is refused.
  EXPECT_TRUE(declareFunction(first, "f", {8, 0}, 16).same_as(f));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, first.declare("f", first.mk_bv_sort(8)));

  const Term bv8 = first.declare("x", first.mk_bv_sort(8));
  const Term boolean = first.declare("b", first.mk_bool_sort());
  const Term application = f(bv8, boolean);
  ASSERT_FALSE(application.is_null());
  EXPECT_EQ(application.kind(), Kind::APPLY);
  EXPECT_EQ(application.sort().bv_size(), 16u);

  API3_EXPECT_ERROR(ErrorCode::ARITY, f(bv8));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, f(boolean, boolean));
  // 2.x applied first's function in the second checker; 3.x has no checker
  // argument, and a function of one manager over the actuals of another is
  // refused.
  const Term otherBv8 = second.declare("x", second.mk_bv_sort(8));
  const Term otherBoolean = second.declare("b", second.mk_bool_sort());
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, f(otherBv8, otherBoolean));
}

// 2.x refused a declaration before 'u' was set, and a zero-arity one. 3.x's
// uninterpreted-functions option never gates construction: a function is
// declared and applied under the default (auto) and under off alike, and off
// makes the check refuse the content instead. A zero-arity function is an
// ordinary symbol of the codomain sort: mk_fun_sort refuses an empty domain.
TEST(UninterpretedFunctionsCAPI, DefaultOffAndZeroArityAreRejected)
{
  TermManager tm;
  const Sort bv8 = tm.mk_bv_sort(8);
  const Term x = tm.declare("x", bv8);

  // the option's default (auto): declared, applied and decided
  const Term byDefault = tm.declare("by_default", tm.mk_fun_sort({bv8}, bv8));
  Solver s(tm, checkerOptions());
  s.add(byDefault(x) == 1);
  EXPECT_TRUE(s.check_sat().is_sat());

  // 3.x: under off the declaration still succeeds; the check is refused
  Options o = checkerOptions();
  o.set("uninterpreted-functions", "off");
  Solver off(tm, o);
  const Term offFunction = tm.declare("off", tm.mk_fun_sort({bv8}, bv8));
  off.add(offFunction(x) == 1);
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, off.check_sat());

  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_fun_sort({}, bv8));
}

TEST(UninterpretedFunctionsCAPI, CertifiedDurableValuesBatchAndRejection)
{
  TermManager first;
  TermManager second;
  Solver s(first, checkerOptions());
  Solver other(second, checkerOptions());

  const Term f = declareFunction(first, "f", {8}, 8);
  const Term x = first.declare("x", first.mk_bv_sort(8));
  const Term application = f(x);
  const Term expected = first.mk_bv(8, 42);
  const Term equation = application == expected;
  s.add(equation);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  // vc_getUninterpretedFunctionValue and vc_getCounterExample
  EXPECT_EQ(m.uint64_value(application), 42u);
  EXPECT_EQ(s.value(application).to_uint64(), 42u);
  // the batch reader, and the function's table at x's value, agree
  const std::vector<Term> values = m.values({application, x});
  ASSERT_EQ(values.size(), 2u);
  EXPECT_EQ(values[0].to_uint64(), 42u);
  EXPECT_EQ(m.function_value(f).apply({values[1]}).to_uint64(), 42u);
  EXPECT_TRUE(m.in_core(f));

  // An application over a symbol the check never saw was not part of the
  // solve. 2.x refused its value; 3.x's strict reader refuses to complete it,
  // while value() completes it.
  const Term y = first.declare("y", first.mk_bv_sort(8));
  const Term inactive = f(y);
  EXPECT_FALSE(m.try_value(inactive).has_value());
  EXPECT_TRUE(m.value(inactive).is_value());
  // A foreign context cannot read the first context's application.
  ASSERT_TRUE(other.check_sat().is_sat());
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, other.model().value(application));

  // 2.x: mutating the asserted root invalidated the certified map at once.
  // 3.x: an assertion never invalidates a model.
  const Term tautology = first.mk_true();
  s.add(tautology);
  EXPECT_EQ(s.model().uint64_value(application), 42u);
  EXPECT_EQ(m.uint64_value(application), 42u);
}

TEST(UninterpretedFunctionsCAPI, CertifiedDurableValuePersistentMode)
{
  TermManager tm;
  Options o = checkerOptions();
  o.set("incremental", "on"); // 'i'
  Solver s(tm, o);

  const Term p = declareFunction(tm, "p", {0, 9}, 0);
  const Term b = tm.declare("b", tm.mk_bool_sort());
  const Term x = tm.declare("x", tm.mk_bv_sort(9));
  const Term application = p(b, x);
  s.add(application);

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_TRUE(m.bool_value(application));
  EXPECT_TRUE(m.value(application).same_as(tm.mk_true()));

  // 2.x: a real stack mutation cleared the block-owned certified map.
  // 3.x: a push leaves the model as it was.
  s.push();
  EXPECT_TRUE(s.model().bool_value(application));

  // Re-check inside the pushed level; 2.x then invalidated the value at the
  // matching pop, 3.x keeps it.
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(s.model().bool_value(application));
  s.pop();
  EXPECT_TRUE(s.model().bool_value(application));
  EXPECT_TRUE(m.bool_value(application));
}

// Reading the model value of a term that *contains* an application, rather
// than an application itself. The enclosing operator needs a value for its
// operand, so refusing is not an option here: an application the solve never
// reached is completed through the function's table. In 2.x every case below
// once aborted the process from the counterexample walk.
TEST(UninterpretedFunctionsCAPI, ValuesOfTermsContainingApplications)
{
  TermManager tm;
  Solver s(tm, checkerOptions());

  const Term f = declareFunction(tm, "f", {8}, 8);
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  const Term seven = tm.mk_bv(8, 7);
  const Term fx = f(x);
  // Same argument tuple as fx once x is pinned to 7, but a distinct term that
  // the solve never reaches.
  const Term fSeven = f(seven);
  ASSERT_FALSE(fSeven.same_as(fx));

  s.add(x == seven);
  s.add(fx == tm.mk_bv(8, 3));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  const Term one = tm.mk_bv(8, 1);

  // A bit-vector operator over an application.
  EXPECT_EQ(m.uint64_value(bvadd(fx, one)), 4u);

  // A predicate over an application.
  EXPECT_TRUE(m.bool_value(fx == tm.mk_bv(8, 3)));

  // Congruence across the reached/unreached boundary: f(7) shares f(x)'s
  // argument tuple and must share its value. Completing with an arbitrary
  // constant instead would break this.
  EXPECT_EQ(m.uint64_value(bvadd(fSeven, one)), 4u);

  // The original term keeps its value, through either reader.
  EXPECT_EQ(m.uint64_value(fx), 3u);
  ASSERT_TRUE(m.try_value(fx).has_value());
  EXPECT_EQ(m.try_value(fx)->to_uint64(), 3u);

  // An application the solve never reached -- not as itself and not as
  // anything it was rewritten to -- has no value of its own. 2.x's root
  // accessor refused it; 3.x's strict reader does, and value() completes it
  // with the function's default.
  const Term fEight = f(tm.mk_bv(8, 8));
  EXPECT_FALSE(m.try_value(fEight).has_value());
  EXPECT_TRUE(m.value(fEight).same_as(m.function_value(f).else_value()));
}

// A Bool-codomain application nested in a formula reaches the formula walk
// rather than the term walk, and in 2.x used to abort there with a different
// diagnostic than the bit-vector case.
TEST(UninterpretedFunctionsCAPI, ValuesOfFormulasContainingBoolApplications)
{
  TermManager tm;
  Solver s(tm, checkerOptions());

  const Term g = declareFunction(tm, "g", {0}, 0);
  const Term p = tm.declare("p", tm.mk_bool_sort());
  const Term q = tm.declare("q", tm.mk_bool_sort());
  const Term gp = g(p);

  s.add(gp);
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  // g(p) is asserted, so it holds; its negation must therefore be false.
  EXPECT_TRUE(m.bool_value(gp));
  const Term negated = !gp;
  EXPECT_FALSE(m.bool_value(negated));

  // With g(p) true, both of these reduce to q's own model value.
  const Term qValue = m.value(q);
  ASSERT_TRUE(qValue.sort().is_bool());
  const bool expected = qValue.to_bool();

  for (const Term& nested : {gp && q, gp == q})
    EXPECT_EQ(m.bool_value(nested), expected) << nested;
}

// The sorts the 2.x C API used to refuse. Its converter had its own
// hand-rolled list, strictly narrower than the one an .smt2 file gets, so a
// signature the parser accepted could not be built there at all.
TEST(UninterpretedFunctionsCAPI, FloatingPointAndRoundingModeSignatures)
{
  TermManager tm;
  Solver s(tm, checkerOptions());

  const Sort single = tm.mk_fp_sort(8, 24);
  const Sort mode = tm.mk_rm_sort();
  const Sort bv4 = tm.mk_bv_sort(4);

  const Term f = tm.declare("f", tm.mk_fun_sort({single}, bv4));
  const Term k = tm.declare("k", tm.mk_fun_sort({bv4}, mode));
  const Term q = tm.declare("q", tm.mk_fun_sort({mode}, single));
  EXPECT_TRUE(f.sort().is_fun());
  EXPECT_TRUE(k(tm.mk_bv(4, 0)).sort().is_rm());

  // An application at a float codomain is a float of the declared format,
  // not its packed carrier: it has to be usable as a floating-point operand.
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term qRne = q(rne);
  EXPECT_EQ(qRne.sort().fp_exp_size(), 8u);
  EXPECT_EQ(qRne.sort().fp_sig_size(), 24u);
  const Term isNaNOfResult = fp_is_nan(qRne);
  EXPECT_TRUE(isNaNOfResult.sort().is_bool());

  // Congruence over a float argument is congruence over its *value*. x and y
  // are both NaN, which is one value however each was built, so f(x) and f(y)
  // must agree -- the entailment below is valid.
  const Term x = tm.declare("x", single);
  const Term y = tm.declare("y", single);
  const Term fx = f(x);
  const Term fy = f(y);
  s.add(fp_is_nan(x));
  s.add(fp_is_nan(y));
  EXPECT_TRUE(s.entails(fx == fy).is_valid());
}

// Reading a float and a rounding mode back out of a model, at the declared
// sort rather than as the packed carrier the solver solved them as.
TEST(UninterpretedFunctionsCAPI, FloatingPointAndRoundingModeModelValues)
{
  TermManager tm;
  Options o = checkerOptions();
  o.set_bool("produce-models", true); // 'c'
  Solver s(tm, o);

  const Sort single = tm.mk_fp_sort(8, 24);
  const Sort mode = tm.mk_rm_sort();
  const Sort bv4 = tm.mk_bv_sort(4);
  const Term k = tm.declare("k", tm.mk_fun_sort({bv4}, mode));
  const Term q = tm.declare("q", tm.mk_fun_sort({bv4}, single));

  const Term index = tm.mk_bv(4, 3);
  const Term kAt = k(index);
  const Term qAt = q(index);

  const Term rtz = tm.mk_rm(RoundingMode::RTZ);
  const Term nan = tm.mk_fp_nan(single);
  s.add(kAt == rtz);
  s.add(fp_is_nan(qAt));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();

  // A rounding mode comes back as one of the five, never as a bare 5-bit
  // vector: all-zeros and the twenty-six other patterns denote no mode.
  EXPECT_EQ(m.rm_value(kAt), RoundingMode::RTZ);
  const Term modeValue = m.value(kAt);
  EXPECT_TRUE(modeValue.sort().is_rm());
  EXPECT_EQ(modeValue.to_rm(), RoundingMode::RTZ);

  // A float comes back at the declared format, and a NaN is the NaN.
  const Term floatValue = m.value(qAt);
  EXPECT_EQ(floatValue.sort().fp_exp_size(), 8u);
  EXPECT_EQ(floatValue.sort().fp_sig_size(), 24u);
  EXPECT_EQ(m.fp_value(qAt).cls, FloatValue::Class::NOT_A_NUMBER);
  EXPECT_TRUE(floatValue.same_as(nan));
}

// Arrays stay refused, and so does anything that is not a sort at all.
TEST(UninterpretedFunctionsCAPI, ArraysAndNonSortsAreStillRejected)
{
  TermManager tm;

  const Sort bv8 = tm.mk_bv_sort(8);
  const Sort array = tm.mk_array_sort(bv8, bv8);
  // 3.x: the function sort can be made; declaring a function of it is refused
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.declare("a", tm.mk_fun_sort({array}, bv8)));
  API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.declare("r", tm.mk_fun_sort({bv8}, array)));

  // 2.x's value expression disguised as a Type cannot be written in C++: a
  // term is not a sort. What can be passed is the null sort, which is refused.
  static_assert(!std::is_convertible_v<Term, Sort>, "a term is not a sort");
  const Term notAType = tm.declare("v", bv8);
  EXPECT_TRUE(notAType.sort() == bv8);
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, tm.mk_fun_sort({Sort()}, bv8));

  // and nothing was declared
  EXPECT_FALSE(tm.symbol("a").has_value());
  EXPECT_FALSE(tm.symbol("r").has_value());
}

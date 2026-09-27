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

// api3_real_capability_api_tests.cpp -- two Real capabilities through the 3.x
// C++ API: a Real-branch if-then-else, and Real as an admissible sort in an
// uninterpreted function's signature. Both are decided by the core and
// reachable from an .smt2 file; these tests pin their API spellings (ite over
// Real branches, a function sort with Real in its domain or codomain), so the
// API cannot drift back behind the parser. Beside them: reading the exact
// model back, the exact-Real options, and the exact-arithmetic budget
// refusing work without harming the manager or the solver.
//
// A plain executable: every case owns its manager and solver, the first
// failed check ends the run with a non-zero exit, and naming one case on the
// command line runs only that case. A check the 3.x API cannot make yet is
// reported as an API gap and skipped, not failed.

#include <stp/stp.hpp>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using namespace stp;

namespace
{

unsigned skipped_checks = 0;

void require(bool condition, const char* detail)
{
  if (!condition)
    throw std::runtime_error(detail);
}

// A check that needs something the 3.x API does not provide yet.
void apiGap(const char* where, const char* what)
{
  ++skipped_checks;
  std::cerr << "SKIP " << where << ": API gap: " << what << '\n';
}

// The code of the RecoverableError that f throws; a run that throws nothing
// is a failure of the calling check.
ErrorCode refusal(const std::function<void()>& f, const char* detail)
{
  try
  {
    f();
  }
  catch (const RecoverableError& error)
  {
    return error.code();
  }
  throw std::runtime_error(detail);
}

Options checkerOptions(bool uninterpreted_functions)
{
  Options options;
  if (uninterpreted_functions)
    options.set_str("uninterpreted-functions", "on");
  return options;
}

// A manager and a solver over it. Uninterpreted functions are switched on for
// the cases that apply them, before the first check as the option requires
// (2.x's 'u' flag; its default, auto, decides them as well).
struct Checker final
{
  explicit Checker(bool uninterpreted_functions = false)
      : s(tm, checkerOptions(uninterpreted_functions))
  {
  }

  TermManager tm;
  Solver s;
};

Term real(Checker& owner, const char* text)
{
  return owner.tm.mk_real(text);
}

Term realSymbol(Checker& owner, const char* name)
{
  return owner.tm.declare(name, owner.tm.mk_real_sort());
}

// check_sat answers the satisfiability of the assertions directly (2.x
// queried the validity of false for it).
Result solve(Checker& owner)
{
  return owner.s.check_sat();
}

// The exact value of a Real term in the model of the last check, as "n/d" or
// "n". A model exists exactly after a check that answered sat, and it values
// every term of its manager: 2.x's two questions, whether an exact model was
// published and whether it valued this term, are that one.
std::string realModelValue(Checker& owner, const Term& term)
{
  return owner.s.model().real_value(term).str();
}

// Whether the model values a Real-valued uninterpreted-function application
// of its own accord. The 3.x model does not yet: it answers every such
// application with the codomain's default, 0, as a completion (try_value
// gives nothing), asserted applications included. A check that needs the
// value is skipped as an API gap until it does.
bool realApplicationValued(Checker& owner, const Term& application,
                           const char* where)
{
  if (owner.s.model().try_value(application).has_value())
    return true;
  apiGap(where, "the model has no value for a Real-valued uninterpreted-"
                "function application (Model::value answers the default 0)");
  return false;
}

// 2.x reported four capabilities: Real construction, QF_LRA, the Real-branch
// ite and QF_UFLRA. 3.x reports one, lra; the other three are what the kinds
// table admits, pinned here by construction.
void capabilitiesAreReported()
{
  const std::map<std::string, std::string> reported = capabilities();
  const auto lra = reported.find("lra");
  require(lra != reported.end() && lra->second == "true",
          "QF_LRA semantic capability");
  TermManager tm;
  const Sort real_sort = tm.mk_real_sort();
  require(real_sort.is_real(), "Real construction capability");
  const Term c = tm.declare("c", tm.mk_bool_sort());
  require(ite(c, tm.mk_real(3), tm.mk_real(5)).sort().is_real(),
          "Real-branch ite construction capability");
  const Sort f = tm.mk_fun_sort({real_sort}, real_sort);
  require(f.is_fun() && f.fun_domain().at(0).is_real() &&
              f.fun_codomain().is_real(),
          "QF_UFLRA semantic capability");
}

// (ite c 3 5) with c pinned each way. The branch not taken must not reach the
// model, which is the whole point of building it as a Real term rather than
// refusing it.
void realIteSelectsItsBranch(bool condition)
{
  Checker owner;
  const Term c = owner.tm.declare("c", owner.tm.mk_bool_sort());
  const Term selected = ite(c, real(owner, "3"), real(owner, "5"));
  const Term x = realSymbol(owner, "x");
  owner.s.add(x == selected);
  owner.s.add(condition ? c : !c);

  require(solve(owner).is_sat(), "pinned Real ite was not SAT");
  const std::string expected = condition ? "3" : "5";
  const std::string actual = realModelValue(owner, x);
  if (actual != expected)
    throw std::runtime_error("Real ite selected " + actual + ", expected " +
                             expected);
}

// A symbolic condition over symbolic branches, constrained so exactly one
// branch can satisfy the surrounding bound: the ite has to be understood by
// the theory, not merely built.
void realIteUnderTheory()
{
  Checker owner;
  const Term c = owner.tm.declare("c", owner.tm.mk_bool_sort());
  const Term lo = realSymbol(owner, "lo");
  const Term hi = realSymbol(owner, "hi");
  owner.s.add(lo == real(owner, "1/4"));
  owner.s.add(hi == real(owner, "9/4"));

  const Term chosen = ite(c, lo, hi);
  // Only the hi branch clears 2, so the condition is forced false.
  owner.s.add(real_gt(chosen, real(owner, "2")));

  require(solve(owner).is_sat(), "symbolic Real ite was not SAT");
  const std::string actual = realModelValue(owner, chosen);
  if (actual != "9/4")
    throw std::runtime_error("Real ite under a bound gave " + actual +
                             ", expected 9/4");
}

// Both branches out of range: the ite must make this UNSAT rather than
// quietly evaluating to one branch.
void realIteConflicts()
{
  Checker owner;
  const Term c = owner.tm.declare("c", owner.tm.mk_bool_sort());
  const Term chosen = ite(c, real(owner, "1"), real(owner, "2"));
  owner.s.add(real_gt(chosen, real(owner, "10")));
  require(solve(owner).is_unsat(), "unsatisfiable Real ite was not UNSAT");
}

// An ite nested under linear arithmetic: the result feeds a sum, so the node
// has to carry Real sort onwards and not just typecheck in isolation.
void realIteFeedsArithmetic()
{
  Checker owner;
  const Term c = owner.tm.declare("c", owner.tm.mk_bool_sort());
  const Term chosen = ite(c, real(owner, "1/2"), real(owner, "3/2"));
  const Term sum = real_add(chosen, real(owner, "1/2"));
  const Term x = realSymbol(owner, "x");
  owner.s.add(x == sum);
  owner.s.add(!c);

  require(solve(owner).is_sat(), "Real ite under addition was not SAT");
  const std::string actual = realModelValue(owner, x);
  if (actual != "2")
    throw std::runtime_error("Real ite under addition gave " + actual +
                             ", expected 2");
}

// An uninterpreted function is a symbol of a function sort; declaring it is
// declaring that symbol.
Term declare(Checker& owner, const char* name, const std::vector<Sort>& domain,
             const Sort& codomain)
{
  return owner.tm.declare(name, owner.tm.mk_fun_sort(domain, codomain));
}

// The SMT-LIB Real lexer does not admit every mixed-sort signature, so use
// the API to pin model completion for all other scalar argument sorts.
void realUfScalarModelCompletion()
{
  for (bool propagate : {false, true})
    for (bool rounding : {false, true})
    {
      Checker owner(true);
      TermManager& tm = owner.tm;
      owner.s.options().set_str("uf-propagate-equalities",
                                propagate ? "on" : "off");
      const Sort domain = rounding ? tm.mk_rm_sort() : tm.mk_bv_sort(8);
      const Term f = declare(owner, "scalar_f", {domain}, tm.mk_real_sort());
      const Term x = tm.declare("scalar_x", domain);
      const Term y = tm.declare("scalar_y", domain);
      const Term z = tm.declare("scalar_z", domain);
      const Term first = rounding ? tm.mk_rm(RoundingMode::RNE) : tm.mk_bv(8, 1);
      const Term second =
          rounding ? tm.mk_rm(RoundingMode::RTZ) : tm.mk_bv(8, 2);
      const Term third = rounding ? tm.mk_rm(RoundingMode::RTP) : tm.mk_bv(8, 3);
      owner.s.add(x == first);
      owner.s.add(y == x);
      owner.s.add(z == second);
      owner.s.add(f(x) == real(owner, "4"));
      owner.s.add(f(second) == real(owner, "6"));
      require(solve(owner).is_sat(), "mixed scalar/Real model was not SAT");

      const Term next =
          rounding ? ite(tm.mk_false(), y, second) : bvadd(y, first);
      // An unobserved tuple is a completion: the codomain's default.
      require(realModelValue(owner, f(third)) == "0",
              "unobserved scalar tuple did not use the default");
      if (!realApplicationValued(owner, f(y), "real-uf-scalar-model-completion"))
        continue;
      require(realModelValue(owner, f(y)) == "4",
              "equal scalar values selected different function results");
      require(realModelValue(owner, f(z)) == "6",
              "distinct scalar values selected the same function result");
      require(realModelValue(owner, f(next)) == "6",
              "computed scalar value did not select the observed result");
    }
}

void realUfFloatingPointModelCompletion()
{
  for (bool propagate : {false, true})
  {
    Checker owner(true);
    TermManager& tm = owner.tm;
    owner.s.options().set_str("uf-propagate-equalities",
                              propagate ? "on" : "off");
    const Sort fp = tm.mk_fp_sort(8, 24);
    const Term f = declare(owner, "fp_f", {fp}, tm.mk_real_sort());
    // The 3.x constructor canonicalises a NaN, so every NaN pattern below is
    // one term; that the function sees one argument is what is pinned.
    const auto bits = [&](std::uint64_t value) {
      return tm.mk_fp_from_bits(fp, tm.mk_bv(32, value));
    };
    const Term x = tm.declare("fp_x", fp);
    const Term y = tm.declare("fp_y", fp);
    const Term pz = tm.declare("fp_pz", fp);
    const Term nz = tm.declare("fp_nz", fp);
    const Term positive_zero = bits(0);
    const Term negative_zero = bits(0x80000000U);
    owner.s.add(x == bits(0x7fc00001U));
    owner.s.add(y == bits(0x7f800002U));
    owner.s.add(pz == positive_zero);
    owner.s.add(nz == negative_zero);
    owner.s.add(f(x) == real(owner, "5"));
    owner.s.add(f(positive_zero) == real(owner, "7"));
    owner.s.add(f(negative_zero) == real(owner, "9"));
    require(solve(owner).is_sat(), "mixed FP/Real model was not SAT");

    if (!realApplicationValued(owner, f(y), "real-uf-fp-model-completion"))
      continue;
    require(realModelValue(owner, f(y)) == "5" &&
                realModelValue(owner, f(bits(0xffc12345U))) == "5",
            "NaN payloads did not name the same function argument");
    require(realModelValue(owner, f(fp_neg(nz))) == "7" &&
                realModelValue(owner, f(fp_neg(pz))) == "9",
            "floating-point signed zeros were conflated");
  }
}

// Real -> Real, declared, applied and solved. The declaration is the half
// that the uninterpreted-function signature check once refused.
void realUninterpretedFunction()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term x = realSymbol(owner, "x");
  const Term fx = f(x);
  owner.s.add(x == real(owner, "7/3"));
  owner.s.add(fx == real(owner, "-5/2"));

  require(solve(owner).is_sat(), "Real-sorted UF application was not SAT");
  const std::string actual = realModelValue(owner, x);
  if (actual != "7/3")
    throw std::runtime_error("Real UF argument gave " + actual +
                             ", expected 7/3");
}

// A constraint on the application alone has to be respected even though no
// equality pins the argument: the result is a solved unknown of its own.
void realUninterpretedFunctionResultIsConstrained()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term x = realSymbol(owner, "x");
  const Term fx = f(x);
  owner.s.add(real_gt(fx, real(owner, "1")));
  owner.s.add(real_lt(fx, real(owner, "1")));
  require(solve(owner).is_unsat(),
          "contradictory bounds on a Real UF result were not UNSAT");
}

// The application itself is readable, not just its argument: the UF lowering
// replaces it with a result symbol before the arithmetic sees it, and the
// solved value has to answer for the node the caller actually holds.
void realUninterpretedFunctionValueIsReadable()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term x = realSymbol(owner, "x");
  const Term fx = f(x);
  owner.s.add(x == real(owner, "7/3"));
  owner.s.add(fx == real(owner, "-5/2"));
  require(solve(owner).is_sat(), "Real-sorted UF application was not SAT");

  if (!realApplicationValued(owner, fx, "real-uf-value-readable"))
    return;
  const std::string actual = realModelValue(owner, fx);
  if (actual != "-5/2")
    throw std::runtime_error("Real UF application read back as " + actual +
                             ", expected -5/2");
  // The numerator and denominator answer for it too.
  const RationalValue value = owner.s.model().real_value(fx);
  if (value.numerator != "-5" || value.denominator != "2")
    throw std::runtime_error("Real UF application components were " +
                             value.numerator + "/" + value.denominator +
                             ", expected -5/2");
}

// Congruence forces two applications to one value, and both nodes have to
// report it -- the mapping covers every application the solve lowered, not
// just the first.
void realUninterpretedFunctionCongruentValuesAgree()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term x = realSymbol(owner, "x");
  const Term y = realSymbol(owner, "y");
  const Term fx = f(x);
  const Term fy = f(y);
  owner.s.add(x == y);
  owner.s.add(fx == real(owner, "11/7"));
  // f(y) has to appear in the formula to be lowered at all: an application
  // the solve never reached has no value of its own, which is the same rule
  // that governs the bit-vector ones.
  owner.s.add(real_gt(fy, real(owner, "0")));
  require(solve(owner).is_sat(), "congruent Real UF applications were not SAT");

  if (!realApplicationValued(owner, fx, "real-uf-congruent-values-agree"))
    return;
  const std::string left = realModelValue(owner, fx);
  const std::string right = realModelValue(owner, fy);
  if (left != "11/7" || right != "11/7")
    throw std::runtime_error("congruent Real UF applications read back as " +
                             left + " and " + right + ", expected 11/7 twice");
}

// Congruence over a Real domain: equal arguments must take equal values,
// decided from the arithmetic's exact model values rather than a packed
// carrier.
void realUninterpretedFunctionCongruence()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term x = realSymbol(owner, "x");
  const Term y = realSymbol(owner, "y");
  owner.s.add(x == y);
  owner.s.add(!(f(x) == f(y)));
  require(solve(owner).is_unsat(), "Real UF congruence was not enforced");
}

// The arguments are equal as *rationals* without being syntactically equal,
// which is the case a carrier-comparing core would get wrong. Both arguments
// stay symbolic; a concrete argument is covered by
// realUninterpretedFunctionConstantArgumentTeardown.
void realUninterpretedFunctionCongruenceAcrossArithmetic()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term x = realSymbol(owner, "x");
  const Term y = realSymbol(owner, "y");
  const Term shift = realSymbol(owner, "shift");
  owner.s.add(x == y);

  // x + shift and y + shift are the same rational however shift is chosen,
  // so f has to agree on them.
  const Term left = real_add(x, shift);
  const Term right = real_add(y, shift);
  owner.s.add(!(f(left) == f(right)));
  require(solve(owner).is_unsat(),
          "Real UF congruence did not survive exact arithmetic");
}

// A Real literal in an uninterpreted-function argument reaches the frontend
// registry, which holds a reference to it for the life of the manager. That
// is correct; what was wrong was where the manager checked that no exact
// constant had outlived its references -- before the delete that releases
// them rather than after -- so this shape asserted at teardown.
//
// The application has to reach the solver for the registry to see it:
// building f(1) and never constraining it was always clean, as was every
// application over symbolic arguments. Nothing about the answers was ever
// wrong.
void realUninterpretedFunctionConstantArgumentTeardown()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term applied = f(real(owner, "1"));
  owner.s.add(real_gt(applied, real(owner, "1")));
  require(solve(owner).is_sat(), "Real UF over a constant argument was not SAT");
}

// Preregistering an assertion does exact arithmetic, so the number budget can
// refuse it: every constant below is individually representable, but folding
// them into one linear form is not. The refusal must never leave a caller
// with an answer to a query missing one of its assertions, which is the
// wrong-answer direction rather than the incomplete one.
//
// The shape is a murxla trace reduced by delta debugging; it is transcribed
// rather than generated because what matters is landing just past the budget
// at normalisation while staying under it at every constructor.
void refusedRealAssertionLeavesNoAnswer()
{
  Checker owner(true);

  const Term x = realSymbol(owner, "x");
  owner.s.add(x == real(owner, "1"));
  require(solve(owner).is_sat(), "a plain Real equality should be SAT");

  Term refused;
  try
  {
    const Term c = real(owner, "85540413.44455765206262857018");
    const Term n0 = real_neg(c);
    const Term p1 = real_mul(c, n0);
    const Term p2 = real_mul(real_mul(p1, real_mul(p1, p1)), p1);
    const Term s3 = real_add(p2, n0);
    const Term p4 = real_mul(real_mul(s3, p2), real_sub(s3, c));
    const Term p5 = real_mul(real_mul(p4, p4), p4);
    const Term d6 = real_sub(p5, n0);
    const Term a7 = real_add(p5, n0);
    const Term lhs = real_sub(real_neg(real_sub(d6, n0)), n0);
    const Term rhs =
        real_mul(real_mul(a7, real_sub(real_mul(real_neg(a7), n0), n0)), a7);
    const Term big = real_mul(real_mul(real_mul(lhs, rhs), d6), real_add(n0, p5));
    refused = real_lt(big, big);
  }
  catch (const RecoverableError&)
  {
    throw std::runtime_error(
        "every constructor should have stayed inside the budget");
  }
  require(!refused.is_null(), "the comparison should have been constructed");

  // 3.x: the refusal is a recoverable error thrown by the assert itself, so
  // the caller learns of it where it happens, and the solver is left as it
  // was: the refused assertion is not held, and the next check answers for
  // the assertions that are.
  const std::size_t held = owner.s.assertions().size();
  require(refusal([&] { owner.s.add(refused); },
                  "an assertion past the budget was accepted") ==
              ErrorCode::UNSUPPORTED,
          "the refused assertion must name the cause");
  require(owner.s.assertions().size() == held,
          "a refused assertion must leave the solver's assertions as they were");
  require(solve(owner).is_sat() && realModelValue(owner, x) == "1",
          "the solver must answer for the assertions it holds");
}

// Distinct arguments leave the function free, so this must stay SAT --
// congruence must not be over-applied.
void realUninterpretedFunctionStaysFree()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term x = realSymbol(owner, "x");
  const Term y = realSymbol(owner, "y");
  owner.s.add(x == real(owner, "1"));
  owner.s.add(y == real(owner, "2"));
  owner.s.add(!(f(x) == f(y)));
  require(solve(owner).is_sat(),
          "Real UF over distinct arguments was wrongly UNSAT");
}

// Real in either half of a signature, and mixed with the sorts that were
// already admissible.
void realUninterpretedFunctionSignatures()
{
  Checker owner(true);
  TermManager& tm = owner.tm;
  const Sort real_sort = tm.mk_real_sort();
  const Sort bool_sort = tm.mk_bool_sort();
  const Sort bv_sort = tm.mk_bv_sort(8);

  const Term predicate = declare(owner, "p", {real_sort}, bool_sort);
  const Term from_bv = declare(owner, "g", {bv_sort}, real_sort);
  const Term mixed = declare(owner, "h", {real_sort, bv_sort}, real_sort);

  const Term x = realSymbol(owner, "x");
  const Term b = tm.declare("b", bv_sort);
  owner.s.add(x == real(owner, "1"));
  owner.s.add(predicate(x));
  owner.s.add(from_bv(b) == x);
  const Term h = mixed(x, b);
  owner.s.add(real_gt(h, real(owner, "10")));

  require(solve(owner).is_sat(), "mixed Real UF signatures were not SAT");
  // x is an ordinary Real leaf, so its value is readable directly.
  const std::string actual = realModelValue(owner, x);
  if (actual != "1")
    throw std::runtime_error("mixed Real UF signatures gave x = " + actual +
                             ", expected 1");
}

// The two capabilities meeting: a Real-sorted application as an ite branch.
// This is the shape that found the type checker's missing Real arm: the ite
// type-checks its operands, and a Real-codomain application has no packed
// bit-vector carrier for the check to assume.
void realIteOverUninterpretedFunction()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term c = owner.tm.declare("c", owner.tm.mk_bool_sort());
  const Term x = realSymbol(owner, "x");
  const Term y = realSymbol(owner, "y");
  const Term chosen = ite(c, f(x), f(y));

  // Pin both applications and force the else branch, so the ite has to carry
  // the second one's value rather than merely typecheck.
  owner.s.add(!c);
  owner.s.add(real_gt(chosen, real(owner, "10")));
  owner.s.add(real_lt(f(y), real(owner, "10")));
  require(solve(owner).is_unsat(),
          "a Real ite over UF applications did not respect the else branch");
}

// An application the assertions never mention has no value of its own -- the
// lowering only reaches the ones they do -- but a caller may still ask about
// it, because a value query is not restricted to terms in the formula. Any
// value satisfies it, so the model completes it with zero rather than
// refusing.
void realUninterpretedFunctionOutsideTheFormula()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term x = realSymbol(owner, "x");
  const Term fx = f(x);
  // Nothing is asserted about f(x) -- nothing is asserted at all.
  require(solve(owner).is_sat(), "an empty query was not SAT");
  const std::string actual = realModelValue(owner, fx);
  if (actual != "0")
    throw std::runtime_error("an unconstrained Real UF application read back as " + actual +
                             ", expected 0");

  // And a predicate over it is decided rather than refused: f(x) < f(x) is
  // false whatever the value, which is the shape that found this.
  const Term self = real_lt(fx, fx);
  require(!owner.s.model().bool_value(self),
          "a predicate over it was not decided");
}

// The value an unlowered application gets is not free: congruence still binds
// it to any lowered application whose arguments take the same values. Keyed
// on those values rather than on syntax, so y reaching x's value is enough.
void realUninterpretedFunctionCongruenceOutsideTheFormula()
{
  Checker owner(true);
  const Sort real_sort = owner.tm.mk_real_sort();
  const Term f = declare(owner, "f", {real_sort}, real_sort);

  const Term x = realSymbol(owner, "x");
  const Term y = realSymbol(owner, "y");
  const Term fx = f(x);
  owner.s.add(x == real(owner, "3/4"));
  owner.s.add(y == real(owner, "3/4"));
  owner.s.add(fx == real(owner, "-9/5"));
  require(solve(owner).is_sat(), "the congruence query was not SAT");

  // f(y) is in no assertion, so it was never lowered -- but y and x hold the
  // same value here, so it has to answer as f(x) does.
  const Term fy = f(y);
  if (!realApplicationValued(owner, fy,
                             "real-uf-congruence-outside-the-formula"))
    return;
  const std::string actual = realModelValue(owner, fy);
  if (actual != "-9/5")
    throw std::runtime_error("an unlowered congruent application read back as " + actual +
                             ", expected -9/5");
}

// A Real ite's condition is decided from the model for every read, not only
// inside the solve: a value query is not a formula check, and reading any
// term with such an ite under it has to evaluate the condition.
void realIteConditionIsDecidedOnTheReadPath()
{
  Checker owner;
  const Term c = owner.tm.declare("c", owner.tm.mk_bool_sort());
  const Term x = realSymbol(owner, "x");
  const Term chosen = ite(c, real_neg(x), x);
  const Term scaled = real_mul(chosen, real(owner, "3"));
  // Nothing constrains the ite; the value query still has to answer.
  owner.s.add(x == real(owner, "2"));
  require(solve(owner).is_sat(), "the Real ite query was not SAT");

  const std::string actual = realModelValue(owner, scaled);
  // c decides which branch, so either 6 or -6, but it must be one of them.
  if (actual != "6" && actual != "-6")
    throw std::runtime_error("Real ite under multiplication read back as " +
                             actual + ", expected 6 or -6");
}

// Reading a model back as terms (2.x's counterexample read). A Real term has
// no bit-vector carrier, and asking 2.x's counterexample map for one once
// reached the width query and took the process down; the 3.x model answers a
// Real symbol with a Real value term, which reads back as itself.
void realCounterExampleReadsTheRealModel()
{
  Checker owner;
  const Term x = realSymbol(owner, "x");
  const Term y = realSymbol(owner, "y");
  owner.s.add(x == real(owner, "7/3"));
  owner.s.add(real_lt(y, x));
  owner.s.add(real_gt(y, real(owner, "0")));
  require(solve(owner).is_sat(), "Real counterexample query was not SAT");

  const Term value = owner.s.model().value(x);
  require(value.is_value() && value.sort().is_real(),
          "no model value for a Real symbol");
  const std::string actual = realModelValue(owner, value);
  if (actual != "7/3")
    throw std::runtime_error("Real counterexample gave " + actual +
                             ", expected 7/3");
  require(owner.s.model().value(y).is_value(),
          "no model value for a constrained Real symbol");
}

// The counterexample check walks the whole formula under the model, so every
// Real predicate in it has to be evaluable; the check once had no Real arm
// and declared each one unimplemented. check-sanity turns the check on (2.x's
// 'd', which every C validity checker had), so building a formula over all
// five predicate kinds, solving and reading a value exercises it.
void realCounterExampleCheckEvaluatesEveryPredicate()
{
  Checker owner;
  owner.s.options().set_bool("check-sanity", true);
  const Term x = realSymbol(owner, "x");
  const Term y = realSymbol(owner, "y");
  const Term b = owner.tm.declare("b", owner.tm.mk_bool_sort());

  owner.s.add(x == real(owner, "5/2"));
  owner.s.add(real_lt(y, x));
  owner.s.add(real_le(y, x));
  owner.s.add(real_gt(x, y));
  owner.s.add(real_ge(x, y));
  // A disjunction keeps the predicates in the formula rather than letting
  // each one be discharged on its own.
  owner.s.add(b || real_gt(y, real(owner, "0")));
  require(solve(owner).is_sat(), "the five-predicate formula was not SAT");

  require(owner.s.model().value(b).is_value(),
          "no model value for the Boolean guard");
  const std::string actual = realModelValue(owner, x);
  if (actual != "5/2")
    throw std::runtime_error("x read back as " + actual + ", expected 5/2");
}

// Every exact-Real control is an option of the registry, where an unknown
// name is refused (OPTION_UNKNOWN), so setting it pins the name; solving with
// each one on and off pins that it is wired to something that still answers.
// The options are given at construction, the window every entry admits
// (lra-verify-canonical is settable at construction only).
void realInterfaceFlagsAreReachable()
{
  static const char* const controls[] = {
      "lra-theory-propagation",
      "lra-verify-conflicts",
      "lra-verify-canonical",
      "lra-presolve-subst",
      "lra-presolve-bounds",
      "lra-presolve-rows",
      "lra-presolve-propagate",
      "lra-presolve-unconstrained",
      "lra-float-driver",
      // Only the SMT-LIB 2 frontend's check-sat reads this one: here the
      // option is pinned, and the solve below runs as it would with it off.
      "lra-incremental-session",
  };

  for (const char* control : controls)
  {
    for (bool on : {false, true})
    {
      TermManager tm;
      Options options;
      options.set_bool(control, on);
      Solver s(tm, options);
      require(s.options().get_bool(control) == on,
              "an exact-Real option did not read back as set");

      // A definition, a pair of bounds and a disjunction: enough shape for
      // the presolve stages to have something to do.
      const Sort real_sort = tm.mk_real_sort();
      const Term x = tm.declare("x", real_sort);
      const Term y = tm.declare("y", real_sort);
      const Term z = tm.declare("z", real_sort);
      s.add(x == real_add(y, tm.mk_real(1)));
      s.add(real_le(x, tm.mk_real(10)));
      s.add(real_ge(x, tm.mk_real(2)));
      s.add(real_lt(z, tm.mk_real(0)) || real_gt(z, tm.mk_real(1)));
      if (!s.check_sat().is_sat())
        throw std::runtime_error(std::string("solving with ") + control +
                                 (on ? " on" : " off") + " was not SAT");
    }
  }
}

// The exact-arithmetic budget refuses work rather than the caller asking for
// something ill-formed, so it is declined and reported, not fatal. Folding
// constants is what reaches it: every step below is a legal linear product,
// and the rationals grow superexponentially until one crosses 64 KiBit.
void realBudgetRefusalIsNotFatal()
{
  Checker owner;
  const Term c = real(owner, "844.208552611343813426147542733770603709125630466");
  const Term power = real_mul(real_mul(c, c), c);
  Term grown = power;
  for (int i = 0; i != 4; ++i)
    grown = real_mul(grown, power);

  // Keep squaring until the budget declines; it must decline rather than die.
  // 3.x: the refusal is a recoverable error (UNSUPPORTED) naming the budget.
  bool declined = false;
  for (int i = 0; i != 8 && !declined; ++i)
  {
    try
    {
      grown = real_mul(grown, grown);
    }
    catch (const RecoverableError& error)
    {
      require(error.code() == ErrorCode::UNSUPPORTED,
              "the budget's refusal was not UNSUPPORTED");
      declined = true;
    }
  }
  require(declined, "the exact-arithmetic budget never declined a product");

  // And the manager and solver are still usable afterwards: a refusal is not
  // a wound.
  const Term x = realSymbol(owner, "x");
  owner.s.add(x == real(owner, "3/4"));
  require(solve(owner).is_sat(), "the checker was unusable after a refusal");
  const std::string actual = realModelValue(owner, x);
  if (actual != "3/4")
    throw std::runtime_error("after a budget refusal x read back as " + actual);
}

// A signature that has to stay refused: an array sort is not comparable as a
// value, so it is inadmissible whatever else changed. 3.x builds the function
// sort and refuses the declaration of a symbol of it (UNSUPPORTED).
void arraySignatureIsStillRefused()
{
  Checker owner(true);
  TermManager& tm = owner.tm;
  const Sort bv_sort = tm.mk_bv_sort(8);
  const Sort array_sort = tm.mk_array_sort(bv_sort, bv_sort);
  const Sort real_sort = tm.mk_real_sort();

  require(refusal([&] { declare(owner, "bad", {array_sort}, real_sort); },
                  "an array domain sort was wrongly admitted") ==
              ErrorCode::UNSUPPORTED,
          "an array domain sort was refused for the wrong reason");
}

} // namespace

int main(int argc, char** argv)
{
  const std::vector<std::pair<const char*, void (*)()>> cases{
      {"capabilities-reported", capabilitiesAreReported},
      {"real-ite-then-branch", [] { realIteSelectsItsBranch(true); }},
      {"real-ite-else-branch", [] { realIteSelectsItsBranch(false); }},
      {"real-ite-under-theory", realIteUnderTheory},
      {"real-ite-conflicts", realIteConflicts},
      {"real-ite-feeds-arithmetic", realIteFeedsArithmetic},
      {"real-uf-application", realUninterpretedFunction},
      {"real-uf-scalar-model-completion", realUfScalarModelCompletion},
      {"real-uf-fp-model-completion", realUfFloatingPointModelCompletion},
      {"real-uf-result-constrained",
       realUninterpretedFunctionResultIsConstrained},
      {"real-uf-value-readable", realUninterpretedFunctionValueIsReadable},
      {"real-uf-congruent-values-agree",
       realUninterpretedFunctionCongruentValuesAgree},
      {"real-uf-congruence", realUninterpretedFunctionCongruence},
      {"real-uf-congruence-across-arithmetic",
       realUninterpretedFunctionCongruenceAcrossArithmetic},
      {"real-uf-stays-free", realUninterpretedFunctionStaysFree},
      {"real-uf-signatures", realUninterpretedFunctionSignatures},
      {"real-ite-over-uf", realIteOverUninterpretedFunction},
      {"real-uf-outside-the-formula",
       realUninterpretedFunctionOutsideTheFormula},
      {"real-uf-congruence-outside-the-formula",
       realUninterpretedFunctionCongruenceOutsideTheFormula},
      {"real-ite-condition-on-the-read-path",
       realIteConditionIsDecidedOnTheReadPath},
      {"real-counterexample-reads-real-model",
       realCounterExampleReadsTheRealModel},
      {"real-counterexample-check-evaluates-predicates",
       realCounterExampleCheckEvaluatesEveryPredicate},
      {"real-interface-flags-reachable", realInterfaceFlagsAreReachable},
      {"real-budget-refusal-is-not-fatal", realBudgetRefusalIsNotFatal},
      {"array-signature-refused", arraySignatureIsStillRefused},
      {"refused-real-assertion-leaves-no-answer",
       refusedRealAssertionLeavesNoAnswer},
      {"real-uf-constant-argument-teardown",
       realUninterpretedFunctionConstantArgumentTeardown},
  };

  // Reproducers for defects that exist independently of what this file
  // pins. Runnable by name, never part of the default run.
  const std::vector<std::pair<const char*, void (*)()>> known_defects{};

  // Naming one case runs only that case, which is what makes a failure here
  // bisectable: every case owns a manager and a solver whose teardown can
  // itself fail, so "which case" is not always readable from the output
  // alone.
  const char* only = argc == 2 ? argv[1] : nullptr;
  std::size_t ran = 0;
  for (const auto* list : {&cases, &known_defects})
  {
    // The known-defect list is opt-in: it is only ever entered by name.
    if (list == &known_defects && only == nullptr)
      continue;
    for (const auto& entry : *list)
    {
      if (only != nullptr && std::string(only) != entry.first)
        continue;
      ++ran;
      std::cerr << "-- " << entry.first << std::endl;
      try
      {
        entry.second();
      }
      catch (const std::exception& failure)
      {
        std::cerr << "FAIL " << entry.first << ": " << failure.what() << '\n';
        return 1;
      }
    }
  }
  if (only != nullptr && ran == 0)
  {
    std::cerr << "unknown case: " << only << '\n';
    return 2;
  }
  std::cout << "PASS real-capability-api (" << ran << " cases";
  if (skipped_checks != 0)
    std::cout << ", " << skipped_checks << " check(s) skipped: API gap";
  std::cout << ")\n";
  return 0;
}

// The two Real capabilities the C API gained after the fragment itself did:
// a Real-branch if-then-else, and Real as an admissible sort in an
// uninterpreted-function signature. Both were already decided by the core and
// reachable from an .smt2 file; neither had a C API spelling. These tests pin
// the spellings, so the interface cannot drift back behind the parser.

#include "stp/c_interface.h"

#include <cstddef>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

// The handler vc_registerErrorHandler installs. A declined call reports
// through it, which is expected where a test asks for one, so it is silenced
// across those calls only.
void ignore_diagnostic(const char* )
{
}

void require(bool condition, const char* detail)
{
  if (!condition)
    throw std::runtime_error(detail);
}

class OwnedVc final
{
public:
  // Uninterpreted functions have to be enabled before any Type or Expr that
  // will reach the UF API is built, so the flag goes on at construction.
  explicit OwnedVc(bool uninterpreted_functions = false)
      : vc_(vc_createValidityChecker())
  {
    if (uninterpreted_functions)
      vc_setFlag(vc_, 'u');
  }
  ~OwnedVc()
  {
    for (auto it = expressions_.rbegin(); it != expressions_.rend(); ++it)
      vc_DeleteExpr(*it);
    vc_Destroy(vc_);
  }
  OwnedVc(const OwnedVc&) = delete;
  OwnedVc& operator=(const OwnedVc&) = delete;

  operator VC() const noexcept { return vc_; }
  Expr own(Expr expression)
  {
    expressions_.push_back(expression);
    return expression;
  }
  // vc_query answers the *validity* of its argument, so querying false asks
  // whether the assertions are satisfiable: 0 is SAT, 1 is UNSAT.
  int solve() { return vc_query(vc_, own(vc_falseExpr(vc_))); }

private:
  VC vc_;
  std::vector<Expr> expressions_;
};

Expr real(OwnedVc& owner, const char* text)
{
  return owner.own(vc_realConstExprFromStr(owner, text));
}

Expr realSymbol(OwnedVc& owner, const char* name)
{
  return owner.own(vc_varExpr(owner, name, vc_realType(owner)));
}

std::string realModelValue(OwnedVc& owner, Expr term)
{
  require(vc_hasRealModel(owner) == 1, "no exact Real model was published");
  require(vc_hasRealModelValue(owner, term) == 1,
          "term has no exact Real model value");
  char* value = vc_getRealModelValue(owner, term);
  require(value != nullptr, "exact Real model value was null");
  const std::string copy(value);
  vc_deleteString(value);
  return copy;
}

void capabilitiesAreReported()
{
  require(vc_hasRealConstruction() == 1, "Real construction capability");
  require(vc_hasQFLRA() == 1, "QF_LRA semantic capability");
  require(vc_hasRealIte() == 1, "Real-branch ite construction capability");
  require(vc_hasQFUFLRA() == 1, "QF_UFLRA semantic capability");
}

// (ite c 3 5) with c pinned each way. The branch not taken must not reach the
// model, which is the whole point of routing this through CreateRealTerm
// rather than refusing it.
void realIteSelectsItsBranch(bool condition)
{
  OwnedVc owner;
  VC vc = owner;
  Expr c = owner.own(vc_varExpr(vc, "c", vc_boolType(vc)));
  Expr selected = owner.own(
      vc_iteExpr(vc, c, real(owner, "3"), real(owner, "5")));
  Expr x = realSymbol(owner, "x");
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, selected)));
  vc_assertFormula(vc, condition ? c : owner.own(vc_notExpr(vc, c)));

  require(owner.solve() == 0, "pinned Real ite was not SAT");
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
  OwnedVc owner;
  VC vc = owner;
  Expr c = owner.own(vc_varExpr(vc, "c", vc_boolType(vc)));
  Expr lo = realSymbol(owner, "lo");
  Expr hi = realSymbol(owner, "hi");
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, lo, real(owner, "1/4"))));
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, hi, real(owner, "9/4"))));

  Expr chosen = owner.own(vc_iteExpr(vc, c, lo, hi));
  // Only the hi branch clears 2, so the condition is forced false.
  vc_assertFormula(vc, owner.own(vc_realGtExpr(vc, chosen, real(owner, "2"))));

  require(owner.solve() == 0, "symbolic Real ite was not SAT");
  const std::string actual = realModelValue(owner, chosen);
  if (actual != "9/4")
    throw std::runtime_error("Real ite under a bound gave " + actual +
                             ", expected 9/4");
}

// Both branches out of range: the ite must make this UNSAT rather than
// quietly evaluating to one branch.
void realIteConflicts()
{
  OwnedVc owner;
  VC vc = owner;
  Expr c = owner.own(vc_varExpr(vc, "c", vc_boolType(vc)));
  Expr chosen =
      owner.own(vc_iteExpr(vc, c, real(owner, "1"), real(owner, "2")));
  vc_assertFormula(vc, owner.own(vc_realGtExpr(vc, chosen, real(owner, "10"))));
  require(owner.solve() == 1, "unsatisfiable Real ite was not UNSAT");
}

// An ite nested under linear arithmetic: the result feeds a sum, so the node
// has to carry Real sort onwards and not just typecheck in isolation.
void realIteFeedsArithmetic()
{
  OwnedVc owner;
  VC vc = owner;
  Expr c = owner.own(vc_varExpr(vc, "c", vc_boolType(vc)));
  Expr chosen =
      owner.own(vc_iteExpr(vc, c, real(owner, "1/2"), real(owner, "3/2")));
  Expr sum = owner.own(vc_realPlusExpr(vc, chosen, real(owner, "1/2")));
  Expr x = realSymbol(owner, "x");
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, sum)));
  vc_assertFormula(vc, owner.own(vc_notExpr(vc, c)));

  require(owner.solve() == 0, "Real ite under addition was not SAT");
  const std::string actual = realModelValue(owner, x);
  if (actual != "2")
    throw std::runtime_error("Real ite under addition gave " + actual +
                             ", expected 2");
}

UFDeclHandle declare(OwnedVc& owner, const char* name,
                     const std::vector<Type>& domain, Type codomain)
{
  UFDeclHandle handle = vc_declareUninterpretedFunction(
      owner, name, domain.data(), domain.size(), codomain);
  if (handle == 0)
    throw std::runtime_error(std::string("could not declare '") + name + "'");
  return handle;
}

Expr apply(OwnedVc& owner, UFDeclHandle function,
           const std::vector<Expr>& arguments)
{
  Expr application = vc_applyUninterpretedFunction(
      owner, function, arguments.data(), arguments.size());
  if (application == nullptr)
    throw std::runtime_error("could not apply uninterpreted function");
  return owner.own(application);
}

// The SMT-LIB Real lexer does not admit every mixed-sort signature, so use
// the C API to pin model completion for all other scalar argument sorts.
void realUfScalarModelCompletion()
{
  for (bool propagate : {false, true})
    for (bool rounding : {false, true})
    {
      OwnedVc owner(true);
      VC vc = owner;
      vc_setInterfaceFlags(vc, UF_PROPAGATE_EQUALITIES, propagate ? 1 : 0);
      Type domain = rounding ? vc_fpRoundingModeType(vc) : vc_bvType(vc, 8);
      UFDeclHandle f = declare(owner, "scalar_f", {domain}, vc_realType(vc));
      Expr x = owner.own(vc_varExpr(vc, "scalar_x", domain));
      Expr y = owner.own(vc_varExpr(vc, "scalar_y", domain));
      Expr z = owner.own(vc_varExpr(vc, "scalar_z", domain));
      Expr first = owner.own(rounding ? vc_fpRoundingMode(vc, VC_RM_RNE)
                                     : vc_bvConstExprFromLL(vc, 8, 1));
      Expr second = owner.own(rounding ? vc_fpRoundingMode(vc, VC_RM_RTZ)
                                      : vc_bvConstExprFromLL(vc, 8, 2));
      Expr third = owner.own(rounding ? vc_fpRoundingMode(vc, VC_RM_RTP)
                                     : vc_bvConstExprFromLL(vc, 8, 3));
      vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, first)));
      vc_assertFormula(vc, owner.own(vc_eqExpr(vc, y, x)));
      vc_assertFormula(vc, owner.own(vc_eqExpr(vc, z, second)));
      vc_assertFormula(vc, owner.own(vc_eqExpr(
          vc, apply(owner, f, {x}), real(owner, "4"))));
      vc_assertFormula(vc, owner.own(vc_eqExpr(
          vc, apply(owner, f, {second}), real(owner, "6"))));
      require(owner.solve() == 0, "mixed scalar/Real model was not SAT");

      require(realModelValue(owner, apply(owner, f, {y})) == "4",
              "equal scalar values selected different function results");
      require(realModelValue(owner, apply(owner, f, {z})) == "6",
              "distinct scalar values selected the same function result");
      Expr next = rounding
                      ? owner.own(vc_iteExpr(vc, owner.own(vc_falseExpr(vc)),
                                            y, second))
                      : owner.own(vc_bvPlusExpr(vc, 8, y, first));
      require(realModelValue(owner, apply(owner, f, {next})) == "6",
              "computed scalar value did not select the observed result");
      require(realModelValue(owner, apply(owner, f, {third})) == "0",
              "unobserved scalar tuple did not use the default");
    }
}

void realUfFloatingPointModelCompletion()
{
  for (bool propagate : {false, true})
  {
    OwnedVc owner(true);
    VC vc = owner;
    vc_setInterfaceFlags(vc, UF_PROPAGATE_EQUALITIES, propagate ? 1 : 0);
    Type fp = vc_fpType(vc, 8, 24);
    UFDeclHandle f = declare(owner, "fp_f", {fp}, vc_realType(vc));
    auto bits = [&](unsigned value) {
      return owner.own(vc_fpConstFromBits(
          vc, 8, 24, owner.own(vc_bvConstExprFromLL(vc, 32, value))));
    };
    Expr x = owner.own(vc_varExpr(vc, "fp_x", fp));
    Expr y = owner.own(vc_varExpr(vc, "fp_y", fp));
    Expr pz = owner.own(vc_varExpr(vc, "fp_pz", fp));
    Expr nz = owner.own(vc_varExpr(vc, "fp_nz", fp));
    Expr positive_zero = bits(0);
    Expr negative_zero = bits(0x80000000U);
    vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, bits(0x7fc00001U))));
    vc_assertFormula(vc, owner.own(vc_eqExpr(vc, y, bits(0x7f800002U))));
    vc_assertFormula(vc, owner.own(vc_eqExpr(vc, pz, positive_zero)));
    vc_assertFormula(vc, owner.own(vc_eqExpr(vc, nz, negative_zero)));
    vc_assertFormula(vc, owner.own(vc_eqExpr(
        vc, apply(owner, f, {x}), real(owner, "5"))));
    vc_assertFormula(vc, owner.own(vc_eqExpr(
        vc, apply(owner, f, {positive_zero}), real(owner, "7"))));
    vc_assertFormula(vc, owner.own(vc_eqExpr(
        vc, apply(owner, f, {negative_zero}), real(owner, "9"))));
    require(owner.solve() == 0, "mixed FP/Real model was not SAT");

    require(realModelValue(owner, apply(owner, f, {y})) == "5" &&
                realModelValue(owner, apply(owner, f, {bits(0xffc12345U)})) == "5",
            "NaN payloads did not name the same function argument");
    require(realModelValue(owner, apply(owner, f,
                {owner.own(vc_fpNegExpr(vc, nz))})) == "7" &&
                realModelValue(owner, apply(owner, f,
                {owner.own(vc_fpNegExpr(vc, pz))})) == "9",
            "floating-point signed zeros were conflated");
  }
}

// Real -> Real, declared, applied and solved. The declaration is the half
// that cTypeToUFSort used to refuse.
void realUninterpretedFunction()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr x = realSymbol(owner, "x");
  Expr fx = apply(owner, f, {x});
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "7/3"))));
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, fx, real(owner, "-5/2"))));

  require(owner.solve() == 0, "Real-sorted UF application was not SAT");
  const std::string actual = realModelValue(owner, x);
  if (actual != "7/3")
    throw std::runtime_error("Real UF argument gave " + actual +
                             ", expected 7/3");
}

// A constraint on the application alone has to be respected even though no
// equality pins the argument: the result is a solved unknown of its own.
void realUninterpretedFunctionResultIsConstrained()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr x = realSymbol(owner, "x");
  Expr fx = apply(owner, f, {x});
  vc_assertFormula(vc, owner.own(vc_realGtExpr(vc, fx, real(owner, "1"))));
  vc_assertFormula(vc, owner.own(vc_realLtExpr(vc, fx, real(owner, "1"))));
  require(owner.solve() == 1,
          "contradictory bounds on a Real UF result were not UNSAT");
}

// The application itself is readable, not just its argument: the UF lowering
// replaced it with a result symbol before the arithmetic saw it, and the
// solved value is copied back onto the application so a caller can ask about
// the node it actually holds.
void realUninterpretedFunctionValueIsReadable()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr x = realSymbol(owner, "x");
  Expr fx = apply(owner, f, {x});
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "7/3"))));
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, fx, real(owner, "-5/2"))));
  require(owner.solve() == 0, "Real-sorted UF application was not SAT");

  const std::string actual = realModelValue(owner, fx);
  if (actual != "-5/2")
    throw std::runtime_error("Real UF application read back as " + actual +
                             ", expected -5/2");
  // The numerator/denominator and SMT-LIB spellings answer for it too.
  char* numerator = vc_getRealModelNumerator(vc, fx);
  char* denominator = vc_getRealModelDenominator(vc, fx);
  const std::string n(numerator ? numerator : "");
  const std::string d(denominator ? denominator : "");
  vc_deleteString(numerator);
  vc_deleteString(denominator);
  if (n != "-5" || d != "2")
    throw std::runtime_error("Real UF application components were " + n + "/" +
                             d + ", expected -5/2");
}

// Congruence forces two applications to one value, and both nodes have to
// report it -- the mapping covers every application the solve lowered, not
// just the first.
void realUninterpretedFunctionCongruentValuesAgree()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr x = realSymbol(owner, "x");
  Expr y = realSymbol(owner, "y");
  Expr fx = apply(owner, f, {x});
  Expr fy = apply(owner, f, {y});
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, y)));
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, fx, real(owner, "11/7"))));
  // f(y) has to appear in the formula to be lowered at all: an application
  // the solve never reached has no value of its own, which is the same rule
  // that governs the bit-vector ones.
  vc_assertFormula(vc, owner.own(vc_realGtExpr(vc, fy, real(owner, "0"))));
  require(owner.solve() == 0, "congruent Real UF applications were not SAT");

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
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr x = realSymbol(owner, "x");
  Expr y = realSymbol(owner, "y");
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, y)));
  Expr differ = owner.own(vc_notExpr(
      vc, owner.own(vc_eqExpr(vc, apply(owner, f, {x}),
                              apply(owner, f, {y})))));
  vc_assertFormula(vc, differ);
  require(owner.solve() == 1, "Real UF congruence was not enforced");
}

// The arguments are equal as *rationals* without being syntactically equal,
// which is the case a carrier-comparing core would get wrong. Both arguments
// stay symbolic; a concrete argument is covered by
// realUninterpretedFunctionConstantArgumentTeardown.
void realUninterpretedFunctionCongruenceAcrossArithmetic()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr x = realSymbol(owner, "x");
  Expr y = realSymbol(owner, "y");
  Expr shift = realSymbol(owner, "shift");
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, y)));

  // x + shift and y + shift are the same rational however shift is chosen,
  // so f has to agree on them.
  Expr left = owner.own(vc_realPlusExpr(vc, x, shift));
  Expr right = owner.own(vc_realPlusExpr(vc, y, shift));
  Expr differ = owner.own(vc_notExpr(
      vc, owner.own(vc_eqExpr(vc, apply(owner, f, {left}),
                              apply(owner, f, {right})))));
  vc_assertFormula(vc, differ);
  require(owner.solve() == 1,
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
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr applied = apply(owner, f, {real(owner, "1")});
  vc_assertFormula(vc,
                   owner.own(vc_realGtExpr(vc, applied, real(owner, "1"))));
  require(owner.solve() == 0, "Real UF over a constant argument was not SAT");
}

// Distinct arguments leave the function free, so this must stay SAT --
// congruence must not be over-applied.
// Preregistering an assertion does exact arithmetic, so the number budget can
// refuse it: every constant below is individually representable, but folding
// them into one linear form is not. That refusal used to escape
// vc_assertFormula, which returns void, and reach terminate. Reporting it is
// only half the fix -- a caller that ignores the diagnostic (murxla installs
// a handler that does exactly that) would then get an answer to a query
// missing one of its assertions, which is the wrong-answer direction rather
// than the incomplete one. So the query has to come back undecided.
//
// The shape is a murxla trace reduced by delta debugging; it is transcribed
// rather than generated because what matters is landing just past the budget
// at normalisation while staying under it at every constructor.
void refusedRealAssertionLeavesNoAnswer()
{
  OwnedVc owner(true);
  VC vc = owner;

  Expr x = realSymbol(owner, "x");
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "1"))));
  require(owner.solve() == 0, "a plain Real equality should be SAT");

  auto neg = [&](Expr e) { return owner.own(vc_realUMinusExpr(vc, e)); };
  auto add = [&](Expr l, Expr r) { return owner.own(vc_realPlusExpr(vc, l, r)); };
  auto sub = [&](Expr l, Expr r) { return owner.own(vc_realMinusExpr(vc, l, r)); };
  auto mul = [&](Expr l, Expr r) { return owner.own(vc_realMultExpr(vc, l, r)); };

  Expr c = real(owner, "85540413.44455765206262857018");
  Expr n0 = neg(c);
  Expr p1 = mul(c, n0);
  Expr p2 = mul(mul(p1, mul(p1, p1)), p1);
  Expr s3 = add(p2, n0);
  Expr p4 = mul(mul(s3, p2), sub(s3, c));
  Expr p5 = mul(mul(p4, p4), p4);
  Expr d6 = sub(p5, n0);
  Expr a7 = add(p5, n0);
  Expr lhs = sub(neg(sub(d6, n0)), n0);
  Expr rhs = mul(mul(a7, sub(mul(neg(a7), n0), n0)), a7);
  Expr big = mul(mul(mul(lhs, rhs), d6), add(n0, p5));
  require(big != nullptr,
          "every constructor should have stayed inside the budget");

  Expr refused = owner.own(vc_realLtExpr(vc, big, big));
  require(refused != nullptr, "the comparison should have been constructed");
  vc_assertFormula(vc, refused);

  require(owner.solve() == 3,
          "a query missing a refused assertion must answer unknown");
  require(vc_getReasonUnknown(vc) == REASON_UNKNOWN_INCOMPLETE,
          "the unknown must name a cause");
}

void realUninterpretedFunctionStaysFree()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr x = realSymbol(owner, "x");
  Expr y = realSymbol(owner, "y");
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "1"))));
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, y, real(owner, "2"))));
  Expr differ = owner.own(vc_notExpr(
      vc, owner.own(vc_eqExpr(vc, apply(owner, f, {x}),
                              apply(owner, f, {y})))));
  vc_assertFormula(vc, differ);
  require(owner.solve() == 0,
          "Real UF over distinct arguments was wrongly UNSAT");
}

// Real in either half of a signature, and mixed with the sorts that were
// already admissible.
void realUninterpretedFunctionSignatures()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  Type bool_type = vc_boolType(vc);
  Type bv_type = vc_bvType(vc, 8);

  UFDeclHandle predicate = declare(owner, "p", {real_type}, bool_type);
  UFDeclHandle from_bv = declare(owner, "g", {bv_type}, real_type);
  UFDeclHandle mixed = declare(owner, "h", {real_type, bv_type}, real_type);

  Expr x = realSymbol(owner, "x");
  Expr b = owner.own(vc_varExpr(vc, "b", bv_type));
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "1"))));
  vc_assertFormula(vc, apply(owner, predicate, {x}));
  vc_assertFormula(
      vc, owner.own(vc_eqExpr(vc, apply(owner, from_bv, {b}), x)));
  Expr h = apply(owner, mixed, {x, b});
  vc_assertFormula(vc, owner.own(vc_realGtExpr(vc, h, real(owner, "10"))));

  require(owner.solve() == 0, "mixed Real UF signatures were not SAT");
  // x is an ordinary Real leaf, so its value is readable directly.
  const std::string actual = realModelValue(owner, x);
  if (actual != "1")
    throw std::runtime_error("mixed Real UF signatures gave x = " + actual +
                             ", expected 1");
}

// The two new capabilities meeting: a Real-sorted application as an ite
// branch. This is the shape that found BVTypeCheck's missing Real arm --
// vc_iteExpr type-checks its operands, and a Real-codomain UF_APPLY is built
// by the width-free constructor, so the fall-through that assumed a packed
// bit-vector carrier declared it malformed. Nothing else type-checks such a
// node: vc_eqExpr takes the Real path before its own check, which is why UFs
// and ites were each fine on their own.
void realIteOverUninterpretedFunction()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr c = owner.own(vc_varExpr(vc, "c", vc_boolType(vc)));
  Expr x = realSymbol(owner, "x");
  Expr y = realSymbol(owner, "y");
  Expr chosen =
      owner.own(vc_iteExpr(vc, c, apply(owner, f, {x}), apply(owner, f, {y})));

  // Pin both applications and force the else branch, so the ite has to carry
  // the second one's value rather than merely typecheck.
  vc_assertFormula(vc, owner.own(vc_notExpr(vc, c)));
  vc_assertFormula(
      vc, owner.own(vc_realGtExpr(vc, chosen, real(owner, "10"))));
  vc_assertFormula(
      vc, owner.own(vc_realLtExpr(vc, apply(owner, f, {y}), real(owner, "10"))));
  require(owner.solve() == 1,
          "a Real ite over UF applications did not respect the else branch");
}

// An application the assertions never mention has no value of its own -- the
// lowering only reaches the ones they do -- but a caller may still ask about
// it, because a value query is not restricted to terms in the formula. Any
// value satisfies it, so it answers zero rather than refusing.
void realUninterpretedFunctionOutsideTheFormula()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr x = realSymbol(owner, "x");
  Expr fx = apply(owner, f, {x});
  // Nothing is asserted about f(x) -- nothing is asserted at all.
  require(owner.solve() == 0, "an empty query was not SAT");
  const std::string actual = realModelValue(owner, fx);
  if (actual != "0")
    throw std::runtime_error("an unconstrained Real UF application read back "
                             "as " + actual + ", expected 0");

  // And a predicate over it is decided rather than refused: f(x) < f(x) is
  // false whatever the value, which is the shape that found this.
  Expr self = owner.own(vc_realLtExpr(vc, fx, fx));
  Expr decided = owner.own(vc_getCounterExample(vc, self));
  require(decided != nullptr, "a predicate over it had no counterexample");
}

// The value an unlowered application gets is not free: congruence still binds
// it to any lowered application whose arguments take the same values. Keyed
// on those values rather than on syntax, so y reaching x's value is enough.
void realUninterpretedFunctionCongruenceOutsideTheFormula()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type real_type = vc_realType(vc);
  UFDeclHandle f = declare(owner, "f", {real_type}, real_type);

  Expr x = realSymbol(owner, "x");
  Expr y = realSymbol(owner, "y");
  Expr fx = apply(owner, f, {x});
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "3/4"))));
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, y, real(owner, "3/4"))));
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, fx, real(owner, "-9/5"))));
  require(owner.solve() == 0, "the congruence query was not SAT");

  // f(y) is in no assertion, so it was never lowered -- but y and x hold the
  // same value here, so it has to answer as f(x) does.
  Expr fy = apply(owner, f, {y});
  const std::string actual = realModelValue(owner, fy);
  if (actual != "-9/5")
    throw std::runtime_error("an unlowered congruent application read back "
                             "as " + actual + ", expected -9/5");
}

// A Real ite's condition is decided from the counterexample for as long as
// the model lives, not only inside the counterexample check: a value query is
// not a formula check, and reading any term with such an ite under it failed
// without the oracle in place.
void realIteConditionIsDecidedOnTheReadPath()
{
  OwnedVc owner;
  VC vc = owner;
  Expr c = owner.own(vc_varExpr(vc, "c", vc_boolType(vc)));
  Expr x = realSymbol(owner, "x");
  Expr chosen = owner.own(
      vc_iteExpr(vc, c, owner.own(vc_realUMinusExpr(vc, x)), x));
  Expr scaled = owner.own(vc_realMultExpr(vc, chosen, real(owner, "3")));
  // Nothing constrains the ite; the value query still has to answer.
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "2"))));
  require(owner.solve() == 0, "the Real ite query was not SAT");

  const std::string actual = realModelValue(owner, scaled);
  // c decides which branch, so either 6 or -6, but it must be one of them.
  if (actual != "6" && actual != "-6")
    throw std::runtime_error("Real ite under multiplication read back as " +
                             actual + ", expected 6 or -6");
}

// Reading a model back through the legacy counterexample entry point. A Real
// term has no carrier, so the counterexample map -- which holds bit patterns
// -- cannot hold its value; asking it for one used to reach GetValueWidth and
// take the process down. It is answered from the Real model instead.
void realCounterExampleReadsTheRealModel()
{
  OwnedVc owner;
  VC vc = owner;
  Expr x = realSymbol(owner, "x");
  Expr y = realSymbol(owner, "y");
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "7/3"))));
  vc_assertFormula(vc, owner.own(vc_realLtExpr(vc, y, x)));
  vc_assertFormula(vc, owner.own(vc_realGtExpr(vc, y, real(owner, "0"))));
  require(owner.solve() == 0, "Real counterexample query was not SAT");

  Expr value = owner.own(vc_getCounterExample(vc, x));
  require(value != nullptr, "no counterexample for a Real symbol");
  const std::string actual = realModelValue(owner, value);
  if (actual != "7/3")
    throw std::runtime_error("Real counterexample gave " + actual +
                             ", expected 7/3");
  require(owner.own(vc_getCounterExample(vc, y)) != nullptr,
          "no counterexample for a constrained Real symbol");
}

// The counterexample check walks the whole formula under the model, so every
// Real predicate in it has to be evaluable. ComputeFormulaUsingModel had no
// Real arm at all and declared each one unimplemented; the check runs lazily,
// when a model is first read, which is why only a value-reading client met
// it. vc_createValidityChecker turns that check on, so building a formula
// over all five predicate kinds and reading a value exercises it.
void realCounterExampleCheckEvaluatesEveryPredicate()
{
  OwnedVc owner;
  VC vc = owner;
  Expr x = realSymbol(owner, "x");
  Expr y = realSymbol(owner, "y");
  Expr b = owner.own(vc_varExpr(vc, "b", vc_boolType(vc)));

  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "5/2"))));
  vc_assertFormula(vc, owner.own(vc_realLtExpr(vc, y, x)));
  vc_assertFormula(vc, owner.own(vc_realLeExpr(vc, y, x)));
  vc_assertFormula(vc, owner.own(vc_realGtExpr(vc, x, y)));
  vc_assertFormula(vc, owner.own(vc_realGeExpr(vc, x, y)));
  // A disjunction keeps the predicates in the formula rather than letting
  // each one be discharged on its own.
  vc_assertFormula(
      vc, owner.own(vc_orExpr(
              vc, b, owner.own(vc_realGtExpr(vc, y, real(owner, "0"))))));
  require(owner.solve() == 0, "the five-predicate formula was not SAT");

  // Reading any value materialises the counterexample and runs the check.
  require(owner.own(vc_getCounterExample(vc, b)) != nullptr,
          "no counterexample for the Boolean guard");
  const std::string actual = realModelValue(owner, x);
  if (actual != "5/2")
    throw std::runtime_error("x read back as " + actual + ", expected 5/2");
}

// Every exact-Real control reaches vc_setInterfaceFlags. An unknown flag is a
// fatal error there, so the call alone pins the enumerator; solving with each
// one on pins that it is wired to something that still answers.
void realInterfaceFlagsAreReachable()
{
  static const struct
  {
    enum ifaceflag_t flag;
    const char* name;
  } controls[] = {
      {LRA_THEORY_PROPAGATION, "lra-theory-propagation"},
      {LRA_VERIFY_CONFLICTS, "lra-verify-conflicts"},
      {LRA_VERIFY_CANONICAL, "lra-verify-canonical"},
      {LRA_PRESOLVE_SUBST, "lra-presolve-subst"},
      {LRA_PRESOLVE_BOUNDS, "lra-presolve-bounds"},
      {LRA_PRESOLVE_ROWS, "lra-presolve-rows"},
      {LRA_PRESOLVE_PROPAGATE, "lra-presolve-propagate"},
      {LRA_PRESOLVE_UNCONSTRAINED, "lra-presolve-unconstrained"},
      {LRA_FLOAT_DRIVER, "lra-float-driver"},
  };

  for (const auto& control : controls)
  {
    for (int on = 0; on != 2; ++on)
    {
      OwnedVc owner;
      VC vc = owner;
      vc_setInterfaceFlags(vc, control.flag, on);

      // A definition, a pair of bounds and a disjunction: enough shape for
      // the presolve stages to have something to do.
      Expr x = realSymbol(owner, "x");
      Expr y = realSymbol(owner, "y");
      Expr z = realSymbol(owner, "z");
      vc_assertFormula(
          vc, owner.own(vc_eqExpr(
                  vc, x, owner.own(vc_realPlusExpr(vc, y, real(owner, "1"))))));
      vc_assertFormula(vc, owner.own(vc_realLeExpr(vc, x, real(owner, "10"))));
      vc_assertFormula(vc, owner.own(vc_realGeExpr(vc, x, real(owner, "2"))));
      vc_assertFormula(
          vc, owner.own(vc_orExpr(
                  vc, owner.own(vc_realLtExpr(vc, z, real(owner, "0"))),
                  owner.own(vc_realGtExpr(vc, z, real(owner, "1"))))));
      if (owner.solve() != 0)
        throw std::runtime_error(std::string("solving with ") + control.name +
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
  OwnedVc owner;
  VC vc = owner;
  Expr c = real(owner, "844.208552611343813426147542733770603709125630466");
  Expr power = owner.own(vc_realMultExpr(vc, owner.own(vc_realMultExpr(vc, c, c)), c));
  Expr grown = power;
  for (int i = 0; i != 4; ++i)
    grown = owner.own(vc_realMultExpr(vc, grown, power));

  // Keep squaring until the budget declines; it must decline rather than die,
  // and it must say so through the error handler.
  bool declined = false;
  for (int i = 0; i != 8 && !declined; ++i)
  {
    vc_registerErrorHandler(ignore_diagnostic);
    Expr next = vc_realMultExpr(vc, grown, grown);
    vc_registerErrorHandler(nullptr);
    if (next == nullptr)
      declined = true;
    else
      grown = owner.own(next);
  }
  require(declined, "the exact-arithmetic budget never declined a product");

  // And the checker is still usable afterwards: a refusal is not a wound.
  Expr x = realSymbol(owner, "x");
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "3/4"))));
  require(owner.solve() == 0, "the checker was unusable after a refusal");
  const std::string actual = realModelValue(owner, x);
  if (actual != "3/4")
    throw std::runtime_error("after a budget refusal x read back as " + actual);
}

// A signature the gate still has to refuse: an array sort is not comparable
// as a value, so it is inadmissible whatever else changed.
void arraySignatureIsStillRefused()
{
  OwnedVc owner(true);
  VC vc = owner;
  Type bv_type = vc_bvType(vc, 8);
  Type array_type = vc_arrayType(vc, bv_type, bv_type);
  Type real_type = vc_realType(vc);

  std::vector<Type> domain{array_type};
  require(vc_declareUninterpretedFunction(vc, "bad", domain.data(),
                                          domain.size(), real_type) == 0,
          "an array domain sort was wrongly admitted");
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
      {"real-budget-refusal-is-not-fatal",
       realBudgetRefusalIsNotFatal},
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
  // bisectable: every case owns a validity checker whose teardown can itself
  // fail, so "which case" is not always readable from the output alone.
  const char* only = argc == 2 ? argv[1] : nullptr;
  std::size_t ran = 0;
  for (const auto* list : {&cases, &known_defects})
  {
    // The known-defect list is opt-in: it is only ever entered by name.
    if (list == &known_defects && only == nullptr) continue;
    for (const auto& entry : *list)
    {
      if (only != nullptr && std::string(only) != entry.first) continue;
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
  std::cout << "PASS real-capability-api (" << ran << " cases)\n";
  return 0;
}

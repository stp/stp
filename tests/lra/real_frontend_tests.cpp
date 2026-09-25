#include "LraFrontend.h"

#include "stp/STPManager/STPManager.h"

#include <cstdint>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#ifndef _WIN32
#include <sys/resource.h>
#endif

namespace printer {
void SMTLIB2_PrintBack(std::ostream&, const stp::ASTNode&, stp::STPMgr*,
                       bool);
}

namespace {

using namespace stp;
using namespace stp::lra;

[[noreturn]] void fail(const std::string& message)
{
  throw std::runtime_error(message);
}

void require(bool condition, const std::string& message)
{
  if (!condition)
    fail(message);
}

std::string print(const ASTNode& node)
{
  std::ostringstream out;
  node.nodeprint(out);
  return out.str();
}

bool evaluateBoolean(const ASTNode& node,
                     const std::map<std::uint64_t, bool>& assignments)
{
  switch (node.GetKind())
  {
    case TRUE:
      return true;
    case FALSE:
      return false;
    case SYMBOL:
    {
      const auto found = assignments.find(node.GetNodeNum());
      if (found == assignments.end())
        fail("Boolean truth-table assignment is incomplete");
      return found->second;
    }
    case NOT:
      return !evaluateBoolean(node[0], assignments);
    case AND:
      for (const ASTNode& child : node.GetChildren())
        if (!evaluateBoolean(child, assignments))
          return false;
      return true;
    case OR:
      for (const ASTNode& child : node.GetChildren())
        if (evaluateBoolean(child, assignments))
          return true;
      return false;
    case XOR:
    {
      bool value = false;
      for (const ASTNode& child : node.GetChildren())
        value = value != evaluateBoolean(child, assignments);
      return value;
    }
    case IFF:
      return evaluateBoolean(node[0], assignments) ==
             evaluateBoolean(node[1], assignments);
    case IMPLIES:
      return !evaluateBoolean(node[0], assignments) ||
             evaluateBoolean(node[1], assignments);
    case ITE:
      return evaluateBoolean(node[0], assignments)
                 ? evaluateBoolean(node[1], assignments)
                 : evaluateBoolean(node[2], assignments);
    default:
      fail("truth-table evaluator encountered non-Boolean syntax");
  }
}

void unit()
{
  require(SourceSort::real().kind() == SourceSort::Kind::Real,
          "Real source sort missing");
  require(SourceSort::real().name() == "Real", "Real sort print drift");
  require(!SourceSort::real().isScalar(), "Real accidentally became array scalar");

  STPMgr manager;
  const ASTNode half_a = manager.CreateRealConst("0.5");
  const ASTNode half_b = manager.CreateRealConst("1", "2");
  const ASTNode half_c = manager.CreateRealConst("0002/0004");
  require(half_a == half_b && half_b == half_c,
          "equal exact constants did not intern together");
  require(half_a.GetType() == REAL_TYPE, "Real constant carrier mismatch");
  require(half_a.GetSourceSort() == SourceSort::real(),
          "Real constant source sort mismatch");
  require(half_a.GetRealCanonical() == "1/2", "constant not canonical");
  require(half_a.GetRealNumerator() == "1" &&
              half_a.GetRealDenominator() == "2",
          "exact numerator/positive denominator access mismatch");
  require(print(half_a) == "(/ 1 2)", "positive fraction SMT-LIB print mismatch");

  const ASTNode negative = manager.CreateRealConst("-7/3");
  const ASTNode integer = manager.CreateRealConst("-9");
  require(print(negative) == "(- (/ 7 3))",
          "negative fraction SMT-LIB print mismatch");
  require(print(integer) == "(- 9)",
          "negative integer SMT-LIB print mismatch");

  ASTNode copied = half_a;
  ASTNode moved = std::move(copied);
  require(moved == half_a && moved.GetRealCanonical() == "1/2",
          "Real constant copy/move ownership mismatch");

  const ASTNode folded = manager.CreateRealTerm(
      REAL_ADD, ASTVec{manager.CreateRealConst("1.25"), half_a});
  require(folded.GetKind() == REAL_CONST &&
              folded.GetRealCanonical() == "7/4",
          "exact Real constant folding mismatch");
  const ASTNode folded_subtract = manager.CreateRealTerm(
      REAL_SUB, ASTVec{manager.CreateRealConst("5/6"),
                       manager.CreateRealConst("1/3"),
                       manager.CreateRealConst("1/6")});
  const ASTNode folded_unary = manager.CreateRealTerm(
      REAL_SUB, ASTVec{manager.CreateRealConst("-7/9")});
  const ASTNode folded_negate = manager.CreateRealTerm(
      REAL_NEG, ASTVec{manager.CreateRealConst("11/13")});
  const ASTNode folded_divide = manager.CreateRealTerm(
      REAL_DIV, ASTVec{manager.CreateRealConst("-14/15"),
                       manager.CreateRealConst("7/5")});
  require(folded_subtract.GetRealCanonical() == "1/3" &&
              folded_unary.GetRealCanonical() == "7/9" &&
              folded_negate.GetRealCanonical() == "-11/13" &&
              folded_divide.GetRealCanonical() == "-2/3",
          "exact subtraction/negation/division folding mismatch");
}

void normalization()
{
  STPMgr manager;
  Frontend frontend(manager);
  const auto b = manager.CreateSourceSymbol("binary_probe_b", SourceSort::real());
  const auto c = manager.CreateSourceSymbol("binary_probe_c", SourceSort::real());
  const auto zero = manager.CreateRealConst("0");
  const auto one = manager.CreateRealConst("1");
  const auto b_zero = manager.CreateNode(EQ, b, zero);
  const auto b_one = manager.CreateNode(EQ, one, b);
  require(frontend.binaryDomainSymbol(manager.CreateNode(OR, b_zero, b_one)) == b,
          "exact binary domain was not recognized");
  require(!frontend.binaryDomainSymbol(manager.CreateNode(
              OR, b_zero, manager.CreateNode(EQ, c, one))),
          "different unregistered symbols were conflated in domain inspection");
  const auto twice_b = manager.CreateRealTerm(
      REAL_MUL, ASTVec{manager.CreateRealConst("2"), b});
  require(frontend.binaryDomainSymbol(manager.CreateNode(
              OR, manager.CreateNode(EQ, twice_b, zero),
              manager.CreateNode(EQ, twice_b, manager.CreateRealConst("2")))) == b,
          "scaled binary domain was not recognized");
  // The successful and unsuccessful inspections above must not register b or
  // c. The existing checks below require x and y to retain IDs 1 and 2.
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode y = manager.CreateSourceSymbol("y", SourceSort::real());
  const ASTNode two_x = manager.CreateRealTerm(
      REAL_MUL, ASTVec{manager.CreateRealConst("2"), x});
  const ASTNode minus_three_y = manager.CreateRealTerm(
      REAL_MUL, ASTVec{manager.CreateRealConst("-3"), y});
  const ASTNode expression = manager.CreateRealTerm(
      REAL_ADD,
      ASTVec{two_x, minus_three_y, manager.CreateRealConst("5/6"),
             manager.CreateRealConst("0.5")});

  const LinearPolynomial polynomial = frontend.normalize(expression);
  require(frontend.exportPolynomial(polynomial) == "s1:2,s2:-3;c:4/3",
          "canonical sparse polynomial export mismatch");
  const std::uint64_t first_hash = frontend.stableHash(polynomial);

  const ASTNode equivalent = manager.CreateRealTerm(
      REAL_SUB,
      ASTVec{manager.CreateRealTerm(
                 REAL_ADD,
                 ASTVec{x, x, manager.CreateRealConst("4/3")}),
             manager.CreateRealTerm(
                 REAL_ADD, ASTVec{y, y, y})});
  const LinearPolynomial again = frontend.normalize(equivalent);
  require(frontend.exportPolynomial(again) ==
              frontend.exportPolynomial(polynomial),
          "algebraically equal forms did not normalize byte-identically");
  require(frontend.stableHash(again) == first_hash,
          "canonical polynomial hash changed across equal forms");

  const ASTNode cancelled = manager.CreateRealTerm(
      REAL_SUB, ASTVec{x, x});
  const LinearPolynomial zero_poly = frontend.normalize(cancelled);
  require(zero_poly.terms.empty() && zero_poly.constant.isZero(),
          "cancellation did not produce canonical zero");

  const ASTNode scaled_zero = manager.CreateRealTerm(
      REAL_MUL, ASTVec{manager.CreateRealConst("0"), expression});
  const LinearPolynomial zero_again = frontend.normalize(scaled_zero);
  require(zero_again.terms.empty() && zero_again.constant.isZero(),
          "zero scaling retained a monomial");

  const ASTNode less_equal = manager.CreateRealPredicate(
      REAL_LE, expression, manager.CreateRealConst("19/6"));
  const NormalizedPredicate comparison =
      frontend.normalizePredicate(less_equal);
  require(!comparison.is_constant &&
              frontend.exportPredicate(comparison.canonical) ==
                  "<=:s1:2,s2:-3;c:-11/6",
          "lhs-minus-rhs comparison orientation/threshold source mismatch");

  STPMgr repeat_manager;
  Frontend repeat_frontend(repeat_manager);
  const ASTNode repeat_x =
      repeat_manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode repeat_y =
      repeat_manager.CreateSourceSymbol("y", SourceSort::real());
  const ASTNode repeat_expression = repeat_manager.CreateRealTerm(
      REAL_ADD,
      ASTVec{repeat_manager.CreateRealTerm(
                 REAL_MUL,
                 ASTVec{repeat_manager.CreateRealConst("2"), repeat_x}),
             repeat_manager.CreateRealTerm(
                 REAL_MUL,
                 ASTVec{repeat_manager.CreateRealConst("-3"), repeat_y}),
             repeat_manager.CreateRealConst("4/3")});
  const LinearPolynomial repeated =
      repeat_frontend.normalize(repeat_expression);
  require(repeat_frontend.exportPolynomial(repeated) ==
              frontend.exportPolynomial(polynomial) &&
              repeat_frontend.stableHash(repeated) == first_hash,
          "canonical output depends on manager/allocator history");
}

void equality()
{
  STPMgr manager;
  Frontend frontend(manager);
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode zero = manager.CreateRealConst("0");
  const ASTNode equal = manager.CreateRealPredicate(EQ, x, zero);

  const PreregisteredFormula registered = frontend.preregister(equal);
  require(registered.equalities.size() == 1,
          "one Real equality did not create one group");
  require(registered.predicates.size() == 2,
          "one Real equality did not create two convex components");
  require(registered.predicates[0].payload.relation ==
              FrontendRelation::LessEqual &&
              registered.predicates[1].payload.relation ==
                  FrontendRelation::GreaterEqual,
          "equality components are not <= and >=");
  require(!Frontend::containsRealSyntax(registered.boolean_formula),
          "Real syntax survived equality preregistration");
  require(registered.boolean_formula.GetKind() == AND,
          "equality definition was not conjoined with its use");

  const EqualityRegistration& group = registered.equalities.front();
  ASTNode definition;
  for (const ASTNode& child : registered.boolean_formula.GetChildren())
    if (child.GetKind() == IFF)
      definition = child;
  require(!definition.IsNull(), "equality Boolean definition is absent");
  for (unsigned mask = 0; mask != 8; ++mask)
  {
    const bool e = (mask & 1U) != 0;
    const bool l = (mask & 2U) != 0;
    const bool g = (mask & 4U) != 0;
    const std::map<std::uint64_t, bool> assignments = {
        {group.equality_atom.GetNodeNum(), e},
        {group.less_equal_atom.GetNodeNum(), l},
        {group.greater_equal_atom.GetNodeNum(), g}};
    require(evaluateBoolean(definition, assignments) == (e == (l && g)),
            "E iff (L and G) truth table mismatch");
    require(evaluateBoolean(registered.boolean_formula, assignments) ==
                ((e == (l && g)) && e),
            "equality use and definition truth table mismatch");
  }

  const ASTNode disequal = manager.defaultNodeFactory->CreateNode(NOT, equal);
  const PreregisteredFormula split = frontend.preregister(disequal);
  require(split.equalities.empty(),
          "disequality incorrectly registered a convex equality");
  require(split.predicates.size() == 2,
          "disequality did not create its two strict branches");
  require(split.predicates[0].payload.relation == FrontendRelation::Less &&
              split.predicates[1].payload.relation ==
                  FrontendRelation::Greater,
          "disequality branches are not < and >");
  require(split.boolean_formula.GetKind() == OR,
          "disequality did not become a Boolean split");
  require(!Frontend::containsRealSyntax(split.boolean_formula),
          "Real syntax survived disequality preregistration");
  for (unsigned mask = 0; mask != 4; ++mask)
  {
    const bool less = (mask & 1U) != 0;
    const bool greater = (mask & 2U) != 0;
    const std::map<std::uint64_t, bool> assignments = {
        {split.predicates[0].opaque_atom.GetNodeNum(), less},
        {split.predicates[1].opaque_atom.GetNodeNum(), greater}};
    require(evaluateBoolean(split.boolean_formula, assignments) ==
                (less || greater),
            "disequality strict-branch truth table mismatch");
  }

  const ASTNode nested = manager.defaultNodeFactory->CreateNode(
      ITE,
      manager.defaultNodeFactory->CreateNode(
          OR, equal,
          manager.CreateRealPredicate(REAL_LT, x,
                                      manager.CreateRealConst("-2"))),
      manager.defaultNodeFactory->CreateNode(NOT, equal),
      manager.defaultNodeFactory->CreateNode(
          AND, equal,
          manager.CreateRealPredicate(REAL_GE, x,
                                      manager.CreateRealConst("5/7"))));
  const PreregisteredFormula nested_registered = frontend.preregister(nested);
  require(!Frontend::containsRealSyntax(nested_registered.boolean_formula),
          "nested Boolean equality/disequality retained Real syntax");
  // One group and six predicates, not two and eight: `equal` occurs twice
  // positively here, and the walk now gives a shared node one atom rather
  // than one per path to it. The second group and the extra pair of
  // predicates were the same equality registered again, for the registry to
  // hash-cons back onto the first.
  require(nested_registered.equalities.size() == 1,
          "a shared positive equality did not collapse to one group");
  require(nested_registered.predicates.size() == 6,
          "nested predicate/equality branch registration count mismatch");

  const ASTNode constant_true = manager.CreateRealPredicate(
      REAL_LT, manager.CreateRealConst("-1/3"), zero);
  const NormalizedPredicate folded = frontend.normalizePredicate(constant_true);
  require(folded.is_constant && folded.constant_value,
          "constant exact predicate did not fold true");
  const ASTNode constant_false = manager.CreateRealPredicate(
      REAL_GE, manager.CreateRealConst("-1/3"), zero);
  const NormalizedPredicate false_fold =
      frontend.normalizePredicate(constant_false);
  require(false_fold.is_constant && !false_fold.constant_value,
          "constant exact predicate did not fold false");
}

void sharedAffineDag()
{
  STPMgr manager;
  Frontend frontend(manager);
  const ASTNode x = manager.CreateSourceSymbol("shared_x", SourceSort::real());
  const ASTNode y = manager.CreateSourceSymbol("shared_y", SourceSort::real());
  ASTNode term = manager.CreateRealTerm(REAL_SUB, ASTVec{x, y});
  constexpr unsigned depth = 40;
  for (unsigned i = 0; i < depth; ++i)
    term = manager.CreateRealTerm(REAL_ADD, ASTVec{term, term});
  const LinearPolynomial polynomial = frontend.normalize(term);
  require(frontend.exportPolynomial(polynomial) ==
              "s1:1099511627776,s2:-1099511627776;c:0",
          "shared affine term lost multiplicity or coefficient signs");

  // Preregistration also walks terms to lift ITEs. Even when no node changes,
  // that walk must retain sharing instead of expanding the term to a tree.
  const PreregisteredFormula registered = frontend.preregister(
      manager.CreateNode(REAL_GT, term, manager.CreateRealConst("0")));
  require(registered.predicates.size() == 1 &&
              registered.metrics.normalization_nodes <= 4 * (depth + 3),
          "shared affine DAG was normalized once per path");

  const ASTNode cancelled = manager.CreateRealTerm(REAL_SUB, ASTVec{term, term});
  const LinearPolynomial zero = frontend.normalize(cancelled);
  require(zero.terms.empty() && zero.constant.isZero(),
          "shared affine cancellation left a coefficient");
}

void collisionAndLifetime()
{
  for (unsigned round = 0; round < 32; ++round)
  {
    STPMgr manager;
    Frontend frontend(manager);
    // Low-level APIs are allowed to construct spellings reserved by the
    // SMT-LIB grammar.  Internal identity, not that spelling alone, must keep
    // the abstraction atom collision-proof.
    const ASTNode user = manager.CreateSourceSymbol(
        "@lra_pred_0", SourceSort::boolean());
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    const ASTNode predicate = manager.CreateRealPredicate(
        REAL_LE, x, manager.CreateRealConst("1"));
    const PreregisteredFormula transformed = frontend.preregister(predicate);
    require(transformed.predicates.size() == 1,
            "ordinary predicate registration count mismatch");
    require(transformed.predicates[0].opaque_atom != user,
            "generated opaque atom collided with a user symbol");
    require(transformed.predicates[0].opaque_atom.GetName()[0] == '@',
            "opaque atom is not in the solver-reserved namespace");

    for (unsigned i = 1; i != 256; ++i)
    {
      const ASTNode value = manager.CreateRealConst(
          std::to_string(i), std::to_string(i + 1));
      require(value.GetSourceSort() == SourceSort::real(),
              "bulk exact constant lost its source sort");
    }
  }
}

void canonicalValidation()
{
  STPMgr manager;
  Frontend frontend(manager);
  const auto malformed = [&](const LinearPolynomial& polynomial,
                             const std::string& label) {
    bool rejected = false;
    try
    {
      Frontend::validateCanonical(polynomial);
    }
    catch (const FrontendFailure& failure)
    {
      rejected = failure.kind() == FrontendFailureKind::Malformed;
    }
    require(rejected, label);
  };

  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode y = manager.CreateSourceSymbol("y", SourceSort::real());
  const ASTNode sum = manager.CreateRealTerm(REAL_ADD, ASTVec{x, y});

  LinearPolynomial unsorted = frontend.normalize(sum);
  std::swap(unsorted.terms[0], unsorted.terms[1]);
  malformed(unsorted, "unsorted external canonical polynomial was accepted");

  LinearPolynomial duplicate = frontend.normalize(sum);
  duplicate.terms[1].symbol = duplicate.terms[0].symbol;
  malformed(duplicate, "duplicate external canonical symbol was accepted");

  LinearPolynomial zero_coefficient = frontend.normalize(x);
  LinearPolynomial exact_zero = frontend.normalize(
      manager.CreateRealTerm(REAL_SUB, ASTVec{x, x}));
  zero_coefficient.terms[0].coefficient = std::move(exact_zero.constant);
  malformed(zero_coefficient,
            "zero external canonical coefficient was accepted");

  const ASTNode boolean =
      manager.CreateSourceSymbol("b", SourceSort::boolean());
  bool wrong_sort = false;
  try
  {
    (void)frontend.normalize(boolean);
  }
  catch (const FrontendFailure& failure)
  {
    wrong_sort = failure.kind() == FrontendFailureKind::WrongSort;
  }
  require(wrong_sort, "wrong-sort normalization did not return typed failure");

  STPMgr foreign_manager;
  const ASTNode foreign =
      foreign_manager.CreateSourceSymbol("foreign", SourceSort::real());
  bool foreign_owner = false;
  try
  {
    (void)frontend.normalize(foreign);
  }
  catch (const FrontendFailure& failure)
  {
    foreign_owner = failure.kind() == FrontendFailureKind::Malformed;
  }
  require(foreign_owner,
          "cross-manager normalization did not return typed failure");
}

void metrics()
{
  STPMgr manager;
  Frontend frontend(manager);
  frontend.resetNumberAccounting();

  const ASTNode x = manager.CreateSourceSymbol("metric_x", SourceSort::real());
  const ASTNode y = manager.CreateSourceSymbol("metric_y", SourceSort::real());
  const ASTNode z = manager.CreateSourceSymbol("metric_z", SourceSort::real());
  const ASTNode expression = manager.CreateRealTerm(
      REAL_ADD,
      ASTVec{manager.CreateRealTerm(
                 REAL_MUL, ASTVec{manager.CreateRealConst("3/7"), x}),
             manager.CreateRealTerm(
                 REAL_MUL, ASTVec{manager.CreateRealConst("-5/11"), y}),
             manager.CreateRealConst("13/17")});
  const ASTNode low = manager.CreateRealPredicate(
      REAL_GT, expression, manager.CreateRealConst("-29/31"));
  const ASTNode high = manager.CreateRealPredicate(
      REAL_LE, expression, manager.CreateRealConst("19/23"));
  const ASTNode equal = manager.CreateRealPredicate(EQ, x, y);
  const ASTNode disequal = manager.defaultNodeFactory->CreateNode(
      NOT, manager.CreateRealPredicate(EQ, y, z));
  const ASTNode formula = manager.defaultNodeFactory->CreateNode(
      AND, ASTVec{low, high, equal, disequal});
  const PreregisteredFormula registered = frontend.preregister(formula);
  require(!Frontend::containsRealSyntax(registered.boolean_formula),
          "metric formula escaped the structural barrier");
  require(registered.metrics.symbols == 3,
          "metric formula symbol count drift");
  require(registered.metrics.equality_groups == 1,
          "metric formula equality-group count drift");

  std::set<std::string> rows;
  for (const PredicateRegistration& predicate : registered.predicates)
    rows.insert(frontend.exportPolynomial(
        predicate.payload.lhs_minus_rhs));
  const NumberMetrics numbers = frontend.numberMetrics();
  std::cout
      << "METRICS {\"frontend\":{"
      << "\"symbols\":" << registered.metrics.symbols << ','
      << "\"canonical_rows\":" << rows.size() << ','
      << "\"source_predicates\":4,"
      << "\"component_atoms\":" << registered.predicates.size() << ','
      << "\"equality_groups\":" << registered.metrics.equality_groups
      << ','
      << "\"opaque_atoms\":" << registered.metrics.opaque_atoms << ','
      << "\"normalization_calls\":"
      << registered.metrics.normalization_calls << ','
      << "\"normalization_nodes\":"
      << registered.metrics.normalization_nodes << ','
      << "\"predicates\":" << registered.metrics.predicates << ','
      << "\"constant_predicates\":"
      << registered.metrics.constant_predicates << ','
      << "\"maximum_coefficient_bits\":"
      << registered.metrics.maximum_coefficient_bits
      << "},\"numbers\":{"
      << "\"constructs\":" << numbers.constructs << ','
      << "\"copies\":" << numbers.copies << ','
      << "\"moves\":" << numbers.moves << ','
      << "\"destroys\":" << numbers.destroys << ','
      << "\"parses\":" << numbers.parses << ','
      << "\"canonicalizations\":" << numbers.canonicalizations << ','
      << "\"comparisons\":" << numbers.comparisons << ','
      << "\"additions\":" << numbers.additions << ','
      << "\"subtractions\":" << numbers.subtractions << ','
      << "\"multiplications\":" << numbers.multiplications << ','
      << "\"divisions\":" << numbers.divisions << ','
      << "\"gcds\":" << numbers.gcds << ','
      << "\"floor_divisions\":" << numbers.floor_divisions << ','
      << "\"allocation_calls\":" << numbers.allocation_calls << ','
      << "\"allocated_bytes\":" << numbers.allocated_bytes << ','
      << "\"peak_live_bytes\":" << numbers.peak_live_bytes << ','
      << "\"current_values\":" << numbers.current_values << ','
      << "\"peak_values\":" << numbers.peak_values << ','
      << "\"maximum_numerator_bits\":"
      << numbers.maximum_numerator_bits << ','
      << "\"maximum_denominator_bits\":"
      << numbers.maximum_denominator_bits << ','
      << "\"preflight_stops\":" << numbers.preflight_stops << ','
      << "\"allocation_stops\":" << numbers.allocation_stops
      << "}}\n";
}

void internalPrintBarrier()
{
  STPMgr manager;
  Frontend frontend(manager);
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const PreregisteredFormula registered = frontend.preregister(
      manager.CreateRealPredicate(REAL_LE, x, manager.CreateRealConst("1")));
  printer::SMTLIB2_PrintBack(std::cout, registered.boolean_formula, &manager,
                             false);
  fail("SMT-LIB2 printer exposed a private LRA atom");
}

} // namespace


// A formula as deep as an unrolled trace: one conjunct nested per step, far
// more levels than a call frame per level could fit in the stack this runs
// under. Every walk the frontend makes over the formula has to hold its
// depth on the heap.
void deep()
{
#ifndef _WIN32
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) == 0)
  {
    rl.rlim_cur = 1024 * 1024;
    setrlimit(RLIMIT_STACK, &rl);
  }
#endif
  STPMgr manager;
  Frontend frontend(manager);
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode y = manager.CreateSourceSymbol("y", SourceSort::real());
  const ASTNode atom = manager.CreateNode(REAL_LE, x, y);
  const ASTNode other = manager.CreateNode(REAL_LT, y, manager.CreateRealConst("7"));
  ASTNode chain = atom;
  for (unsigned i = 0; i < 200000; ++i)
    chain = manager.CreateNode(AND, (i % 2 == 0) ? other : atom, chain);
  const PreregisteredFormula pre = frontend.preregister(chain);
  require(!pre.boolean_formula.IsNull() &&
              !Frontend::containsRealSyntax(pre.boolean_formula),
          "deep chain was not preregistered to a pure Boolean formula");
}

int main(int argc, char** argv)
{
  try
  {
    if (argc != 2)
      fail("usage: real_frontend_tests MODE");
    const std::string mode(argv[1]);
    if (mode == "unit")
      unit();
    else if (mode == "deep")
      deep();
    else if (mode == "normalization")
      normalization();
    else if (mode == "shared-dag")
      sharedAffineDag();
    else if (mode == "equality")
      equality();
    else if (mode == "lifetime")
      collisionAndLifetime();
    else if (mode == "validation")
      canonicalValidation();
    else if (mode == "metrics")
      metrics();
    else if (mode == "internal-print-barrier")
      internalPrintBarrier();
    else
      fail("unknown mode: " + mode);
    std::cout << "PASS " << mode << '\n';
    return 0;
  }
  catch (const std::exception& failure)
  {
    std::cerr << "FAIL " << failure.what() << '\n';
    return 1;
  }
}

#include "Lra/LraPresolve.h"

#include "Lra/AffineNormalization.h"
#include "Lra/ASTRealConst.h"
#include "Lra/ExactRational.h"
#include "Lra/LraReconstruction.h"
#include "Lra/LraRelu.h"
#include "Lra/LraHighs.h"
#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFContext.h"

#include <array>
#include <chrono>
#include <deque>
#include <map>
#include <optional>

#include <iostream>
#include <limits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace stp {
namespace lra {
namespace {

using NodeMap = std::unordered_map<std::uint64_t, ASTNode>;

struct SubstitutionLimit {};

// A heuristic refusal keeps the complete input equations. It must not poison
// the query's arithmetic budget or be replenished by another presolve round.
class SubstitutionBudget final
{
public:
  SubstitutionBudget(STPMgr& manager, SATSolver* solver)
      : manager_(manager), solver_(solver),
        growth_limit_(manager.UserFlags.lra_presolve_subst_growth),
        work_limit_(manager.UserFlags.lra_presolve_subst_work) {}

  bool enabled() const { return growth_limit_ != 0; }
  bool stopped() const { return stopped_; }

  void poll()
  {
    if ((work_ & 255U) == 0)
    {
      manager_.checkPreparation(PreparationStage::LraPresolve);
      if (solver_ && solver_->timeLimitExpired())
        throw PreparationInterrupted(PreparationStage::LraPresolve,
                                     std::chrono::steady_clock::now());
    }
    if (work_ >= work_limit_)
      stop("work");
    ++work_;
  }

  void begin(const ASTNode& input)
  {
    before_.reset();
    after_.reset();
    before_ = measure(input, true);
    after_ = before_;
  }

  void created(const ASTNode& root)
  {
    ASTVec todo{root};
    while (!todo.empty())
    {
      poll();
      const auto node = todo.back();
      todo.pop_back();
      if (known_.count(node))
        continue;
      const auto degree = static_cast<std::uint64_t>(node.Degree());
      // Subtraction before addition avoids wraparound even at UINT64_MAX.
      if (growth_ >= growth_limit_ || degree > growth_limit_ - growth_ - 1)
        stop("growth");
      growth_ += degree + 1;
      ++added_nodes_;
      known_.insert(node);
      for (const auto& child : node.GetChildren())
        todo.push_back(child);
    }
  }

  void finish(const ASTNode& result)
  {
    created(result);
    after_ = measure(result, false);
  }

  void refused() { ++refusals_; }

  void report(unsigned round) const
  {
    std::cerr << "LRA substitution round: index=" << round
              << ", work=" << work_ << ", growth=" << growth_
              << ", added_nodes=" << added_nodes_ << ", refusals=" << refusals_
              << ", stop=" << reason_ << ", dag_before=";
    printSize(before_);
    std::cerr << ", dag_after=";
    printSize(after_);
    std::cerr << '\n';
  }

private:
  struct Size { std::uint64_t nodes = 0, edges = 0; };
  static std::uint64_t add(std::uint64_t a, std::uint64_t b)
  {
    const auto max = std::numeric_limits<std::uint64_t>::max();
    return b > max - a ? max : a + b;
  }
  static void printSize(const std::optional<Size>& size)
  {
    if (size)
      std::cerr << size->nodes << '/' << size->edges;
    else
      std::cerr << "unmeasured";
  }
  Size measure(const ASTNode& root, bool baseline)
  {
    Size size;
    ASTNodeSet seen;
    ASTVec todo{root};
    while (!todo.empty())
    {
      poll();
      const auto node = todo.back();
      todo.pop_back();
      if (!seen.insert(node).second)
        continue;
      size.nodes = add(size.nodes, 1);
      size.edges = add(size.edges, node.Degree());
      if (baseline)
        known_.insert(node);
      for (const auto& child : node.GetChildren())
        todo.push_back(child);
    }
    return size;
  }
  [[noreturn]] void stop(const char* reason)
  {
    stopped_ = true;
    reason_ = reason;
    throw SubstitutionLimit{};
  }
  STPMgr& manager_;
  SATSolver* solver_;
  std::uint64_t growth_limit_, work_limit_;
  std::uint64_t work_ = 0, growth_ = 0, added_nodes_ = 0, refusals_ = 0;
  bool stopped_ = false;
  const char* reason_ = "none";
  // Pin observed nodes so an intermediate node number cannot be recycled
  // while the next round uses it for growth accounting.
  ASTNodeSet known_;
  std::optional<Size> before_, after_;
};

/* Top-level conjuncts, through nested ANDs only. */
void flattenConjuncts(const ASTNode& input, ASTVec& out,
                     const std::function<void()>& poll = {})
{
  std::vector<ASTNode> work{input};
  ASTNodeSet seen;
  while (!work.empty())
  {
    if (poll)
      poll();
    const ASTNode node = work.back();
    work.pop_back();
    if (poll && !seen.insert(node).second)
      continue;
    if (node.GetKind() == AND)
    {
      for (std::size_t i = node.Degree(); i > 0; --i)
        work.push_back(node[i - 1]);
      continue;
    }
    out.push_back(node);
  }
}

bool occurs(const ASTNode& haystack, const ASTNode& needle,
            const std::function<void()>& poll = {})
{
  std::unordered_set<std::uint64_t> seen;
  std::vector<ASTNode> work{haystack};
  while (!work.empty())
  {
    if (poll)
      poll();
    const ASTNode node = work.back();
    work.pop_back();
    if (node == needle)
      return true;
    if (node.Degree() == 0 || !seen.insert(node.GetNodeNum()).second)
      continue;
    for (const ASTNode& child : node.GetChildren())
      work.push_back(child);
  }
  return false;
}

/* Memoized DAG rewrite under a symbol substitution. Rebuilding goes
 * through the same constructors the parser used: CreateRealTerm for Real
 * terms, CreateNode for formulas. Bit-vector terms cannot contain a Real
 * symbol, so an unchanged subtree returns itself and never rebuilds. */
class Rewriter final
{
public:
  Rewriter(STPMgr& manager, const NodeMap& substitution)
      : manager_(manager), substitution_(substitution)
  {
  }

  ASTNode apply(const ASTNode& root, const std::function<void()>& poll = {},
                const std::function<void(const ASTNode&)>& created = {})
  {
    /* Explicit stack: the query is as deep as the trace it was unrolled
     * from, and a call frame per level overflows exactly the way the
     * frontend's own walkers document. */
    struct Frame final
    {
      ASTNode node;
      std::size_t next = 0;
    };
    std::vector<Frame> pending;
    pending.push_back(Frame{root});
    while (!pending.empty())
    {
      if (poll)
        poll();
      Frame& frame = pending.back();
      const ASTNode& node = frame.node;
      if (memo_.find(node.GetNodeNum()) != memo_.end())
      {
        pending.pop_back();
        continue;
      }
      if (substitution_.find(node.GetNodeNum()) == substitution_.end() &&
          frame.next < node.Degree())
      {
        const ASTNode child = node[frame.next++];
        if (memo_.find(child.GetNodeNum()) == memo_.end())
          pending.push_back(Frame{child});
        continue;
      }
      ASTNode result = node;
      const auto replaced = substitution_.find(node.GetNodeNum());
      if (replaced != substitution_.end())
        result = replaced->second;
      else if (node.Degree() != 0)
      {
        ASTVec children;
        children.reserve(node.Degree());
        bool changed = false;
        for (const ASTNode& child : node.GetChildren())
        {
          const ASTNode& rebuilt = memo_.at(child.GetNodeNum());
          changed = changed || !(rebuilt == child);
          children.push_back(rebuilt);
        }
        if (changed)
        {
          if (node.isRealTerm())
            result = manager_.CreateRealTerm(node.GetKind(), children);
          else if (node.GetType() == BOOLEAN_TYPE)
            result = manager_.CreateNode(node.GetKind(), children);
        }
      }
      if (created && result != node)
        created(result);
      memo_.emplace(node.GetNodeNum(), result);
      pending.pop_back();
    }
    return memo_.at(root.GetNodeNum());
  }

private:
  STPMgr& manager_;
  const NodeMap& substitution_;
  NodeMap memo_;
};

bool realSymbol(const ASTNode& node)
{
  return node.GetKind() == SYMBOL &&
         node.GetSourceSort().kind() == SourceSort::Kind::Real;
}


/* A linear view of a Real term: coefficients by symbol node, plus the
 * constant. Extraction mirrors the frontend's normalization for the
 * supported fragment and refuses anything else. */
struct LinearView final
{
  std::map<std::uint64_t, ExactRational> coefficients;
  std::unordered_map<std::uint64_t, ASTNode> symbols;
  ExactRational constant;
};

template <typename Poll>
bool addLinear(LinearView& view, const ASTNode& term,
               const ExactRational& scale, Poll& poll)
{
  const auto resolve = [&](const ASTNode& symbol) {
    view.symbols.emplace(symbol.GetNodeNum(), symbol);
    return symbol.GetNodeNum();
  };
  const auto visit = [](const ASTNode&) {};
  AffinePolynomial polynomial;
  try
  {
    polynomial = normalizeAffineDag(term, scale, resolve, visit, poll,
                                    {false, true});
  }
  catch (const FrontendFailure& failure)
  {
    if (failure.kind() != FrontendFailureKind::Unsupported &&
        failure.kind() != FrontendFailureKind::WrongSort &&
        failure.kind() != FrontendFailureKind::Malformed)
      throw;
    return false;
  }
  for (auto& entry : polynomial.coefficients)
  {
    auto found = view.coefficients.find(entry.first);
    if (found == view.coefficients.end())
      view.coefficients.emplace(entry.first, std::move(entry.second));
    else
    {
      found->second += entry.second;
      if (found->second.isZero())
        view.coefficients.erase(found);
    }
  }
  view.constant += polynomial.constant;
  return true;
}

bool addLinear(LinearView& view, const ASTNode& term,
               const ExactRational& scale)
{
  auto poll = []() {};
  return addLinear(view, term, scale, poll);
}

/* Rebuild a linear view (minus one solved variable) as a Real term:
 * t = (-constant - sum of other monomials) / a for the solved variable's
 * coefficient a. Constants print through the exact canonical fraction, so
 * the parser-facing constructors stay the single entry point for values. */
ASTNode constantNode(STPMgr& manager, const ExactRational& value)
{
  return manager.CreateRealConst(value.canonicalFraction());
}

ASTNode solveViewFor(STPMgr& manager, const LinearView& view,
                     std::uint64_t solve_for,
                     const std::function<void()>& poll = {},
                     const std::function<void(const ASTNode&)>& created = {})
{
  const ExactRational& a = view.coefficients.at(solve_for);
  ExactRational minus_inverse = a.inverse();
  minus_inverse *= ExactRational(std::int64_t{-1});
  ASTVec monomials;
  for (const auto& entry : view.coefficients)
  {
    if (poll)
      poll();
    if (entry.first == solve_for)
      continue;
    ExactRational coefficient = entry.second;
    coefficient *= minus_inverse;
    const ASTNode& symbol = view.symbols.at(entry.first);
    if (coefficient.compare(ExactRational(std::int64_t{1})) == 0)
      monomials.push_back(symbol);
    else
      monomials.push_back(manager.CreateRealTerm(
          REAL_MUL, ASTVec{constantNode(manager, coefficient), symbol}));
    if (created)
      created(monomials.back());
  }
  if (!view.constant.isZero() || monomials.empty())
  {
    ExactRational constant = view.constant;
    constant *= minus_inverse;
    monomials.push_back(constantNode(manager, constant));
    if (created)
      created(monomials.back());
  }
  if (monomials.size() == 1)
    return monomials[0];
  return manager.CreateRealTerm(REAL_ADD, monomials);
}

/* Stage one: solved definitions. A top-level conjunct EQ(x, t) with x a
 * Real symbol not occurring in t defines x; substitute it through every
 * other conjunct and keep the definition conjoined, so x still has its
 * one defining row and every model question about it stays answerable.
 * Later definitions see earlier substitutions applied first, which keeps
 * the map triangular without a transitive-closure pass. */
ASTNode substituteDefinitionsImpl(STPMgr& manager, const ASTNode& input,
                                  std::size_t& definitions_used,
                                  SubstitutionBudget* budget)
{
  std::function<void()> poll;
  std::function<void(const ASTNode&)> created;
  if (budget)
  {
    poll = [&]() { budget->poll(); };
    created = [&](const ASTNode& node) { budget->created(node); };
  }
  ASTVec conjuncts;
  flattenConjuncts(input, conjuncts, poll);
  if (conjuncts.size() < 2)
    return input;

  NodeMap substitution;
  std::unordered_set<std::uint64_t> defined;
  std::vector<bool> is_definition(conjuncts.size(), false);
  std::vector<ASTNode> defines(conjuncts.size());
  for (std::size_t i = 0; i < conjuncts.size(); ++i)
  {
    if (poll)
      poll();
    const ASTNode& conjunct = conjuncts[i];
    if (conjunct.GetKind() != EQ || conjunct.Degree() != 2)
      continue;
    ASTNode symbol;
    ASTNode definition;
    if (realSymbol(conjunct[0]) && !defined.count(conjunct[0].GetNodeNum()))
    {
      symbol = conjunct[0];
      definition = conjunct[1];
    }
    else if (realSymbol(conjunct[1]) &&
             !defined.count(conjunct[1].GetNodeNum()))
    {
      symbol = conjunct[1];
      definition = conjunct[0];
    }
    else
      continue;
    if (!definition.isRealTerm() && definition.GetKind() != SYMBOL)
      continue;
    if (definition.GetKind() == SYMBOL &&
        definition.GetSourceSort().kind() != SourceSort::Kind::Real)
      continue;
    Rewriter forward(manager, substitution);
    const ASTNode resolved = forward.apply(definition, poll, created);
    if (occurs(resolved, symbol, poll))
      continue;
    substitution.emplace(symbol.GetNodeNum(), resolved);
    defined.insert(symbol.GetNodeNum());
    is_definition[i] = true;
    defines[i] = symbol;
  }

  /* Gaussian pass: any remaining top-level linear equality is solved for
   * one of its variables, syntax notwithstanding -- 2x + 3y = z - 1
   * defines x as much as x = t does. Earlier substitutions are applied
   * first, so the solved form cannot smuggle a defined variable back in; a
   * variable-free equality that misses refutes the query outright. */
  ASTVec gaussian_conflict;
  for (std::size_t i = 0; i < conjuncts.size(); ++i)
  {
    if (poll)
      poll();
    if (is_definition[i])
      continue;
    const ASTNode& conjunct = conjuncts[i];
    if (conjunct.GetKind() != EQ || conjunct.Degree() != 2 ||
        conjunct[0].GetSourceSort().kind() != SourceSort::Kind::Real)
      continue;
    Rewriter forward(manager, substitution);
    const ASTNode resolved_conjunct = forward.apply(conjunct, poll, created);
    /* Substitution can collapse the equality at the factory: a second
     * definition of an already-defined symbol folds to a constant. Guard
     * on the RESOLVED shape, not the original's -- indexing a folded
     * constant's children is exactly the crash this comment prevents. */
    if (resolved_conjunct == manager.ASTFalse)
    {
      gaussian_conflict.push_back(conjunct);
      break;
    }
    if (resolved_conjunct == manager.ASTTrue ||
        resolved_conjunct.GetKind() != EQ || resolved_conjunct.Degree() != 2 ||
        resolved_conjunct[0].GetSourceSort().kind() != SourceSort::Kind::Real)
      continue;
    LinearView view;
    const ExactRational plus(std::int64_t{1});
    const ExactRational minus(std::int64_t{-1});
    const auto linear = [&](const ASTNode& term, const ExactRational& scale) {
      return budget ? addLinear(view, term, scale, poll)
                    : addLinear(view, term, scale);
    };
    if (!linear(resolved_conjunct[0], plus) || !linear(resolved_conjunct[1], minus))
      continue;
    if (view.coefficients.empty())
    {
      if (!view.constant.isZero())
      {
        gaussian_conflict.push_back(conjunct);
        break;
      }
      continue; // 0 = 0: registration folds it away.
    }
    // Prefer a variable that is not yet defined; first such in map order.
    std::uint64_t solve_for = 0;
    bool found = false;
    for (const auto& entry : view.coefficients)
      if (!defined.count(entry.first))
      {
        solve_for = entry.first;
        found = true;
        break;
      }
    if (!found)
      continue;
    const ASTNode symbol = view.symbols.at(solve_for);
    const ASTNode solved = solveViewFor(manager, view, solve_for, poll, created);
    if (created)
      created(solved);
    if (occurs(solved, symbol, poll))
      continue;
    substitution.emplace(symbol.GetNodeNum(), solved);
    defined.insert(symbol.GetNodeNum());
    is_definition[i] = true;
    defines[i] = symbol;
  }
  if (!gaussian_conflict.empty())
    return manager.ASTFalse;
  if (substitution.empty())
    return input;

  definitions_used = substitution.size();
  Rewriter rewriter(manager, substitution);
  ASTVec rebuilt;
  rebuilt.reserve(conjuncts.size());
  for (std::size_t i = 0; i < conjuncts.size(); ++i)
  {
    if (poll)
      poll();
    if (is_definition[i])
    {
      // The definition keeps its solved shape, EQ(x, t), from the record
      // made when it was solved -- no re-derivation, no guessing.
      const ASTNode& symbol = defines[i];
      const auto target = substitution.find(symbol.GetNodeNum());
      rebuilt.push_back(manager.CreateNode(EQ, symbol, target->second));
      if (created)
        created(rebuilt.back());
      continue;
    }
    rebuilt.push_back(rewriter.apply(conjuncts[i], poll, created));
  }
  if (rebuilt.size() == 1)
    return rebuilt[0];
  return manager.CreateNode(AND, rebuilt);
}

ASTNode substituteDefinitions(STPMgr& manager, const ASTNode& input,
                              std::size_t& definitions_used,
                              SubstitutionBudget& budget)
{
  if (!budget.enabled())
    return substituteDefinitionsImpl(manager, input, definitions_used, nullptr);
  if (budget.stopped())
    return input;
  try
  {
    budget.begin(input);
    const auto result = substituteDefinitionsImpl(manager, input, definitions_used, &budget);
    budget.finish(result);
    return result;
  }
  catch (const SubstitutionLimit&)
  {
    definitions_used = 0;
    budget.refused();
    return input;
  }
}

/* ---- Stage: propagation. ----------------------------------------------

   The under-structure half of constant propagation: a top-level conjunct
   is a truth, and every occurrence of it -- or of its negation -- below
   any Boolean structure may be replaced by that truth.
   C and F[phi] is C and F[true] whenever phi is one of C's conjuncts. The
   facts themselves stay asserted; the factory folds the constants the
   replacement exposes as the rebuild goes, and a conjunct that collapses
   to a new literal feeds the next round, to a small fixed cap. */
ASTNode propagateFacts(STPMgr& manager, const ASTNode& input,
                       std::size_t& facts_propagated, bool& proved_unsat)
{
  ASTNode current = input;
  for (int round = 0; round != 3; ++round)
  {
    ASTVec conjuncts;
    flattenConjuncts(current, conjuncts);
    if (conjuncts.size() < 2)
      return current;
    NodeMap facts;
    for (const ASTNode& conjunct : conjuncts)
    {
      if (conjunct.GetKind() == NOT && conjunct.Degree() == 1)
        facts.emplace(conjunct[0].GetNodeNum(), manager.ASTFalse);
      else if (conjunct.GetKind() != AND)
        facts.emplace(conjunct.GetNodeNum(), manager.ASTTrue);
    }
    if (facts.empty())
      return current;
    Rewriter rewriter(manager, facts);
    ASTVec rebuilt;
    rebuilt.reserve(conjuncts.size());
    bool changed = false;
    std::size_t replaced = 0;
    for (const ASTNode& conjunct : conjuncts)
    {
      /* Each conjunct is rewritten under the full fact map minus itself.
       * A DAG node cannot contain itself, so a conjunct's own entry can
       * only ever fire at its root: rewriting the CHILDREN under the one
       * shared map and rebuilding the root by hand is exactly root-skip,
       * with the memo shared and the walk linear. A negated fact is kept
       * whole -- rewriting its body to FALSE would fold the assertion
       * itself away. */
      if (conjunct.GetKind() == NOT && conjunct.Degree() == 1 &&
          facts.count(conjunct[0].GetNodeNum()) != 0)
      {
        rebuilt.push_back(conjunct);
        continue;
      }
      ASTNode replacement = conjunct;
      if (conjunct.Degree() != 0 && conjunct.GetType() == BOOLEAN_TYPE &&
          !conjunct.isRealTerm())
      {
        ASTVec children;
        children.reserve(conjunct.Degree());
        bool child_changed = false;
        for (const ASTNode& child : conjunct.GetChildren())
        {
          ASTNode rebuilt_child = rewriter.apply(child);
          child_changed = child_changed || !(rebuilt_child == child);
          children.push_back(std::move(rebuilt_child));
        }
        if (child_changed)
          replacement = manager.CreateNode(conjunct.GetKind(), children);
      }
      if (!(replacement == conjunct))
      {
        ++replaced;
        changed = true;
      }
      if (replacement == manager.ASTFalse)
      {
        proved_unsat = true;
        return manager.ASTFalse;
      }
      if (replacement == manager.ASTTrue)
        continue;
      rebuilt.push_back(replacement);
    }
    facts_propagated += replaced;
    if (!changed)
      return current;
    if (rebuilt.empty())
      return manager.ASTTrue;
    current = rebuilt.size() == 1 ? rebuilt[0]
                                  : manager.CreateNode(AND, rebuilt);
  }
  return current;
}

/* ---- Stage two: bounds. ------------------------------------------------ */


enum class Relation : std::uint8_t
{
  Less,
  LessEqual,
  GreaterEqual,
  Greater,
  Equal
};

bool relationFor(Kind kind, Relation& out)
{
  switch (kind)
  {
    case REAL_LT: out = Relation::Less; return true;
    case REAL_LE: out = Relation::LessEqual; return true;
    case REAL_GE: out = Relation::GreaterEqual; return true;
    case REAL_GT: out = Relation::Greater; return true;
    case EQ: out = Relation::Equal; return true;
    default: return false;
  }
}

struct Bound final
{
  ExactRational value;
  bool strict = false;
  bool present = false;
};

struct VariableBounds final
{
  Bound lower;
  Bound upper;
  ASTNode symbol;
};

/* Merge a derived bound, keeping the tighter one. */
bool mergeLower(VariableBounds& bounds, const ExactRational& value, bool strict)
{
  if (!bounds.lower.present)
  {
    bounds.lower = Bound{value, strict, true};
    return true;
  }
  const int order = value.compare(bounds.lower.value);
  if (order > 0 || (order == 0 && strict && !bounds.lower.strict))
  {
    bounds.lower = Bound{value, strict, true};
    return true;
  }
  return false;
}

bool mergeUpper(VariableBounds& bounds, const ExactRational& value, bool strict)
{
  if (!bounds.upper.present)
  {
    bounds.upper = Bound{value, strict, true};
    return true;
  }
  const int order = value.compare(bounds.upper.value);
  if (order < 0 || (order == 0 && strict && !bounds.upper.strict))
  {
    bounds.upper = Bound{value, strict, true};
    return true;
  }
  return false;
}

/* lower > upper, or equal with either side strict, is infeasible. */
bool infeasible(const VariableBounds& bounds)
{
  if (!bounds.lower.present || !bounds.upper.present)
    return false;
  const int order = bounds.lower.value.compare(bounds.upper.value);
  return order > 0 ||
         (order == 0 && (bounds.lower.strict || bounds.upper.strict));
}

bool fixed(const VariableBounds& bounds)
{
  return bounds.lower.present && bounds.upper.present &&
         !bounds.lower.strict && !bounds.upper.strict &&
         bounds.lower.value.compare(bounds.upper.value) == 0;
}

/* poly REL 0 over one variable c*x + k: bound x by -k/c, orientation
 * flipped when c is negative. */
void applyUnit(std::map<std::uint64_t, VariableBounds>& table,
               const LinearView& view, Relation relation)
{
  const auto entry = view.coefficients.begin();
  const ExactRational& c = entry->second;
  ExactRational bound = view.constant;
  bound *= ExactRational(std::int64_t{-1});
  bound *= c.inverse();
  const bool negative = c.sign() < 0;
  VariableBounds& bounds = table[entry->first];
  bounds.symbol = view.symbols.at(entry->first);
  switch (relation)
  {
    case Relation::Less:
      negative ? mergeLower(bounds, bound, true)
               : mergeUpper(bounds, bound, true);
      break;
    case Relation::LessEqual:
      negative ? mergeLower(bounds, bound, false)
               : mergeUpper(bounds, bound, false);
      break;
    case Relation::GreaterEqual:
      negative ? mergeUpper(bounds, bound, false)
               : mergeLower(bounds, bound, false);
      break;
    case Relation::Greater:
      negative ? mergeUpper(bounds, bound, true)
               : mergeLower(bounds, bound, true);
      break;
    case Relation::Equal:
      mergeLower(bounds, bound, false);
      mergeUpper(bounds, bound, false);
      break;
  }
}

/* One propagation round: for c*x + rest REL 0, a bound on x follows when
 * every other variable is bounded on the side the signs need. */
void propagateRow(std::map<std::uint64_t, VariableBounds>& table,
                  const LinearView& view, Relation relation)
{
  // Sum each bound contribution once. Removing the target's contribution
  // gives the same rest-of-row extreme that the quadratic loop computed.
  // Counts let us exclude its missing bound and its strictness as well.
  struct Extreme
  {
    ExactRational value;
    std::size_t missing = 0;
    std::size_t strict = 0;
  };
  struct Entry
  {
    std::uint64_t id;
    const ExactRational* coefficient;
    VariableBounds* bounds;
    std::array<Bound, 2> contributions; // minimum, maximum
  };
  std::array<Extreme, 2> totals{Extreme{view.constant}, Extreme{view.constant}};
  const std::array<bool, 2> enabled{
      relation == Relation::Less || relation == Relation::LessEqual ||
          relation == Relation::Equal,
      relation == Relation::Greater || relation == Relation::GreaterEqual ||
          relation == Relation::Equal};
  std::vector<Entry> entries;
  entries.reserve(view.coefficients.size());
  for (const auto& target : view.coefficients)
  {
    const auto found = table.find(target.first);
    VariableBounds* bounds = found == table.end() ? nullptr : &found->second;
    entries.push_back(Entry{target.first, &target.second, bounds, {}});
    Entry& entry = entries.back();
    for (std::size_t side = 0; side != 2; ++side)
    {
      if (!enabled[side])
        continue;
      const bool lower = (side == 0) == (target.second.sign() > 0);
      const Bound* bound = bounds == nullptr ? nullptr
                           : lower           ? &bounds->lower
                                             : &bounds->upper;
      if (bound == nullptr || !bound->present)
      {
        ++totals[side].missing;
        continue;
      }
      Bound& contribution = entry.contributions[side];
      contribution = Bound{target.second * bound->value, bound->strict, true};
      totals[side].value += contribution.value;
      totals[side].strict += contribution.strict ? 1U : 0U;
    }
  }
  for (Entry& entry : entries)
  {
    const ExactRational& c = *entry.coefficient;
    for (std::size_t side = 0; side != 2; ++side)
    {
      if (!enabled[side])
        continue;
      const Bound& own = entry.contributions[side];
      const Extreme& total = totals[side];
      if (total.missing != (own.present ? 0U : 1U))
        continue;
      const bool strict = relation == Relation::Less ||
                          relation == Relation::Greater ||
                          total.strict > (own.strict ? 1U : 0U);
      ExactRational extreme = -total.value;
      if (own.present)
        extreme += own.value;
      const ExactRational bound_value = extreme / c;
      if (entry.bounds == nullptr)
      {
        entry.bounds = &table[entry.id];
        entry.bounds->symbol = view.symbols.at(entry.id);
      }
      VariableBounds& bounds = *entry.bounds;
      const bool upper = (side == 0) == (c.sign() > 0);
      const bool changed = upper ? mergeUpper(bounds, bound_value, strict)
                                 : mergeLower(bounds, bound_value, strict);
      if (!changed || !enabled[1U - side])
        continue;

      // A minimum yields an upper bound on c*x, changing its maximum
      // contribution (and conversely). Refresh immediately, including
      // newly present or newly strict bounds, so later targets and the
      // other side of this equality see the same sequential updates.
      Bound& contribution = entry.contributions[1U - side];
      Extreme& opposite = totals[1U - side];
      if (contribution.present)
      {
        opposite.value -= contribution.value;
        opposite.strict -= contribution.strict ? 1U : 0U;
      }
      else
        --opposite.missing;
      const Bound& bound = upper ? bounds.upper : bounds.lower;
      contribution = Bound{c * bound.value, bound.strict, true};
      opposite.value += contribution.value;
      opposite.strict += contribution.strict ? 1U : 0U;
    }
  }
}

ASTNode boundsPresolve(STPMgr& manager, const ASTNode& input,
                       std::size_t& fixed_variables,
                       std::size_t& atoms_folded, bool& proved_unsat)
{
  ASTVec conjuncts;
  flattenConjuncts(input, conjuncts);
  if (conjuncts.empty())
    return input;

  std::vector<std::optional<std::pair<LinearView, Relation>>> rows;
  rows.reserve(conjuncts.size());
  for (const ASTNode& conjunct : conjuncts)
  {
    Relation relation;
    if (conjunct.Degree() == 2 && relationFor(conjunct.GetKind(), relation) &&
        (conjunct[0].isRealTerm() || conjunct[0].GetKind() == SYMBOL) &&
        conjunct[0].GetSourceSort().kind() == SourceSort::Kind::Real)
    {
      LinearView view;
      const ExactRational plus(std::int64_t{1});
      const ExactRational minus(std::int64_t{-1});
      if (addLinear(view, conjunct[0], plus) &&
          addLinear(view, conjunct[1], minus) && !view.coefficients.empty())
      {
        rows.emplace_back(std::in_place, std::move(view), relation);
        continue;
      }
    }
    rows.emplace_back(std::nullopt);
  }

  // These immutable views are needed again while deciding atoms. Dense
  // affine equalities dominate extraction cost; do not parse them twice.
  // Build the index after the vector is complete so pointers stay stable.
  std::unordered_map<std::uint64_t, const LinearView*> row_views;
  row_views.reserve(rows.size());
  for (std::size_t i = 0; i != rows.size(); ++i)
    if (rows[i])
      row_views.emplace(conjuncts[i].GetNodeNum(), &rows[i]->first);

  std::map<std::uint64_t, VariableBounds> table;
  for (const auto& row : rows)
    if (row && row->first.coefficients.size() == 1)
      applyUnit(table, row->first, row->second);
  for (const auto& row : rows)
    if (row && row->first.coefficients.size() > 1)
      propagateRow(table, row->first, row->second);

  /* Bound-driven atom simplification: with the table in hand, any Real
   * atom anywhere in the structure whose polynomial the bounds already
   * decide folds to its truth -- implied atoms to TRUE, refuted ones to
   * FALSE -- sound at every polarity, since the implication holds in every
   * model of the top-level conjuncts. Atoms are collected from the whole
   * DAG, evaluated against the table, and the conjuncts rebuilt by the
   * same child-rewrite that propagation uses, so a top-level unit is never
   * folded by itself. */
  NodeMap atom_truths;
  {
    std::unordered_set<std::uint64_t> visited;
    std::vector<ASTNode> work(conjuncts.begin(), conjuncts.end());
    while (!work.empty())
    {
      const ASTNode node = work.back();
      work.pop_back();
      if (!visited.insert(node.GetNodeNum()).second)
        continue;
      Relation relation;
      if (node.Degree() == 2 && relationFor(node.GetKind(), relation) &&
          node[0].GetSourceSort().kind() == SourceSort::Kind::Real)
      {
        const auto cached = row_views.find(node.GetNodeNum());
        const LinearView* view = cached == row_views.end() ? nullptr
                                                          : cached->second;
        std::optional<LinearView> extracted;
        if (view == nullptr)
        {
          extracted.emplace();
          const ExactRational plus(std::int64_t{1});
          const ExactRational minus(std::int64_t{-1});
          if (addLinear(*extracted, node[0], plus) &&
              addLinear(*extracted, node[1], minus) &&
              !extracted->coefficients.empty())
            view = &*extracted;
        }
        if (view != nullptr)
        {
          // min and max of the polynomial under the table, where bounded.
          Bound lower_total{view->constant, false, true};
          Bound upper_total{view->constant, false, true};
          for (const auto& term : view->coefficients)
          {
            const auto found = table.find(term.first);
            const bool positive = term.second.sign() > 0;
            const Bound* for_min = nullptr;
            const Bound* for_max = nullptr;
            if (found != table.end())
            {
              for_min =
                  positive ? &found->second.lower : &found->second.upper;
              for_max =
                  positive ? &found->second.upper : &found->second.lower;
            }
            if (lower_total.present)
            {
              if (for_min == nullptr || !for_min->present)
                lower_total.present = false;
              else
              {
                ExactRational contribution = term.second;
                contribution *= for_min->value;
                lower_total.value += contribution;
                lower_total.strict = lower_total.strict || for_min->strict;
              }
            }
            if (upper_total.present)
            {
              if (for_max == nullptr || !for_max->present)
                upper_total.present = false;
              else
              {
                ExactRational contribution = term.second;
                contribution *= for_max->value;
                upper_total.value += contribution;
                upper_total.strict = upper_total.strict || for_max->strict;
              }
            }
            if (!lower_total.present && !upper_total.present)
              break;
          }
          // poly REL 0: decide from whichever extreme is available.
          bool implied = false;
          bool refuted = false;
          const int max_sign =
              upper_total.present ? upper_total.value.sign() : 0;
          const int min_sign =
              lower_total.present ? lower_total.value.sign() : 0;
          switch (relation)
          {
            case Relation::LessEqual:
              implied = upper_total.present && max_sign <= 0;
              refuted = lower_total.present &&
                        (min_sign > 0 ||
                         (min_sign == 0 && lower_total.strict));
              break;
            case Relation::Less:
              implied = upper_total.present &&
                        (max_sign < 0 || (max_sign == 0 &&
                                          upper_total.strict));
              refuted = lower_total.present && min_sign >= 0;
              break;
            case Relation::GreaterEqual:
              implied = lower_total.present && min_sign >= 0;
              refuted = upper_total.present &&
                        (max_sign < 0 ||
                         (max_sign == 0 && upper_total.strict));
              break;
            case Relation::Greater:
              implied = lower_total.present &&
                        (min_sign > 0 || (min_sign == 0 &&
                                          lower_total.strict));
              refuted = upper_total.present && max_sign <= 0;
              break;
            case Relation::Equal:
              refuted = (lower_total.present &&
                         (min_sign > 0 ||
                          (min_sign == 0 && lower_total.strict))) ||
                        (upper_total.present &&
                         (max_sign < 0 ||
                          (max_sign == 0 && upper_total.strict)));
              break;
          }
          if (implied)
          {
            atom_truths.emplace(node.GetNodeNum(), manager.ASTTrue);
            ++atoms_folded;
          }
          else if (refuted)
          {
            atom_truths.emplace(node.GetNodeNum(), manager.ASTFalse);
            ++atoms_folded;
          }
        }
        continue; // Atoms have no Boolean children to descend into.
      }
      if (node.isRealTerm())
        continue;
      for (const ASTNode& child : node.GetChildren())
        work.push_back(child);
    }
  }

  NodeMap substitution;
  ASTVec fixes;
  for (const auto& entry : table)
  {
    if (infeasible(entry.second))
    {
      proved_unsat = true;
      return manager.ASTFalse;
    }
    if (fixed(entry.second))
    {
      const ASTNode constant = manager.CreateRealConst(
          entry.second.lower.value.canonicalFraction());
      substitution.emplace(entry.first, constant);
      fixes.push_back(
          manager.CreateNode(EQ, entry.second.symbol, constant));
    }
  }
  if (substitution.empty() && atom_truths.empty())
    return input;

  fixed_variables = substitution.size();
  for (const auto& truth : atom_truths)
    substitution.emplace(truth.first, truth.second);
  Rewriter rewriter(manager, substitution);
  ASTVec rebuilt;
  rebuilt.reserve(conjuncts.size() + fixes.size());
  for (const ASTNode& conjunct : conjuncts)
  {
    /* Child-rewrite, as in propagation: a top-level unit that sourced a
     * bound must not be folded away by the truth its own bound implies;
     * deeper occurrences fold freely. Variable fixes still substitute at
     * the root -- a fixed symbol's occurrence at root is impossible, the
     * conjunct is a formula. */
    ASTNode replacement = conjunct;
    if (conjunct.Degree() != 0)
    {
      ASTVec children;
      children.reserve(conjunct.Degree());
      bool child_changed = false;
      for (const ASTNode& child : conjunct.GetChildren())
      {
        ASTNode rebuilt_child = rewriter.apply(child);
        child_changed = child_changed || !(rebuilt_child == child);
        children.push_back(std::move(rebuilt_child));
      }
      if (child_changed)
        replacement =
            conjunct.isRealTerm()
                ? manager.CreateRealTerm(conjunct.GetKind(), children)
                : manager.CreateNode(conjunct.GetKind(), children);
    }
    if (replacement == manager.ASTFalse)
    {
      proved_unsat = true;
      return manager.ASTFalse;
    }
    if (replacement == manager.ASTTrue)
      continue;
    rebuilt.push_back(replacement);
  }
  for (const ASTNode& fix : fixes)
    rebuilt.push_back(fix);
  if (rebuilt.empty())
    return manager.ASTTrue;
  if (rebuilt.size() == 1)
    return rebuilt[0];
  return manager.CreateNode(AND, rebuilt);
}

/* ---- Stage three: rows. ------------------------------------------------ */

/* Scale a linear view so its lowest-numbered symbol carries coefficient
 * one; the relation flips when the scale is negative. The signature that
 * results names the polynomial independently of how the input spelled it,
 * so same-polynomial conjuncts meet in one group. */
struct RowKey final
{
  std::string signature;
  ExactRational bound;   // scaled -constant: poly' REL bound
  Relation relation;
};

bool canonicalRow(const LinearView& view, Relation relation, RowKey& out)
{
  if (view.coefficients.empty())
    return false;
  const ExactRational& lead = view.coefficients.begin()->second;
  ExactRational scale = lead.inverse();
  if (lead.sign() < 0)
  {
    switch (relation)
    {
      case Relation::Less: relation = Relation::Greater; break;
      case Relation::LessEqual: relation = Relation::GreaterEqual; break;
      case Relation::GreaterEqual: relation = Relation::LessEqual; break;
      case Relation::Greater: relation = Relation::Less; break;
      case Relation::Equal: break;
    }
  }
  std::string signature;
  for (const auto& entry : view.coefficients)
  {
    ExactRational scaled = entry.second;
    scaled *= scale;
    signature += std::to_string(entry.first);
    signature += ':';
    signature += scaled.canonicalFraction();
    signature += ';';
  }
  ExactRational bound = view.constant;
  bound *= scale;
  bound *= ExactRational(std::int64_t{-1});
  out = RowKey{std::move(signature), std::move(bound), relation};
  return true;
}

/* Group top-level conjuncts by canonical polynomial; inside a group a
 * conjunct implied by a sibling is dropped (the sibling stays, so the
 * implication survives in the query), and contradictory bounds refute the
 * query. Equalities stay untouched -- stage one owns those. */
ASTNode tightenRows(STPMgr& manager, const ASTNode& input,
                    std::size_t& rows_dropped, bool& proved_unsat)
{
  ASTVec conjuncts;
  flattenConjuncts(input, conjuncts);
  if (conjuncts.size() < 2)
    return input;

  struct GroupBest final
  {
    Bound lower;
    Bound upper;
  };
  std::unordered_map<std::string, GroupBest> groups;
  std::vector<std::optional<RowKey>> keys(conjuncts.size());
  for (std::size_t i = 0; i < conjuncts.size(); ++i)
  {
    const ASTNode& conjunct = conjuncts[i];
    Relation relation;
    if (conjunct.Degree() != 2 || !relationFor(conjunct.GetKind(), relation) ||
        relation == Relation::Equal ||
        conjunct[0].GetSourceSort().kind() != SourceSort::Kind::Real)
      continue;
    LinearView view;
    const ExactRational plus(std::int64_t{1});
    const ExactRational minus(std::int64_t{-1});
    if (!addLinear(view, conjunct[0], plus) ||
        !addLinear(view, conjunct[1], minus) || view.coefficients.empty())
      continue;
    RowKey key;
    if (!canonicalRow(view, relation, key))
      continue;
    GroupBest& best = groups[key.signature];
    const bool strict =
        key.relation == Relation::Less || key.relation == Relation::Greater;
    if (key.relation == Relation::Less || key.relation == Relation::LessEqual)
    {
      Bound proposed{key.bound, strict, true};
      if (!best.upper.present)
        best.upper = proposed;
      else
      {
        const int order = key.bound.compare(best.upper.value);
        if (order < 0 || (order == 0 && strict && !best.upper.strict))
          best.upper = proposed;
      }
    }
    else
    {
      Bound proposed{key.bound, strict, true};
      if (!best.lower.present)
        best.lower = proposed;
      else
      {
        const int order = key.bound.compare(best.lower.value);
        if (order > 0 || (order == 0 && strict && !best.lower.strict))
          best.lower = proposed;
      }
    }
    keys[i].emplace(std::move(key));
  }

  for (const auto& group : groups)
  {
    if (!group.second.lower.present || !group.second.upper.present)
      continue;
    const int order =
        group.second.lower.value.compare(group.second.upper.value);
    if (order > 0 || (order == 0 && (group.second.lower.strict ||
                                     group.second.upper.strict)))
    {
      proved_unsat = true;
      return manager.ASTFalse;
    }
  }

  ASTVec rebuilt;
  rebuilt.reserve(conjuncts.size());
  for (std::size_t i = 0; i < conjuncts.size(); ++i)
  {
    if (!keys[i])
    {
      rebuilt.push_back(conjuncts[i]);
      continue;
    }
    const RowKey& key = *keys[i];
    const GroupBest& best = groups.at(key.signature);
    const bool is_upper = key.relation == Relation::Less ||
                          key.relation == Relation::LessEqual;
    const Bound& strongest = is_upper ? best.upper : best.lower;
    const bool strict =
        key.relation == Relation::Less || key.relation == Relation::Greater;
    const int order = key.bound.compare(strongest.value);
    const bool weaker =
        is_upper ? (order > 0 || (order == 0 && !strict && strongest.strict))
                 : (order < 0 || (order == 0 && !strict && strongest.strict));
    if (weaker)
    {
      ++rows_dropped;
      continue;
    }
    rebuilt.push_back(conjuncts[i]);
  }
  if (rows_dropped == 0)
    return input;
  if (rebuilt.empty())
    return manager.ASTTrue;
  if (rebuilt.size() == 1)
    return rebuilt[0];
  return manager.CreateNode(AND, rebuilt);
}

/* A monotone variable can satisfy all its effective literals by moving far
 * enough in one direction. Analyse each Boolean DAG node at each polarity,
 * then remove atoms through an incidence worklist. Each removed atom is
 * visited once, including when its removal exposes another candidate.
 *
 * This is the trivial one-sided case of Fourier-Motzkin elimination (a
 * variable bounded from one side only is projected away with every atom
 * that bounds it; Schrijver, "Theory of Linear and Integer Programming",
 * Wiley 1986), and the model is recovered as in LP postsolve, witnesses
 * replayed in reverse elimination order (Andersen & Andersen, "Presolving
 * in linear programming", Math. Programming 71 (1995)). */
ASTNode eliminateMonotone(STPMgr& manager, const ASTNode& input,
                          SATSolver* solver, LraReconstruction& reconstruction,
                          std::size_t& variables_removed,
                          std::size_t& atoms_removed)
{
  // Lowered UF results are not independent variables: later congruence
  // lemmas can constrain them. Keep the existing unconstrained-pass guard.
  if (manager.getUFContextIfAny() != nullptr)
    return input;
  struct WorkLimit {};
  std::uint64_t visits = 0;
  auto poll = [&]() {
    if ((visits & 255U) == 0)
      manager.checkPreparation(PreparationStage::LraPresolve);
    if (visits >= manager.UserFlags.lra_presolve_monotone_work ||
        ((visits & 255U) == 0 && solver && solver->timeLimitExpired()))
      throw WorkLimit{};
    ++visits;
  };
  try
  {
    struct Atom
    {
      ASTNode node;
      Relation relation;
      std::uint8_t polarity;
      LinearView view;
      bool active = true;
    };
    struct Walk { ASTNode node; std::uint8_t polarity; };
    std::vector<Walk> work{{input, 1}};
    std::unordered_map<std::uint64_t, std::uint8_t> seen;
    std::map<std::uint64_t, ASTNode> atom_nodes;
    std::unordered_set<std::uint64_t> blocked, opaque_seen;
    const auto blockVariables = [&](const ASTNode& root) {
      ASTVec pending{root};
      while (!pending.empty())
      {
        poll();
        const auto node = pending.back();
        pending.pop_back();
        if (!opaque_seen.insert(node.GetNodeNum()).second)
          continue;
        if (realSymbol(node))
          blocked.insert(node.GetNodeNum());
        for (const auto& child : node.GetChildren())
          pending.push_back(child);
      }
    };
    const auto negate = [](std::uint8_t p) -> std::uint8_t {
      return p == 1 ? 2 : p == 2 ? 1 : 3;
    };
    while (!work.empty())
    {
      poll();
      const auto frame = work.back();
      work.pop_back();
      const auto& node = frame.node;
      auto& visited = seen[node.GetNodeNum()];
      if ((visited & frame.polarity) == frame.polarity)
        continue;
      visited = static_cast<std::uint8_t>(visited | frame.polarity);
      Relation relation;
      if (node.Degree() == 2 && relationFor(node.GetKind(), relation) &&
          node[0].isRealTerm() && node[1].isRealTerm())
      {
        atom_nodes.emplace(node.GetNodeNum(), node);
        continue;
      }
      // An opaque context pins all of its Real variables, but need not
      // prevent elimination of independent supported arithmetic elsewhere.
      if (node.GetType() != BOOLEAN_TYPE)
      {
        blockVariables(node);
        continue;
      }
      const auto kind = node.GetKind();
      switch (kind)
      {
        case TRUE: case FALSE: case SYMBOL: break;
        case NOT: case AND: case OR: case IMPLIES: case IFF: case XOR:
        case ITE: case NAND: case NOR: break;
        default:
          blockVariables(node);
          continue;
      }
      for (std::size_t i = 0; i < node.Degree(); ++i)
      {
        poll();
        auto polarity = frame.polarity;
        if (kind == NOT || kind == NAND || kind == NOR ||
            (kind == IMPLIES && i == 0))
          polarity = negate(polarity);
        else if (kind == IFF || kind == XOR || (kind == ITE && i == 0))
          polarity = 3;
        work.push_back({node[i], polarity});
      }
    }
    struct Variable
    {
      ASTNode symbol;
      // 0: unsupported use, 1: increasing, 2: decreasing.
      std::array<std::size_t, 3> counts{};
      std::vector<std::size_t> atoms;
      bool queued = false;
    };
    std::map<std::uint64_t, Variable> variables;
    std::vector<Atom> atoms;
    const auto direction = [](const Atom& atom,
                              const ExactRational& coefficient) -> unsigned {
      if (atom.relation == Relation::Equal || atom.polarity == 3)
        return 0;
      bool positive = atom.relation == Relation::Greater ||
                      atom.relation == Relation::GreaterEqual;
      if (atom.polarity == 2)
        positive = !positive;
      return (coefficient.sign() > 0) == positive ? 1U : 2U;
    };
    for (const auto& entry : atom_nodes)
    {
      poll();
      Relation relation;
      if (!relationFor(entry.second.GetKind(), relation))
        return input;
      Atom atom{entry.second, relation, seen.at(entry.first), {}, true};
      if (!addLinear(atom.view, atom.node[0], ExactRational(std::int64_t{1}), poll) ||
          !addLinear(atom.view, atom.node[1], ExactRational(std::int64_t{-1}), poll))
      {
        // Block the whole atom, including any supported leaves: none of its
        // thresholds can be saved safely for reconstruction after removal.
        blockVariables(atom.node);
        continue;
      }
      const auto index = atoms.size();
      for (const auto& term : atom.view.coefficients)
      {
        poll();
        if (term.second.isZero())
          continue;
        auto& variable = variables[term.first];
        variable.symbol = atom.view.symbols.at(term.first);
        ++variable.counts[direction(atom, term.second)];
        variable.atoms.push_back(index);
      }
      atoms.push_back(std::move(atom));
    }
    const auto eligible = [&](const Variable& v) {
      return v.counts[0] == 0 && ((v.counts[1] != 0) != (v.counts[2] != 0)) &&
             blocked.count(v.symbol.GetNodeNum()) == 0 &&
             !manager.FoundIntroducedSymbolSet(v.symbol);
    };
    std::deque<std::uint64_t> queue;
    for (auto& entry : variables)
      if (eligible(entry.second))
      {
        queue.push_back(entry.first);
        entry.second.queued = true;
      }
    NodeMap truths;
    std::vector<RealModelDefinition> eliminated;
    while (!queue.empty())
    {
      poll();
      const auto id = queue.front();
      queue.pop_front();
      auto& variable = variables.at(id);
      variable.queued = false;
      if (!eligible(variable))
        continue;
      const bool lower = variable.counts[1] != 0;
      ASTVec bounds;
      for (const auto index : variable.atoms)
      {
        poll();
        auto& atom = atoms[index];
        if (!atom.active)
          continue;
        bounds.push_back(solveViewFor(manager, atom.view, id));
        truths.emplace(atom.node.GetNodeNum(), atom.polarity == 1
                                                  ? manager.ASTTrue
                                                  : manager.ASTFalse);
        atom.active = false;
        for (const auto& term : atom.view.coefficients)
        {
          poll();
          if (term.second.isZero())
            continue;
          auto& affected = variables.at(term.first);
          --affected.counts[direction(atom, term.second)];
          if (term.first != id && !affected.queued && eligible(affected))
          {
            affected.queued = true;
            queue.push_back(term.first);
          }
        }
      }
      using Kind = RealModelDefinition::Kind;
      eliminated.emplace_back(variable.symbol, std::move(bounds),
                              lower ? Kind::AboveMaximum : Kind::BelowMinimum);
    }
    if (truths.empty())
      return input;
    const auto removed_atoms = truths.size();
    // A normalized zero coefficient may leave syntactic occurrences behind,
    // e.g. y = x-x after removing x > y. They are independent of x, but a
    // later affine reconstruction would otherwise record a spurious cycle
    // y -> x -> y. Erase these cancelled occurrences from the working formula;
    // the saved witnesses and final original-formula check still value x.
    const auto zero = manager.CreateRealConst("0");
    for (const auto& definition : eliminated)
    {
      poll();
      truths.emplace(definition.symbol.GetNodeNum(), zero);
    }
    Rewriter rewriter(manager, truths);
    const auto result = rewriter.apply(input, poll);
    poll();
    // Commit formula and witnesses together. Any work/deadline refusal above
    // leaves both the input and the caller's reconstruction unchanged.
    std::reverse(eliminated.begin(), eliminated.end());
    reconstruction.definitions.insert(reconstruction.definitions.begin(),
                                      eliminated.begin(), eliminated.end());
    variables_removed += eliminated.size();
    atoms_removed += removed_atoms;
    return result;
  }
  catch (const WorkLimit&)
  {
    return input;
  }
}

/* ---- Stage: unconstrained. ---------------------------------------------

   A Real variable occurring in exactly one atom, with that atom at a pure
   polarity, leaves the atom free: over the reals a nonzero coefficient
   lets x realise either truth of a linear comparison. The atom folds to
   its polarity's truth, and the witness equality x = t that realises it
   is conjoined -- the model stays complete by construction, and the
   equality is exactly the solved shape the Gaussian stage dissolves. A
   mixed-polarity occurrence, a second atom, or a nonlinear shape
   disqualifies the variable. */
ASTNode eliminateUnconstrained(STPMgr& manager, const ASTNode& input,
                               std::size_t& vars_witnessed,
                               bool& proved_unsat)
{
  /* An active UF view fills the query with lowered result scalars that
   * look single-use here but are constrained by the congruence lemmas
   * refinement adds later; witnessing one to an arbitrary value refutes
   * satisfiable queries. */
  if (manager.getUFContextIfAny() != nullptr)
    return input; // Any UF context at all: its lowered scalars are
                  // constrained by congruence later, and the solve-scope
                  // flag is not yet raised when presolve runs.
  ASTVec conjuncts;
  flattenConjuncts(input, conjuncts);
  if (conjuncts.empty())
    return input;

  enum class Polarity : std::uint8_t
  {
    Positive,
    Negative,
    Mixed
  };
  struct AtomUse final
  {
    ASTNode atom;
    Polarity polarity = Polarity::Positive;
    bool sole = true;
  };
  std::unordered_map<std::uint64_t, AtomUse> uses; // by variable node
  std::unordered_map<std::uint64_t, Polarity> atom_polarity;

  struct Walk final
  {
    ASTNode node;
    Polarity polarity;
  };
  std::vector<Walk> work;
  for (const ASTNode& conjunct : conjuncts)
    work.push_back(Walk{conjunct, Polarity::Positive});
  std::unordered_map<std::uint64_t, std::uint8_t> seen; // polarity mask
  const auto mask = [](Polarity p) -> std::uint8_t {
    return p == Polarity::Positive ? 1 : p == Polarity::Negative ? 2 : 3;
  };
  while (!work.empty())
  {
    const Walk frame = work.back();
    work.pop_back();
    const ASTNode& node = frame.node;
    std::uint8_t& visited = seen[node.GetNodeNum()];
    if ((visited & mask(frame.polarity)) == mask(frame.polarity))
      continue;
    visited = static_cast<std::uint8_t>(visited | mask(frame.polarity));
    Relation relation;
    if (node.Degree() == 2 && relationFor(node.GetKind(), relation) &&
        node[0].GetSourceSort().kind() == SourceSort::Kind::Real)
    {
      const auto recorded = atom_polarity.find(node.GetNodeNum());
      if (recorded == atom_polarity.end())
        atom_polarity.emplace(node.GetNodeNum(), frame.polarity);
      else if (recorded->second != frame.polarity)
        recorded->second = Polarity::Mixed;
      LinearView view;
      const ExactRational plus(std::int64_t{1});
      const ExactRational minus(std::int64_t{-1});
      const bool linear = addLinear(view, node[0], plus) &&
                          addLinear(view, node[1], minus);
      // Every variable of the atom is charged with this use; a nonlinear
      // atom charges through a plain symbol walk so nothing escapes.
      if (linear)
      {
        for (const auto& entry : view.coefficients)
        {
          auto use = uses.find(entry.first);
          if (use == uses.end())
            uses.emplace(entry.first, AtomUse{node, frame.polarity, true});
          else if (!(use->second.atom == node))
            use->second.sole = false;
        }
      }
      else
      {
        /* Once per node of the atom, not once per path to it. The walk
         * outside this branch is protected by `seen`; this one was not, and
         * its input is the same hash-consed DAG -- a nonlinear atom over an
         * unrolled conditional shares each level's term between the branches
         * above it, so the untracked walk follows 2^depth paths through a
         * few hundred nodes. What it records is idempotent per node (a
         * symbol is charged unusable however many times it is reached), so
         * visiting each once says exactly what visiting each repeatedly
         * said. */
        std::unordered_set<std::uint64_t> walked;
        std::vector<ASTNode> symbols{node};
        while (!symbols.empty())
        {
          const ASTNode t = symbols.back();
          symbols.pop_back();
          if (!walked.insert(t.GetNodeNum()).second)
            continue;
          if (t.GetKind() == SYMBOL &&
              t.GetSourceSort().kind() == SourceSort::Kind::Real)
          {
            auto use = uses.find(t.GetNodeNum());
            if (use == uses.end())
              uses.emplace(t.GetNodeNum(), AtomUse{ASTNode(), Polarity::Mixed,
                                                   false});
            else
              use->second.sole = false;
          }
          for (const ASTNode& child : t.GetChildren())
            symbols.push_back(child);
        }
      }
      continue;
    }
    if (node.isRealTerm())
      continue;
    const Kind kind = node.GetKind();
    for (std::size_t i = 0; i < node.Degree(); ++i)
    {
      Polarity child = frame.polarity;
      if (kind == NOT)
        child = frame.polarity == Polarity::Positive ? Polarity::Negative
                : frame.polarity == Polarity::Negative ? Polarity::Positive
                                                       : Polarity::Mixed;
      else if (kind == IMPLIES && i == 0)
        child = frame.polarity == Polarity::Positive ? Polarity::Negative
                : frame.polarity == Polarity::Negative ? Polarity::Positive
                                                       : Polarity::Mixed;
      else if (kind == IFF || kind == XOR ||
               (kind == ITE && i == 0) || kind == NAND || kind == NOR)
        child = Polarity::Mixed;
      work.push_back(Walk{node[i], child});
    }
  }

  NodeMap atom_truths;
  ASTVec witnesses;
  std::unordered_set<std::uint64_t> handled_atoms;
  for (const auto& entry : uses)
  {
    const AtomUse& use = entry.second;
    if (!use.sole || use.atom.IsNull())
      continue;
    const auto polarity = atom_polarity.find(use.atom.GetNodeNum());
    if (polarity == atom_polarity.end() ||
        polarity->second == Polarity::Mixed)
      continue;
    if (handled_atoms.count(use.atom.GetNodeNum()) != 0)
      continue;
    Relation relation;
    if (!relationFor(use.atom.GetKind(), relation))
      continue;
    LinearView view;
    const ExactRational plus(std::int64_t{1});
    const ExactRational minus(std::int64_t{-1});
    if (!addLinear(view, use.atom[0], plus) ||
        !addLinear(view, use.atom[1], minus))
      continue;
    const auto coeff = view.coefficients.find(entry.first);
    if (coeff == view.coefficients.end() || coeff->second.isZero())
      continue;
    /* Only a variable the query itself declared may be witnessed. A symbol
     * STP introduced stands for something else -- an uninterpreted
     * function's result, an array read -- and what decides its value is not
     * among the conjuncts this walk can see: the UF lowering states
     * congruence as lemmas it adds during the solve, and marks these symbols
     * protected for exactly that reason, so ordinary preprocessing cannot
     * substitute one away and leave a lemma talking about a value nothing
     * links.
     *
     * Pinning one is unsound rather than merely wasteful. Two applications
     * of a function with equal arguments have equal results, so their result
     * symbols are not independent; witnessing either to make an atom over
     * them false forces a disagreement congruence forbids, and a satisfiable
     * query comes back unsat. */
    const ASTNode& candidate = view.symbols.at(entry.first);
    if (manager.FoundIntroducedSymbolSet(candidate))
      continue;
    const bool make_true = polarity->second == Polarity::Positive;
    // Target value for the polynomial: 0 satisfies the non-strict
    // relations and refutes the strict ones; +-1 covers the rest.
    std::int64_t target = 0;
    switch (relation)
    {
      case Relation::Less: target = make_true ? -1 : 0; break;
      case Relation::LessEqual: target = make_true ? 0 : 1; break;
      case Relation::GreaterEqual: target = make_true ? 0 : -1; break;
      case Relation::Greater: target = make_true ? 1 : 0; break;
      case Relation::Equal:
        if (!make_true)
          target = 1;
        break;
    }
    LinearView adjusted = view;
    adjusted.constant -= ExactRational(target);
    const ASTNode symbol = view.symbols.at(entry.first);
    const ASTNode witness_term =
        solveViewFor(manager, adjusted, entry.first);
    atom_truths.emplace(use.atom.GetNodeNum(),
                        make_true ? manager.ASTTrue : manager.ASTFalse);
    handled_atoms.insert(use.atom.GetNodeNum());
    witnesses.push_back(manager.CreateNode(EQ, symbol, witness_term));
    ++vars_witnessed;
  }
  if (atom_truths.empty())
    return input;

  Rewriter rewriter(manager, atom_truths);
  ASTVec rebuilt;
  rebuilt.reserve(conjuncts.size() + witnesses.size());
  for (const ASTNode& conjunct : conjuncts)
  {
    const ASTNode replacement = rewriter.apply(conjunct);
    if (replacement == manager.ASTFalse)
    {
      proved_unsat = true;
      return manager.ASTFalse;
    }
    if (replacement == manager.ASTTrue)
      continue;
    rebuilt.push_back(replacement);
  }
  for (const ASTNode& witness : witnesses)
    rebuilt.push_back(witness);
  if (rebuilt.empty())
    return manager.ASTTrue;
  if (rebuilt.size() == 1)
    return rebuilt[0];
  return manager.CreateNode(AND, rebuilt);
}

} // namespace

ASTNode presolveForSolve(STPMgr& manager, const ASTNode& input,
                         SATSolver* solver, LraReconstruction* reconstruction,
                         bool highs_enabled)
{
  ASTNode current = input;
  const auto expired = [&]()
  {
    manager.checkPreparation(PreparationStage::LraPresolve);
    if (!solver || !solver->timeLimitExpired())
      return false;
    manager.soft_timeout_expired = true;
    manager.noteBudgetExhausted(*solver);
    return true;
  };
  if (expired())
    return current;
  using Mode = UserDefinedFlags::OptionMode;
  if (reconstruction)
  {
    /* Keep the query as the caller wrote it, always, so that the model
     * commit has something to check against.
     *
     * Everything below rewrites `current`, and the three exact checks that
     * pass judgement on a satisfiable answer -- the core's own, the model
     * verifier's, and the coordinator's re-evaluation of its submitted
     * formula -- all read what comes out of here, not what went in. Without
     * this record the one layer of the answer path outside the verification
     * perimeter would be the layer doing the rewriting, where a wrong
     * rewrite would go unchecked (see eliminateUnconstrained). Recording
     * the input costs a node reference; checking against it costs one
     * evaluation of the original formula, once, on a committed model.
     *
     * `eliminate_definitions` is separate. It selects a transformation, not
     * a check, and the definitions it leaves behind are what
     * `RealModel::reconstruct` replays. Like a replay, it is selected only
     * where the caller allows one. */
    reconstruction->original = input;
    reconstruction->replay_selected =
        reconstruction->replay_allowed &&
        (highs_enabled ||
         manager.UserFlags.lra_model_reconstruction == Mode::ON);
    reconstruction->eliminate_definitions =
        reconstruction->replay_allowed &&
        manager.UserFlags.lra_model_reconstruction == Mode::ON;
  }
  if (highs_enabled)
  {
    current = presolveHighs(manager, current, solver, reconstruction,
                           manager.lra_ast_state->number_budget);
    if (current == manager.ASTTrue || current == manager.ASTFalse || expired())
      return current;
  }
  std::size_t definitions_used = 0;
  std::size_t fixed_variables = 0;
  std::size_t rows_dropped = 0;
  std::size_t facts_propagated = 0;
  std::size_t atoms_folded = 0;
  std::size_t vars_witnessed = 0;
  std::size_t monotone_variables = 0;
  std::size_t monotone_atoms = 0;
  std::uint64_t bounds_nanoseconds = 0;
  std::uint64_t bounds_operations = 0;
  bool proved_unsat = false;
  SubstitutionBudget substitution_budget(manager, solver);
  {
    // One budget scope over every stage, in the one function the manager
    // befriends; the helpers below only consume the active budget. Stage
    // one needs it too since the Gaussian pass works in exact rationals.
    NumberOperationScope operation(manager.lra_ast_state->number_budget);
    bool relu_graph = false;
    if (manager.UserFlags.lra_relu_bounds != Mode::OFF || manager.UserFlags.lra_relu_cases ||
        manager.UserFlags.lra_relu_lp != Mode::OFF ||
        manager.UserFlags.lra_relu_branch)
      current =
          presolveRelus(manager, current, relu_graph, solver, reconstruction);
    if (expired())
      return current;
    const auto operations = [&]() {
      const auto metrics = manager.lra_ast_state->number_budget.metrics();
      return metrics.additions + metrics.subtractions +
             metrics.multiplications + metrics.divisions;
    };
    const unsigned limit = std::max(1U, std::min(8U, manager.UserFlags.lra_presolve_rounds));
    for (unsigned round = 0; round < limit; ++round)
    {
      if (expired())
        return current;
      if (current == manager.ASTTrue || current == manager.ASTFalse)
        break;
      const ASTNode before_round = current;
      const auto before_operations = manager.UserFlags.stats_flag ? operations() : 0;
      // Some helpers assign counters, and tightenRows reads its local count
      // to decide whether anything changed. Never feed them accumulated totals.
      std::size_t definitions = 0, fixed = 0, rows = 0, facts = 0, folded = 0;
      std::size_t witnessed = 0, monotone_vars = 0, removed_atoms = 0;
      // Keep a recognized ReLU graph sparse across every round. Recognition,
      // LP attempts and the final dead-definition pass stay outside this loop.
      if (manager.UserFlags.lra_presolve_subst && !relu_graph)
      {
        current = substituteDefinitions(manager, current, definitions, substitution_budget);
        if (manager.UserFlags.stats_flag && substitution_budget.enabled())
          substitution_budget.report(round + 1);
      }
      if (expired())
        return current;
      if (manager.UserFlags.lra_presolve_propagate && current != manager.ASTFalse)
        current = propagateFacts(manager, current, facts, proved_unsat);
      if (expired())
        return current;
      if (manager.UserFlags.lra_presolve_monotone && reconstruction &&
          !relu_graph && current != manager.ASTFalse && current != manager.ASTTrue)
      {
        if (manager.getUFContextIfAny() == nullptr)
        {
          // Solved equalities retained for model publication can make an
          // otherwise one-sided variable appear pinned. Save dead definitions
          // before analysing directions, even when optional LP replay is off.
          // Each subsequent elimination prepends its dependencies to this same
          // trail. UF results may acquire constraints later and stay protected.
          std::uint64_t visits = 0;
          const auto poll = [&]() {
            if ((visits++ & 255U) == 0 && expired())
              throw PreparationInterrupted(PreparationStage::LraPresolve,
                                           std::chrono::steady_clock::now());
          };
          current = removeDeadRealDefinitions(manager, current, *reconstruction, poll);
        }
        current = eliminateMonotone(manager, current, solver, *reconstruction,
                                    monotone_vars, removed_atoms);
      }
      if (expired())
        return current;
      if (manager.UserFlags.lra_presolve_unconstrained && !relu_graph &&
          current != manager.ASTFalse)
        current = eliminateUnconstrained(manager, current, witnessed, proved_unsat);
      if (expired())
        return current;
      if (manager.UserFlags.lra_presolve_rows && current != manager.ASTFalse)
        current = tightenRows(manager, current, rows, proved_unsat);
      if (expired())
        return current;
      if (manager.UserFlags.lra_presolve_bounds && !proved_unsat &&
          current != manager.ASTFalse)
      {
        const auto before = manager.UserFlags.stats_flag ? operations() : 0;
        const auto start = manager.UserFlags.stats_flag
                               ? std::chrono::steady_clock::now()
                               : std::chrono::steady_clock::time_point{};
        current = boundsPresolve(manager, current, fixed, folded, proved_unsat);
        if (manager.UserFlags.stats_flag)
        {
          bounds_operations += operations() - before;
          bounds_nanoseconds += static_cast<std::uint64_t>(
              std::chrono::duration_cast<std::chrono::nanoseconds>(
                  std::chrono::steady_clock::now() - start).count());
        }
      }
      definitions_used += definitions;
      fixed_variables += fixed;
      rows_dropped += rows;
      facts_propagated += facts;
      atoms_folded += folded;
      vars_witnessed += witnessed;
      monotone_variables += monotone_vars;
      monotone_atoms += removed_atoms;
      if (manager.UserFlags.stats_flag && limit > 1)
        std::cerr << "LRA presolve round: index=" << round + 1
                  << ", changed=" << (current != before_round)
                  << ", definitions=" << definitions << ", fixed=" << fixed
                  << ", rows=" << rows << ", facts=" << facts
                  << ", folded=" << folded << ", witnessed=" << witnessed
                  << ", monotone=" << monotone_vars
                  << ", arithmetic_ops=" << operations() - before_operations << '\n';
      if (current == before_round || proved_unsat)
        break;
    }
  }
  if (expired())
    return current;
  if (reconstruction && reconstruction->eliminate_definitions &&
      current != manager.ASTFalse)
    current = removeDeadRealDefinitions(manager, current, *reconstruction);
  if (manager.UserFlags.stats_flag &&
      (definitions_used != 0 || fixed_variables != 0 || rows_dropped != 0 ||
       facts_propagated != 0 || atoms_folded != 0 || vars_witnessed != 0 ||
       proved_unsat || bounds_nanoseconds != 0 || monotone_variables != 0))
    std::cerr << "LRA presolve: " << definitions_used << " definitions, "
              << fixed_variables << " fixed variables, " << rows_dropped
              << " rows dropped, " << facts_propagated << " facts propagated, "
              << atoms_folded << " atoms folded, " << vars_witnessed
              << " unconstrained witnessed"
              << (proved_unsat ? ", infeasible" : "")
              << ", bounds_ns=" << bounds_nanoseconds
              << ", bounds_ops=" << bounds_operations << std::endl;
  if (manager.UserFlags.stats_flag && manager.UserFlags.lra_presolve_monotone)
    std::cerr << "LRA monotone: variables=" << monotone_variables
              << ", atoms=" << monotone_atoms << '\n';
  return current;
}

} // namespace lra
} // namespace stp

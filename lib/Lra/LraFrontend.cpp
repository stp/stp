#include "LraFrontend.h"

#include "AffineNormalization.h"
#include "ASTRealConst.h"
#include "ImathAllocHooks.h"
#include "LraAtomRegistry.h"
#include "RealModel.h"
#include "stp/STPManager/STPManager.h"

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <map>
#include <optional>
#include <new>
#include <sstream>
#include <utility>

namespace stp {

namespace {

struct ResolvedFrontendSymbol final
{
  ASTNode symbol;
  lra::LraSymbolId id;
};

} // namespace

// Kept opaque even from the installed STPManager header.  A stored ASTNode
// pins the symbol, so an STP node number cannot be recycled beneath a stable
// frontend ID.
class LraFrontendRegistryState final
{
public:
  std::map<std::uint64_t, ResolvedFrontendSymbol> symbols_by_node;
  // The same symbols by frontend ID: the registry asks for the node of
  // every term's symbol as it registers a formula, and a walk of the map
  // above for each made registration quadratic in the symbols.
  std::map<std::uint64_t, ASTNode> symbol_by_id;
  std::uint64_t next_symbol_id = 1;
  std::uint64_t next_predicate_id = 1;
  std::uint64_t next_equality_group_id = 1;
  std::uint64_t generation = 0;

  void swap(LraFrontendRegistryState& other) noexcept
  {
    symbols_by_node.swap(other.symbols_by_node);
    symbol_by_id.swap(other.symbol_by_id);
    std::swap(next_symbol_id, other.next_symbol_id);
    std::swap(next_predicate_id, other.next_predicate_id);
    std::swap(next_equality_group_id, other.next_equality_group_id);
    std::swap(generation, other.generation);
  }
};

LraAstState::~LraAstState()
{
  // The committed model owns ASTNode references and must disappear before
  // registry metadata or the manager's AST ownership tables.
  delete real_model;
  real_model = nullptr;
  // The atom registry may own exact frontend payloads and AST nodes.  Release
  // it before the symbol registry, exact-constant table, and their
  // NumberBudget.  Its concrete state remains private to LraAtomRegistry.cpp.
  lra::destroyLraAtomRegistryState(atom_registry);
  atom_registry = nullptr;
  // Registry payloads can own ASTRealConst references.  Release them while
  // both the exact constant table and its NumberBudget are still alive.
  delete frontend_registry;
  frontend_registry = nullptr;
  // Manager-lifetime references to public Real symbols, released for the same
  // reason and in the same window as the registries above.
  real_symbol_ids.clear();
  real_symbols.clear();

  // Every reference this state owned is gone, so anything still interned in
  // real_constants is a constant a caller still holds an Expr for.  Forgetting
  // to release an Expr is a leak c_interface.h documents and a bit-vector
  // constant survives, because those are owned by the manager's tables and go
  // when the manager does.  A Real constant is refcount-owned and interns
  // itself here, so the same mistake used to leave this set holding raw
  // pointers that nothing would ever free -- and, while assertions reached
  // this directory, took the host process down with it.
  //
  // Free them, which makes the Real path behave like the bit-vector one: a
  // caller who leaks an Expr leaks nothing past vc_Destroy, and a caller who
  // uses one afterwards was already using a dangling handle.
  //
  // The table is moved out first.  Deleting through ASTRealConst::CleanUp
  // would call EraseRealConst and mutate the container being walked; these
  // are deleted directly, whose destructor does not, but taking the table
  // first keeps that from being a trap for a later edit.
  auto orphaned = std::move(real_constants);
  real_constants.clear();
  for (ASTRealConst* orphan : orphaned)
    delete orphan;
}

void STPMgr::DestroyLraAtomRegistry()
{
  if (lra_ast_state == nullptr || lra_ast_state->atom_registry == nullptr)
    return;
  lra::destroyLraAtomRegistryState(lra_ast_state->atom_registry);
  lra_ast_state->atom_registry = nullptr;
  lra_ast_state->assertion_frames.clear();
}


void STPMgr::ResetLraStateForPublicReset()
{
  if (lra_ast_state == nullptr)
    return;

  // A full public reset is a new declaration and identity domain.  Release
  // every solve-independent consumer first, then both persistent registries,
  // and finally the manager-owned references that made old declarations
  // reachable.  AST handles retained by a low-level embedder remain memory
  // safe, but are no longer interned as current public Real declarations.
  InvalidateRealModel();
  DestroyLraAtomRegistry();
  delete lra_ast_state->frontend_registry;
  lra_ast_state->frontend_registry = nullptr;
  lra_ast_state->real_symbol_ids.clear();
  lra_ast_state->real_symbols.clear();
  lra_ast_state->assertion_frames.clear();
  lra_ast_state->number_budget.resetAccounting();
  has_real = false;
}

namespace lra {

namespace {

using WorkingPolynomial = AffinePolynomial;

void incrementSaturating(std::uint64_t& value) noexcept
{
  if (value != std::numeric_limits<std::uint64_t>::max())
    ++value;
}

void advanceGeneration(LraFrontendRegistryState& registry)
{
  if (registry.generation == std::numeric_limits<std::uint64_t>::max())
    throw FrontendFailure(FrontendFailureKind::ResourceLimit,
                          "frontend registry generation space exhausted");
  ++registry.generation;
}

FrontendFailure translateNumberFailure(const NumberFailure& failure)
{
  FrontendFailureKind kind = FrontendFailureKind::InternalError;
  switch (failure.kind())
  {
    case NumberFailureKind::ResourceLimit:
      kind = FrontendFailureKind::ResourceLimit;
      break;
    case NumberFailureKind::AllocationFailure:
      kind = FrontendFailureKind::AllocationFailure;
      break;
    case NumberFailureKind::InvalidText:
    case NumberFailureKind::ZeroDenominator:
    case NumberFailureKind::DivisionByZero:
    case NumberFailureKind::NonIntegerOperand:
    case NumberFailureKind::RangeError:
      kind = FrontendFailureKind::Malformed;
      break;
    case NumberFailureKind::InternalError:
      kind = FrontendFailureKind::InternalError;
      break;
  }
  return FrontendFailure(kind, failure.what());
}

[[noreturn]] void wrongSort(const char* operation, const ASTNode& node)
{
  std::ostringstream out;
  out << operation << " requires Real operands, got "
      << node.GetSourceSort().name();
  throw FrontendFailure(FrontendFailureKind::WrongSort, out.str());
}

LraSymbolId resolveSymbol(LraFrontendRegistryState& registry,
                          const ASTNode& symbol)
{
  const std::uint64_t node_number = symbol.GetNodeNum();
  const auto found = registry.symbols_by_node.find(node_number);
  if (found != registry.symbols_by_node.end())
  {
    if (found->second.symbol != symbol)
      throw FrontendFailure(FrontendFailureKind::InternalError,
                            "frontend symbol node identity was recycled");
    return found->second.id;
  }

  if (registry.next_symbol_id == 0)
    throw FrontendFailure(FrontendFailureKind::ResourceLimit,
                          "frontend Real-symbol ID space exhausted");
  const LraSymbolId id{registry.next_symbol_id++};
  registry.symbols_by_node.emplace(
      node_number, ResolvedFrontendSymbol{symbol, id});
  try
  {
    registry.symbol_by_id.emplace(id.value, symbol);
  }
  catch (...)
  {
    registry.symbols_by_node.erase(node_number);
    throw;
  }
  return id;
}

/* destination += scale * source, in place. A failure part-way leaves the
 * destination half-updated, and that is fine: a working polynomial lives
 * only inside one normalisation, whose failure discards it and takes the
 * whole preregistration back. Copying the destination for a strong
 * guarantee here made a sum of n terms cost n copies of a growing map --
 * quadratic, and a fifth of the frontend on the wide LassoRanker rows. */
void addScaled(WorkingPolynomial& destination,
               const WorkingPolynomial& source,
               const ExactRational& scale, PreparationPoller& poll)
{
  for (const auto& entry : source.coefficients)
  {
    poll();
    ExactRational contribution = entry.second * scale;
    auto found = destination.coefficients.find(entry.first);
    if (found == destination.coefficients.end())
    {
      if (!contribution.isZero())
        destination.coefficients.emplace(entry.first,
                                         std::move(contribution));
    }
    else
    {
      found->second += contribution;
      if (found->second.isZero())
        destination.coefficients.erase(found);
    }
  }
  destination.constant += source.constant * scale;
}

WorkingPolynomial normalizeTerm(const ASTNode& term,
                                LraFrontendRegistryState& registry,
                                FrontendMetrics& metrics,
                                PreparationPoller& poll)
{
  const auto resolve = [&](const ASTNode& symbol) {
    return resolveSymbol(registry, symbol).value;
  };
  const auto visit = [&](const ASTNode&) {
    incrementSaturating(metrics.normalization_nodes);
  };
  return normalizeAffineDag(term, ExactRational(std::int64_t{1}), resolve,
                            visit, poll, {true, false});
}

LinearPolynomial finishPolynomial(WorkingPolynomial working,
                                  FrontendMetrics& metrics,
                                  PreparationPoller& poll)
{
  LinearPolynomial result;
  result.terms.reserve(working.coefficients.size());
  for (auto& entry : working.coefficients)
  {
    poll();
    if (entry.second.isZero())
      continue;
    metrics.maximum_coefficient_bits = std::max(
        metrics.maximum_coefficient_bits,
        std::max(entry.second.numeratorBits(), entry.second.denominatorBits()));
    result.terms.push_back(
        LinearMonomial{LraSymbolId{entry.first}, std::move(entry.second)});
  }
  metrics.maximum_coefficient_bits = std::max(
      metrics.maximum_coefficient_bits,
      std::max(working.constant.numeratorBits(),
               working.constant.denominatorBits()));
  result.constant = std::move(working.constant);
  Frontend::validateCanonical(result);
  return result;
}

FrontendRelation relationForKind(Kind kind)
{
  switch (kind)
  {
    case REAL_LT:
      return FrontendRelation::Less;
    case REAL_LE:
      return FrontendRelation::LessEqual;
    case REAL_GT:
      return FrontendRelation::Greater;
    case REAL_GE:
      return FrontendRelation::GreaterEqual;
    case EQ:
      return FrontendRelation::Equal;
    default:
      throw FrontendFailure(FrontendFailureKind::Malformed,
                            "expected a binary Real comparison");
  }
}

bool evaluateConstant(FrontendRelation relation,
                      const ExactRational& value)
{
  const int sign = value.sign();
  switch (relation)
  {
    case FrontendRelation::Less:
      return sign < 0;
    case FrontendRelation::LessEqual:
      return sign <= 0;
    case FrontendRelation::Greater:
      return sign > 0;
    case FrontendRelation::GreaterEqual:
      return sign >= 0;
    case FrontendRelation::Equal:
      return sign == 0;
  }
  return false;
}

NormalizedPredicate normalizePredicateImpl(
    const ASTNode& predicate,
    LraFrontendRegistryState& registry,
    FrontendMetrics& metrics, PreparationPoller& poll)
{
  const Kind kind = predicate.GetKind();
  const FrontendRelation relation = relationForKind(kind);
  if (predicate.Degree() != 2)
    throw FrontendFailure(FrontendFailureKind::Malformed,
                          "Real comparisons must be binary");
  if (predicate[0].GetSourceSort().kind() != SourceSort::Kind::Real)
    wrongSort("Real comparison", predicate[0]);
  if (predicate[1].GetSourceSort().kind() != SourceSort::Kind::Real)
    wrongSort("Real comparison", predicate[1]);

  WorkingPolynomial left =
      normalizeTerm(predicate[0], registry, metrics, poll);
  const WorkingPolynomial right =
      normalizeTerm(predicate[1], registry, metrics, poll);
  addScaled(left, right, ExactRational(std::int64_t{-1}), poll);
  LinearPolynomial polynomial = finishPolynomial(std::move(left), metrics, poll);

  NormalizedPredicate result;
  result.canonical =
      CanonicalLraPredicate{relation, std::move(polynomial), predicate};
  result.is_constant = result.canonical.lhs_minus_rhs.terms.empty();
  if (result.is_constant)
  {
    result.constant_value = evaluateConstant(
        relation, result.canonical.lhs_minus_rhs.constant);
    incrementSaturating(metrics.constant_predicates);
  }
  return result;
}

CanonicalLraPredicate withRelation(const CanonicalLraPredicate& source,
                                   FrontendRelation relation)
{
  CanonicalLraPredicate result = source;
  result.relation = relation;
  return result;
}

} // namespace

class PreregistrationBuilder final
{
public:
  PreregistrationBuilder(STPMgr& manager,
                         LraFrontendRegistryState& registry,
                         FrontendMetrics& metrics,
                         std::vector<ASTNode>& introduced)
      : manager_(manager), registry_(registry), metrics_(metrics),
        introduced_(introduced),
        poll_(manager.preparation_control, PreparationStage::LraPreregistration)
  {
  }

  // What one node becomes on its own, if it is decided without its children:
  // a Real predicate by its registration, a Boolean application by an opaque
  // atom, a non-Boolean by itself. Null for a Boolean connective, whose
  // result is built from its children's.
  std::optional<ASTNode> transformLeaf(const ASTNode& node)
  {
    poll_();
    if (isOrdinaryRealPredicate(node))
      return ordinary(node);

    if (isRealDistinct(node))
      return distinct(node);

    if (isRealEquality(node))
      return equality(node);

    if (node.GetKind() == NOT && node.Degree() == 1 &&
        isRealEquality(node[0]))
      return disequality(node[0]);

    if (node.GetSourceSort().kind() == SourceSort::Kind::Real ||
        node.isRealTerm())
    {
      throw FrontendFailure(
          FrontendFailureKind::Unsupported,
          "a Real term occurred outside a supported Real predicate");
    }

    if (node.GetSourceSort().kind() != SourceSort::Kind::Bool)
      return node;

    // A Boolean-valued application is one atom, whatever its arguments are
    // made of. Descending into it would meet Real arguments outside any Real
    // predicate and refuse them, but they are not this walk's to interpret:
    // the arguments reach the arithmetic through the congruence constraints
    // the lowering installs, and the application itself is opaque here. It
    // is replaced rather than passed through so that no Real syntax survives
    // the walk; by the time the solve-time coordinator runs, lowering has
    // already retired every application anyway.
    if (node.GetKind() == UF_APPLY)
      return freshOpaque("lra_uf");

    return std::nullopt;
  }

  // Rewrite the Boolean structure, bottom up, over an explicit stack. The
  // formulas this meets are as deep as the programs they were unrolled from
  // -- a bounded-model-checking trace nests one conjunct per step, tens of
  // thousands deep -- and a call frame per level is a stack overflow on
  // exactly the inputs that matter. Results are memoised by node, so a
  // subterm the DAG shares is rewritten once and, where it is an application,
  // gets one opaque atom rather than one per path to it.
  ASTNode transform(const ASTNode& root)
  {
    struct Frame
    {
      ASTNode node;
      size_t next = 0;
      ASTVec rewritten;
      bool changed = false;
    };
    std::vector<Frame> stack;
    // Everything that mints an atom is memoised by node, so a subterm the
    // DAG shares becomes one atom however many paths reach it: an
    // application, and a Real predicate.
    //
    // Predicates used to be registered once per occurrence, on the grounds
    // that the registry hash-conses the row and its components anyway. It
    // does, but only after each occurrence has been given a fresh opaque
    // atom, normalised, and turned into a registration for the registry to
    // collapse. On a bounded-model-checking trace that is most of the work
    // and nearly all of it is thrown away: 4,600 distinct Real predicates
    // in one cs_fib query produced 3,443,036 registrations, of which 19,772
    // components survived. Across the QF_UFLRA family the median is about
    // ten occurrences per distinct predicate.
    //
    // The occurrence list stays in step with what the registry returns:
    // registerFormula still emits one component occurrence per entry, and
    // the coordinator still zips the two by index to alias each atom onto
    // its interned representative. There is simply one entry per distinct
    // predicate rather than per path to it, which is what the alias map
    // wanted in the first place -- it existed to reunite atoms that were
    // only ever distinct because this memo stopped short.
    auto settle = [&](const ASTNode& node) -> std::optional<ASTNode> {
      const auto memo = transformed_.find(node);
      if (memo != transformed_.end())
        return memo->second;
      std::optional<ASTNode> leaf = transformLeaf(node);
      // Only when the walk replaced the node. The pass-through case returns
      // the node itself and has nothing to remember.
      if (leaf && *leaf != node)
        transformed_.emplace(node, *leaf);
      return leaf;
    };
    auto open = [&](const ASTNode& node) {
      Frame frame;
      frame.node = node;
      frame.rewritten.reserve(node.Degree());
      stack.push_back(std::move(frame));
    };

    if (std::optional<ASTNode> done = settle(root))
      return *done;
    open(root);
    ASTNode result;
    while (!stack.empty())
    {
      poll_();
      Frame& frame = stack.back();
      if (frame.next < frame.node.Degree())
      {
        const ASTNode child = frame.node[frame.next++];
        if (child.GetSourceSort().kind() != SourceSort::Kind::Bool)
        {
          if (Frontend::containsRealSyntax(child))
            throw FrontendFailure(FrontendFailureKind::Unsupported,
                                  "unsupported Real syntax crossed a Boolean "
                                  "abstraction boundary");
          frame.rewritten.push_back(child);
          continue;
        }
        if (std::optional<ASTNode> done = settle(child))
        {
          frame.changed = frame.changed || *done != child;
          frame.rewritten.push_back(*done);
          continue;
        }
        open(child);
        continue;
      }
      // Every child is in: this node is decided.
      const ASTNode built =
          frame.changed ? manager_.defaultNodeFactory->CreateNode(
                              frame.node.GetKind(), frame.rewritten)
                        : frame.node;
      transformed_.emplace(frame.node, built);
      const ASTNode finished_node = frame.node;
      stack.pop_back();
      if (stack.empty())
      {
        result = built;
        break;
      }
      Frame& parent = stack.back();
      parent.changed = parent.changed || built != finished_node;
      parent.rewritten.push_back(built);
    }
    return result;
  }

  ASTNode finish(const ASTNode& transformed)
  {
    if (definitions_.empty())
      return transformed;
    ASTVec conjuncts = definitions_;
    conjuncts.push_back(transformed);
    return manager_.defaultNodeFactory->CreateNode(AND, conjuncts);
  }

  std::vector<PredicateRegistration> predicates;
  std::vector<EqualityRegistration> equalities;

private:
  static bool isOrdinaryRealPredicate(const ASTNode& node)
  {
    const Kind kind = node.GetKind();
    return kind == REAL_LT || kind == REAL_LE || kind == REAL_GT ||
           kind == REAL_GE;
  }

  static bool isRealEquality(const ASTNode& node)
  {
    return node.GetKind() == EQ && node.Degree() == 2 &&
           node[0].GetSourceSort().kind() == SourceSort::Kind::Real &&
           node[1].GetSourceSort().kind() == SourceSort::Kind::Real;
  }

  static bool isRealDistinct(const ASTNode& node)
  {
    if (node.GetKind() != DISTINCT || node.Degree() < 2)
      return false;
    for (const ASTNode& operand : node.GetChildren())
      if (operand.GetSourceSort().kind() != SourceSort::Kind::Real)
        return false;
    return true;
  }

  ASTNode freshOpaque(const char* role)
  {
    if (manager_._symbol_count == std::numeric_limits<unsigned int>::max())
      throw FrontendFailure(FrontendFailureKind::ResourceLimit,
                            "internal Boolean-symbol serial space exhausted");
    const ASTNode atom =
        manager_.CreateFreshInternalSourceVariable(SourceSort::boolean(),
                                                   role);
    introduced_.push_back(atom);
    incrementSaturating(metrics_.opaque_atoms);
    return atom;
  }

  /* Replace every Real-sorted ite inside a Real term by a fresh Real symbol,
   * recording what that symbol stands for.
   *
   * A term-level ite is not a linear expression, so the simplex cannot take
   * it. The standard remedy applies: name the value, and say what the name
   * means on each branch -- (c -> t = a) and (not c -> t = b). Both halves
   * are ordinary Real equalities, so they register through exactly the same
   * path as any other equality in the formula and inherit its verification.
   *
   * This is the same transformation STP already performs for bit-vector
   * term-ites; only the sort differs. The condition is rewritten first,
   * because it is an ordinary Boolean formula that may itself contain Real
   * predicates -- min/max chains nest ites inside their own conditions. */
  ASTNode liftRealTermItes(const ASTNode& term)
  {
    poll_();
    /* Once per node, not once per path to it.  The input is a hash-consed
     * DAG, and an unrolled conditional update shares each level's term
     * between both branches of the level above, so a walk with no memo names
     * the same value 2^depth times and states 2^depth pairs of branch
     * equalities for it -- twenty levels of legal QF_LRA in under a kilobyte
     * do not finish.  The sibling Boolean walk in this class learned the
     * same lesson (`transformed_`); this keeps its own map, because the two
     * walks answer different questions about the same nodes -- both are
     * entered at a predicate -- and one's answer is not the other's. */
    const auto memo = lifted_.find(term);
    if (memo != lifted_.end())
      return memo->second;
    const ASTNode lifted = liftRealTermItesUncached(term);
    // Identity results also matter: a shared affine subtree with no ite
    // otherwise gets walked once per path through the input DAG.
    lifted_.emplace(term, lifted);
    return lifted;
  }

  ASTNode liftRealTermItesUncached(const ASTNode& term)
  {
    if (term.GetKind() == ITE && term.Degree() == 3 &&
        term.GetSourceSort().kind() == SourceSort::Kind::Real)
    {
      const ASTNode condition = transform(term[0]);
      const ASTNode on_true = liftRealTermItes(term[1]);
      const ASTNode on_false = liftRealTermItes(term[2]);
      if (manager_._symbol_count == std::numeric_limits<unsigned int>::max())
        throw FrontendFailure(FrontendFailureKind::ResourceLimit,
                              "internal Real-symbol serial space exhausted");
      const ASTNode named = manager_.CreateFreshInternalSourceVariable(
          SourceSort::real(), "lra_ite");
      introduced_.push_back(named);
      NodeFactory& factory = *manager_.defaultNodeFactory;
      const ASTNode true_case = equality(
          factory.CreateNode(EQ, named, on_true));
      const ASTNode false_case = equality(
          factory.CreateNode(EQ, named, on_false));
      definitions_.push_back(factory.CreateNode(
          AND,
          factory.CreateNode(OR, factory.CreateNode(NOT, condition),
                             true_case),
          factory.CreateNode(OR, condition, false_case)));
      incrementSaturating(metrics_.lifted_term_ites);
      return named;
    }
    if (term.Degree() == 0)
      return term;
    ASTVec rewritten;
    rewritten.reserve(term.Degree());
    bool changed = false;
    for (const ASTNode& child : term.GetChildren())
    {
      const ASTNode replacement = liftRealTermItes(child);
      changed = changed || replacement != child;
      rewritten.push_back(replacement);
    }
    if (!changed)
      return term;
    return manager_.defaultNodeFactory->CreateNode(term.GetKind(), rewritten);
  }

  ASTNode registerCanonical(CanonicalLraPredicate payload,
                            std::uint64_t equality_group,
                            EqualityComponent component)
  {
    if (payload.lhs_minus_rhs.terms.empty())
    {
      incrementSaturating(metrics_.constant_predicates);
      return evaluateConstant(payload.relation,
                              payload.lhs_minus_rhs.constant)
                 ? manager_.ASTTrue
                 : manager_.ASTFalse;
    }
    if (registry_.next_predicate_id == 0)
      throw FrontendFailure(FrontendFailureKind::ResourceLimit,
                            "frontend predicate ID space exhausted");
    const ASTNode atom = freshOpaque("lra_pred");
    predicates.push_back(PredicateRegistration{
        registry_.next_predicate_id++, atom, std::move(payload),
        equality_group, component});
    incrementSaturating(metrics_.predicates);
    return atom;
  }

  ASTNode ordinary(const ASTNode& source)
  {
    const ASTNode lifted = liftRealTermItes(source);
    NormalizedPredicate normalized =
        normalizePredicateImpl(lifted, registry_, metrics_, poll_);
    if (normalized.is_constant)
      return normalized.constant_value ? manager_.ASTTrue : manager_.ASTFalse;
    return registerCanonical(std::move(normalized.canonical), 0,
                             EqualityComponent::None);
  }

  ASTNode equality(const ASTNode& source)
  {
    const ASTNode lifted = liftRealTermItes(source);
    NormalizedPredicate normalized =
        normalizePredicateImpl(lifted, registry_, metrics_, poll_);
    if (normalized.is_constant)
      return normalized.constant_value ? manager_.ASTTrue : manager_.ASTFalse;

    if (registry_.next_equality_group_id == 0)
      throw FrontendFailure(FrontendFailureKind::ResourceLimit,
                            "frontend equality-group ID space exhausted");
    const std::uint64_t group = registry_.next_equality_group_id++;
    const ASTNode less_equal = registerCanonical(
        withRelation(normalized.canonical, FrontendRelation::LessEqual),
        group, EqualityComponent::LessEqual);
    const ASTNode greater_equal = registerCanonical(
        withRelation(normalized.canonical, FrontendRelation::GreaterEqual),
        group, EqualityComponent::GreaterEqual);
    const ASTNode equality_atom = freshOpaque("lra_eq");
    const ASTNode both = manager_.defaultNodeFactory->CreateNode(
        AND, less_equal, greater_equal);
    definitions_.push_back(manager_.defaultNodeFactory->CreateNode(
        IFF, equality_atom, both));
    equalities.push_back(EqualityRegistration{
        group, source, equality_atom, less_equal, greater_equal});
    incrementSaturating(metrics_.equality_groups);
    return equality_atom;
  }

  ASTNode disequality(const ASTNode& equality_source)
  {
    const ASTNode lifted = liftRealTermItes(equality_source);
    NormalizedPredicate normalized =
        normalizePredicateImpl(lifted, registry_, metrics_, poll_);
    if (normalized.is_constant)
      return normalized.constant_value ? manager_.ASTFalse : manager_.ASTTrue;

    const ASTNode less = registerCanonical(
        withRelation(normalized.canonical, FrontendRelation::Less), 0,
        EqualityComponent::DisequalityLess);
    const ASTNode greater = registerCanonical(
        withRelation(normalized.canonical, FrontendRelation::Greater), 0,
        EqualityComponent::DisequalityGreater);
    return manager_.defaultNodeFactory->CreateNode(OR, less, greater);
  }

  ASTNode distinct(const ASTNode& source)
  {
    ASTVec pairwise;
    pairwise.reserve(source.Degree() * (source.Degree() - 1) / 2);
    for (std::size_t i = 0; i < source.Degree(); ++i)
      for (std::size_t j = i + 1; j < source.Degree(); ++j)
      {
        poll_();
        const ASTNode equality_source =
            manager_.defaultNodeFactory->CreateNode(EQ, source[i], source[j]);
        // Two concrete operands let the node factory settle the equality
        // outright, so what comes back is the Boolean answer rather than an
        // EQ to normalize. Answer this pair directly: equal operands make the
        // disequality false, and settled-unequal ones make it true.
        if (equality_source == manager_.ASTTrue)
          pairwise.push_back(manager_.ASTFalse);
        else if (equality_source == manager_.ASTFalse)
          pairwise.push_back(manager_.ASTTrue);
        else
          pairwise.push_back(disequality(equality_source));
      }
    return pairwise.size() == 1
               ? pairwise.front()
               : manager_.defaultNodeFactory->CreateNode(AND, pairwise);
  }

  STPMgr& manager_;
  LraFrontendRegistryState& registry_;
  FrontendMetrics& metrics_;
  std::vector<ASTNode>& introduced_;
  PreparationPoller poll_;
  ASTVec definitions_;
  std::map<ASTNode, ASTNode, ExprLess> transformed_;
  std::map<ASTNode, ASTNode, ExprLess> lifted_;
};

namespace {

void appendU64(std::uint64_t value, std::uint64_t& hash)
{
  for (unsigned shift = 0; shift != 64; shift += 8)
  {
    hash ^= static_cast<unsigned char>((value >> shift) & UINT64_C(0xff));
    hash *= UINT64_C(1099511628211);
  }
}

void appendText(const std::string& value, std::uint64_t& hash)
{
  appendU64(static_cast<std::uint64_t>(value.size()), hash);
  for (char character : value)
  {
    const unsigned char byte = static_cast<unsigned char>(character);
    hash ^= byte;
    hash *= UINT64_C(1099511628211);
  }
}

void requireCanonicalInvariant(const ExactRational& value,
                               const char* malformed_detail)
{
  // ExactRational's frozen diagnostic predicate is noexcept and therefore
  // reports an allocator/resource failure as `false`.  Preserve that public
  // contract while recovering the native failure category here, where the
  // frontend must distinguish corrupt input from a resumable failed attempt.
  stp_lra_imath_clear_failure();
  if (value.invariantHolds())
    return;
  if (stp_lra_imath_last_failure() != STP_LRA_IMATH_FAILURE_NONE)
    throw detail::BudgetAccess::allocationFailure(
        "validateCanonical", "exact invariant audit could not allocate");
  throw FrontendFailure(FrontendFailureKind::Malformed, malformed_detail);
}

} // namespace

FrontendFailure::FrontendFailure(FrontendFailureKind kind, std::string detail)
    : std::runtime_error(std::move(detail)), kind_(kind)
{
}

Frontend::Frontend(STPMgr& manager) : manager_(manager)
{
  if (manager_.lra_ast_state == nullptr)
    manager_.lra_ast_state = new LraAstState();
  if (manager_.lra_ast_state->frontend_registry == nullptr)
    manager_.lra_ast_state->frontend_registry =
        new LraFrontendRegistryState();
}

LinearPolynomial Frontend::normalize(const ASTNode& term)
{
  try
  {
    // Standalone normalization also serves candidate verification. Only the
    // preregistration builder enables preparation cancellation.
    PreparationPoller poll(nullptr, PreparationStage::LraPreregistration);
    if (term.GetSTPMgr() != &manager_)
      throw FrontendFailure(
          FrontendFailureKind::Malformed,
          "linear normalization received a node owned by another manager");
    NumberOperationScope operation(manager_.lra_ast_state->number_budget);
    LraFrontendRegistryState staged =
        *manager_.lra_ast_state->frontend_registry;
    FrontendMetrics metrics;
    metrics.normalization_calls = 1;
    LinearPolynomial result = finishPolynomial(
        normalizeTerm(term, staged, metrics, poll), metrics, poll);
    advanceGeneration(staged);
    manager_.lra_ast_state->frontend_registry->swap(staged);
    return result;
  }
  catch (const NumberFailure& failure)
  {
    throw translateNumberFailure(failure);
  }
  catch (const std::bad_alloc&)
  {
    throw FrontendFailure(FrontendFailureKind::AllocationFailure,
                          "allocation failure during linear normalization");
  }
}

NormalizedPredicate Frontend::normalizePredicate(const ASTNode& predicate)
{
  try
  {
    PreparationPoller poll(nullptr, PreparationStage::LraPreregistration);
    if (predicate.GetSTPMgr() != &manager_)
      throw FrontendFailure(
          FrontendFailureKind::Malformed,
          "predicate normalization received a node owned by another manager");
    NumberOperationScope operation(manager_.lra_ast_state->number_budget);
    LraFrontendRegistryState staged =
        *manager_.lra_ast_state->frontend_registry;
    FrontendMetrics metrics;
    metrics.normalization_calls = 1;
    NormalizedPredicate result =
        normalizePredicateImpl(predicate, staged, metrics, poll);
    advanceGeneration(staged);
    manager_.lra_ast_state->frontend_registry->swap(staged);
    return result;
  }
  catch (const NumberFailure& failure)
  {
    throw translateNumberFailure(failure);
  }
  catch (const std::bad_alloc&)
  {
    throw FrontendFailure(FrontendFailureKind::AllocationFailure,
                          "allocation failure during predicate normalization");
  }
}

PreregisteredFormula Frontend::preregister(const ASTNode& formula)
{
  try
  {
    if (formula.GetSTPMgr() != &manager_)
      throw FrontendFailure(
          FrontendFailureKind::Malformed,
          "preregistration received a node owned by another manager");
    if (formula.GetSourceSort().kind() != SourceSort::Kind::Bool)
      throw FrontendFailure(FrontendFailureKind::WrongSort,
                            "preregistration requires a Boolean formula");

    NumberOperationScope operation(manager_.lra_ast_state->number_budget);
    LraFrontendRegistryState& registry =
        *manager_.lra_ast_state->frontend_registry;

    /* Preregistration only adds: symbols with IDs from next_symbol_id up,
     * predicate and equality-group serials, and opaque atoms -- ordinary
     * manager-owned AST symbols, so the existing Boolean pipeline can
     * consume them -- which enter the manager's set of introduced symbols.
     * A failure part-way takes exactly those back: the atoms the builder
     * recorded leave the set, the symbols at or past the ID mark leave the
     * registry, and the serials go back, which makes a retry byte-for-byte
     * deterministic. Working on a copy of the registry and of the introduced
     * set instead, and swapping them in on success, gave the same guarantee
     * at the cost of copying every symbol ever introduced on every
     * assertion: on an 18 MB LassoRanker file, three minutes before the
     * search. */
    const std::uint64_t symbol_id_before = registry.next_symbol_id;
    const std::uint64_t predicate_id_before = registry.next_predicate_id;
    const std::uint64_t group_id_before = registry.next_equality_group_id;
    const std::uint64_t generation_before = registry.generation;
    const unsigned int symbol_count_before = manager_._symbol_count;
    std::vector<ASTNode> introduced;
    try
    {
      FrontendMetrics metrics;
      metrics.normalization_calls = 1;
      PreregistrationBuilder builder(manager_, registry, metrics, introduced);
      const ASTNode transformed = builder.transform(formula);
      const ASTNode completed = builder.finish(transformed);
      if (containsRealSyntax(completed))
        throw FrontendFailure(
            FrontendFailureKind::InternalError,
            "Real syntax remained after opaque preregistration");

      manager_.checkPreparation(PreparationStage::LraPreregistration);
      advanceGeneration(registry);
      const std::uint64_t generation = registry.generation;
      metrics.symbols = registry.symbols_by_node.size();

      return PreregisteredFormula{completed, std::move(builder.predicates),
                                  std::move(builder.equalities), generation,
                                  metrics};
    }
    catch (...)
    {
      for (const ASTNode& atom : introduced)
        manager_.Introduced_SymbolsSet.erase(atom);
      manager_._symbol_count = symbol_count_before;
      for (auto it = registry.symbol_by_id.lower_bound(symbol_id_before);
           it != registry.symbol_by_id.end();)
      {
        registry.symbols_by_node.erase(it->second.GetNodeNum());
        it = registry.symbol_by_id.erase(it);
      }
      registry.next_symbol_id = symbol_id_before;
      registry.next_predicate_id = predicate_id_before;
      registry.next_equality_group_id = group_id_before;
      registry.generation = generation_before;
      throw;
    }
  }
  catch (const NumberFailure& failure)
  {
    throw translateNumberFailure(failure);
  }
  catch (const std::bad_alloc&)
  {
    throw FrontendFailure(FrontendFailureKind::AllocationFailure,
                          "allocation failure during LRA preregistration");
  }
}

std::string Frontend::exportPolynomial(
    const LinearPolynomial& polynomial) const
{
  NumberOperationScope operation(manager_.lra_ast_state->number_budget);
  validateCanonical(polynomial);
  std::ostringstream out;
  bool first = true;
  for (const LinearMonomial& term : polynomial.terms)
  {
    if (!first)
      out << ',';
    first = false;
    out << 's' << term.symbol.value << ':'
        << term.coefficient.canonicalFraction();
  }
  out << ";c:" << polynomial.constant.canonicalFraction();
  return out.str();
}

std::string Frontend::exportCoefficientVector(
    const LinearPolynomial& polynomial) const
{
  NumberOperationScope operation(manager_.lra_ast_state->number_budget);
  validateCanonical(polynomial);
  std::ostringstream out;
  bool first = true;
  for (const LinearMonomial& term : polynomial.terms)
  {
    if (!first)
      out << ',';
    first = false;
    out << 's' << term.symbol.value << ':'
        << term.coefficient.canonicalFraction();
  }
  return out.str();
}

std::string Frontend::exportPredicate(
    const CanonicalLraPredicate& predicate) const
{
  static const char* const relations[] = {"<", "<=", ">", ">=", "="};
  return std::string(relations[static_cast<unsigned>(predicate.relation)]) +
         ":" + exportPolynomial(predicate.lhs_minus_rhs);
}

std::uint64_t Frontend::stableHash(
    const LinearPolynomial& polynomial) const
{
  NumberOperationScope operation(manager_.lra_ast_state->number_budget);
  validateCanonical(polynomial);
  std::uint64_t hash = UINT64_C(14695981039346656037);
  appendU64(static_cast<std::uint64_t>(polynomial.terms.size()), hash);
  for (const LinearMonomial& term : polynomial.terms)
  {
    appendU64(term.symbol.value, hash);
    appendText(term.coefficient.numeratorDecimal(), hash);
    appendText(term.coefficient.denominatorDecimal(), hash);
  }
  appendText(polynomial.constant.numeratorDecimal(), hash);
  appendText(polynomial.constant.denominatorDecimal(), hash);
  return hash;
}

ASTNode Frontend::symbolNode(LraSymbolId symbol) const
{
  if (symbol.value == 0)
    throw FrontendFailure(FrontendFailureKind::Malformed,
                          "frontend symbol ID zero is reserved");
  const LraFrontendRegistryState& registry =
      *manager_.lra_ast_state->frontend_registry;
  const auto found = registry.symbol_by_id.find(symbol.value);
  if (found == registry.symbol_by_id.end())
    throw FrontendFailure(FrontendFailureKind::Malformed,
                          "unknown or stale frontend Real-symbol ID");
  return found->second;
}

bool Frontend::ownsNode(const ASTNode& node) const noexcept
{
  return !node.IsNull() && node.GetSTPMgr() == &manager_;
}

void Frontend::configureNumberLimits(NumberLimits limits)
{
  LraFrontendRegistryState& registry =
      *manager_.lra_ast_state->frontend_registry;
  if (!manager_.lra_ast_state->real_constants.empty() ||
      !registry.symbols_by_node.empty() || registry.generation != 0)
    throw FrontendFailure(
        FrontendFailureKind::InternalError,
        "exact frontend number limits must be configured before Real values");
  NumberBudget replacement(limits);
  manager_.lra_ast_state->number_budget = std::move(replacement);
}

NumberLimits Frontend::numberLimits() const noexcept
{
  return manager_.lra_ast_state->number_budget.limits();
}

NumberMetrics Frontend::numberMetrics() const noexcept
{
  return manager_.lra_ast_state->number_budget.metrics();
}

void Frontend::resetNumberAccounting() noexcept
{
  manager_.lra_ast_state->number_budget.resetAccounting();
}

bool Frontend::numberStopped() const noexcept
{
  return manager_.lra_ast_state->number_budget.stopped();
}

std::uint64_t Frontend::registryGeneration() const noexcept
{
  return manager_.lra_ast_state->frontend_registry->generation;
}

bool Frontend::containsRealSyntax(const ASTNode& formula)
{
  if (formula.IsNull())
    return false;
  ASTVec pending(1, formula);
  ASTNodeSet seen;
  while (!pending.empty())
  {
    const ASTNode current = pending.back();
    pending.pop_back();
    if (!seen.insert(current).second)
      continue;
    if (current.isRealTerm() || current.GetKind() == REAL_LT ||
        current.GetKind() == REAL_LE || current.GetKind() == REAL_GT ||
        current.GetKind() == REAL_GE ||
        (current.GetKind() == EQ && current.Degree() == 2 &&
         (current[0].GetSourceSort().kind() == SourceSort::Kind::Real ||
          current[1].GetSourceSort().kind() == SourceSort::Kind::Real)))
      return true;
    for (const ASTNode& child : current.GetChildren())
      pending.push_back(child);
  }
  return false;
}

void Frontend::validateCanonical(const LinearPolynomial& polynomial)
{
  std::uint64_t previous = 0;
  for (const LinearMonomial& term : polynomial.terms)
  {
    if (term.symbol.value == 0 || term.symbol.value <= previous)
      throw FrontendFailure(
          FrontendFailureKind::Malformed,
          "canonical polynomial symbols must be positive and strictly sorted");
    if (term.coefficient.isZero())
      throw FrontendFailure(
          FrontendFailureKind::Malformed,
          "canonical polynomial coefficients must be exact and nonzero");
    requireCanonicalInvariant(
        term.coefficient,
        "canonical polynomial coefficients must be exact and nonzero");
    previous = term.symbol.value;
  }
  requireCanonicalInvariant(polynomial.constant,
                            "canonical polynomial constant is invalid");
}

} // namespace lra
} // namespace stp

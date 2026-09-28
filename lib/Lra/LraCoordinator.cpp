#include "Lra/ASTRealConst.h"
#include "LraCoordinator.h"
#include "LraBudgetRefusal.h"
#include "LraModelIndex.h"

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/ToSATBase.h"

#include <iterator>
#include <map>
#include <algorithm>
#include <iostream>
#include <limits>
#include <set>
#include <stdexcept>
#include <utility>

namespace stp
{
namespace lra
{
namespace
{

// A context that is not ready has already told the two apart: it separates a
// budget it ran out of from a state that is wrong. Throwing a bare
// runtime_error here collapsed that back into one untyped thing, and the top
// of the solver -- which is where the difference turns into either "no
// answer" or "a bug in STP" -- had nothing left to read it from.
[[noreturn]] void rethrowContextFailure(const LraSolveContext& context,
                                        const char* fallback)
{
  context.rethrowPreparationInterruption();
  const std::string detail =
      context.failureDetail().empty() ? std::string(fallback)
                                      : context.failureDetail();
  throw SolveContextFailure(
      context.status() == SolveContextStatus::ResourceLimit
          ? SolveContextFailureKind::ResourceLimit
          : SolveContextFailureKind::Invalid,
      detail);
}
}
}
}

namespace stp::lra {

// Defined beside the counterexample implementation.  Keeping this narrow
// bridge here avoids pulling the entire legacy counterexample header (and its
// unrelated warning surface) into the warning-fatal private LRA target.
ASTNode evaluateAgainstCounterexample(
    AbsRefine_CounterExample& counterexample, const ASTNode& formula);

namespace {

void increment(std::uint64_t& value) noexcept
{
  if (value != std::numeric_limits<std::uint64_t>::max())
    ++value;
}

void printNumberProfile(std::ostream& out, const NumberMetrics& metrics)
{
  struct NamedSite
  {
    const char* name;
    stp_lra_imath_allocation_site site;
  };
  const NamedSite sites[] = {
      {"unattributed", STP_LRA_IMATH_ALLOCATION_UNATTRIBUTED},
      {"construct", STP_LRA_IMATH_ALLOCATION_CONSTRUCT},
      {"parse", STP_LRA_IMATH_ALLOCATION_PARSE},
      {"materialize", STP_LRA_IMATH_ALLOCATION_MATERIALIZE},
      {"canonicalize", STP_LRA_IMATH_ALLOCATION_CANONICALIZE},
      {"add", STP_LRA_IMATH_ALLOCATION_ADD},
      {"subtract", STP_LRA_IMATH_ALLOCATION_SUBTRACT},
      {"multiply", STP_LRA_IMATH_ALLOCATION_MULTIPLY},
      {"divide", STP_LRA_IMATH_ALLOCATION_DIVIDE},
  };
  out << "{\"allocation_calls\":" << metrics.allocation_calls
      << ",\"allocated_bytes\":" << metrics.allocated_bytes
      << ",\"native_materializations\":" << metrics.native_materializations
      << ",\"native_demotions\":" << metrics.native_demotions
      << ",\"big_operations\":" << metrics.big_operations
      << ",\"native_additions\":" << metrics.native_additions
      << ",\"native_subtractions\":" << metrics.native_subtractions
      << ",\"native_multiplications\":" << metrics.native_multiplications
      << ",\"native_divisions\":" << metrics.native_divisions
      << ",\"allocation_sites\":{";
  bool first = true;
  for (const NamedSite& named : sites)
  {
    if (!first)
      out << ',';
    first = false;
    const NumberMetrics::AllocationSite& site =
        metrics.allocation_sites[static_cast<std::size_t>(named.site)];
    out << '\"' << named.name << "\":{\"calls\":" << site.calls
        << ",\"bytes\":" << site.bytes << '}';
  }
  out << "}}";
}


bool isRealEquality(const ASTNode& node)
{
  return node.GetKind() == EQ && node.Degree() == 2 &&
         node[0].GetSourceSort().kind() == SourceSort::Kind::Real &&
         node[1].GetSourceSort().kind() == SourceSort::Kind::Real;
}

bool isRealComparison(const ASTNode& node)
{
  return node.GetKind() == REAL_LT || node.GetKind() == REAL_LE ||
         node.GetKind() == REAL_GT || node.GetKind() == REAL_GE ||
         isRealEquality(node);
}

bool relationValue(int comparison, FrontendRelation relation)
{
  switch (relation)
  {
    case FrontendRelation::Less: return comparison < 0;
    case FrontendRelation::LessEqual: return comparison <= 0;
    case FrontendRelation::Greater: return comparison > 0;
    case FrontendRelation::GreaterEqual: return comparison >= 0;
    case FrontendRelation::Equal: return comparison == 0;
  }
  throw std::runtime_error("invalid frontend Real relation");
}

} // namespace

// AUTO asks the query rather than the option: separating coincident values
// only pays where something reads the model by grouping values, and the
// lazy congruence round is the only such reader.
//
// The spread symbols are exactly that signal, and the coordinator is handed
// them already: they are the arguments of uninterpreted applications, the
// values the congruence round groups by. A query with none has nothing that
// a coincidence could mislead. Asking the UF layer directly would say the
// same thing and would make the arithmetic depend on it.
bool LraCoordinator::separateModelValuesEnabled() const
{
  using Mode = UserDefinedFlags::OptionMode;
  const Mode mode = manager_.UserFlags.lra_separate_model_values;
  if (mode != Mode::AUTO)
    return mode == Mode::ON;
  return !spread_symbols_.empty();
}

bool LraCoordinator::decisionPolarityEnabled() const
{
  return manager_.UserFlags.lra_decision_polarity &&
         manager_.UserFlags.lra_theory_propagation &&
         solver_.supportsTheoryPropagator() && solver_.supportsDecisionPolarity();
}

LraCoordinator::LraCoordinator(STPMgr& manager, SATSolver& solver,
                               const ASTNode& submitted_formula,
                               const std::vector<ASTNode>& spread_symbols)
    : manager_(manager), solver_(solver),
      submitted_formula_(submitted_formula), frontend_(manager),
      registry_(manager)
{
  spread_symbols_ = spread_symbols;
  manager_.InvalidateRealModel();
  try
  {
    if (submitted_formula_.IsNull() || !frontend_.ownsNode(submitted_formula_) ||
        submitted_formula_.GetSourceSort().kind() != SourceSort::Kind::Bool)
      throw std::runtime_error(
          "LRA coordinator requires one manager-owned Boolean formula");

    if (manager_.UserFlags.lra_decision_polarity &&
        manager_.UserFlags.lra_decision_polarity_explicit)
    {
      if (!manager_.UserFlags.lra_theory_propagation)
        throw std::runtime_error(
            "--lra-decision-polarity requires --lra-theory-propagation=1");
      if (!solver_.supportsDecisionPolarity())
        throw std::runtime_error(
            "--lra-decision-polarity requires CaDiCaL built with "
            "cmake/deps-utils/cadical-decision-polarity.patch");
    }

    const auto& controls = manager_.UserFlags;
    if (controls.lra_extension_mode > 3 || controls.lra_row_order > 3)
      throw std::runtime_error("invalid LRA experimental control");
    if ((controls.lra_extension_mode || controls.lra_row_order ||
         controls.lra_extension_restart_float_basis || controls.lra_extension_restart_sat) &&
        (controls.lra_incremental_session || controls.lra_persistent_state))
      throw std::runtime_error("LRA extension controls require batch solves");
    if (controls.lra_extension_restart_sat && !solver_.supportsSearchReset())
      throw std::runtime_error("LRA SAT search reset requires CaDiCaL with factoring disabled");

    frame_ = registry_.pushAssertionFrame();
    frame_live_ = true;
    const auto preregistration_start = std::chrono::steady_clock::now();
    preregistered_ = frontend_.preregister(submitted_formula_);
    registered_ = registry_.registerFormula(preregistered_, frame_);
    addElapsed(metrics_.preregistration_nanoseconds,
               preregistration_start);
    if (registered_.boolean_formula.IsNull() ||
        Frontend::containsRealSyntax(registered_.boolean_formula))
      throw std::runtime_error(
          "LRA preregistration did not produce a pure Boolean formula");
    base_submitted_ = submitted_formula_;
    base_registered_ = registered_.boolean_formula;

    // The complete Boolean formula is activated as a solve-local assumption
    // at the final CNF boundary.  Consequently a verified no-good can be
    // inserted after the candidate-producing assumption has been released,
    // even when the no-good refutes the whole abstraction.  The next call to
    // assumed solver call then proves global UNSAT.  This is required for
    // common backends whose strict addClause reports a root conflict when a
    // clause is inserted against permanent assertion units.
    solve_activation_ = manager_.CreateFreshInternalSourceVariable(
        SourceSort::boolean(), "lra_solve_activation");

    PreparationPoller poll(manager_.preparation_control, PreparationStage::LraCore);

    // Registry hash-consing can replace a newly preregistered component atom
    // with the stable representative retained by an older public assertion
    // frame. Bind the atoms that actually occur in the canonical Boolean
    // formula and in this solve frame's checked snapshot.
    const LraRegistrySnapshot solve_snapshot =
        registry_.frameSnapshot(frame_, manager_.preparation_control);
    if (registered_.component_occurrences.size() !=
        preregistered_.predicates.size())
      throw std::runtime_error(
          "registry component occurrence coverage is incomplete");
    // Components by id, once: a scan of the snapshot per predicate was
    // quadratic, and on a LassoRanker file the cost of the whole solve.
    std::map<LraComponentId, const RegistryComponent*> component_by_id;
    for (const RegistryComponent& component : solve_snapshot.components)
    {
      poll();
      component_by_id.emplace(component.id, &component);
    }
    for (std::size_t i = 0; i < preregistered_.predicates.size(); ++i)
    {
      poll();
      const auto found =
          component_by_id.find(registered_.component_occurrences[i]);
      if (found == component_by_id.end() ||
          !source_atom_aliases_
               .emplace(preregistered_.predicates[i].opaque_atom,
                        found->second->opaque_atom)
               .second)
        throw std::runtime_error(
            "registry lost an LRA component occurrence alias");
    }
    opaque_atoms_.reserve(solve_snapshot.components.size() +
                          solve_snapshot.equalities.size());
    // opaque_atom_set_ outlives this loop: extendInternal appends to the
    // list and needs the same duplicate check across extensions that this
    // does within construction.
    opaque_atom_set_.clear();
    for (const RegistryComponent& component : solve_snapshot.components)
    {
      poll();
      if (!opaque_atom_set_.insert(component.opaque_atom).second)
        throw std::runtime_error("duplicate LRA component representative");
      else
        opaque_atoms_.push_back(component.opaque_atom);
    }
    for (const RegistryEqualityGroup& equality : solve_snapshot.equalities)
    {
      poll();
      if (!opaque_atom_set_.insert(equality.equality_atom).second)
        throw std::runtime_error("duplicate LRA equality opaque atom");
      else
        opaque_atoms_.push_back(equality.equality_atom);
    }

    const auto context_start = std::chrono::steady_clock::now();
    context_ = std::make_unique<LraSolveContext>(
        registry_, solver_, frontend_.numberLimits(), frame_,
        std::numeric_limits<std::uint64_t>::max(), nullptr,
        manager_.UserFlags.lra_row_order);
    increment(metrics_.core_rebuilds);
    /* The context verifies by default so that anything building one directly
     * keeps the check; the solver follows the flag, which is off unless the
     * caller asks for it. */
    context_->setConflictVerification(
        manager_.UserFlags.lra_verify_conflicts);
    context_->setEarlyConflictDetection(manager_.UserFlags.lra_early_conflicts);
    context_->setSoi(manager_.UserFlags.lra_soi);
    context_->setFloatDormantRows(manager_.UserFlags.lra_float_dormant_rows,
                                  manager_.UserFlags.lra_float_dormant_min_cells);
    context_->setFloatPromotionBudget(manager_.UserFlags.lra_float_promotion_budget);
    context_->setSeparateModelValues(separateModelValuesEnabled());
    context_->setDenseRecovery(manager_.UserFlags.lra_dense_recovery);
    context_->setFloatDriver(manager_.UserFlags.lra_float_driver &&
                             !manager_.UserFlags.lra_force_exact_driver);
    context_->setFloatRerouteBudget(manager_.UserFlags.lra_float_reroute);
    context_->setFloatRerouteFloor(manager_.UserFlags.lra_float_reroute_floor);
    context_->setConflictRecovery(manager_.UserFlags.lra_conflict_recovery);
    if (!context_->ready())
      rethrowContextFailure(*context_, "exact LRA context creation failed");
    adapter_ = std::make_unique<LraCandidateAdapter>(*context_, solver_);
    adapter_->setDecisionPolarity(decisionPolarityEnabled());
    if (!context_->ready())
      rethrowContextFailure(*context_, "exact LRA adapter creation failed");
    addElapsed(metrics_.context_rebuild_nanoseconds, context_start);
    metrics_.solve_epoch = context_->solveEpoch();
  }
  catch (...)
  {
    adapter_.reset();
    context_.reset();
    if (frame_live_)
    {
      try
      {
        registry_.popAssertionFrame(frame_);
      }
      catch (...)
      {
      }
      frame_live_ = false;
    }
    throw;
  }
}

LraCoordinator::~LraCoordinator() noexcept
{
  if (manager_.UserFlags.stats_flag)
  {
    try
    {
      printMetrics(std::cerr);
    }
    catch (...)
    {
      // Metrics are diagnostic and can never alter the semantic result.
    }
  }
  if (propagating_)
  {
    adapter_->endTheoryPropagation();
    solver_.disconnectTheoryPropagator();
    propagating_ = false;
  }
  adapter_.reset();
  context_.reset();
  opaque_bindings_.clear();
  if (frame_live_)
  {
    try
    {
      registry_.popAssertionFrame(frame_);
    }
    catch (...)
    {
      // A destructor cannot publish a result or recover a stale registry.
      manager_.InvalidateRealModel();
    }
    frame_live_ = false;
  }
}

bool LraCoordinator::gaveUp() const noexcept
{
  return context_ != nullptr &&
         context_->status() == SolveContextStatus::ResourceLimit;
}

bool LraCoordinator::ready() const noexcept
{
  const bool base_ready = !preparation_stop_ && failure_detail_.empty() &&
                          context_ != nullptr && adapter_ != nullptr &&
                          context_->ready();
  return base_ready;
}

std::uint64_t LraCoordinator::solveEpoch() const noexcept
{
  return context_ == nullptr ? 0 : context_->solve_epoch_;
}

std::uint64_t LraCoordinator::candidateSerial() const noexcept
{
  return context_ == nullptr ? 0 : context_->current_candidate_serial_;
}

void LraCoordinator::addElapsed(
    std::uint64_t& destination,
    std::chrono::steady_clock::time_point start) noexcept
{
  const auto elapsed = std::chrono::duration_cast<std::chrono::nanoseconds>(
                           std::chrono::steady_clock::now() - start)
                           .count();
  if (elapsed <= 0)
    return;
  const std::uint64_t amount = static_cast<std::uint64_t>(elapsed);
  destination = amount > std::numeric_limits<std::uint64_t>::max() - destination
                    ? std::numeric_limits<std::uint64_t>::max()
                    : destination + amount;
}

void LraCoordinator::failClosed(std::string detail) noexcept
{
  if (failure_detail_.empty())
    failure_detail_ = std::move(detail);
  manager_.InvalidateRealModel();
  legacy_refinement_pending_ = false;
  if (context_ != nullptr)
    context_->invalidate(failure_detail_);
}

void LraCoordinator::discardStagedModel(StagedDiscardReason reason) noexcept
{
  if (context_ == nullptr || !context_->staged_model_)
    return;
  context_->staged_model_.reset();
  increment(metrics_.staged_models_discarded);
  switch (reason)
  {
    case StagedDiscardReason::ArrayConflict:
      increment(metrics_.discarded_for_array);
      break;
    case StagedDiscardReason::OrdinaryRefinement:
      increment(metrics_.discarded_for_ordinary);
      break;
    case StagedDiscardReason::LegacyArrayReadRefinement:
      increment(metrics_.discarded_for_legacy);
      break;
    case StagedDiscardReason::SolverCall:
    case StagedDiscardReason::StopOrError:
      break;
  }
}

namespace
{

// Clauses for a small Boolean formula, into a solver that has already been
// running. Everything the formula names is either a scalar the first encoding
// gave variables to -- looked up in the symbol map -- or an opaque LRA atom
// that has none yet, which takes a fresh variable and is entered in that map
// for the context to bind. The connectives are Tseitin-encoded, one fresh
// variable per gate. Anything else is refused, and the caller starts over.
class LemmaClauseEncoder final
{
public:
  LemmaClauseEncoder(SATSolver& solver, ToSATBase::ASTNodeToSATVar& map,
                     const PreparationControl* preparation)
      : solver_(solver), map_(map),
        poll_(preparation, PreparationStage::RefinementEncoding)
  {
  }

  bool ok() const noexcept { return ok_; }
  void checkPreparation() const { poll_.check(); }

  static SATSolver::Lit neg(SATSolver::Lit literal)
  {
    return SATSolver::mkLit(SATSolver::var(literal), !SATSolver::sign(literal));
  }

  SATSolver::Lit encode(const ASTNode& node)
  {
    poll_();
    const auto memo = memo_.find(node);
    if (memo != memo_.end())
      return memo->second;
    SATSolver::Lit out = SATSolver::mkLit(0, false);
    const Kind kind = node.GetKind();
    switch (kind)
    {
      case TRUE:
        out = constantTrue();
        break;
      case FALSE:
        out = neg(constantTrue());
        break;
      case SYMBOL:
        out = symbolLiteral(node);
        break;
      case NOT:
        out = neg(encode(node[0]));
        break;
      case AND:
      case OR:
      {
        std::vector<SATSolver::Lit> inputs;
        for (size_t i = 0; i < node.Degree(); ++i)
          inputs.push_back(encode(node[i]));
        out = gate(kind == AND, inputs);
        break;
      }
      case XOR:
      case IFF:
      {
        if (node.Degree() != 2)
        {
          ok_ = false;
          break;
        }
        const SATSolver::Lit a = encode(node[0]);
        const SATSolver::Lit b = encode(node[1]);
        out = kind == XOR ? exclusive(a, b) : neg(exclusive(a, b));
        break;
      }
      case IMPLIES:
      {
        std::vector<SATSolver::Lit> inputs;
        inputs.push_back(neg(encode(node[0])));
        inputs.push_back(encode(node[1]));
        out = gate(false, inputs);
        break;
      }
      case ITE:
      {
        const SATSolver::Lit c = encode(node[0]);
        const SATSolver::Lit t = encode(node[1]);
        const SATSolver::Lit e = encode(node[2]);
        std::vector<SATSolver::Lit> whenTrue;
        whenTrue.push_back(neg(c));
        whenTrue.push_back(t);
        std::vector<SATSolver::Lit> whenFalse;
        whenFalse.push_back(c);
        whenFalse.push_back(e);
        std::vector<SATSolver::Lit> both;
        both.push_back(gate(false, whenTrue));
        both.push_back(gate(false, whenFalse));
        out = gate(true, both);
        break;
      }
      case EQ:
        out = bitEquality(node[0], node[1]);
        break;
      default:
        ok_ = false;
        break;
    }
    memo_.emplace(node, out);
    return out;
  }

  void unitUnder(SATSolver::Lit guard, SATSolver::Lit literal)
  {
    add({neg(guard), literal});
  }

private:
  SATSolver::Lit fresh()
  {
    poll_();
    const unsigned variable = solver_.newVar();
    solver_.setFrozen(variable);
    return SATSolver::mkLit(variable, false);
  }

  void add(std::initializer_list<SATSolver::Lit> literals)
  {
    poll_();
    SATSolver::vec_literals clause;
    for (SATSolver::Lit literal : literals)
      clause.push(literal);
    solver_.addClause(clause);
  }

  SATSolver::Lit constantTrue()
  {
    if (!have_true_)
    {
      true_ = fresh();
      add({true_});
      have_true_ = true;
    }
    return true_;
  }

  // A Boolean scalar's variable, or a fresh one for an atom that has none.
  SATSolver::Lit symbolLiteral(const ASTNode& symbol)
  {
    const auto found = map_.find(symbol);
    if (found != map_.end())
    {
      if (found->second.size() != 1 ||
          found->second[0] == ~static_cast<unsigned>(0) ||
          !solver_.validVariable(found->second[0]))
      {
        ok_ = false;
        return SATSolver::mkLit(0, false);
      }
      return SATSolver::mkLit(found->second[0], false);
    }
    if (symbol.GetType() != BOOLEAN_TYPE)
    {
      ok_ = false;
      return SATSolver::mkLit(0, false);
    }
    const SATSolver::Lit literal = fresh();
    map_[symbol] = std::vector<unsigned>{SATSolver::var(literal)};
    return literal;
  }

  // z <-> AND(inputs), or z <-> OR(inputs).
  SATSolver::Lit gate(bool conjunction, const std::vector<SATSolver::Lit>& in)
  {
    const SATSolver::Lit z = fresh();
    SATSolver::vec_literals wide;
    wide.push(conjunction ? z : neg(z));
    for (SATSolver::Lit literal : in)
    {
      add({conjunction ? neg(z) : z, conjunction ? literal : neg(literal)});
      wide.push(conjunction ? neg(literal) : literal);
    }
    solver_.addClause(wide);
    return z;
  }

  // z <-> (a xor b).
  SATSolver::Lit exclusive(SATSolver::Lit a, SATSolver::Lit b)
  {
    const SATSolver::Lit z = fresh();
    add({neg(z), a, b});
    add({neg(z), neg(a), neg(b)});
    add({z, neg(a), b});
    add({z, a, neg(b)});
    return z;
  }

  // z <-> (every bit of a equals the same bit of b), for two scalars whose
  // bits the first encoding gave variables to.
  SATSolver::Lit bitEquality(const ASTNode& a, const ASTNode& b)
  {
    const auto left = map_.find(a);
    const auto right = map_.find(b);
    if (a.GetKind() != SYMBOL || b.GetKind() != SYMBOL ||
        left == map_.end() || right == map_.end() ||
        left->second.size() != right->second.size() || left->second.empty())
    {
      ok_ = false;
      return SATSolver::mkLit(0, false);
    }
    std::vector<SATSolver::Lit> bits;
    for (size_t i = 0; i < left->second.size(); ++i)
    {
      const unsigned x = left->second[i];
      const unsigned y = right->second[i];
      if (x == ~static_cast<unsigned>(0) || y == ~static_cast<unsigned>(0) ||
          !solver_.validVariable(x) || !solver_.validVariable(y))
      {
        ok_ = false;
        return SATSolver::mkLit(0, false);
      }
      bits.push_back(neg(exclusive(SATSolver::mkLit(x, false),
                                   SATSolver::mkLit(y, false))));
    }
    return gate(true, bits);
  }

  SATSolver& solver_;
  ToSATBase::ASTNodeToSATVar& map_;
  PreparationPoller poll_;
  std::map<ASTNode, SATSolver::Lit, ExprLess> memo_;
  SATSolver::Lit true_ = SATSolver::mkLit(0, false);
  bool have_true_ = false;
  bool ok_ = true;
};

} // namespace

void LraCoordinator::rebuildCoreAndContext()
{
  const auto context_start = std::chrono::steady_clock::now();
  adapter_.reset();
  const auto& controls = manager_.UserFlags;
  const bool reuse = controls.lra_extension_mode == 1 ||
                     controls.lra_extension_mode == 3 ||
                     (controls.lra_extension_mode == 0 &&
                      controls.lra_persistent_state);
  if (reuse)
  {
    if (!context_->extendFromRegistry())
      rethrowContextFailure(*context_, "persistent LRA extension failed");
    increment(metrics_.context_reuses);
  }
  else
  {
    const auto solve = context_->metrics();
    metrics_.retired_exact_pivots += context_->coreStatistics().engine_pivots;
    metrics_.retired_float_checks += solve.float_checks;
    metrics_.retired_float_pivots += solve.float_pivots;
    metrics_.retired_float_check_nanoseconds += solve.float_check_nanoseconds;
    metrics_.retired_float_sync_nanoseconds += solve.float_sync_nanoseconds;
    context_.reset();
    context_ = std::make_unique<LraSolveContext>(
        registry_, solver_, frontend_.numberLimits(), frame_,
        std::numeric_limits<std::uint64_t>::max(), nullptr,
        controls.lra_row_order);
    increment(metrics_.core_rebuilds);
    context_->setConflictVerification(manager_.UserFlags.lra_verify_conflicts);
    context_->setEarlyConflictDetection(manager_.UserFlags.lra_early_conflicts);
    context_->setSoi(manager_.UserFlags.lra_soi);
    context_->setFloatDormantRows(manager_.UserFlags.lra_float_dormant_rows,
                                  manager_.UserFlags.lra_float_dormant_min_cells);
    context_->setFloatPromotionBudget(manager_.UserFlags.lra_float_promotion_budget);
    context_->setSeparateModelValues(separateModelValuesEnabled());
    context_->setDenseRecovery(manager_.UserFlags.lra_dense_recovery);
    context_->setFloatDriver(manager_.UserFlags.lra_float_driver &&
                             !manager_.UserFlags.lra_force_exact_driver);
    context_->setFloatRerouteBudget(manager_.UserFlags.lra_float_reroute);
    context_->setFloatRerouteFloor(manager_.UserFlags.lra_float_reroute_floor);
    context_->setConflictRecovery(manager_.UserFlags.lra_conflict_recovery);
  }
  if (!context_->ready())
    rethrowContextFailure(*context_, "exact LRA context rebuild failed");
  if (controls.lra_extension_mode == 3 || controls.lra_extension_restart_float_basis)
  {
    const bool basis_only = controls.lra_extension_mode != 3;
    if (!context_->restartArithmeticState(basis_only))
      rethrowContextFailure(*context_, "arithmetic search reset failed");
    increment(basis_only ? metrics_.float_basis_resets : metrics_.arithmetic_state_resets);
  }
  adapter_ = std::make_unique<LraCandidateAdapter>(*context_, solver_);
  adapter_->setDecisionPolarity(decisionPolarityEnabled());
  if (!context_->ready())
    rethrowContextFailure(*context_, "exact LRA adapter rebuild failed");
  addElapsed(metrics_.context_rebuild_nanoseconds, context_start);
  metrics_.solve_epoch = context_->solveEpoch();
  bindings_ready_ = false;
  // Every row keeps its clauses in the solver; re-stating the ordering
  // axioms alongside is harmless.
  ordering_axioms_emitted_ = false;
}

ExtensionOutcome LraCoordinator::extendWithFormula(const ASTNode& formula,
                                                   ToSATBase& tosat) noexcept
{
  return extendInternal(formula, tosat, nullptr);
}

ExtensionOutcome LraCoordinator::extendFrame(const ASTNode& formula,
                                             ToSATBase& tosat,
                                             const ASTNode& activation) noexcept
{
  if (activation.IsNull() || activation.GetKind() != SYMBOL ||
      activation.GetSourceSort().kind() != SourceSort::Kind::Bool)
    return ExtensionOutcome::Declined;
  return extendInternal(formula, tosat, &activation);
}

bool LraCoordinator::retractFrame(const ASTNode& activation) noexcept
{
  try
  {
    // A frame that grew across checks was encoded by repeated extendFrame
    // calls under one activation, so several SessionFrames can share it.
    // Retract them all: deactivating only the first would leave the rest
    // live, and liveActivations() would then assume an activation the
    // permanent unit below forces false -- an immediate spurious conflict.
    SATSolver::Lit literal{};
    bool found = false;
    bool any_live = false;
    for (SessionFrame& frame : frames_)
    {
      if (!(frame.activation == activation))
        continue;
      if (!found)
        literal = frame.literal;
      found = true;
      if (frame.live)
      {
        frame.live = false;
        any_live = true;
      }
    }
    if (!found)
      return false;
    if (!any_live)
      return true;
    if (propagating_)
    {
      adapter_->endTheoryPropagation();
      solver_.disconnectTheoryPropagator();
      propagating_ = false;
    }
    SATSolver::vec_literals unit;
    unit.push(SATSolver::mkLit(SATSolver::var(literal),
                               !SATSolver::sign(literal)));
    if (!solver_.addClause(unit) && !solver_.okay())
      return false;
    manager_.InvalidateRealModel();
    rebuildLiveFormulas();
    // Retired atoms remain registered. Public pops may change the global
    // registry identity, but do not change this session's owned rows.
    if (manager_.UserFlags.lra_persistent_state)
    {
      context_->clearSemanticState();
      if (!defer_rebuild_ && !context_->refreshRegistryIdentity())
        return false;
    }
    else if (defer_rebuild_)
      rebuild_pending_ = true;
    else
      rebuildCoreAndContext();
    return true;
  }
  catch (...)
  {
    return false;
  }
}

void LraCoordinator::beginExtensionBatch() noexcept
{
  defer_rebuild_ = true;
  rebuild_pending_ = false;
}

bool LraCoordinator::endExtensionBatch() noexcept
{
  defer_rebuild_ = false;
  if (!rebuild_pending_)
    return !manager_.UserFlags.lra_persistent_state ||
           context_->refreshRegistryIdentity();
  rebuild_pending_ = false;
  try
  {
    rebuildCoreAndContext();
    return true;
  }
  catch (const PreparationInterrupted& stopped)
  {
    preparation_stop_ = stopped;
    manager_.InvalidateRealModel();
    return false;
  }
  catch (const std::exception& failure)
  {
    failClosed(failure.what());
    return false;
  }
  catch (...)
  {
    failClosed("deferred LRA core rebuild failed");
    return false;
  }
}

ASTVec LraCoordinator::liveActivations() const
{
  ASTVec live{solve_activation_};
  for (const SessionFrame& frame : frames_)
    if (frame.live)
      live.push_back(frame.activation);
  return live;
}

void LraCoordinator::rebuildLiveFormulas()
{
  ASTVec submitted{base_submitted_};
  ASTVec registered{base_registered_};
  for (const SessionFrame& frame : frames_)
  {
    if (!frame.live)
      continue;
    submitted.push_back(frame.submitted);
    registered.push_back(frame.registered);
  }
  submitted.insert(submitted.end(), permanent_submitted_.begin(),
                   permanent_submitted_.end());
  registered.insert(registered.end(), permanent_registered_.begin(),
                    permanent_registered_.end());
  submitted_formula_ =
      submitted.size() == 1 ? submitted[0] : manager_.CreateNode(AND, submitted);
  registered_.boolean_formula = registered.size() == 1
                                    ? registered[0]
                                    : manager_.CreateNode(AND, registered);
}

ExtensionOutcome LraCoordinator::extendInternal(
    const ASTNode& formula, ToSATBase& tosat,
    const ASTNode* frame_activation) noexcept
{
  /* Everything that can be answered without touching this coordinator, so
   * that a decline really is one. Past this point the propagator comes out
   * of the solver, the committed model is dropped and the registry grows,
   * and a caller told to start over would find none of the three. The sort
   * and ownership tests used to sit inside the work below and throw, which
   * failed a well-formed refusal closed. */
  if (!ready() || formula.IsNull() || !frontend_.ownsNode(formula) ||
      formula.GetSourceSort().kind() != SourceSort::Kind::Bool)
    return ExtensionOutcome::Declined;
  try
  {
    // The propagator owns the adapter this rebuilds. Take it out of the
    // solver for the duration of the rebuild, and put it back before this
    // returns: disconnecting releases the observed variables, and a solve
    // run in between could eliminate one, after which the backend refuses to
    // observe it again. Reconnected in the same breath, nothing has moved.
    const bool was_propagating = propagating_;
    if (propagating_)
    {
      // CaDiCaL can deliver assignments while removing observed variables.
      // Retire the arithmetic trail first, so those teardown notifications
      // cannot reassert bounds into the accepted candidate or its conflict.
      adapter_->endTheoryPropagation();
      solver_.disconnectTheoryPropagator();
      propagating_ = false;
    }
    manager_.InvalidateRealModel();

    const auto preregistration_start = std::chrono::steady_clock::now();
    const PreregisteredFormula preregistered = frontend_.preregister(formula);
    const RegisteredLraFormula registered =
        registry_.registerFormula(preregistered, frame_);
    addElapsed(metrics_.preregistration_nanoseconds, preregistration_start);
    if (registered.boolean_formula.IsNull() ||
        Frontend::containsRealSyntax(registered.boolean_formula))
      throw std::runtime_error(
          "LRA extension did not produce a pure Boolean formula");

    // The same alias bookkeeping as construction, for the new predicates.
    //
    // This used to snapshot the whole frame and index every component in it
    // to answer a question about the handful the new formula produced, and
    // then rebuild the atom list from that snapshot. Both are O(frame), the
    // frame grows with every lemma, and a refinement round adds one lemma,
    // so a query that took fifteen rounds paid for fifteen copies of an
    // ever-larger frame. Everything else in this function was already an
    // append; these are now too.
    if (registered.component_occurrences.size() !=
        preregistered.predicates.size())
      throw std::runtime_error(
          "registry component occurrence coverage is incomplete");
    for (std::size_t i = 0; i < preregistered.predicates.size(); ++i)
    {
      const ASTNode interned = registry_.componentOpaqueAtom(
          registered.component_occurrences[i], frame_);
      if (interned.IsNull())
        throw std::runtime_error(
            "registry lost an LRA component occurrence alias");
      source_atom_aliases_.emplace(preregistered.predicates[i].opaque_atom,
                                   interned);
    }

    // Append what this formula added. opaque_atom_set_ carries the same
    // duplicate check the rebuild did with a local set, across extensions
    // rather than within one, so an atom the registry hands back twice --
    // which is what interning a component onto an older representative
    // looks like from here -- is dropped rather than listed twice.
    //
    // The bindings are still discarded: the context that follows binds every
    // atom afresh, and a binding names a SAT variable of the solve that is
    // being rebuilt. Appending to the atom list is safe because the list is
    // the input to that rebind, not its output.
    opaque_bindings_.clear();
    for (const LraComponentId id : registered.component_occurrences)
    {
      const ASTNode atom = registry_.componentOpaqueAtom(id, frame_);
      if (atom.IsNull())
        throw std::runtime_error("registry lost an LRA component atom");
      if (opaque_atom_set_.insert(atom).second)
        opaque_atoms_.push_back(atom);
    }
    for (const LraEqualityGroupId id : registered.equality_groups)
    {
      const ASTNode atom = registry_.equalityOpaqueAtom(id, frame_);
      if (atom.IsNull())
        throw std::runtime_error("registry lost an LRA equality atom");
      if (opaque_atom_set_.insert(atom).second)
        opaque_atoms_.push_back(atom);
    }

    // What the solve now stands on: a frame's part can be retracted, a
    // permanent extension's cannot.
    if (frame_activation == nullptr)
    {
      permanent_submitted_.push_back(formula);
      permanent_registered_.push_back(registered.boolean_formula);
    }
    {
      NumberOperationScope operation(manager_.lra_ast_state->number_budget);
      preregistered_.predicates.insert(
          preregistered_.predicates.end(),
          std::make_move_iterator(preregistered.predicates.begin()),
          std::make_move_iterator(preregistered.predicates.end()));
      preregistered_.equalities.insert(
          preregistered_.equalities.end(),
          std::make_move_iterator(preregistered.equalities.begin()),
          std::make_move_iterator(preregistered.equalities.end()));
    }
    registered_.component_occurrences.insert(
        registered_.component_occurrences.end(),
        registered.component_occurrences.begin(),
        registered.component_occurrences.end());
    registered_.equality_groups.insert(registered_.equality_groups.end(),
                                       registered.equality_groups.begin(),
                                       registered.equality_groups.end());
    if (frame_activation == nullptr)
      rebuildLiveFormulas();

    // Extend or rebuild arithmetic over the enlarged registry. The SAT
    // solver stays; old and new atoms are bound after encoding the lemma.
    // The encoding below reads only the ToSAT map, so a batch may defer this.
    if (defer_rebuild_)
      rebuild_pending_ = true;
    else
      rebuildCoreAndContext();

    ToSATBase::ASTNodeToSATVar& map = tosat.SATVar_to_SymbolIndexMap();
    QueryPhaseScope encoding_time(manager_.query_timing, QueryPhase::EncodingOther);
    LemmaClauseEncoder encoder(solver_, map, manager_.preparation_control);
    SATSolver::Lit guard;
    if (frame_activation == nullptr)
    {
      const auto activation = map.find(solve_activation_);
      if (activation == map.end() || activation->second.size() != 1 ||
          !solver_.validVariable(activation->second[0]))
        throw std::runtime_error("LRA extension found no activation variable");
      guard = SATSolver::mkLit(activation->second[0], false);
    }
    else
    {
      guard = encoder.encode(*frame_activation);
      if (!encoder.ok())
        throw std::runtime_error("LRA frame activation could not be encoded");
    }
    const SATSolver::Lit root = encoder.encode(registered.boolean_formula);
    if (!encoder.ok())
      throw std::runtime_error(
          "LRA extension formula holds something the clause encoder does "
          "not cover");
    encoder.unitUnder(guard, root);
    encoder.checkPreparation();
    encoding_time.finish();
    // A prior assumption solve may have returned UNSAT. Adding the new
    // guarded clause releases that result (not a permanent inconsistency).
    if (!solver_.okay())
      throw std::runtime_error("SAT solver rejected the guarded LRA extension");
    if (frame_activation != nullptr)
    {
      frames_.push_back(SessionFrame{*frame_activation, guard, formula,
                                     registered.boolean_formula, true});
      rebuildLiveFormulas();
    }
    increment(metrics_.extensions);
    if (frame_activation == nullptr && manager_.UserFlags.lra_extension_restart_sat)
    {
      const auto reset_start = std::chrono::steady_clock::now();
      if (!solver_.resetSearch())
        throw std::runtime_error("SAT backend declined search reset");
      increment(metrics_.sat_search_resets);
      addElapsed(metrics_.sat_search_reset_nanoseconds, reset_start);
    }
    if (was_propagating && !defer_rebuild_)
    {
      // The map is complete now -- the atoms the solver already held and
      // the ones the encoder just gave variables to -- so the rebuilt
      // context can bind them at once and the propagator resume without a
      // full-lazy solve in between.
      if (!bindOpaqueAtoms(tosat))
        throw std::runtime_error("LRA extension could not bind its atoms");
      std::vector<uint32_t> observed;
      if (!adapter_->beginTheoryPropagation(observed))
        throw std::runtime_error("theory propagation setup failed after extension");
      if (!solver_.connectTheoryPropagator(adapter_.get(), observed))
      {
        adapter_->endTheoryPropagation();
        throw std::runtime_error("backend refused the theory propagator after extension");
      }
      propagating_ = true;
    }
    return ExtensionOutcome::Extended;
  }
  catch (const PreparationInterrupted& stopped)
  {
    preparation_stop_ = stopped;
    manager_.InvalidateRealModel();
    return ExtensionOutcome::Interrupted;
  }
  catch (const std::exception& failure)
  {
    failClosed(failure.what());
    /* Four layers do exact arithmetic on the way in and each refuses in its
     * own currency; none of those refusals is a fault of STP's. Tell them
     * apart here, where the exception is still in hand. */
    return gaveUpOnABudget(failure) ? ExtensionOutcome::ResourceLimit
                                    : ExtensionOutcome::Failed;
  }
  catch (...)
  {
    failClosed("unexpected LRA extension failure");
    return ExtensionOutcome::Failed;
  }
}

bool LraCoordinator::beforeSolverCall() noexcept
{
  if (!ready())
    return false;
  if (legacy_refinement_pending_)
  {
    failClosed("SAT re-solve attempted before legacy refinement encoding");
    return false;
  }
  if (context_->staged_model_)
    discardStagedModel(StagedDiscardReason::SolverCall);
  manager_.InvalidateRealModel();
  if (!context_->beforeSolverCall())
  {
    failClosed(context_->failureDetail());
    return false;
  }
  if (context_->current_candidate_serial_ != 0)
    increment(metrics_.sat_resolves);
  return prepareTheorySearch();
}

bool LraCoordinator::afterCnf(ToSATBase& tosat) noexcept
{
  if (!ready())
    return false;
  bool const first_binding = !bindings_ready_;
  if (!bindOpaqueAtoms(tosat) || !prepareTheorySearch())
    return false;
  if (first_binding && propagating_ && context_->current_candidate_serial_ == 0)
    increment(metrics_.first_search_connections);
  return true;
}

bool LraCoordinator::prepareTheorySearch() noexcept
{
  try
  {
    /* Take the theory's seat inside the search, if the backend has one to
     * offer. Same timing as the ordering axioms and for the same reason: the
     * atoms are only bound to SAT variables once a CNF exists, and connecting
     * a propagator is only legal between solves. afterCnf supplies this window
     * for the first search when the first-search experiment is enabled. */
    if (manager_.UserFlags.lra_theory_propagation && !propagating_ &&
        solver_.supportsTheoryPropagator())
    {
      /* Before the first solve as well as the later ones: a backend that
       * must keep its variables observable has to know before it first
       * simplifies. */
      solver_.expectTheoryPropagator();
    }
    if (manager_.UserFlags.lra_theory_propagation && bindings_ready_ &&
        !propagating_ && solver_.supportsTheoryPropagator())
    {
      std::vector<uint32_t> observed;
      if (!adapter_->beginTheoryPropagation(observed))
      {
        failClosed("theory propagation setup failed");
        return false;
      }
      if (!solver_.connectTheoryPropagator(adapter_.get(), observed))
      {
        adapter_->endTheoryPropagation();
        failClosed("backend refused the theory propagator");
        return false;
      }
      propagating_ = true;
    }
    /* State the per-row bound ordering to the SAT solver, once, as plain
     * clauses.  This has to happen between solves: the atoms are only bound to
     * SAT variables once the CNF exists, and adding a clause while a
     * backend is in its satisfied state invalidates the model the candidate
     * reader is about to consume. The after-CNF hook can also emit them
     * before the first search.
     *
     * They are entailed by the theory, so they cannot change a verdict; they
     * only stop the full-lazy loop from handing over candidates that differ
     * solely in atoms the theory already implies. */
    if (bindings_ready_ && !ordering_axioms_emitted_)
    {
      if (manager_.UserFlags.lra_persistent_state)
      {
        // Frame guards control assertions, not the meaning of an opaque
        // equality. Keep E <-> (LE && GE) after a frame is retired, so its
        // still-observed atoms cannot disagree in subsequent models.
        for (auto const& equality : context_->registry_snapshot_.equalities)
        {
          if (!context_->equalityBound(equality.id) ||
              !context_->componentBound(equality.less_equal_component) ||
              !context_->componentBound(equality.greater_equal_component))
            continue;
          auto e = context_->equalityBinding(equality.id);
          auto le = context_->componentBinding(equality.less_equal_component);
          auto ge = context_->componentBinding(equality.greater_equal_component);
          auto neg = [](SATSolver::Lit lit) { lit.x ^= 1U; return lit; };
          auto addDefinition = [&](std::initializer_list<SATSolver::Lit> literals) {
            SATSolver::vec_literals clause;
            for (auto lit : literals)
              clause.push(lit);
            if (!solver_.addClause(clause))
            {
              failClosed("SAT solver rejected a persistent equality definition");
              return false;
            }
            increment(metrics_.persistent_equality_clauses);
            return true;
          };
          if (!addDefinition({neg(e), le}) || !addDefinition({neg(e), ge}) ||
              !addDefinition({e, neg(le), neg(ge)}))
            return false;
        }
      }
      const AdapterResult axioms = adapter_->emitBoundOrderingAxioms();
      if (axioms.outcome != AdapterOutcome::ClauseInserted)
      {
        failClosed(axioms.detail.empty() ? "bound ordering axiom emission failed"
                                         : axioms.detail);
        return false;
      }
      ordering_axioms_emitted_ = true;
    }
    return true;
  }
  catch (std::exception const& failure)
  {
    failClosed(failure.what());
    return false;
  }
  catch (...)
  {
    failClosed("unexpected theory search setup failure");
    return false;
  }
}


bool LraCoordinator::bindOpaqueAtoms(ToSATBase& tosat) noexcept
{
  try
  {
    if (bindings_ready_)
      return context_->bindingsReady();
    const ToSATBase::ASTNodeToSATVar& map =
        tosat.SATVar_to_SymbolIndexMap();
    std::vector<LraSatBinding> bindings;
    // Atoms the Boolean formula never mentions, declared to the context so
    // its coverage check stays exact rather than merely permissive.
    std::vector<ASTNode> omitted;
    bindings.reserve(opaque_atoms_.size());
    std::map<ASTNode, SATSolver::Lit, ExprLess> copied;
    for (const ASTNode& atom : opaque_atoms_)
    {
      const auto found = map.find(atom);
      if (found == map.end())
      {
        /* No SAT variable at all, which is not a mapping fault: this map is
         * what the CNF conversion records for the nodes it converted, so an
         * absent atom is one the converted formula does not mention. A frame
         * keeps every component preregistration created, including ones
         * whose enclosing subformula was later folded away; nothing in the
         * query constrains such a predicate, so nothing needs to assert it.
         * It stays registered in the core, unasserted, and cannot reach a
         * conflict.
         *
         * This used to ask instead whether the atom occurred in
         * registered_.boolean_formula, which is the frontend's output and so
         * predates every simplification between it and the CNF. An atom the
         * simplifier removed therefore still occurred there and was refused.
         * A valid Boolean skeleton removes *all* of them, which is how a
         * plain tautology over Real atoms --
         *   (=> (>= y x) (=> (< y 1) (=> (< y 1) (>= y x))))
         * -- reached the caller as an error rather than as sat. */
        omitted.push_back(atom);
        continue;
      }
      if (found->second.size() != 1 ||
          found->second[0] == ~static_cast<unsigned>(0) ||
          !solver_.validVariable(found->second[0]))
      {
        /* Recorded, and still unusable: the conversion mentioned this atom
         * and then gave it no single valid variable. That is a genuine
         * mapping fault, and refusing it is what keeps a theory verdict from
         * silently disagreeing with a SAT assignment nothing bound it to. */
        throw std::runtime_error(
            "opaque LRA atom " + std::string(atom.GetName()) + " (node " +
            std::to_string(atom.GetNodeNum()) +
            ") has no complete AST-to-SAT binding");
      }
      const SATSolver::Lit literal = SATSolver::mkLit(found->second[0], false);
      bindings.push_back(LraSatBinding{atom, literal});
      if (!copied.emplace(atom, literal).second)
        throw std::runtime_error("duplicate copied opaque LRA binding");
    }
    if (!context_->bindOpaqueAtoms(bindings, omitted))
      rethrowContextFailure(*context_, "exact LRA atom binding failed");
    opaque_bindings_.swap(copied);
    bindings_ready_ = true;
    return true;
  }
  catch (const std::exception& failure)
  {
    failClosed(failure.what());
    return false;
  }
  catch (...)
  {
    failClosed("unexpected opaque LRA binding failure");
    return false;
  }
}

CoordinatorCandidateOutcome
LraCoordinator::checkCompleteCandidate(ToSATBase& tosat) noexcept
{
  if (!ready() || !bindOpaqueAtoms(tosat))
  {
    /* A context that gave up says so; only a genuinely invalid one is a
     * fault of ours. Collapsing the two here is what put "no answer" and "a
     * bug in STP" behind the same verdict at the caller. Recorded by hand
     * rather than through failClosed, which invalidates the context and
     * would turn the give-up back into the fault it is not. */
    if (context_ != nullptr
        && context_->status() == SolveContextStatus::ResourceLimit)
    {
      if (failure_detail_.empty())
        failure_detail_ = context_->failureDetail();
      manager_.InvalidateRealModel();
      return CoordinatorCandidateOutcome::ResourceLimit;
    }
    return CoordinatorCandidateOutcome::InternalNoResult;
  }
  /* Under propagation the theory has already asserted every literal as the
   * search assigned it, and cb_check_found_model has already passed exact
   * judgement -- a SAT verdict cannot reach here otherwise. Re-asserting the
   * model would drive the same state twice. */
  const AdapterResult result = propagating_
                                   ? adapter_->acceptPropagatedModel()
                                   : adapter_->checkCompleteCandidate();
  if (result.candidate_serial != context_->current_candidate_serial_ ||
      result.solve_epoch != context_->solve_epoch_)
  {
    failClosed("candidate adapter returned a stale epoch or serial");
    return CoordinatorCandidateOutcome::InternalNoResult;
  }
  increment(metrics_.candidates);
  switch (result.outcome)
  {
    case AdapterOutcome::ModelStaged:
      increment(metrics_.lra_consistent);
      return CoordinatorCandidateOutcome::ModelStaged;
    case AdapterOutcome::ConflictPending:
      increment(metrics_.lra_conflicts);
      if (const PendingLraClause* pending =
              context_->pendingClauseForTesting())
      {
        const std::uint64_t support =
            static_cast<std::uint64_t>(pending->support.size());
        const std::uint64_t terms = static_cast<std::uint64_t>(
            pending->verified_conflict.terms.size());
        metrics_.conflict_support_literals =
            support > std::numeric_limits<std::uint64_t>::max() -
                          metrics_.conflict_support_literals
                ? std::numeric_limits<std::uint64_t>::max()
                : metrics_.conflict_support_literals + support;
        metrics_.maximum_conflict_support =
            std::max(metrics_.maximum_conflict_support, support);
        if (support < terms)
          increment(metrics_.equality_support_compressions);
      }
      return CoordinatorCandidateOutcome::ConflictPending;
    case AdapterOutcome::Interrupted:
      manager_.InvalidateRealModel();
      return CoordinatorCandidateOutcome::Interrupted;
    case AdapterOutcome::ResourceLimit:
      resource_limit_detail_ = result.detail;
      manager_.InvalidateRealModel();
      return CoordinatorCandidateOutcome::ResourceLimit;
    case AdapterOutcome::ClauseInserted:
      failClosed("candidate check unexpectedly inserted an LRA clause");
      return CoordinatorCandidateOutcome::InternalNoResult;
    case AdapterOutcome::InternalNoResult:
      failClosed(result.detail.empty() ? "exact LRA candidate check failed"
                                       : result.detail);
      return CoordinatorCandidateOutcome::InternalNoResult;
  }
  failClosed("unknown exact LRA candidate outcome");
  return CoordinatorCandidateOutcome::InternalNoResult;
}

bool LraCoordinator::hasPendingLraClause() const noexcept
{
  return ready() && context_->pendingClauseState() ==
                        PendingClauseState::CandidateConflict;
}

bool LraCoordinator::encodePendingLraClause() noexcept
{
  if (!hasPendingLraClause())
  {
    failClosed("no verified pending LRA clause at refinement boundary");
    return false;
  }
  const AdapterResult result = adapter_->encodeAndInsertPendingClause();
  if (result.outcome != AdapterOutcome::ClauseInserted ||
      result.solve_epoch != context_->solve_epoch_ ||
      result.candidate_serial != context_->current_candidate_serial_)
  {
    failClosed(result.detail.empty() ? "verified LRA clause insertion failed"
                                     : result.detail);
    return false;
  }
  increment(metrics_.lra_clauses);
  if (const PendingLraClause* pending = context_->pendingClauseForTesting())
  {
    const std::uint64_t clause =
        static_cast<std::uint64_t>(pending->encoded_clause.size());
    metrics_.learned_clause_literals =
        clause > std::numeric_limits<std::uint64_t>::max() -
                     metrics_.learned_clause_literals
            ? std::numeric_limits<std::uint64_t>::max()
            : metrics_.learned_clause_literals + clause;
    metrics_.maximum_learned_clause =
        std::max(metrics_.maximum_learned_clause, clause);
  }
  manager_.InvalidateRealModel();
  return true;
}

bool LraCoordinator::hasStagedModel() const noexcept
{
  return ready() && context_->staged_model_.has_value() &&
         context_->staged_model_->solve_epoch == context_->solve_epoch_ &&
         context_->staged_model_->candidate_serial ==
             context_->current_candidate_serial_;
}

void LraCoordinator::noteArrayOutcome(bool consistent) noexcept
{
  if (!ready() || !hasStagedModel())
  {
    failClosed("array checker observed no current staged Real model");
    return;
  }
  if (consistent)
  {
    increment(metrics_.array_consistent);
    return;
  }
  increment(metrics_.array_conflicts);
  discardStagedModel(StagedDiscardReason::ArrayConflict);
  manager_.InvalidateRealModel();
}

void LraCoordinator::noteArrayNotApplicable() noexcept
{
  if (!ready() || !hasStagedModel())
  {
    failClosed("array-order boundary observed no current staged Real model");
    return;
  }
  increment(metrics_.array_not_applicable);
}

void LraCoordinator::noteOrdinaryOutcome(bool consistent) noexcept
{
  if (!ready() || !hasStagedModel())
  {
    failClosed("ordinary checker observed no current staged Real model");
    return;
  }
  if (consistent)
  {
    increment(metrics_.ordinary_consistent);
    return;
  }

  increment(metrics_.ordinary_refinements);
  if (legacy_array_refinement_enabled_)
  {
    // The legacy checker has not yet certified that it owns the mismatch.
    // Keep the candidate-local stage private until that checker emits its
    // exact refinement; noteLegacyArrayRefinementEncoded then destroys the
    // stage before the next SAT call and attributes the discard correctly.
    legacy_refinement_pending_ = true;
    return;
  }

  discardStagedModel(StagedDiscardReason::OrdinaryRefinement);
  manager_.InvalidateRealModel();
  failClosed("ordinary candidate mismatch has no exact permitted refinement");
}

void LraCoordinator::noteLegacyArrayRefinementEncoded() noexcept
{
  if (!ready() || !legacy_refinement_pending_)
  {
    failClosed("legacy array refinement was not pending for this candidate");
    return;
  }
  discardStagedModel(StagedDiscardReason::LegacyArrayReadRefinement);
  legacy_refinement_pending_ = false;
  increment(metrics_.legacy_refinements);
  manager_.InvalidateRealModel();
}

bool LraCoordinator::readOpaqueValue(const ASTNode& atom,
                                     bool& value) const noexcept
{
  const auto alias = source_atom_aliases_.find(atom);
  const ASTNode& canonical =
      alias == source_atom_aliases_.end() ? atom : alias->second;
  const auto found = opaque_bindings_.find(canonical);
  if (found == opaque_bindings_.end() ||
      !solver_.validVariable(SATSolver::var(found->second)))
    return false;
  const SATSolver::lbool raw = solver_.modelValue(SATSolver::var(found->second));
  if (raw == solver_.undef_literal())
    return false;
  if (raw == solver_.true_literal())
    value = !SATSolver::sign(found->second);
  else if (raw == solver_.false_literal())
    value = SATSolver::sign(found->second);
  else
    return false;
  return true;
}

bool LraCoordinator::checkAgainstOriginal(
    const RealModel& model, AbsRefine_CounterExample& counterexample)
{
  const bool held =
      evaluateSubmittedFormula(reconstruction_.original, model, counterexample);
  if (held)
    increment(metrics_.original_formula_checks);
  return held;
}

bool LraCoordinator::validateSourcePredicates(const RealModel& model) const
{
  for (const PredicateRegistration& predicate : preregistered_.predicates)
  {
    if (predicate.payload.source.Degree() != 2)
      throw std::runtime_error("registered source predicate is not binary");
    // Ask the cheap question first. What this loop compares is a SAT value
    // against an exactly evaluated one, and a predicate the simplifications
    // dropped from the formula has no SAT value to compare -- it is skipped
    // below. Evaluating its terms before finding that out is the one thing
    // here that walks a term and does exact arithmetic, and it was being
    // paid for every dropped predicate before the skip.
    bool selected = false;
    if (!readOpaqueValue(predicate.opaque_atom, selected))
    {
      // Dropped from the formula, so there is no SAT value to agree with and
      // nothing that depends on this predicate either way. Asked of the
      // bindings rather than of registered_.boolean_formula, for the reason
      // bindOpaqueAtoms gives: that formula predates the simplifications
      // that do the dropping, so it answers for atoms that are long gone.
      // An atom bindOpaqueAtoms omitted has no binding here by construction.
      const auto alias = source_atom_aliases_.find(predicate.opaque_atom);
      const ASTNode& canonical = alias == source_atom_aliases_.end()
                                     ? predicate.opaque_atom
                                     : alias->second;
      if (opaque_bindings_.find(canonical) == opaque_bindings_.end())
        continue;
      throw std::runtime_error(
          "selected opaque LRA predicate has no SAT value");
    }
    const int comparison = model.compareTerms(predicate.payload.source[0],
                                              predicate.payload.source[1]);
    const bool exact = relationValue(comparison, predicate.payload.relation);
    if (selected != exact)
      throw std::runtime_error(
          "selected opaque LRA predicate disagrees with exact model");
  }

  for (const EqualityRegistration& equality : preregistered_.equalities)
  {
    const bool exact = model.predicateValue(equality.source_equality);
    bool selected = false;
    bool less = false;
    bool greater = false;
    if (!readOpaqueValue(equality.equality_atom, selected) ||
        !readOpaqueValue(equality.less_equal_atom, less) ||
        !readOpaqueValue(equality.greater_equal_atom, greater) ||
        selected != exact || selected != (less && greater))
      throw std::runtime_error(
          "LRA equality definition disagrees with exact model or SAT value");
  }
  return true;
}

bool LraCoordinator::evaluateSubmittedFormula(
    const ASTNode& formula, const RealModel& model,
    AbsRefine_CounterExample& counterexample) const
{
  // One save/restore of the query maps for the whole evaluation instead of
  // one per Boolean leaf (QueryFormulaAgainstModel's per-call guard was the
  // dominant cost of an incremental session's per-candidate verify).
  AbsRefine_CounterExample::ModelQueryScope query_scope(counterexample);
  /* Evaluate the mixed formula bottom up over an explicit stack. The formula
   * is as deep as the trace it was unrolled from, so a call frame per level
   * overflows on the queries that matter; and whether a subterm holds Real
   * syntax is decided once per node from its children, where asking the
   * whole subtree at every node made this quadratic. Values are memoised, so
   * a shared subterm is evaluated once; connectives short-circuit, so a
   * conjunction stops at its first false child. */
  std::unordered_map<ASTNode, bool, ASTNode::ASTNodeHasher,
                     ASTNode::ASTNodeEqual>
      has_real;
  {
    struct Mark
    {
      ASTNode node;
      std::size_t next = 0;
    };
    std::vector<Mark> pending;
    pending.push_back(Mark{formula});
    while (!pending.empty())
    {
      Mark& mark = pending.back();
      if (has_real.count(mark.node) != 0)
      {
        pending.pop_back();
        continue;
      }
      if (mark.next < mark.node.Degree())
      {
        const ASTNode child = mark.node[mark.next++];
        if (has_real.count(child) == 0)
          pending.push_back(Mark{child});
        continue;
      }
      bool real = isRealComparison(mark.node) || mark.node.isRealTerm() ||
                  mark.node.GetSourceSort().kind() == SourceSort::Kind::Real;
      for (std::size_t i = 0; i < mark.node.Degree() && !real; ++i)
        real = has_real[mark.node[i]];
      has_real[mark.node] = real;
      pending.pop_back();
    }
  }

  std::unordered_map<ASTNode, bool, ASTNode::ASTNodeHasher,
                     ASTNode::ASTNodeEqual>
      value;
  auto leaf = [&](const ASTNode& node) -> std::optional<bool> {
    if (isRealComparison(node))
      return model.predicateValue(node);
    if (!has_real[node])
    {
      const ASTNode result = counterexample.ComputeFormulaUsingModel(node);
      if (result == manager_.ASTTrue)
        return true;
      if (result == manager_.ASTFalse)
        return false;
      throw std::runtime_error(
          "non-Real submitted formula did not evaluate to Boolean constant");
    }
    switch (node.GetKind())
    {
      case TRUE: return true;
      case FALSE: return false;
      case NOT: if (node.Degree() == 1) return std::nullopt; break;
      case AND: case OR: case NAND: case NOR: case XOR: return std::nullopt;
      case IFF: if (node.Degree() != 0) return std::nullopt; break;
      case IMPLIES: if (node.Degree() == 2) return std::nullopt; break;
      case ITE:
        if (node.Degree() == 3 &&
            node.GetSourceSort().kind() == SourceSort::Kind::Bool)
          return std::nullopt;
        break;
      default: break;
    }
    throw std::runtime_error(
        "unsupported Real syntax reached original-formula evaluation");
  };

  struct Frame
  {
    ASTNode node;
    std::size_t next = 0;   // next child to evaluate
    bool first = false;     // IFF: the first child's value; ITE: the condition
    bool parity = false;    // XOR
    bool done = false;
    bool result = false;
  };
  // Fold one child's value into its parent; true when the parent is settled.
  auto fold = [](Frame& frame, std::size_t index, bool child) -> bool {
    switch (frame.node.GetKind())
    {
      case NOT: frame.result = !child; return true;
      case AND: if (!child) { frame.result = false; return true; } return false;
      case NAND: if (!child) { frame.result = true; return true; } return false;
      case OR: if (child) { frame.result = true; return true; } return false;
      case NOR: if (child) { frame.result = false; return true; } return false;
      case XOR: frame.parity = frame.parity != child; return false;
      case IFF:
        if (index == 0) { frame.first = child; return false; }
        if (child != frame.first) { frame.result = false; return true; }
        return false;
      case IMPLIES:
        if (index == 0)
        {
          if (!child) { frame.result = true; return true; }
          return false;
        }
        frame.result = child; return true;
      case ITE:
        if (index == 0) { frame.first = child; return false; }
        frame.result = child; return true;
      default: return false;
    }
  };
  // The value a connective takes once every child it needed has been seen.
  auto exhausted = [](const Frame& frame) -> bool {
    switch (frame.node.GetKind())
    {
      case AND: return true;
      case NAND: return false;
      case OR: return false;
      case NOR: return true;
      case XOR: return frame.parity;
      case IFF: return true;
      default: return frame.result;
    }
  };
  // Which child a connective wants next; ITE picks a branch by its condition.
  auto nextChild = [](const Frame& frame) -> std::size_t {
    if (frame.node.GetKind() == ITE && frame.next == 1)
      return frame.first ? 1 : 2;
    return frame.next;
  };

  std::vector<Frame> stack;
  auto settle = [&](const ASTNode& node) -> std::optional<bool> {
    const auto memo = value.find(node);
    if (memo != value.end())
      return memo->second;
    std::optional<bool> known = leaf(node);
    if (known)
      value[node] = *known;
    return known;
  };
  if (std::optional<bool> known = settle(formula))
    return *known;
  stack.push_back(Frame{formula});
  bool answer = false;
  while (!stack.empty())
  {
    Frame& frame = stack.back();
    const bool ite = frame.node.GetKind() == ITE;
    // An ITE evaluates its condition and then exactly one branch.
    const bool wants_more =
        !frame.done && (ite ? frame.next < 2 : frame.next < frame.node.Degree());
    if (wants_more)
    {
      const std::size_t index = nextChild(frame);
      const std::size_t position = frame.next++;
      const ASTNode child = frame.node[index];
      if (std::optional<bool> known = settle(child))
      {
        if (fold(frame, position, *known))
          frame.done = true;
        continue;
      }
      stack.push_back(Frame{child});
      continue;
    }
    const bool result = frame.done ? frame.result : exhausted(frame);
    const ASTNode node = frame.node;
    value[node] = result;
    stack.pop_back();
    if (stack.empty())
    {
      answer = result;
      break;
    }
    Frame& parent = stack.back();
    // The child just finished sat at the position the parent handed out last.
    if (fold(parent, parent.next - 1, result))
      parent.done = true;
  }
  return answer;
}

ASTVec LraCoordinator::requiredRealSymbols() const
{
  ASTVec result = manager_.AllRealSymbols();
  ASTVec pending(1, submitted_formula_);
  ASTNodeSet seen;
  std::set<ASTNode, ExprLess> included(result.begin(), result.end());
  while (!pending.empty())
  {
    const ASTNode node = pending.back();
    pending.pop_back();
    if (!seen.insert(node).second)
      continue;
    if (node.GetKind() == SYMBOL &&
        node.GetSourceSort().kind() == SourceSort::Kind::Real &&
        included.insert(node).second)
      result.push_back(node);
    for (const ASTNode& child : node.GetChildren())
      pending.push_back(child);
  }
  return result;
}

std::unique_ptr<RealModel> LraCoordinator::materializeStagedModel(
    ) const
{
  if (!ready() || !hasStagedModel() || legacy_refinement_pending_)
    throw std::runtime_error(
        "exact model materialization lacks one current private stage");

  const StagedExactModel& staged = *context_->staged_model_;
  if (staged.values.size() != context_->registry_snapshot_.symbols.size())
    throw std::runtime_error(
        "staged exact model has incomplete registry-symbol coverage");

  std::set<ASTNode, ExprLess> expected;
  std::set<ASTNode, ExprLess> public_expected;
  for (const RegistrySymbol& symbol : context_->registry_snapshot_.symbols)
  {
    if (!expected.insert(symbol.symbol).second)
      throw std::runtime_error(
          "solve registry contains a duplicate Real symbol");
    const CoreVariableMapEntry& mapped = context_->variableMap(symbol.id);
    if (mapped.role == CoreVariableRole::PublicRealSymbol)
      public_expected.insert(symbol.symbol);
    else if (mapped.role != CoreVariableRole::BridgeResult)
      throw std::runtime_error(
          "registry Real symbol has an invalid core-variable role");
  }

  std::set<ASTNode, ExprLess> copied;
  std::vector<RealModelSeed> seeds;
  seeds.reserve(staged.values.size());
  {
    // Recheck the private adapter DTO under its owning solve budget.  The
    // adapter validated this material when it staged the candidate, but the
    // public-model boundary must independently reject later corruption of an
    // identity or of either exact text field.
    NumberOperationScope operation(context_->mapping_budget_);
    const LraModelIndex symbol_index(context_->registry_snapshot_.symbols,
                                     &RegistrySymbol::id,
                                     context_->mapping_budget_.limits(),
                                     "registry symbol for public model");
    for (const StagedRealValue& value : staged.values)
    {
      const RegistrySymbol& registry_symbol = symbol_index.at(value.registry_symbol);
      if (registry_symbol.frontend_id != value.frontend_symbol ||
          registry_symbol.symbol != value.symbol ||
          context_->variableMap(value.registry_symbol).role != value.role ||
          value.role == CoreVariableRole::BridgeBit)
        throw std::runtime_error(
            "staged exact model contains inconsistent symbol identities");
      if (value.value.numeratorDecimal() != value.numerator_decimal ||
          value.value.denominatorDecimal() != value.denominator_decimal)
        throw std::runtime_error(
            "staged exact model contains inconsistent exact value text");
      if (expected.find(value.symbol) == expected.end() ||
          !copied.insert(value.symbol).second)
        throw std::runtime_error(
            "staged exact model contains a foreign or duplicate symbol");
      if (value.role == CoreVariableRole::PublicRealSymbol)
        seeds.push_back(RealModelSeed{value.symbol, value.numerator_decimal,
                                     value.denominator_decimal});
    }
  }
  if (copied != expected)
    throw std::runtime_error(
        "staged exact model misses a registered Real symbol");

  std::set<ASTNode, ExprLess> copied_public;
  for (const RealModelSeed& seed : seeds)
    copied_public.insert(seed.symbol);
  if (copied_public != public_expected)
    throw std::runtime_error(
        "staged exact model misses a public registered Real symbol");

  auto model = std::make_unique<RealModel>(
      frontend_.numberLimits(), seeds, requiredRealSymbols(), spread_symbols_);
  if (!reconstruction_.definitions.empty())
    model->reconstruct(reconstruction_.definitions);
  return model;
}


CommitOutcome LraCoordinator::verifyAndCommit(
    AbsRefine_CounterExample& counterexample) noexcept
{
  try
  {
    if (!ready() || !hasStagedModel() || legacy_refinement_pending_ ||
        !solver_.okay())
      throw std::runtime_error(
          "combined model commit lacks one current accepted candidate");
    const auto evaluation_start = std::chrono::steady_clock::now();
    auto candidate = materializeStagedModel();
    /* Lend the model somewhere to resolve the Boolean part of a Real ite's
     * condition. Only the counterexample knows those values, and it is only
     * available here.
     *
     * Captured by pointer, and deliberately not `this`: this oracle outlives
     * the call by design -- it is installed on the candidate, and the
     * candidate becomes the committed model -- while this coordinator is a
     * local of the solve and goes away with it. A read through that model
     * afterwards then called back into a destroyed object and took manager_
     * from freed memory. What surfaced was ASTTrue and ASTFalse comparing
     * equal to nothing, so a condition that had evaluated perfectly well to
     * FALSE was reported as not a Boolean constant. Both of these outlive any
     * model: the manager owns everything, and the counterexample belongs to
     * the STP object. */
    STPMgr* const manager = &manager_;
    AbsRefine_CounterExample* const oracle_counterexample = &counterexample;
    candidate->setConditionOracle(
        [manager, oracle_counterexample](const ASTNode& condition) {
          const ASTNode value =
              evaluateAgainstCounterexample(*oracle_counterexample, condition);
          if (value == manager->ASTTrue)
            return true;
          if (value == manager->ASTFalse)
            return false;
          throw std::runtime_error(
              "Real ite condition did not evaluate to a Boolean constant");
        });
    if (!validateSourcePredicates(*candidate) ||
        !evaluateSubmittedFormula(submitted_formula_, *candidate,
                                  counterexample) ||
        (!reconstruction_.original.IsNull() &&
         !checkAgainstOriginal(*candidate, counterexample)))
      throw std::runtime_error(
          "original submitted formula rejects the combined exact model");
    addElapsed(metrics_.formula_evaluation_nanoseconds, evaluation_start);

    const auto publication_start = std::chrono::steady_clock::now();
    metrics_.committed_model_values =
        static_cast<std::uint64_t>(candidate->size());
    manager_.InstallRealModel(candidate.release());
    addElapsed(metrics_.publication_nanoseconds, publication_start);
    increment(metrics_.models_committed);
    return CommitOutcome::Committed;
  }
  catch (const std::exception& failure)
  {
    /* Everything above here does exact arithmetic -- materialising the
     * staged values, replaying the reconstruction, re-evaluating the
     * submitted formula -- so a budget can run out on the last step of a
     * query that has otherwise been answered. That is a query STP could not
     * finish, and the candidate path two call sites up already reports it
     * that way; only this one turned it into a fault. */
    if (!gaveUpOnABudget(failure))
    {
      failClosed(failure.what());
      return CommitOutcome::Failed;
    }
    if (failure_detail_.empty())
      failure_detail_ = failure.what();
    resource_limit_detail_ = failure.what();
    manager_.InvalidateRealModel();
    legacy_refinement_pending_ = false;
    if (context_ != nullptr)
      context_->giveUp(failure_detail_);
    return CommitOutcome::ResourceLimit;
  }
  catch (...)
  {
    failClosed("unexpected combined exact model verification failure");
    return CommitOutcome::Failed;
  }
}

LraCoordinatorMetrics LraCoordinator::metrics() const noexcept
{
  return metrics_;
}

LraSolveMetrics LraCoordinator::solveMetrics() const noexcept
{
  return context_ == nullptr ? LraSolveMetrics{} : context_->metrics();
}

CoreStatistics LraCoordinator::coreStatistics() const noexcept
{
  return context_ == nullptr ? CoreStatistics{} : context_->coreStatistics();
}

void LraCoordinator::printMetrics(std::ostream& out) const
{
  const LraSolveMetrics solve = solveMetrics();
  const CoreStatistics core = coreStatistics();
  const LraRegistryMetrics registry_metrics = registry_.metrics();
  const FrontendMetrics& frontend_metrics = preregistered_.metrics;
  const NumberMetrics frontend_numbers = frontend_.numberMetrics();
  out << "LRA-METRICS {" << "\"failure\":\"" << failure_detail_ << "\","
      << "\"solve_epoch\":" << metrics_.solve_epoch
      << ",\"frontend_symbols\":" << frontend_metrics.symbols
      << ",\"frontend_rows\":" << solve.rows_registered
      << ",\"frontend_predicates\":" << frontend_metrics.predicates
      << ",\"frontend_equality_groups\":"
      << frontend_metrics.equality_groups
      << ",\"frontend_opaque_atoms\":" << frontend_metrics.opaque_atoms
      << ",\"normalization_nodes\":"
      << frontend_metrics.normalization_nodes
      << ",\"normalization_time_ns\":"
      << metrics_.preregistration_nanoseconds
      << ",\"maximum_coefficient_bits\":"
      << frontend_metrics.maximum_coefficient_bits
      << ",\"registry_active_components\":"
      << registry_metrics.active_components
      << ",\"ordering_axioms\":" << solve.ordering_axioms
      << ",\"sat_candidates\":" << metrics_.candidates
      << ",\"lra_consistent\":" << metrics_.lra_consistent
      << ",\"lra_conflicts\":" << metrics_.lra_conflicts
      << ",\"lra_clauses\":" << metrics_.lra_clauses << ",\"extensions\":" << metrics_.extensions
      << ",\"extension_mode\":" << manager_.UserFlags.lra_extension_mode
      << ",\"row_order\":" << manager_.UserFlags.lra_row_order
      << ",\"context_reuses\":" << metrics_.context_reuses
      << ",\"arithmetic_state_resets\":" << metrics_.arithmetic_state_resets
      << ",\"float_basis_resets\":" << metrics_.float_basis_resets
      << ",\"sat_search_resets\":" << metrics_.sat_search_resets
      << ",\"sat_search_reset_ns\":" << metrics_.sat_search_reset_nanoseconds
      << ",\"total_exact_pivots\":" << metrics_.retired_exact_pivots + core.engine_pivots
      << ",\"total_float_checks\":" << metrics_.retired_float_checks + solve.float_checks
      << ",\"total_float_pivots\":" << metrics_.retired_float_pivots + solve.float_pivots
      << ",\"total_float_check_ns\":"
      << metrics_.retired_float_check_nanoseconds + solve.float_check_nanoseconds
      << ",\"total_float_sync_ns\":"
      << metrics_.retired_float_sync_nanoseconds + solve.float_sync_nanoseconds
      << ",\"candidate_materialization_ns\":"
      << solve.candidate_read_nanoseconds
      << ",\"exact_assertions\":" << solve.exact_assertions
      << ",\"exact_checks\":" << solve.exact_checks
      << ",\"exact_pushes\":" << solve.exact_pushes
      << ",\"exact_pops\":" << solve.exact_pops
      << ",\"core_pivots\":" << core.engine_pivots
      << ",\"core_bland_steps\":" << core.engine_bland_steps
      << ",\"core_activations\":" << core.engine_activations
      << ",\"core_deactivations\":" << core.engine_deactivations
      << ",\"core_normalised_cells\":" << core.engine_normalised_cells
      << ",\"core_identity_rows\":" << core.identity_rows
      << ",\"core_singleton_rows\":" << core.singleton_rows
      << ",\"core_direct_rows\":" << core.direct_rows
      << ",\"core_early_conflicts\":" << core.engine_early_conflicts
      << ",\"core_soi_steps\":" << core.engine_soi_steps
      << ",\"core_soi_bound_flips\":" << core.engine_soi_bound_flips
      << ",\"core_soi_fallbacks\":" << core.engine_soi_fallbacks
      << ",\"exact_conflicts\":"
      << (solve.immediate_conflicts + solve.tableau_conflicts)
      << ",\"partial_conflicts\":" << solve.partial_conflicts
      << ",\"partial_checks_abandoned\":" << solve.partial_checks_abandoned
      << ",\"partial_checks_disabled\":" << solve.partial_checks_disabled
      << ",\"float_assertions\":" << solve.float_assertions
      << ",\"float_checks\":" << solve.float_checks
      << ",\"float_check_conflicts\":" << solve.float_check_conflicts
      << ",\"float_local_conflicts\":" << solve.float_local_conflicts
      << ",\"float_checks_abandoned\":" << solve.float_checks_abandoned
      << ",\"float_replays\":" << solve.float_replays
      << ",\"float_replay_conflicts\":" << solve.float_replay_conflicts
      << ",\"float_replay_consistent\":" << solve.float_replay_consistent
      << ",\"float_disabled\":" << solve.float_disabled
      << ",\"float_pivots\":" << solve.float_pivots
      << ",\"float_early_conflicts\":" << solve.float_early_conflicts
      << ",\"float_soi_steps\":" << solve.float_soi_steps
      << ",\"float_soi_bound_flips\":" << solve.float_soi_bound_flips
      << ",\"float_soi_fallbacks\":" << solve.float_soi_fallbacks
      << ",\"float_check_ns\":" << solve.float_check_nanoseconds
      << ",\"float_sync_ns\":" << solve.float_sync_nanoseconds
      << ",\"float_certified\":" << solve.float_certified
      << ",\"float_certificate_failed\":" << solve.float_certificate_failed
      << ",\"conflict_recovery_attempts\":" << core.conflict_recovery_attempts
      << ",\"conflict_recoveries\":" << core.conflict_recoveries
      << ",\"conflict_recovery_ns\":" << core.conflict_recovery_nanoseconds
      << ",\"float_models_refined\":" << solve.float_models_refined
      << ",\"float_model_refine_failed\":"
      << solve.float_model_refine_failed
      << ",\"float_restarts\":" << solve.float_restarts
      << ",\"float_row_activations\":" << solve.float_row_activations
      << ",\"float_rows_dormant\":" << solve.float_rows_dormant
      << ",\"float_dormant_evaluations\":" << solve.float_dormant_evaluations
      << ",\"float_rebuilds\":" << solve.float_rebuilds
      << ",\"float_generalisations\":" << solve.float_generalisations
      << ",\"float_factorized\":" << solve.float_factorized
      << ",\"float_complete_recoveries\":" << solve.float_complete_recoveries
      << ",\"float_cold_recoveries\":" << solve.float_cold_recoveries
      << ",\"float_refactor_failures\":" << solve.float_refactor_failures
      << ",\"float_robust_refactors\":" << solve.float_robust_refactors
      << ",\"float_promotions\":" << solve.float_promotions
      << ",\"exact_pivots\":" << core.pivots
      << ",\"bland_pivots\":" << core.bland_pivots
      << ",\"support_literals\":" << metrics_.conflict_support_literals
      << ",\"learned_clause_literals\":"
      << metrics_.learned_clause_literals
      << ",\"maximum_support\":" << metrics_.maximum_conflict_support
      << ",\"maximum_clause\":" << metrics_.maximum_learned_clause
      << ",\"equality_support_compressions\":"
      << metrics_.equality_support_compressions
      << ",\"sat_resolves\":" << metrics_.sat_resolves
      << ",\"first_search_connections\":" << metrics_.first_search_connections
      << ",\"polarity_supported\":" << (solver_.supportsDecisionPolarity() ? 1 : 0)
      << ",\"polarity_enabled\":" << (decisionPolarityEnabled() ? 1 : 0)
      << ",\"polarity_queries\":" << solve.polarity_queries
      << ",\"polarity_advice\":" << solve.polarity_advice
      << ",\"polarity_changes\":" << solve.polarity_changes
      << ",\"polarity_abstentions\":" << solve.polarity_abstentions
      << ",\"polarity_float\":" << solve.polarity_float
      << ",\"polarity_exact\":" << solve.polarity_exact
      << ",\"persistent_extensions\":" << solve.persistent_extensions
      << ",\"persistent_equality_clauses\":" << metrics_.persistent_equality_clauses
      << ",\"float_extensions\":" << solve.float_extensions
      << ",\"core_rebuilds\":" << metrics_.core_rebuilds
      << ",\"core_rebuild_time_ns\":"
      << metrics_.context_rebuild_nanoseconds
      << ",\"models_staged\":" << solve.models_staged
      << ",\"model_values_staged\":" << solve.model_values_staged
      << ",\"committed_model_values\":"
      << metrics_.committed_model_values
      << ",\"model_row_count\":" << solve.rows_registered
      << ",\"model_producer_ns\":" << solve.exact_check_nanoseconds
      << ",\"model_verifier_ns\":"
      << solve.model_evaluation_nanoseconds
      << ",\"model_mapping_ns\":" << solve.model_mapping_nanoseconds
      << ",\"original_formula_evaluation_ns\":"
      << metrics_.formula_evaluation_nanoseconds
      << ",\"original_formula_checks\":" << metrics_.original_formula_checks
      << ",\"publication_ns\":" << metrics_.publication_nanoseconds
      << ",\"array_consistent\":" << metrics_.array_consistent
      << ",\"array_conflicts\":" << metrics_.array_conflicts
      << ",\"array_not_applicable\":"
      << metrics_.array_not_applicable
      << ",\"lra_consistent_rejected_by_arrays\":"
      << metrics_.discarded_for_array
      << ",\"ordinary_consistent\":" << metrics_.ordinary_consistent
      << ",\"ordinary_refinements\":" << metrics_.ordinary_refinements
      << ",\"legacy_refinements\":" << metrics_.legacy_refinements
      << ",\"staged_models_discarded\":"
      << metrics_.staged_models_discarded
      << ",\"discarded_for_array\":" << metrics_.discarded_for_array
      << ",\"discarded_for_ordinary\":"
      << metrics_.discarded_for_ordinary
      << ",\"discarded_for_legacy\":" << metrics_.discarded_for_legacy
      << ",\"models_committed\":" << metrics_.models_committed
      << ",\"interruptions\":" << core.interruptions
      << ",\"resource_stops\":" << core.resource_stops
      << ",\"internal_errors\":" << core.internal_errors
      << ",\"number_operations\":"
      << (core.numbers.additions + core.numbers.subtractions +
          core.numbers.multiplications + core.numbers.divisions +
          core.numbers.comparisons)
      << ",\"number_allocation_calls\":"
      << core.numbers.allocation_calls
      << ",\"number_allocated_bytes\":" << core.numbers.allocated_bytes
      << ",\"number_profile\":";
  printNumberProfile(out, core.numbers);
  out << ",\"frontend_numbers\":";
  printNumberProfile(out, frontend_numbers);
  out << ",\"maximum_numerator_bits\":"
      << core.numbers.maximum_numerator_bits
      << ",\"maximum_denominator_bits\":"
      << core.numbers.maximum_denominator_bits << "}\n";
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
void LraCoordinator::testCorruptCandidateSerial() noexcept
{
  if (context_ != nullptr)
    ++context_->current_candidate_serial_;
}

void LraCoordinator::testCorruptStagedEpoch() noexcept
{
  if (context_ != nullptr && context_->staged_model_)
    ++context_->staged_model_->solve_epoch;
}

void LraCoordinator::testCorruptStagedCandidateSerial() noexcept
{
  if (context_ != nullptr && context_->staged_model_)
    ++context_->staged_model_->candidate_serial;
}

void LraCoordinator::testDropStagedValue() noexcept
{
  if (context_ != nullptr && context_->staged_model_ &&
      !context_->staged_model_->values.empty())
    context_->staged_model_->values.pop_back();
}

void LraCoordinator::testDuplicateStagedValue()
{
  if (context_ != nullptr && context_->staged_model_ &&
      !context_->staged_model_->values.empty())
  {
    NumberOperationScope operation(context_->mapping_budget_);
    context_->staged_model_->values.push_back(
        context_->staged_model_->values.front());
  }
}

void LraCoordinator::testCorruptStagedSymbol() noexcept
{
  if (context_ != nullptr && context_->staged_model_ &&
      !context_->staged_model_->values.empty())
    context_->staged_model_->values.front().symbol = solve_activation_;
}

void LraCoordinator::testCorruptStagedRegistryId() noexcept
{
  if (context_ != nullptr && context_->staged_model_ &&
      !context_->staged_model_->values.empty())
    ++context_->staged_model_->values.front().registry_symbol.serial;
}

void LraCoordinator::testCorruptStagedNumerator()
{
  if (context_ != nullptr && context_->staged_model_ &&
      !context_->staged_model_->values.empty())
    context_->staged_model_->values.front().numerator_decimal = "999";
}

void LraCoordinator::testCorruptStagedDenominator()
{
  if (context_ != nullptr && context_->staged_model_ &&
      !context_->staged_model_->values.empty())
    context_->staged_model_->values.front().denominator_decimal = "0";
}

void LraCoordinator::testReplaceStagedExactValue()
{
  if (context_ == nullptr || !context_->staged_model_ ||
      context_->staged_model_->values.empty())
    return;
  NumberOperationScope operation(context_->mapping_budget_);
  StagedRealValue& value = context_->staged_model_->values.front();
  value.value = ExactRational::fromCanonicalIntegers("999", "1");
  value.numerator_decimal = value.value.numeratorDecimal();
  value.denominator_decimal = value.value.denominatorDecimal();
}

bool LraCoordinator::testValidateStagedModel() noexcept
{
  try
  {
    const std::unique_ptr<RealModel> checked = materializeStagedModel();
    if (checked == nullptr || !validateSourcePredicates(*checked))
      throw std::runtime_error(
          "staged exact model failed independent source validation");
    return true;
  }
  catch (const std::exception& failure)
  {
    failClosed(failure.what());
    return false;
  }
  catch (...)
  {
    failClosed("unexpected staged-model validation failure");
    return false;
  }
}
#endif

} // namespace stp::lra

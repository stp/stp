#include "LraCoordinator.h"
#include "LraBudgetRefusal.h"
#include "LraModelIndex.h"

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/ToSATBase.h"

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

bool LraCoordinator::decisionPolarityEnabled() const
{
  return manager_.UserFlags.lra_decision_polarity &&
         manager_.UserFlags.lra_theory_propagation &&
         solver_.supportsTheoryPropagator() && solver_.supportsDecisionPolarity();
}

LraCoordinator::LraCoordinator(STPMgr& manager, SATSolver& solver,
                               const ASTNode& submitted_formula)
    : manager_(manager), solver_(solver),
      submitted_formula_(submitted_formula), frontend_(manager),
      registry_(manager)
{
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
    std::set<ASTNode, ExprLess> unique;
    for (const RegistryComponent& component : solve_snapshot.components)
    {
      poll();
      if (!unique.insert(component.opaque_atom).second)
        throw std::runtime_error("duplicate LRA component representative");
      else
        opaque_atoms_.push_back(component.opaque_atom);
    }
    for (const RegistryEqualityGroup& equality : solve_snapshot.equalities)
    {
      poll();
      if (!unique.insert(equality.equality_atom).second)
        throw std::runtime_error("duplicate LRA equality opaque atom");
      else
        opaque_atoms_.push_back(equality.equality_atom);
    }

    const auto context_start = std::chrono::steady_clock::now();
    context_ = std::make_unique<LraSolveContext>(
        registry_, solver_, frontend_.numberLimits(), frame_);
    increment(metrics_.core_rebuilds);
    /* The context verifies by default so that anything building one directly
     * keeps the check; the solver follows the flag, which is off unless the
     * caller asks for it. */
    context_->setConflictVerification(
        manager_.UserFlags.lra_verify_conflicts);
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

bool LraCoordinator::prepareTheorySearch() noexcept
{
  try
  {
    /* Take the theory's seat inside the search, if the backend has one to
     * offer. Same timing as the ordering axioms and for the same reason: the
     * atoms are only bound to SAT variables once a CNF exists, and connecting
     * a propagator is only legal between solves. So the first solve runs the
     * full-lazy way and every later one is driven. */
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
     * SAT variables once the first CNF exists, and adding a clause while a
     * backend is in its satisfied state invalidates the model the candidate
     * reader is about to consume.  So the first solve runs without the axioms
     * and every later one has them -- which is where they pay anyway, since the
     * enumeration blowup is in the re-solves.
     *
     * They are entailed by the theory, so they cannot change a verdict; they
     * only stop the full-lazy loop from handing over candidates that differ
     * solely in atoms the theory already implies. */
    if (bindings_ready_ && !ordering_axioms_emitted_)
    {
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
      frontend_.numberLimits(), seeds, requiredRealSymbols());
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
                                  counterexample))
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
     * staged values, re-evaluating the
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
      << ",\"sat_candidates\":" << metrics_.candidates
      << ",\"lra_consistent\":" << metrics_.lra_consistent
      << ",\"lra_conflicts\":" << metrics_.lra_conflicts
      << ",\"lra_clauses\":" << metrics_.lra_clauses
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
      << ",\"exact_conflicts\":"
      << (solve.immediate_conflicts + solve.tableau_conflicts)
      << ",\"partial_conflicts\":" << solve.partial_conflicts
      << ",\"partial_checks_abandoned\":" << solve.partial_checks_abandoned
      << ",\"partial_checks_disabled\":" << solve.partial_checks_disabled
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
      << ",\"polarity_supported\":" << (solver_.supportsDecisionPolarity() ? 1 : 0)
      << ",\"polarity_enabled\":" << (decisionPolarityEnabled() ? 1 : 0)
      << ",\"polarity_queries\":" << solve.polarity_queries
      << ",\"polarity_advice\":" << solve.polarity_advice
      << ",\"polarity_changes\":" << solve.polarity_changes
      << ",\"polarity_abstentions\":" << solve.polarity_abstentions
      << ",\"polarity_exact\":" << solve.polarity_exact
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

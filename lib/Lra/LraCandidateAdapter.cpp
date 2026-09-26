#include "LraCandidateAdapter.h"
#include "LraBudgetRefusal.h"
#include "LraModelIndex.h"

#include "ExactLraVerificationData.h"

#include <algorithm>
#include <chrono>
#include <limits>
#include <map>
#include <new>
#include <optional>
#include <set>
#include <sstream>
#include <utility>

namespace stp::lra {

namespace {


void addElapsed(std::uint64_t& destination,
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

bool sameLiteral(SATSolver::Lit lhs, SATSolver::Lit rhs) noexcept
{
  return lhs.x == rhs.x;
}

bool relationHolds(const ExactRational& value, Relation relation,
                   const ExactRational& threshold)
{
  const int comparison = value.compare(threshold);
  switch (relation)
  {
    case Relation::Less:
      return comparison < 0;
    case Relation::LessEqual:
      return comparison <= 0;
    case Relation::Greater:
      return comparison > 0;
    case Relation::GreaterEqual:
      return comparison >= 0;
  }
  return false;
}

Relation registeredRelation(FrontendRelation relation)
{
  switch (relation)
  {
    case FrontendRelation::Less:
      return Relation::Less;
    case FrontendRelation::LessEqual:
      return Relation::LessEqual;
    case FrontendRelation::Greater:
      return Relation::Greater;
    case FrontendRelation::GreaterEqual:
      return Relation::GreaterEqual;
    case FrontendRelation::Equal:
      break;
  }
  throw SolveContextFailure(SolveContextFailureKind::Invalid,
                            "equality relation reached candidate adapter");
}

template <class T, class Predicate>
const T& requireOne(const std::vector<T>& values, Predicate predicate,
                    const char* description)
{
  const T* result = nullptr;
  for (const T& value : values)
  {
    if (!predicate(value))
      continue;
    if (result != nullptr)
    {
      std::ostringstream out;
      out << "duplicate " << description;
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                out.str());
    }
    result = &value;
  }
  if (result == nullptr)
  {
    std::ostringstream out;
    out << "missing " << description;
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              out.str());
  }
  return *result;
}

// Position by serial, with the same fail-closed duplicate check requireOne
// performs -- paid once over the table rather than once per lookup. The scan
// it replaces never stopped early, because finding a second match is how it
// detected a duplicate, so every lookup cost the whole table.
template <class T, class Member>
SerialIndex indexBySerial(const std::vector<T>& values, Member member,
                          const char* description)
{
  SerialIndex index;
  index.reserve(values.size());
  for (std::size_t position = 0; position < values.size(); ++position)
    if (!index.emplace((values[position].*member).serial, position).second)
    {
      std::ostringstream out;
      out << "duplicate " << description;
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                out.str());
    }
  return index;
}

// The identifier is compared in full on the one entry the index offers, so a
// stale or foreign identifier misses exactly as the scan made it miss.
template <class T, class Id, class Member>
const T& requireIndexed(const std::vector<T>& values, const SerialIndex& index,
                        Id id, Member member, const char* description)
{
  const auto found = index.find(id.serial);
  if (found == index.end() || found->second >= values.size() ||
      !(values[found->second].*member == id))
  {
    std::ostringstream out;
    out << "missing " << description;
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              out.str());
  }
  return values[found->second];
}

} // namespace

LraCandidateAdapter::LraCandidateAdapter(LraSolveContext& context,
                                         SATSolver& solver)
    : context_(context), solver_(solver)
{
  if (&solver_ != &context_.solver_)
  {
    context_.invalidate(
        "candidate adapter received a different SAT solver instance");
  }
}

AdapterResult LraCandidateAdapter::result(AdapterOutcome outcome,
                                          std::uint64_t candidate,
                                          std::string detail) const
{
  return AdapterResult{outcome, context_.solve_epoch_, candidate,
                       std::move(detail)};
}

AdapterResult LraCandidateAdapter::refusal(const std::exception& failure,
                                           std::uint64_t candidate) noexcept
{
  if (!gaveUpOnABudget(failure))
  {
    context_.invalidate(failure.what());
    return result(AdapterOutcome::InternalNoResult, candidate,
                  context_.failure_detail_);
  }
  context_.giveUp(failure.what());
  return result(AdapterOutcome::ResourceLimit, candidate,
                context_.failure_detail_);
}

bool LraCandidateAdapter::readLiteral(SATSolver::Lit literal, bool& value,
                                      std::string& detail) const
{
  const std::uint32_t variable = SATSolver::var(literal);
  if (!solver_.validVariable(variable))
  {
    detail = "candidate read used an out-of-range SAT variable";
    return false;
  }
  const SATSolver::lbool raw = solver_.modelValue(variable);
  if (raw == solver_.undef_literal())
  {
    detail = "complete LRA candidate contains undef";
    return false;
  }
  bool variable_value = false;
  if (raw == solver_.true_literal())
    variable_value = true;
  else if (raw == solver_.false_literal())
    variable_value = false;
  else
  {
    detail = "SAT backend returned an unknown model value";
    return false;
  }
  value = SATSolver::sign(literal) ? !variable_value : variable_value;
  return true;
}

/* Read the SAT assignment of every bound component and equality group into
 * the context's current selection, and index it.
 *
 * Both candidate paths need exactly this and each had written it out: the
 * full-lazy driver and the propagated accept differed only in whether they
 * reserved, and in the re-read below. Two transcriptions of one loop over
 * the registry snapshot is two things to keep in step with the snapshot.
 *
 * `verify_stable` reads the complete deterministic sequence a second time
 * and requires it to agree. The common SAT interface has no backend-neutral
 * model revision, so that is the only proof available that one unchanged
 * model supplied the whole snapshot. The propagated path does not ask for
 * it, as it did not before: there the theory has already judged this
 * assignment literal by literal as the search made it. */
void LraCandidateAdapter::readSelectionFromSolver(bool verify_stable)
{
  context_.current_selection_.clear();
  context_.current_equalities_.clear();
  context_.current_selection_index_.clear();
  context_.current_equalities_index_.clear();

  const auto read_start = std::chrono::steady_clock::now();
  std::string detail;
  context_.current_selection_.reserve(
      context_.registry_snapshot_.components.size());
  for (const RegistryComponent& component :
       context_.registry_snapshot_.components)
  {
    /* A component the Boolean formula never mentions has no SAT variable to
     * read. Nothing constrains it, so it takes no part in the candidate: it
     * is not selected, not asserted, and cannot appear in a conflict. */
    const SATSolver::Lit* const bound =
        context_.componentBindingOrNull(component.id);
    if (bound == nullptr)
      continue;
    const SATSolver::Lit binding = *bound;
    bool positive = false;
    if (!readLiteral(binding, positive, detail))
      throw SolveContextFailure(SolveContextFailureKind::Invalid, detail);
    context_.current_selection_.push_back(CandidateComponentSelection{
        component.id, positive,
        SATSolver::mkLit(SATSolver::var(binding), !positive), binding});
  }
  context_.current_equalities_.reserve(
      context_.registry_snapshot_.equalities.size());
  for (const RegistryEqualityGroup& equality :
       context_.registry_snapshot_.equalities)
  {
    if (!context_.equalityBound(equality.id))
      continue;
    const SATSolver::Lit binding = context_.equalityBinding(equality.id);
    bool value = false;
    if (!readLiteral(binding, value, detail))
      throw SolveContextFailure(SolveContextFailureKind::Invalid, detail);
    context_.current_equalities_.push_back(CandidateEqualitySelection{
        equality.id, value,
        SATSolver::mkLit(SATSolver::var(binding), !value)});
  }

  context_.current_selection_index_ =
      indexBySerial(context_.current_selection_,
                    &CandidateComponentSelection::component,
                    "component selection");
  context_.current_equalities_index_ =
      indexBySerial(context_.current_equalities_,
                    &CandidateEqualitySelection::group, "equality selection");

  if (!verify_stable)
    return;
  for (const CandidateComponentSelection& selected :
       context_.current_selection_)
  {
    bool repeated = false;
    if (!readLiteral(selected.binding, repeated, detail) ||
        repeated != selected.positive)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "SAT model changed during LRA snapshot");
  }
  for (const CandidateEqualitySelection& selected :
       context_.current_equalities_)
  {
    bool repeated = false;
    if (!readLiteral(context_.equalityBinding(selected.group), repeated,
                     detail) ||
        repeated != selected.equality_value)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "SAT equality model changed during snapshot");
  }
  if (!solver_.okay())
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              "SAT solver changed state during model read");
  ++context_.metrics_.complete_model_reads;
  addElapsed(context_.metrics_.candidate_read_nanoseconds, read_start);
}

AdapterResult LraCandidateAdapter::checkCompleteCandidate() noexcept
{
  std::optional<Checkpoint> checkpoint;
  std::uint64_t candidate = 0;
  auto popCandidate = [&]() noexcept {
    if (!checkpoint || context_.core_ == nullptr)
      return true;
    const InputStatus popped = context_.core_->pop(*checkpoint);
    checkpoint.reset();
    if (popped != InputStatus::Accepted ||
        context_.core_->status() != CheckStatus::Ready)
      return false;
    ++context_.metrics_.exact_pops;
    return true;
  };

  try
  {
    if (&solver_ != &context_.solver_ || !context_.ready() ||
        !context_.bindings_ready_ || !context_.validateCurrentState())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "candidate requires current complete bindings");
    if (!solver_.okay())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "SAT solver is not okay before candidate read");
    if (context_.staged_model_)
      throw SolveContextFailure(
          SolveContextFailureKind::Invalid,
          "staged model was not invalidated before a new candidate");
    if (context_.pending_clause_)
    {
      if (context_.pending_clause_->state == PendingClauseState::Cleared)
        context_.pending_clause_.reset();
      else
        throw SolveContextFailure(
            SolveContextFailureKind::Invalid,
            "new candidate started with unconsumed pending clause state");
    }

    candidate = context_.allocateCandidateSerial();
    context_.current_candidate_serial_ = candidate;
    ++context_.metrics_.candidates_started;
    context_.observer_.beginCandidate();
    readSelectionFromSolver(/*verify_stable=*/true);

    for (const RegistryEqualityGroup& equality :
         context_.registry_snapshot_.equalities)
    {
      if (!context_.equalityBound(equality.id) ||
          !context_.componentBound(equality.less_equal_component) ||
          !context_.componentBound(equality.greater_equal_component))
        continue;
      const CandidateComponentSelection& less = requireIndexed(
          context_.current_selection_, context_.current_selection_index_,
          equality.less_equal_component,
          &CandidateComponentSelection::component,
          "less-equal equality-component selection");
      const CandidateComponentSelection& greater = requireIndexed(
          context_.current_selection_, context_.current_selection_index_,
          equality.greater_equal_component,
          &CandidateComponentSelection::component,
          "greater-equal equality-component selection");
      const CandidateEqualitySelection& source = requireIndexed(
          context_.current_equalities_, context_.current_equalities_index_,
          equality.id, &CandidateEqualitySelection::group,
          "source equality selection");
      if (source.equality_value != (less.positive && greater.positive))
        throw SolveContextFailure(
            SolveContextFailureKind::Invalid,
            "SAT model violates the preregistered equality definition");
    }

    const InputResult<Checkpoint> pushed = context_.core_->push();
    if (pushed.status == InputStatus::ResourceLimit)
    {
      context_.clearSemanticState();
      return result(AdapterOutcome::ResourceLimit, candidate,
                    "exact core push reached a resource limit");
    }
    if (pushed.status != InputStatus::Accepted || !pushed.value)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "exact core candidate push failed");
    checkpoint = *pushed.value;
    const bool misplaced_bridge_checkpoint = false;
    if (checkpoint->generation != context_.core_->generation() ||
        checkpoint->depth == 0 || misplaced_bridge_checkpoint)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "candidate checkpoint is stale or misplaced");

    bool immediate = false;
    for (const CandidateComponentSelection& selection :
         context_.current_selection_)
    {
      const CoreComponentMapEntry& mapped =
          context_.componentMap(selection.component);
      const AssertResult asserted =
          context_.core_->assertLiteral(mapped.core_atom, selection.positive);
      ++context_.metrics_.exact_assertions;
      if (!exactLraAssertResultShapeValid(asserted))
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "malformed exact assertion result");
      if (asserted.status == InputStatus::ResourceLimit)
      {
        if (!popCandidate())
          throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                                    "pop failed after assertion limit");
        context_.clearSemanticState();
        return result(AdapterOutcome::ResourceLimit, candidate,
                      "exact assertion reached a resource limit");
      }
      if (asserted.status != InputStatus::Accepted)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "exact literal assertion was not accepted");
      if (!asserted.immediate_conflict)
        continue;

      const VerificationResult verified =
          context_.verifyConflictChecked(*asserted.immediate_conflict);
      if (!verified.verified())
      {
        if (verified.error == VerificationError::ResourceLimit)
        {
          if (!popCandidate())
            throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                                      "pop failed after verifier limit");
          context_.clearSemanticState();
          return result(AdapterOutcome::ResourceLimit, candidate,
                        "immediate conflict verification reached a limit");
        }
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "immediate conflict failed verification");
      }
      copyVerifiedConflict(*asserted.immediate_conflict, candidate);
      ++context_.metrics_.immediate_conflicts;
      immediate = true;
      break;
    }


    if (!immediate)
    {
      const auto check_start = std::chrono::steady_clock::now();
      const CheckResult checked = context_.core_->check(context_.observer_);
      addElapsed(context_.metrics_.exact_check_nanoseconds, check_start);
      ++context_.metrics_.exact_checks;
      if (!exactLraCheckResultShapeValid(checked))
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "malformed exact check result");
      switch (checked.status)
      {
        case CheckStatus::Interrupted:
          if (!popCandidate())
            throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                                      "pop failed after interruption");
          context_.clearSemanticState();
          return result(AdapterOutcome::Interrupted, candidate,
                        "exact LRA check interrupted");
        case CheckStatus::ResourceLimit:
          if (!popCandidate())
            throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                                      "pop failed after exact resource stop");
          context_.clearSemanticState();
          return result(AdapterOutcome::ResourceLimit, candidate,
                        "exact LRA check reached a resource limit");
        case CheckStatus::Conflict:
        {
          const VerificationResult verified =
              context_.verifyConflictChecked(*checked.conflict);
          if (!verified.verified())
          {
            if (verified.error == VerificationError::ResourceLimit)
            {
              if (!popCandidate())
                throw SolveContextFailure(
                    SolveContextFailureKind::ResourceLimit,
                    "pop failed after conflict verifier limit");
              context_.clearSemanticState();
              return result(AdapterOutcome::ResourceLimit, candidate,
                            "conflict verification reached a limit");
            }
            throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                      "tableau conflict failed verification");
          }
          copyVerifiedConflict(*checked.conflict, candidate);
          ++context_.metrics_.tableau_conflicts;
          break;
        }
        case CheckStatus::Consistent:
        {
          const VerificationResult verified =
              context_.core_->verifyModel(*checked.model);
          if (!verified.verified())
          {
            if (verified.error == VerificationError::ResourceLimit)
            {
              if (!popCandidate())
                throw SolveContextFailure(
                    SolveContextFailureKind::ResourceLimit,
                    "pop failed after model verifier limit");
              context_.clearSemanticState();
              return result(AdapterOutcome::ResourceLimit, candidate,
                            "model verification reached a limit");
            }
            throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                      "exact model failed verification");
          }
          stageVerifiedModel(*checked.model, candidate);
          break;
        }
        case CheckStatus::Ready:
        case CheckStatus::InternalError:
          throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                    "impossible final exact check status");
      }
    }

    const bool produced_conflict =
        context_.pending_clause_ &&
        context_.pending_clause_->state == PendingClauseState::CandidateConflict;
    const bool produced_model = context_.staged_model_.has_value();
    if (produced_conflict == produced_model)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "candidate published an invalid result shape");
    if (!popCandidate())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "exact core failed to pop to base checkpoint");
    return result(produced_conflict ? AdapterOutcome::ConflictPending
                                    : AdapterOutcome::ModelStaged,
                  candidate);
  }
  catch (const std::exception& failure)
  {
    /* One clause for all three of what used to be caught separately --
     * SolveContextFailure, NumberFailure and everything else -- because they
     * were three copies of one decision that had drifted: each tested its own
     * kind() for a resource limit, and each dropped that limit back to an
     * internal fault when the checkpoint pop that follows could not restore
     * the core. A core stopped by a budget is not Ready afterwards either, so
     * that pop is the same refusal counted twice. Nothing here is used again
     * -- `refusal` gives the context up -- so what this decides is only
     * whether the query comes back as a no-answer or as a fault of ours. */
    const bool popped = popCandidate();
    context_.clearSemanticState();
    if (!popped && !gaveUpOnABudget(failure))
    {
      context_.invalidate("candidate failure and checkpoint pop failed");
      return result(AdapterOutcome::InternalNoResult, candidate,
                    context_.failure_detail_);
    }
    return refusal(failure, candidate);
  }
  catch (...)
  {
    (void)popCandidate();
    context_.invalidate("unexpected complete-candidate failure");
    return result(AdapterOutcome::InternalNoResult, candidate,
                  context_.failure_detail_);
  }
}

void LraCandidateAdapter::copyVerifiedConflict(
    const Conflict& conflict, std::uint64_t candidate_serial)
{
  if (conflict.tag.generation != context_.core_->generation() ||
      conflict.tag.state_revision == 0 || conflict.terms.empty() ||
      context_.core_->status() != CheckStatus::Conflict)
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              "conflict witness is stale or non-final");
  const NumberLimits limits = context_.mapping_budget_.limits();
  const std::uint64_t conflict_terms =
      static_cast<std::uint64_t>(conflict.terms.size());
  if (conflict.terms.size() >
          std::vector<PendingSupportEvidence>().max_size() ||
      (conflict_terms != 0 &&
       conflict_terms > limits.maximum_allocation_bytes /
                            sizeof(PendingSupportEvidence)))
    throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                              "bridge conflict-support preflight failed");

  NumberOperationScope operation(context_.mapping_budget_);
  Conflict copied{conflict.tag, {}};
  copied.terms.reserve(conflict.terms.size());
  std::vector<PendingSupportEvidence> support;
  support.reserve(conflict.terms.size());
  std::set<OriginId> origins;
  for (const ConflictTerm& term : conflict.terms)
  {
    if (term.origin.solve_epoch != context_.solve_epoch_ ||
        term.bound.generation() != context_.core_->generation() ||
        term.weight.sign() <= 0 || !origins.insert(term.origin).second)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "conflict support has stale or duplicate data");
    const OriginMapEntry& origin = context_.originMap(term.origin);
    if (origin.core_generation != context_.core_->generation() ||
        !(origin.origin == term.origin) ||
        origin.core_atom.generation() != context_.core_->generation())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "conflict origin mapping is stale");

    if (origin.role == SolveOriginRole::ExistingLraLiteral)
    {
      const CoreComponentMapEntry& mapped =
          context_.componentMap(origin.registry_component);
      if (origin.core_atom != mapped.core_atom ||
          origin.relation != mapped.relation ||
          !((origin.positive ? mapped.positive_origin
                             : mapped.negative_origin) == term.origin))
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "ordinary origin mapping is inconsistent");
      const CandidateComponentSelection& selected = requireOne(
          context_.current_selection_,
          [&origin](const CandidateComponentSelection& selection) {
            return selection.component == origin.registry_component;
          },
          "selected conflict component");
      const SATSolver::Lit binding =
          context_.componentBinding(origin.registry_component);
      const SATSolver::Lit expected =
          SATSolver::mkLit(SATSolver::var(binding), !origin.positive);
      if (selected.positive != origin.positive ||
          !sameLiteral(selected.asserting_literal, expected))
        throw SolveContextFailure(
            SolveContextFailureKind::Invalid,
            "ordinary conflict origin was not selected by candidate");

      const RegistryComponent& component =
          context_.registryComponent(origin.registry_component);
      if (component.sources.empty() ||
          registeredRelation(component.relation) != origin.relation)
        throw SolveContextFailure(
            SolveContextFailureKind::Invalid,
            "conflict component ownership is incomplete");
      for (const RegistrySourceOwnership& source : component.sources)
      {
        if (!source.frame.valid() ||
            source.frame.domain != context_.registry_snapshot_.tag.domain ||
            source.source.IsNull())
          throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                    "component source ownership is stale");
        if (source.equality_group.valid())
        {
          const RegistryEqualityGroup& group =
              context_.registryEquality(source.equality_group);
          const bool less =
              group.less_equal_component == origin.registry_component;
          const bool greater =
              group.greater_equal_component == origin.registry_component;
          if (less == greater ||
              (less && source.equality_component !=
                           EqualityComponent::LessEqual) ||
              (greater && source.equality_component !=
                              EqualityComponent::GreaterEqual))
            throw SolveContextFailure(
                SolveContextFailureKind::Invalid,
                "equality-group component ownership is inconsistent");
        }
        else if (source.equality_component ==
                     EqualityComponent::LessEqual ||
                 source.equality_component ==
                     EqualityComponent::GreaterEqual)
        {
          throw SolveContextFailure(
              SolveContextFailureKind::Invalid,
              "equality component lost its source group");
        }
      }

      const RegistryRow& row = context_.registryRow(component.row);
      support.push_back(PendingSupportEvidence{
          term.origin, term.bound, origin.registry_component,
          origin.positive, expected, term.weight, component.threshold,
          row.terms});
    }
    copied.terms.push_back(
        ConflictTerm{term.origin, term.bound, term.weight});
  }

  PendingLraClause pending;
  pending.state = PendingClauseState::CandidateConflict;
  pending.solve_epoch = context_.solve_epoch_;
  pending.candidate_serial = candidate_serial;
  pending.final_verified = true;
  pending.verified_conflict = std::move(copied);
  pending.support = std::move(support);
  context_.staged_model_.reset();
  context_.pending_clause_ = std::move(pending);
}

void LraCandidateAdapter::stageVerifiedModel(
    const Model& model, std::uint64_t candidate_serial, bool core_derived)
{
  if (model.tag.generation != context_.core_->generation() ||
      model.tag.state_revision == 0 ||
      (core_derived &&
       context_.core_->status() != CheckStatus::Consistent) ||
      model.values.size() != context_.variable_map_.size())
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              "model witness is stale or incomplete");
  const NumberLimits limits = context_.mapping_budget_.limits();
  const std::uint64_t variable_count =
      static_cast<std::uint64_t>(context_.variable_map_.size());
  std::uint64_t model_copy_size = sizeof(StagedRealValue);
  if (context_.variable_map_.size() >
          std::vector<StagedRealValue>().max_size() ||
      (variable_count != 0 &&
       variable_count >
           limits.maximum_allocation_bytes / model_copy_size))
    throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                              "bridge model-copy preflight failed");

  const auto mapping_start = std::chrono::steady_clock::now();
  NumberOperationScope operation(context_.mapping_budget_);
  const LraModelIndex model_index(model.values, &ModelValue::variable, limits,
                                  "core model variable");
  const LraModelIndex symbol_index(context_.registry_snapshot_.symbols,
                                   &RegistrySymbol::id, limits,
                                   "registry symbol for staged model");
  StagedExactModel stage;
  stage.solve_epoch = context_.solve_epoch_;
  stage.candidate_serial = candidate_serial;
  stage.values.reserve(context_.variable_map_.size());
  std::set<VariableId> seen_core;
  std::set<LraRegistrySymbolId> seen_registry;
  for (const CoreVariableMapEntry& mapped : context_.variable_map_)
  {
    const ModelValue& value = model_index.at(mapped.core_variable);
    if (!seen_core.insert(value.variable).second ||
        value.variable.generation() != context_.core_->generation() ||
        !value.value.invariantHolds())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "model contains duplicate or invalid values");
    if (!mapped.registry_symbol.valid() ||
        !seen_registry.insert(mapped.registry_symbol).second)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "model registry-symbol role is invalid");
    const RegistrySymbol& symbol = symbol_index.at(mapped.registry_symbol);
    stage.values.push_back(StagedRealValue{mapped.registry_symbol,
                                           mapped.frontend_symbol,
                                           symbol.symbol,
                                           value.value,
                                           value.value.numeratorDecimal(),
                                           value.value.denominatorDecimal(),
                                           mapped.role});
  }
  std::sort(stage.values.begin(), stage.values.end(),
            [](const StagedRealValue& lhs, const StagedRealValue& rhs) {
              return lhs.frontend_symbol < rhs.frontend_symbol;
            });
  for (std::size_t i = 1; i < stage.values.size(); ++i)
    if (!(stage.values[i - 1].frontend_symbol <
          stage.values[i].frontend_symbol))
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "staged frontend symbols are not unique");


  context_.pending_clause_.reset();
  context_.staged_model_ = std::move(stage);
  addElapsed(context_.metrics_.model_mapping_nanoseconds, mapping_start);
  const auto evaluation_start = std::chrono::steady_clock::now();
  independentlyCheckStagedModel();
  addElapsed(context_.metrics_.model_evaluation_nanoseconds, evaluation_start);
  ++context_.metrics_.models_staged;
  context_.metrics_.model_values_staged +=
      static_cast<std::uint64_t>(context_.staged_model_->values.size());
}

void LraCandidateAdapter::independentlyCheckStagedModel() const
{
  if (!context_.staged_model_ ||
      context_.staged_model_->solve_epoch != context_.solve_epoch_ ||
      context_.staged_model_->candidate_serial !=
          context_.current_candidate_serial_)
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              "staged model tag is stale");

  NumberOperationScope operation(context_.mapping_budget_);
  std::map<LraRegistrySymbolId, const ExactRational*> values;
  for (const StagedRealValue& value : context_.staged_model_->values)
  {
    if (value.value.numeratorDecimal() != value.numerator_decimal ||
        value.value.denominatorDecimal() != value.denominator_decimal ||
        value.denominator_decimal.empty() ||
        value.denominator_decimal.front() == '-')
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "staged exact text/value ownership mismatch");
    const CoreVariableMapEntry& mapped =
        context_.variableMap(value.registry_symbol);
    if (mapped.role != value.role ||
        mapped.role == CoreVariableRole::BridgeBit ||
        mapped.frontend_symbol != value.frontend_symbol)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "staged exact variable role is inconsistent");
    if (!values.emplace(value.registry_symbol, &value.value).second)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "duplicate staged registry symbol");
  }

  std::map<LraCanonicalRowId, ExactRational> row_values;
  for (const RegistryRow& row : context_.registry_snapshot_.rows)
  {
    ExactRational sum(std::int64_t{0});
    LraSymbolId previous_frontend;
    for (const RegistryMonomial& term : row.terms)
    {
      const LraSymbolId frontend =
          context_.variableMap(term.symbol).frontend_symbol;
      if (previous_frontend.value != 0 &&
          !(previous_frontend < frontend))
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "frontend row terms are not canonically sorted");
      previous_frontend = frontend;
      const auto value = values.find(term.symbol);
      if (value == values.end())
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "staged model misses a row variable");
      sum += term.coefficient * *value->second;
    }
    row_values.emplace(row.id, std::move(sum));
  }

  // Every component with a SAT binding has to have been read. One the
  // Boolean formula never mentions has no binding and is not selected -- it
  // is registered, unasserted, and cannot reach a conflict -- so it is not
  // counted either.
  std::size_t bound_components = 0;
  for (const RegistryComponent& component :
       context_.registry_snapshot_.components)
    if (context_.componentBound(component.id))
      ++bound_components;
  if (context_.current_selection_.size() != bound_components)
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              "selected predicate coverage is incomplete");
  for (const RegistryComponent& component :
       context_.registry_snapshot_.components)
  {
    if (!context_.componentBound(component.id))
      continue;  // never mentioned, never selected, never asserted
    const auto row = row_values.find(component.row);
    if (row == row_values.end())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "staged model misses a canonical row");
    const CandidateComponentSelection& selected = requireIndexed(
        context_.current_selection_, context_.current_selection_index_,
        component.id, &CandidateComponentSelection::component,
        "selected predicate for staged model");
    const bool holds = relationHolds(
        row->second, context_.componentMap(component.id).relation,
        component.threshold);
    if (holds != selected.positive)
      throw SolveContextFailure(
          SolveContextFailureKind::Invalid,
          "independent frontend predicate evaluation rejected core model");
  }

}



// ---------------------------------------------------------------------------
// Theory propagation.
//
// The full-lazy path asserts a whole model, checks it, and throws the theory
// state away; the next candidate rebuilds all of it. Here the theory trail
// instead follows the SAT trail: a decision level opens a checkpoint, a
// backtrack pops to it, and each assignment asserts exactly one bound. Work
// is retracted only when the search actually retracts it.
//
// Nothing below may throw. These run inside CaDiCaL's search across a
// boundary that cannot unwind, so each entry point catches everything and
// reports through failed(); once that is set the rest go quiet and the
// coordinator discards the solve rather than trusting its verdict.
// ---------------------------------------------------------------------------

bool LraCandidateAdapter::failed() const
{
  return !context_.ready();
}

bool LraCandidateAdapter::beginTheoryPropagation(
    std::vector<uint32_t>& observed) noexcept
{
  context_.propagated_model_.reset();
  try
  {
    advice_source_ = AdviceSource::None;
    if (&solver_ != &context_.solver_ || !context_.ready() ||
        !context_.bindingsReady())
      return false;
    component_by_variable_.clear();
    level_checkpoints_.clear();
    pending_theory_clause_.clear();
    partial_checks_enabled_ = true;
    partial_checks_abandoned_ = 0;
    conflict_pending_ = false;
    observed.clear();
    observed.reserve(context_.registry_snapshot_.components.size());
    for (const RegistryComponent& component :
         context_.registry_snapshot_.components)
    {
      /* A component the Boolean formula never mentions has no SAT variable
       * to observe and is never assigned, so there is nothing for the theory
       * to be told about.  Demanding a binding here would refuse the whole
       * query -- the same mistake the full-lazy readers were fixed for. */
      if (!context_.componentBound(component.id))
        continue;
      const SATSolver::Lit binding = context_.componentBinding(component.id);
      const uint32_t variable = SATSolver::var(binding);
      if (!solver_.validVariable(variable))
        return false;
      // Two components sharing a SAT variable would make an assignment
      // ambiguous, and bindOpaqueAtoms has already refused duplicates.
      if (!component_by_variable_.emplace(variable, component.id).second)
        return false;
      observed.push_back(variable);
    }
    // The root level. Its checkpoint is opened by the first bound asserted
    // at it, like every other level.
    level_checkpoints_.emplace_back();
    propagating_ = true;
    return true;
  }
  catch (...)
  {
    return false;
  }
}

void LraCandidateAdapter::endTheoryPropagation() noexcept
{
  context_.propagated_model_.reset();
  advice_source_ = AdviceSource::None;
  // Disconnecting must release the root as well as decision levels.
  std::optional<Checkpoint> first;
  for (auto const& checkpoint : level_checkpoints_)
    if (checkpoint && (!first || checkpoint->depth < first->depth))
      first = checkpoint;
  if (first && context_.core_)
  {
    if (context_.core_->pop(*first) != InputStatus::Accepted)
      context_.invalidate("failed to release arithmetic trail on disconnect");
    else
      ++context_.metrics_.exact_pops;
  }
  propagating_ = false;
  component_by_variable_.clear();
  level_checkpoints_.clear();
  pending_theory_clause_.clear();
  conflict_pending_ = false;
}

/* Turn a verified conflict into the clause that forbids it: the support is a
 * set of asserting literals whose conjunction the theory refutes, so the
 * no-good is the disjunction of their negations. Same shape the full-lazy
 * path encodes, without the pending-clause staging, because here the backend
 * takes the clause directly. */
bool LraCandidateAdapter::stageTheoryConflict(const Conflict& conflict) noexcept
{
  try
  {
    return context_.verifyConflictChecked(conflict).verified() &&
           stageVerifiedTheoryConflict(conflict);
  }
  catch (...)
  {
    return false;
  }
}

bool LraCandidateAdapter::stageVerifiedTheoryConflict(
    const Conflict& conflict) noexcept
{
  context_.propagated_model_.reset();
  try
  {
    if (conflict.terms.empty())
      return false;
    std::vector<SATSolver::Lit> clause;
    clause.reserve(conflict.terms.size());
    std::set<OriginId> seen;
    for (const ConflictTerm& term : conflict.terms)
    {
      if (term.origin.solve_epoch != context_.solve_epoch_ ||
          !seen.insert(term.origin).second)
        return false;
      const OriginMapEntry& origin = context_.originMap(term.origin);
      if (origin.core_generation != context_.core_->generation())
        return false;
      const SATSolver::Lit binding =
          context_.componentBinding(origin.registry_component);
      // The asserting literal is the one whose truth put this bound in; the
      // clause carries its negation.
      SATSolver::Lit negated =
          SATSolver::mkLit(SATSolver::var(binding), origin.positive);
      clause.push_back(negated);
    }
    if (clause.empty())
      return false;
    pending_theory_clause_ = std::move(clause);
    conflict_pending_ = true;
    ++context_.metrics_.tableau_conflicts;
    return true;
  }
  catch (...)
  {
    return false;
  }
}

bool LraCandidateAdapter::ensureLevelCheckpoint() noexcept
{
  try
  {
    if (level_checkpoints_.empty())
      level_checkpoints_.emplace_back();
    if (level_checkpoints_.back())
      return true;
    const InputResult<Checkpoint> pushed = context_.core_->push();
    if (pushed.status != InputStatus::Accepted || !pushed.value)
    {
      context_.invalidate("theory push failed opening a level");
      return false;
    }
    level_checkpoints_.back() = *pushed.value;
    ++context_.metrics_.exact_pushes;
    return true;
  }
  catch (...)
  {
    context_.invalidate("unexpected failure opening a theory level");
    return false;
  }
}

bool LraCandidateAdapter::assertOneLiteral(SATSolver::Lit literal) noexcept
{
  try
  {
    const auto found = component_by_variable_.find(SATSolver::var(literal));
    if (found == component_by_variable_.end())
      return true;  // not an LRA atom; nothing to assert
    advice_source_ = AdviceSource::None;
    const CoreComponentMapEntry& mapped = context_.componentMap(found->second);
    if (!ensureLevelCheckpoint())
      return false;
    const bool positive = !SATSolver::sign(literal);
    const AssertResult asserted =
        context_.core_->assertLiteral(mapped.core_atom, positive);
    ++context_.metrics_.exact_assertions;
    if (asserted.status == InputStatus::ResourceLimit)
    {
      context_.invalidate("exact assertion reached a resource limit");
      return false;
    }
    if (asserted.status != InputStatus::Accepted)
    {
      context_.invalidate("exact literal assertion was not accepted");
      return false;
    }
    if (!asserted.immediate_conflict)
    {
      theory_dirty_ = true;
      return true;
    }
    // An eager conflict, on a partial assignment. This is the pruning the
    // full-lazy loop never gets to do.
    if (!stageTheoryConflict(*asserted.immediate_conflict))
    {
      context_.invalidate("immediate theory conflict failed verification");
      return false;
    }
    ++context_.metrics_.immediate_conflicts;
    return true;
  }
  catch (...)
  {
    context_.invalidate("unexpected failure asserting a theory literal");
    return false;
  }
}

void LraCandidateAdapter::notifyAssigned(
    const std::vector<SATSolver::Lit>& literals)
{
  if (literals.empty())
    return;
  context_.propagated_model_.reset();
  if (!propagating_ || failed() || conflict_pending_)
    return;
  if (pastTimeLimit())
    return;
  for (SATSolver::Lit literal : literals)
  {
    if (!assertOneLiteral(literal) || conflict_pending_)
      return;
  }
}

void LraCandidateAdapter::notifyNewLevel()
{
  context_.propagated_model_.reset();
  if (!propagating_ || failed())
    return;
  // The core checkpoint waits for the first bound asserted here.
  level_checkpoints_.emplace_back();
}

void LraCandidateAdapter::notifyBacktrack(size_t level)
{
  // Backends can unwind after accepting a model but before returning SAT.
  // Its owned witness survives this cleanup; new search activity and the
  // next beforeSolverCall discard it, and publication checks the SAT model.
  // Assignments persist across pops, including failed repair attempts.
  // Wait for an existing partial check to establish feasibility again.
  advice_source_ = AdviceSource::None;
  pending_theory_clause_.clear();
  conflict_pending_ = false;
  theory_dirty_ = false;
  if (!propagating_ || failed())
    return;
  try
  {
    // level_checkpoints_[0] is the root, so decision level n keeps n+1
    // entries. Pop the ones the search has just abandoned.
    while (level_checkpoints_.size() > level + 1)
    {
      const std::optional<Checkpoint> checkpoint = level_checkpoints_.back();
      level_checkpoints_.pop_back();
      if (!checkpoint)
        continue;  // nothing was asserted at this level
      if (context_.core_->pop(*checkpoint) != InputStatus::Accepted)
      {
        context_.invalidate("theory pop failed on backtrack");
        return;
      }
      ++context_.metrics_.exact_pops;
    }
  }
  catch (...)
  {
    context_.invalidate("unexpected failure backtracking the theory");
  }
}

bool LraCandidateAdapter::takeClause(std::vector<SATSolver::Lit>& clause)
{
  // The backend polls for a clause after every round of propagation, before
  // it decides again: the moment to ask the tableau whether the bounds
  // asserted so far are feasible together. An immediate conflict catches two
  // bounds on one variable; this catches a Farkas combination across rows,
  // with the partial assignment still small, and hands it back as a clause
  // before the search has committed to a whole model on top of it.
  checkPartialAssignment();
  if (!conflict_pending_ || pending_theory_clause_.empty())
    return false;
  clause = pending_theory_clause_;
  pending_theory_clause_.clear();
  conflict_pending_ = false;
  ++context_.metrics_.clauses_inserted;
  return true;
}

void LraCandidateAdapter::checkPartialAssignment() noexcept
{
  if (!propagating_ || failed() || conflict_pending_ || !theory_dirty_ ||
      !partial_checks_enabled_ || pastTimeLimit())
    return;
  theory_dirty_ = false;
  try
  {
    constexpr unsigned kAbandonedBeforeOff = 2;
    context_.observer_.beginCheck(true);
    const CheckResult checked =
        context_.core_->check(context_.observer_, /*verify_model=*/false);
    context_.observer_.beginCheck(false);
    if (checked.status == CheckStatus::Interrupted &&
        context_.observer_.guardStopped())
    {
      ++context_.metrics_.partial_checks_abandoned;
      if (++partial_checks_abandoned_ >= kAbandonedBeforeOff)
      {
        partial_checks_enabled_ = false;
        ++context_.metrics_.partial_checks_disabled;
      }
      return;
    }
    if (context_.observer_.guardedRateExceeded())
    {
      partial_checks_enabled_ = false;
      ++context_.metrics_.partial_checks_disabled;
    }
    if (checked.status == CheckStatus::Conflict && checked.conflict)
    {
      if (!stageTheoryConflict(*checked.conflict))
        context_.invalidate("partial theory conflict failed verification");
      else
        ++context_.metrics_.partial_conflicts;
    }
    else if (checked.status == CheckStatus::Consistent)
      advice_source_ = AdviceSource::Exact;
  }
  catch (...)
  {
    context_.observer_.beginCheck(false);
    context_.invalidate("unexpected failure checking a partial assignment");
  }
}

bool LraCandidateAdapter::decisionPolarity(uint32_t variable, bool& value) noexcept
{
  if (!decision_polarity_)
    return false;
  ++context_.metrics_.polarity_queries;
  try
  {
    if (propagating_ && context_.ready() && !conflict_pending_ && !theory_dirty_ &&
        advice_source_ != AdviceSource::None && !solver_.timeLimitExpired())
    {
      auto found = component_by_variable_.find(variable);
      if (found != component_by_variable_.end())
      {
        auto const& mapped = context_.componentMap(found->second);
        std::optional<bool> advice;
        if (advice_source_ == AdviceSource::Exact)
          advice = context_.core_->preferredPolarity(mapped.core_atom);
        if (advice)
        {
          ++context_.metrics_.polarity_advice;
          if (value != *advice)
            ++context_.metrics_.polarity_changes;
          ++context_.metrics_.polarity_exact;
          value = *advice;
          return true;
        }
      }
    }
  }
  catch (...)
  {
    // This callback supplies no clauses or assignments. A failed lookup or
    // exhausted arithmetic hint budget leaves the backend's choice intact.
  }
  ++context_.metrics_.polarity_abstentions;
  return false;
}

// The backend polls its terminator between its own steps, not inside a
// callback; a long stretch of theory work after the deadline would run to
// its end. Each callback looks itself, and once the limit has passed it
// asks the observer to interrupt the next check and does nothing more, so
// that the solve reports a timeout rather than an answer it kept computing.
bool LraCandidateAdapter::pastTimeLimit() noexcept
{
  if (!deadline_interrupted_ && !solver_.timeLimitExpired())
    return false;
  deadline_interrupted_ = true;
  context_.requestInterrupt();
  return true;
}

bool LraCandidateAdapter::retainPropagatedModel(Model witness)
{
  const std::uint64_t candidate = context_.allocateCandidateSerial();
  context_.current_candidate_serial_ = candidate;
  context_.propagated_model_ = LraSolveContext::PropagatedModel{
      context_.solve_epoch_, candidate, std::move(witness)};
  return true;
}

bool LraCandidateAdapter::checkFoundModel()
{
  context_.propagated_model_.reset();
  if (!propagating_ || failed())
    return true;  // the caller discards a failed solve; do not stall here
  if (pastTimeLimit())
    return true;  // accepted only to end search; publication reports timeout
  try
  {
    ++context_.metrics_.candidates_started;
    /* Everything observed is assigned, so the bounds are already in. This is
     * the final exact check, and the only place a model is accepted. */
    if (!ensureLevelCheckpoint())
      return true;
    CheckResult checked = context_.core_->check(context_.observer_);
    if (checked.status == CheckStatus::Consistent && checked.model)
      return retainPropagatedModel(std::move(*checked.model));
    if (checked.status == CheckStatus::Conflict && checked.conflict)
    {
      if (!stageTheoryConflict(*checked.conflict))
      {
        context_.invalidate("final theory conflict failed verification");
        return true;
      }
      return false;  // rejected; the clause follows
    }
    if (checked.status == CheckStatus::Interrupted && pastTimeLimit())
      return true;
    context_.invalidate(
        "exact check produced no usable verdict: status=" +
        std::to_string(static_cast<int>(checked.status)) +
        " core_status=" +
        std::to_string(static_cast<int>(context_.core_->status())) +
        " levels=" + std::to_string(level_checkpoints_.size()));
    return true;
  }
  catch (const std::exception& failure)
  {
    (void)refusal(failure, context_.current_candidate_serial_);
    return true;
  }
  catch (...)
  {
    context_.invalidate("unexpected failure checking a found model");
    return true;
  }
}

AdapterResult LraCandidateAdapter::acceptPropagatedModel() noexcept
{
  const std::uint64_t candidate = context_.current_candidate_serial_;
  try
  {
    if (!propagating_ || failed())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "no live theory propagation to accept from");
    // Deadline callbacks may accept solely to end the search. No witness
    // from an earlier callback can authorize publication after that stop.
    if (pastTimeLimit())
    {
      context_.clearSemanticState();
      return result(AdapterOutcome::Interrupted, candidate,
                    "theory propagation reached the query deadline");
    }
    if (!context_.propagated_model_ || candidate == 0 ||
        context_.propagated_model_->solve_epoch != context_.solve_epoch_ ||
        context_.propagated_model_->candidate_serial != candidate)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "no current certified propagated model");
    Model witness = std::move(context_.propagated_model_->witness);
    context_.propagated_model_.reset();
    // The backend may have unwound the arithmetic trail after accepting the
    // callback. The owned witness remains valid; the independent predicate
    // evaluation in staging checks it against the actual returned SAT model.
    readSelectionFromSolver(/*verify_stable=*/false);
    stageVerifiedModel(witness, candidate, /*core_derived=*/false);
    return result(AdapterOutcome::ModelStaged, candidate);
  }
  catch (const std::exception& failure)
  {
    return refusal(failure, candidate);
  }
  catch (...)
  {
    context_.invalidate("unexpected propagated-model acceptance failure");
    return result(AdapterOutcome::InternalNoResult, candidate,
                  context_.failure_detail_);
  }
}

AdapterResult LraCandidateAdapter::emitBoundOrderingAxioms() noexcept
{
  const std::uint64_t candidate = context_.current_candidate_serial_;
  try
  {
    if (&solver_ != &context_.solver_ || !context_.ready() ||
        !context_.bindingsReady())
      throw SolveContextFailure(
          SolveContextFailureKind::Invalid,
          "bound ordering axioms require current complete bindings");
    if (!solver_.okay())
      return result(AdapterOutcome::ClauseInserted, candidate);

    /* Every LRA atom on a canonical row r is a half-line, and each one can be
     * written as an *upper* half-line by flipping its literal where the
     * relation is a lower bound: not(r > t) is r <= t, and not(r >= t) is
     * r < t.  A whole row therefore reduces to one totally ordered family of
     * "r is at most this" literals, and once they are sorted every implication
     * between two atoms of the row is either adjacent or carried by unit
     * propagation along the adjacent chain.  That is O(k) binary clauses per
     * row instead of the O(k^2) pairwise encoding.
     *
     * Stating them up front is what the full-lazy loop needs.  Nothing else
     * tells the SAT solver that r <= 3 rules out r >= 5, so without these it
     * hands over complete models that differ only in already-implied atoms and
     * pays a full simplex check to reject each one. */
    struct HalfLine final
    {
      SATSolver::Lit literal;        // true exactly when r is at most bound
      const ExactRational* bound;
      bool closed;                   // r <= bound rather than r < bound
    };

    NumberOperationScope operation(context_.mapping_budget_);
    std::map<LraCanonicalRowId, std::vector<HalfLine>> rows;
    for (const RegistryComponent& component :
         context_.registry_snapshot_.components)
    {
      if (!context_.componentBound(component.id))
        continue;
      const SATSolver::Lit binding = context_.componentBinding(component.id);
      if (!solver_.validVariable(SATSolver::var(binding)))
        throw SolveContextFailure(
            SolveContextFailureKind::Invalid,
            "ordering axiom component binding is out of range");
      HalfLine entry{binding, &component.threshold, false};
      switch (component.relation)
      {
        case FrontendRelation::Less:
          break;
        case FrontendRelation::LessEqual:
          entry.closed = true;
          break;
        case FrontendRelation::Greater:
          entry.literal.x ^= 1U;
          entry.closed = true;
          break;
        case FrontendRelation::GreaterEqual:
          entry.literal.x ^= 1U;
          break;
        case FrontendRelation::Equal:
          throw SolveContextFailure(
              SolveContextFailureKind::Invalid,
              "equality relation reached the bound ordering axioms");
      }
      rows[component.row].push_back(entry);
    }

    // At a shared bound the strict claim is the tighter one: r < t entails
    // r <= t, never the reverse.
    const auto tighter = [](const HalfLine& lhs, const HalfLine& rhs) {
      const int order = lhs.bound->compare(*rhs.bound);
      if (order != 0)
        return order < 0;
      return !lhs.closed && rhs.closed;
    };

    const auto addImplication = [&](SATSolver::Lit antecedent,
                                    SATSolver::Lit consequent) {
      SATSolver::vec_literals clause;
      SATSolver::Lit negated = antecedent;
      negated.x ^= 1U;
      clause.push(negated);
      clause.push(consequent);
      const std::uint64_t before = solver_.submittedClauses();
      const bool accepted = solver_.addClause(clause);
      if (before == std::numeric_limits<std::uint64_t>::max() ||
          solver_.submittedClauses() != before + 1)
        throw SolveContextFailure(
            SolveContextFailureKind::Invalid,
            "common SAT clause accounting is inconsistent");
      if (!accepted)
        throw SolveContextFailure(
            SolveContextFailureKind::Invalid,
            "common SAT addClause rejected a bound ordering axiom");
      if (!solver_.okay())
        throw SolveContextFailure(
            SolveContextFailureKind::Invalid,
            "SAT solver became not-okay after a bound ordering axiom");
      ++context_.metrics_.ordering_axioms;
    };

    const auto emitChain = [&](std::vector<HalfLine>& entries) {
      if (entries.size() < 2)
        return;
      std::sort(entries.begin(), entries.end(), tighter);
      for (std::size_t i = 1; i < entries.size(); ++i)
      {
        const HalfLine& stronger = entries[i - 1];
        const HalfLine& weaker = entries[i];
        /* Distinct components own distinct opaque atoms, and bindOpaqueAtoms
         * has already refused duplicates, so two entries of one row sharing a
         * SAT variable means the mapping is corrupt.  Emitting anyway could
         * turn a tautology into a unit clause, so fail closed instead. */
        if (SATSolver::var(stronger.literal) == SATSolver::var(weaker.literal))
          throw SolveContextFailure(
              SolveContextFailureKind::Invalid,
              "two ordering axiom entries share a SAT variable");
        addImplication(stronger.literal, weaker.literal);
        // Two atoms denoting the very same half-line are equivalent, and the
        // converse has to be said explicitly -- this is what ties r <= t to
        // the complement of r > t.
        if (stronger.bound->compare(*weaker.bound) == 0 &&
            stronger.closed == weaker.closed)
          addImplication(weaker.literal, stronger.literal);
      }
    };
    for (auto& row : rows)
      emitChain(row.second);
    return result(AdapterOutcome::ClauseInserted, candidate);
  }
  catch (const std::exception& failure)
  {
    return refusal(failure, candidate);
  }
  catch (...)
  {
    context_.invalidate("unexpected bound ordering axiom failure");
    return result(AdapterOutcome::InternalNoResult, candidate,
                  context_.failure_detail_);
  }
}

AdapterResult LraCandidateAdapter::encodeAndInsertPendingClause() noexcept
{
  const std::uint64_t candidate = context_.current_candidate_serial_;
  try
  {
    if (&solver_ != &context_.solver_ || !context_.validateCurrentState() ||
        !context_.pending_clause_ ||
        context_.pending_clause_->state !=
            PendingClauseState::CandidateConflict)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "no current candidate conflict to encode");
    PendingLraClause& pending = *context_.pending_clause_;
    if (!pending.final_verified ||
        pending.solve_epoch != context_.solve_epoch_ ||
        pending.candidate_serial != candidate ||
        pending.verified_conflict.tag.generation !=
            context_.core_->generation() ||
        pending.verified_conflict.terms.empty() || pending.support.empty())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "pending conflict tag or support is invalid");
    if (!solver_.okay())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "SAT solver is not okay before clause insertion");

    struct Resolved final
    {
      LraComponentId component;
      bool positive;
      SATSolver::Lit literal;
      bool consumed = false;
    };
    std::vector<Resolved> resolved;
    resolved.reserve(pending.support.size());
    std::set<BoundRef> covered_bounds;
    for (const PendingSupportEvidence& evidence : pending.support)
    {
      const OriginMapEntry& origin = context_.originMap(evidence.origin);
      if (!(origin.origin == evidence.origin) ||
          origin.role != evidence.role ||
          origin.core_generation != context_.core_->generation() ||
          evidence.origin.solve_epoch != context_.solve_epoch_ ||
          evidence.bound.generation() != context_.core_->generation() ||
          evidence.weight.sign() <= 0)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "pending conflict support mapping is corrupt");

      if (evidence.role == SolveOriginRole::ExistingLraLiteral)
      {
        const RegistryComponent& component =
            context_.registryComponent(evidence.component);
        const RegistryRow& row = context_.registryRow(component.row);
        const CandidateComponentSelection& selected = requireOne(
            context_.current_selection_,
            [&evidence](const CandidateComponentSelection& selection) {
              return selection.component == evidence.component;
            },
            "current selected conflict component");
        const SATSolver::Lit binding =
            context_.componentBinding(evidence.component);
        const SATSolver::Lit expected = SATSolver::mkLit(
            SATSolver::var(binding), !evidence.positive);
        if (origin.registry_component != evidence.component ||
            origin.positive != evidence.positive ||
            origin.relation !=
                context_.componentMap(evidence.component).relation ||
            evidence.threshold != component.threshold ||
            evidence.row_terms.size() != row.terms.size() ||
            selected.positive != evidence.positive ||
            !sameLiteral(selected.asserting_literal, expected) ||
            !sameLiteral(evidence.asserting_literal, expected) ||
            !solver_.validVariable(SATSolver::var(expected)))
          throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                    "ordinary pending support is corrupt");
        for (std::size_t i = 0; i < row.terms.size(); ++i)
          if (evidence.row_terms[i].symbol != row.terms[i].symbol ||
              evidence.row_terms[i].coefficient != row.terms[i].coefficient)
            throw SolveContextFailure(
                SolveContextFailureKind::Invalid,
                "pending ordinary exact row evidence is corrupt");
        resolved.push_back(
            Resolved{evidence.component, evidence.positive, expected, false});
      }

      bool matched_conflict_term = false;
      for (const ConflictTerm& term : pending.verified_conflict.terms)
      {
        if (term.origin == evidence.origin && term.bound == evidence.bound &&
            term.weight == evidence.weight)
        {
          matched_conflict_term = true;
          covered_bounds.insert(term.bound);
          break;
        }
      }
      if (!matched_conflict_term)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "support is absent from verified conflict");
    }
    if (covered_bounds.size() != pending.verified_conflict.terms.size())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "verified conflict support coverage is incomplete");

    std::vector<SATSolver::Lit> active_support;
    active_support.reserve(resolved.size());
    // E's current checked definition proves both positive components whenever
    // E is selected.  Thus each positive equality-origin support may use the
    // actual source E literal; if both components occur they collapse to the
    // same literal below. Every false-equality branch remains the actual
    // signed component literal because !E does not choose which branch fails.
    for (const RegistryEqualityGroup& equality :
         context_.registry_snapshot_.equalities)
    {
      std::vector<std::size_t> less_indexes;
      std::vector<std::size_t> greater_indexes;
      for (std::size_t i = 0; i < resolved.size(); ++i)
      {
        if (resolved[i].consumed || !resolved[i].positive)
          continue;
        if (resolved[i].component == equality.less_equal_component)
          less_indexes.push_back(i);
        if (resolved[i].component == equality.greater_equal_component)
          greater_indexes.push_back(i);
      }
      if (less_indexes.empty() && greater_indexes.empty())
        continue;
      /* A group the formula never mentioned has no SAT literal to compress
       * onto, and no selection to read. */
      if (!context_.equalityBound(equality.id) ||
          !context_.componentBound(equality.less_equal_component) ||
          !context_.componentBound(equality.greater_equal_component))
        continue;
      const CandidateEqualitySelection& source = requireOne(
          context_.current_equalities_,
          [&equality](const CandidateEqualitySelection& selection) {
            return selection.group == equality.id;
          },
          "equality source for support compression");
      const CandidateComponentSelection& less = requireOne(
          context_.current_selection_,
          [&equality](const CandidateComponentSelection& selection) {
            return selection.component == equality.less_equal_component;
          },
          "less-equal component for support compression");
      const CandidateComponentSelection& greater = requireOne(
          context_.current_selection_,
          [&equality](const CandidateComponentSelection& selection) {
            return selection.component == equality.greater_equal_component;
          },
          "greater-equal component for support compression");
      /* Compression is sound only when E's definition proves both
       * components -- E holds exactly when both do. One component true and
       * the other false makes E false, and substituting its literal would
       * then claim something the candidate does not support.
       *
       * That is a reason to leave the support alone, not to fail: the
       * uncompressed literals are the Farkas support itself and are always
       * a valid no-good. Compression only ever makes that clause shorter. */
      if (!source.equality_value || !less.positive || !greater.positive)
        continue;
      const SATSolver::Lit equality_binding =
          context_.equalityBinding(equality.id);
      const SATSolver::Lit equality_literal =
          SATSolver::mkLit(SATSolver::var(equality_binding), false);
      if (!sameLiteral(source.equality_literal, equality_literal))
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "source equality literal mapping is stale");
      for (std::size_t index : less_indexes)
        resolved[index].consumed = true;
      for (std::size_t index : greater_indexes)
        resolved[index].consumed = true;
      active_support.push_back(equality_literal);
    }
    for (const Resolved& entry : resolved)
      if (!entry.consumed)
        active_support.push_back(entry.literal);
    if (active_support.empty())
      throw SolveContextFailure(
          SolveContextFailureKind::Invalid,
          "verified conflict contains only bridge definitions/constant axioms");

    std::sort(active_support.begin(), active_support.end(),
              [](SATSolver::Lit lhs, SATSolver::Lit rhs) {
                return lhs.x < rhs.x;
              });
    active_support.erase(
        std::unique(active_support.begin(), active_support.end(), sameLiteral),
        active_support.end());
    for (std::size_t i = 1; i < active_support.size(); ++i)
      if (SATSolver::var(active_support[i - 1]) ==
              SATSolver::var(active_support[i]) &&
          SATSolver::sign(active_support[i - 1]) !=
              SATSolver::sign(active_support[i]))
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "LRA conflict support is tautological");

    SATSolver::vec_literals clause;
    std::vector<SATSolver::Lit> copied_clause;
    copied_clause.reserve(active_support.size());
    for (SATSolver::Lit selected : active_support)
    {
      if (!solver_.validVariable(SATSolver::var(selected)))
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "selected support literal is out of range");
      SATSolver::Lit negated = selected;
      negated.x ^= 1U;
      clause.push(negated);
      copied_clause.push_back(negated);
    }
    pending.encoded_clause = copied_clause;
    ++context_.metrics_.clauses_encoded;
    context_.staged_model_.reset();

    const std::uint64_t before = solver_.submittedClauses();
    const bool accepted = solver_.addClause(clause);
    const bool okay_after = solver_.okay();
    if (before == std::numeric_limits<std::uint64_t>::max() ||
        solver_.submittedClauses() != before + 1)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "common SAT clause accounting is inconsistent");
    if (!accepted)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "common SAT addClause rejected the no-good");
    if (!okay_after)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "SAT solver became not-okay after addClause");

    pending.state = PendingClauseState::ClauseEncoded;
    ++context_.metrics_.clauses_inserted;
    return result(AdapterOutcome::ClauseInserted, candidate);
  }
  catch (const std::exception& failure)
  {
    return refusal(failure, candidate);
  }
  catch (...)
  {
    context_.invalidate("unexpected LRA clause encoding failure");
    return result(AdapterOutcome::InternalNoResult, candidate,
                  context_.failure_detail_);
  }
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
bool LraCandidateAdapter::testValidateStagedModel() noexcept
{
  try
  {
    independentlyCheckStagedModel();
    return true;
  }
  catch (const std::exception& failure)
  {
    context_.invalidate(failure.what());
    return false;
  }
  catch (...)
  {
    context_.invalidate("unexpected staged-model test validation failure");
    return false;
  }
}
#endif

} // namespace stp::lra

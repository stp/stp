#include "LraCandidateAdapter.h"
#include "LraBudgetRefusal.h"
#include "LraModelIndex.h"

#include "ExactLraVerificationData.h"
#include "FloatSimplex.h"
#include "PortableBits.h"

#include <algorithm>
#include <chrono>
#include <cmath>
#include <limits>
#include <map>
#include <new>
#include <optional>
#include <set>
#include <sstream>
#include <utility>

namespace stp::lra {

namespace
{
/* A double is a dyadic rational; this is its exact value, no rounding.
 * mantissa * 2^exponent, with the power applied in word-sized chunks so
 * the intermediate stays a plain rational under the caller's scope. */
ExactRational exactOfDouble(double value)
{
  int exponent = 0;
  double const fraction = std::frexp(value, &exponent);
  auto const mantissa =
      static_cast<std::int64_t>(std::ldexp(fraction, 53));
  exponent -= 53;
  ExactRational result(mantissa);
  ExactRational const chunk(std::int64_t{1} << 62);
  while (exponent >= 62)
  {
    result *= chunk;
    exponent -= 62;
  }
  if (exponent > 0)
    result *= ExactRational(std::int64_t{1} << exponent);
  while (exponent <= -62)
  {
    result /= chunk;
    exponent += 62;
  }
  if (exponent < 0)
    result /= ExactRational(std::int64_t{1} << -exponent);
  return result;
}

/* The nearest small rational to the double, by continued fractions.  The
 * true Farkas weights of small-coefficient problems are small rationals
 * -- pivot ratios like a third -- that a double only approximates, and
 * the exact combination needs the true value to cancel; reconstruction
 * recovers it whenever the approximation is within rounding of a
 * rational with a modest denominator.  A weight that is exactly dyadic
 * reconstructs to itself, and anything that fails the round-trip test
 * falls back to the exact dyadic value (whose certificate then simply
 * fails verification, as before). */
ExactRational rationalOfDouble(double value)
{
  double x = value;
  std::int64_t p0 = 0;
  std::int64_t q0 = 1;
  std::int64_t p1 = 1;
  std::int64_t q1 = 0;
  for (int iteration = 0; iteration < 40; ++iteration)
  {
    double const floor_x = std::floor(x);
    if (!(floor_x >= -9.0e15 && floor_x <= 9.0e15))
      break;
    auto const a = static_cast<std::int64_t>(floor_x);
    std::int64_t scaled_p = 0;
    std::int64_t scaled_q = 0;
    std::int64_t p2 = 0;
    std::int64_t q2 = 0;
    if (multiplyOverflows(a, p1, &scaled_p) ||
        multiplyOverflows(a, q1, &scaled_q) ||
        addOverflows(scaled_p, p0, &p2) ||
        addOverflows(scaled_q, q0, &q2))
      break;
    p0 = p1;
    q0 = q1;
    p1 = p2;
    q1 = q2;
    if (q1 != 0)
    {
      double const approximation =
          static_cast<double>(p1) / static_cast<double>(q1);
      /* The snap tolerance absorbs pivot drift, not just rounding: a
       * coefficient that is one in truth arrives as 1 - 2^-42 after a
       * long substitution history, and at a tighter tolerance every
       * such certificate fell through to its dyadic value and was
       * rejected as not contradictory -- ten percent of the conflicts on
       * tta_startup, each paying a full exact replay.  A wrong snap is
       * harmless: the exact verifier rejects it, as it did the dyadic. */
      if (std::fabs(approximation - value) <=
          std::fabs(value) * 1.0e-9)
      {
        if (q1 < 0)
        {
          p1 = -p1;
          q1 = -q1;
        }
        return ExactRational(p1, static_cast<std::uint64_t>(q1));
      }
    }
    double const remainder = x - floor_x;
    if (remainder < 1.0e-12)
      break;
    x = 1.0 / remainder;
  }
  return exactOfDouble(value);
}
}  // namespace

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

    /* The float engine first, as a scratch candidate: certificate or
     * refined model, exactly verified either way, and the exact core's
     * driver untouched.  Any shortfall falls through to the exact path
     * below unchanged. */
    {
      AdapterResult float_result;
      if (floatCompleteCandidate(candidate, float_result))
        return float_result;
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
    const Conflict& conflict, std::uint64_t candidate_serial,
    bool core_derived)
{
  if (conflict.tag.generation != context_.core_->generation() ||
      conflict.tag.state_revision == 0 || conflict.terms.empty() ||
      (core_derived &&
       context_.core_->status() != CheckStatus::Conflict))
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
    float_checks_degraded_ = false;
    float_restarts_ = 0;
    float_promotions_ = 0;
    conflict_pending_ = false;
    float_level_marks_.clear();
    sync_batches_.clear();
    unwind_low_level_ = static_cast<std::size_t>(-1);
    if (context_.floatActive())
      context_.float_core_->undoTo(0);
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
    float_level_marks_.emplace_back();
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
  for (auto const& batch : sync_batches_)
    if (!first || batch.checkpoint.depth < first->depth)
      first = batch.checkpoint;
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
  float_level_marks_.clear();
  sync_batches_.clear();
  unwind_low_level_ = static_cast<std::size_t>(-1);
  if (context_.floatActive())
    context_.float_core_->undoTo(0);
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
    /* Dispatch before the exact level is opened: the advisory tier keeps
     * its own trail marks, and an exact level opened here would never be
     * popped by the float-mode backtrack path. */
    if (context_.floatActive())
      return assertOneLiteralFloat(literal, mapped);
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

bool LraCandidateAdapter::ensureFloatLevelMark() noexcept
{
  try
  {
    if (float_level_marks_.empty())
      float_level_marks_.emplace_back();
    if (float_level_marks_.back())
      return true;
    float_level_marks_.back() = context_.float_core_->mark();
    return true;
  }
  catch (...)
  {
    context_.invalidate("unexpected failure marking a float level");
    return false;
  }
}

bool LraCandidateAdapter::unwindDeadBatches(std::size_t level) noexcept
{
  if (sync_batches_.empty() || sync_batches_.back().level <= level)
    return true;
  try
  {
    Checkpoint deepest = sync_batches_.back().checkpoint;
    while (!sync_batches_.empty() && sync_batches_.back().level > level)
    {
      deepest = sync_batches_.back().checkpoint;
      sync_batches_.pop_back();
    }
    if (context_.core_->pop(deepest) != InputStatus::Accepted)
    {
      context_.invalidate("dead batch unwind failed to pop");
      return false;
    }
    ++context_.metrics_.exact_pops;
    return true;
  }
  catch (...)
  {
    context_.invalidate("unexpected failure unwinding dead batches");
    return false;
  }
}

namespace
{
class ModelRefinementObserver final : public ExactLraResourceObserver
{
 public:
  explicit ModelRefinementObserver(ExactLraResourceObserver& observer)
      : observer_(observer)
  {}
  StopReason pollBeforePivot() noexcept override
  {
    if (stop_ == StopReason::Continue)
      stop_ = observer_.pollBeforePivot();
    return stop_;
  }
  void accountPivot(bool bland) noexcept override
  {
    observer_.accountPivot(bland);
  }
  StopReason stop() const noexcept { return stop_; }

 private:
  ExactLraResourceObserver& observer_;
  StopReason stop_ = StopReason::Continue;
};
}  // namespace

LraCandidateAdapter::ModelRefinement
LraCandidateAdapter::refineAndCertifyModel() noexcept
{
  ModelRefinementObserver observer(context_.observer_);
  try
  {
    if (observer.pollBeforePivot() != StopReason::Continue)
      return {std::nullopt, observer.stop()};
    const std::size_t base_count = context_.registry_snapshot_.symbols.size();
    if (context_.variable_map_.size() != base_count)
      return {};
    std::vector<ModelCandidateValue> values;
    {
      NumberOperationScope operation(context_.mapping_budget_);
      values.reserve(base_count);
      for (std::size_t i = 0; i < base_count; ++i)
      {
        if (i % 256 == 0 && observer.pollBeforePivot() != StopReason::Continue)
          return {std::nullopt, observer.stop()};
        const FloatSimplex::DVal assignment =
            context_.float_core_->assignmentOf(
                context_.variable_map_[i].float_variable);
        if (!std::isfinite(assignment.value) ||
            !std::isfinite(assignment.delta))
          return {};
        values.push_back(
            ModelCandidateValue{context_.variable_map_[i].core_variable,
                                rationalOfDouble(assignment.value),
                                rationalOfDouble(assignment.delta)});
      }
    }
    const std::vector<FloatSimplex::TrailEntry>& trail =
        context_.float_core_->trail();
    std::vector<CandidateBound> bounds;
    bounds.reserve(trail.size());
    for (const FloatSimplex::TrailEntry& entry : trail)
    {
      if (bounds.size() % 256 == 0 &&
          observer.pollBeforePivot() != StopReason::Continue)
        return {std::nullopt, observer.stop()};
      bounds.push_back(CandidateBound{
          context_.float_atom_core_atoms_[entry.atom], entry.positive});
    }
    /* The float point's tight set: the bounds the assignment sits on,
     * which the core solves exactly when the reconstructed coordinates
     * alone fail -- decimal instances put vertices where no
     * double-reconstructed rational lands. */
    std::vector<FloatSimplex::PinnedBound> pinned_float;
    context_.float_core_->collectPinnedBounds(pinned_float);
    std::vector<CandidateBound> pinned;
    pinned.reserve(pinned_float.size());
    for (const FloatSimplex::PinnedBound& entry : pinned_float)
    {
      if (pinned.size() % 256 == 0 &&
          observer.pollBeforePivot() != StopReason::Continue)
        return {std::nullopt, observer.stop()};
      pinned.push_back(CandidateBound{
          context_.float_atom_core_atoms_[entry.atom], entry.positive});
    }
    InputResult<Model> certified = context_.core_->certifyCandidateModel(
        values.data(), values.data() + values.size(), bounds.data(),
        bounds.data() + bounds.size(), pinned.data(),
        pinned.data() + pinned.size(), &observer);
    if (certified.status != InputStatus::Accepted || !certified.value)
      return {std::nullopt, observer.stop()};
    return {std::move(certified.value), observer.stop()};
  }
  catch (...)
  {
    return {std::nullopt, observer.stop()};
  }
}

std::optional<Conflict> LraCandidateAdapter::certifyFloatCertificate() noexcept
{
  try
  {
    FloatSimplex::Certificate const& certificate =
        context_.float_core_->lastCertificate();
    if (!certificate.valid || certificate.items.empty())
      return std::nullopt;
    std::vector<ConflictCandidateTerm> terms;
    {
      NumberOperationScope operation(context_.mapping_budget_);
      terms.reserve(certificate.items.size());
      for (FloatSimplex::CertificateItem const& item : certificate.items)
      {
        if (!std::isfinite(item.weight) || !(item.weight > 0.0))
          return std::nullopt;
        terms.push_back(ConflictCandidateTerm{
            context_.float_atom_core_atoms_[item.atom], item.positive,
            rationalOfDouble(item.weight)});
      }
    }
    /* The core resolves the bounds and judges the exact combination --
     * always, independent of the verification flag; an unverified
     * certificate never becomes a clause.  The support's assertedness is
     * the float trail's, which mirrors the search's own. */
    InputResult<Conflict> certified = context_.core_->certifyCandidateConflict(
        terms.data(), terms.data() + terms.size(), context_.conflict_recovery_,
        &context_.observer_);
    if (certified.status != InputStatus::Accepted || !certified.value)
      return std::nullopt;
    return std::move(certified.value);
  }
  catch (...)
  {
    return std::nullopt;
  }
}

bool LraCandidateAdapter::stageCertificateConflict() noexcept
{
  try
  {
    const std::optional<Conflict> certified = certifyFloatCertificate();
    // Candidate verification already checked the exact Farkas combination.
    // Its support belongs to the float/SAT trail; the exact trail may be
    // unsynchronized. Requiring that support to be active in the exact
    // core would spuriously reject it when --lra-verify-conflicts is on.
    return certified && stageVerifiedTheoryConflict(*certified);
  }
  catch (...)
  {
    return false;
  }
}

bool LraCandidateAdapter::floatCompleteCandidate(std::uint64_t candidate,
                                                 AdapterResult& out)
{
  if (!context_.floatActive() || float_checks_degraded_)
    return false;
  const std::size_t float_mark = context_.float_core_->mark();
  std::optional<Conflict> conflict;
  std::optional<Model> witness;
  try
  {
    for (const CandidateComponentSelection& selection :
         context_.current_selection_)
    {
      const CoreComponentMapEntry& mapped =
          context_.componentMap(selection.component);
      if (mapped.float_atom == FloatSimplex::kNoAtom)
      {
        context_.float_core_->undoTo(float_mark);
        return false;
      }
      ++context_.metrics_.float_assertions;
      if (context_.float_core_->assertAtom(mapped.float_atom,
                                           selection.positive) ==
          FloatSimplex::AssertOutcome::LocalConflict)
      {
        ++context_.metrics_.float_local_conflicts;
        conflict = certifyFloatCertificate();
        if (!conflict)
        {
          ++context_.metrics_.float_certificate_failed;
          context_.float_core_->undoTo(float_mark);
          return false;
        }
        ++context_.metrics_.float_certified;
        break;
      }
    }
    if (!conflict)
    {
      auto check = [&]()
      {
        ++context_.metrics_.float_checks;
        const auto start = std::chrono::steady_clock::now();
        const auto pivots = context_.float_core_->pivots();
        const auto verdict =
            context_.float_core_->check(context_.observer_, true);
        context_.metrics_.float_pivots +=
            context_.float_core_->pivots() - pivots;
        context_.metrics_.float_check_nanoseconds += static_cast<std::uint64_t>(
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                std::chrono::steady_clock::now() - start)
                .count());
        maybeRequestFloatReroute();
        return verdict;
      };
      auto verdict = check();
      if (verdict == FloatSimplex::Verdict::InfeasibleCandidate)
      {
        ++context_.metrics_.float_check_conflicts;
        conflict = certifyFloatCertificate();
        if (!conflict)
        {
          ++context_.metrics_.float_certificate_failed;
          context_.float_core_->undoTo(float_mark);
          return false;
        }
        ++context_.metrics_.float_certified;
      }
      else if (verdict != FloatSimplex::Verdict::Feasible)
      {
        ++context_.metrics_.float_checks_abandoned;
        context_.float_core_->undoTo(float_mark);
        return false;
      }
      else
      {
        ModelRefinement refined = refineAndCertifyModel();
        if (refined.stop != StopReason::Continue)
        {
          context_.float_core_->undoTo(float_mark);
          context_.clearSemanticState();
          out = result(refined.stop == StopReason::Interrupted
                           ? AdapterOutcome::Interrupted
                           : AdapterOutcome::ResourceLimit,
                       candidate, "model refinement reached a query limit");
          return true;
        }
        witness = std::move(refined.witness);
      }
    }
    context_.float_core_->undoTo(float_mark);
    if (!conflict && !witness)
    {
      ++context_.metrics_.float_model_refine_failed;
      return false;
    }
  }
  catch (...)
  {
    try
    {
      context_.float_core_->undoTo(float_mark);
    }
    catch (...)
    {
    }
    return false;
  }
  /* Staging: failures here propagate to the caller's catch, exactly as
   * the exact path's staging failures do. */
  if (conflict)
  {
    copyVerifiedConflict(*conflict, candidate, /*core_derived=*/false);
    ++context_.metrics_.tableau_conflicts;
    out = result(AdapterOutcome::ConflictPending, candidate);
    return true;
  }
  ++context_.metrics_.float_models_refined;
  stageVerifiedModel(*witness, candidate, /*core_derived=*/false);
  out = result(AdapterOutcome::ModelStaged, candidate);
  return true;
}

LraCandidateAdapter::SyncOutcome
LraCandidateAdapter::syncFloatTrailIntoExact() noexcept
{
  try
  {
    const std::size_t current_level =
        float_level_marks_.empty() ? 0 : float_level_marks_.size() - 1;
    if (!unwindDeadBatches(std::min(unwind_low_level_, current_level)))
      return SyncOutcome::Failed;
    unwind_low_level_ = static_cast<std::size_t>(-1);
    if (context_.core_->status() == CheckStatus::Conflict)
      return SyncOutcome::CoreBusy;
    const std::vector<FloatSimplex::TrailEntry>& trail =
        context_.float_core_->trail();
    std::size_t from = sync_batches_.empty() ? 0 : sync_batches_.back().to;
    if (from == trail.size())
    {
      if (!sync_batches_.empty())
        return SyncOutcome::Clean;  // already mirrored
      /* Nothing on the trail and nothing pushed: not the same as mirrored.
       * The exact core only answers check() with a candidate open, and the
       * loop below is what opens one, so returning Clean here handed the
       * checker a core still in Ready and got InternalError back -- on every
       * query whose float trail stays empty, which is every query carrying a
       * Real declaration but no Real atom to assert. Open the candidate the
       * check is about to be asked about; it is empty, and an empty one is
       * exactly what "the theory has no objection" looks like. */
      const InputResult<Checkpoint> opened = context_.core_->push();
      if (opened.status != InputStatus::Accepted || !opened.value)
      {
        context_.invalidate("sync push failed opening an empty candidate");
        return SyncOutcome::Failed;
      }
      ++context_.metrics_.exact_pushes;
      sync_batches_.push_back(SyncBatch{*opened.value, 0U, 0U});
      return SyncOutcome::Clean;
    }
    /* One exact level per decision level with asserts, so the backtrack
     * walk pops exactly the batches of the levels the search leaves.
     * Entry tags are nondecreasing along the trail, so the slices are
     * contiguous. */
    while (from < trail.size())
    {
      const std::uint32_t level = trail[from].user_tag;
      std::size_t to = from;
      while (to < trail.size() && trail[to].user_tag == level)
        ++to;
      const InputResult<Checkpoint> pushed = context_.core_->push();
      if (pushed.status != InputStatus::Accepted || !pushed.value)
      {
        context_.invalidate("sync push failed");
        return SyncOutcome::Failed;
      }
      ++context_.metrics_.exact_pushes;
      ++context_.metrics_.float_replays;
      sync_batches_.push_back(
          SyncBatch{*pushed.value, static_cast<std::size_t>(level), to});
      for (std::size_t i = from; i < to; ++i)
      {
        const FloatSimplex::TrailEntry& entry = trail[i];
        const AtomId atom = context_.float_atom_core_atoms_[entry.atom];
        const AssertResult asserted =
            context_.core_->assertLiteral(atom, entry.positive);
        ++context_.metrics_.exact_assertions;
        if (asserted.status != InputStatus::Accepted)
        {
          context_.invalidate(
              asserted.status == InputStatus::ResourceLimit
                  ? "synced assertion reached a resource limit"
                  : "synced assertion was not accepted");
          return SyncOutcome::Failed;
        }
        if (asserted.immediate_conflict)
        {
          if (!stageTheoryConflict(*asserted.immediate_conflict))
          {
            context_.invalidate("synced conflict failed verification");
            return SyncOutcome::Failed;
          }
          /* The conflicting assert records nothing -- the core refuses it
           * before pushing -- so the batch covers entries only up to it.
           * A batch whose very first assert conflicted holds no bound at
           * all: its checkpoint aliases the previous batch's (two pushes
           * with no bound between them share a checkpoint), so the record
           * is dropped rather than left to misresolve a later unwind. */
          if (i == from)
            sync_batches_.pop_back();
          else
            sync_batches_.back().to = i + 1;
          ++context_.metrics_.float_replay_conflicts;
          return SyncOutcome::ConflictStaged;
        }
      }
      from = to;
    }
    return SyncOutcome::Clean;
  }
  catch (...)
  {
    context_.invalidate("unexpected failure syncing the float trail");
    return SyncOutcome::Failed;
  }
}

LraCandidateAdapter::ReplayVerdict
LraCandidateAdapter::syncAndCheckExact(bool final_check,
                                     std::optional<Model>* witness) noexcept
{
  const auto sync_start = std::chrono::steady_clock::now();
  const auto account = [&]() noexcept {
    context_.metrics_.float_sync_nanoseconds += static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            std::chrono::steady_clock::now() - sync_start)
            .count());
  };
  try
  {
    switch (syncFloatTrailIntoExact())
    {
      case SyncOutcome::ConflictStaged:
        account();
        return ReplayVerdict::ConflictStaged;
      case SyncOutcome::CoreBusy:
      case SyncOutcome::Failed:
        account();
        return ReplayVerdict::Inconclusive;
      case SyncOutcome::Clean:
        break;
    }
    context_.observer_.beginCheck(!final_check);
    CheckResult checked = context_.core_->check(
        context_.observer_, /*verify_model=*/final_check);
    ++context_.metrics_.exact_checks;
    if (!final_check)
      context_.observer_.beginCheck(false);
    if (checked.status == CheckStatus::Conflict && checked.conflict)
    {
      if (!stageTheoryConflict(*checked.conflict))
      {
        context_.invalidate("synced check conflict failed verification");
        return ReplayVerdict::Inconclusive;
      }
      ++context_.metrics_.float_replay_conflicts;
      /* The core stays in Conflict until the staged clause's backtrack
       * pops the level batches -- the exact path's own lifecycle. */
      account();
      return ReplayVerdict::ConflictStaged;
    }
    if (checked.status == CheckStatus::Consistent)
    {
      if (witness != nullptr)
      {
        if (!final_check || !checked.model)
        {
          context_.invalidate("synced final check omitted its certified model");
          account();
          return ReplayVerdict::Inconclusive;
        }
        *witness = std::move(checked.model);
      }
      advice_source_ = AdviceSource::Exact;
      ++context_.metrics_.float_replay_consistent;
      account();
      return ReplayVerdict::Consistent;
    }
    if (checked.status == CheckStatus::InternalError)
    {
      /* Not a give-up: the core is telling us its own state is wrong, and
       * the caller's stop-without-deciding path would report that as a query
       * nobody could answer. Fail as a fault so it stays visible. */
      context_.invalidate("synced check reported an internal error");
      account();
      return ReplayVerdict::Inconclusive;
    }
    // Interrupted, guard-stopped, or out of budget: decide nothing.
    account();
    return ReplayVerdict::Inconclusive;
  }
  catch (...)
  {
    context_.invalidate("unexpected failure checking the synced state");
    account();
    return ReplayVerdict::Inconclusive;
  }
}

bool LraCandidateAdapter::assertOneLiteralFloat(
    SATSolver::Lit literal, const CoreComponentMapEntry& mapped) noexcept
{
  try
  {
    if (!ensureFloatLevelMark())
      return false;
    const bool positive = !SATSolver::sign(literal);
    const std::uint32_t level = static_cast<std::uint32_t>(
        float_level_marks_.empty() ? 0 : float_level_marks_.size() - 1);
    const FloatSimplex::AssertOutcome outcome =
        context_.float_core_->assertAtom(mapped.float_atom, positive, level);
    ++context_.metrics_.float_assertions;
    if (outcome == FloatSimplex::AssertOutcome::Ok)
    {
      theory_dirty_ = true;
      return true;
    }
    /* The advisory tier sees a direct bound clash.  Certify it exactly; a
     * disagreement -- the doubles lied within rounding -- just leaves the
     * search to continue. */
    ++context_.metrics_.float_local_conflicts;
    if (stageCertificateConflict())
    {
      ++context_.metrics_.float_certified;
      ++context_.metrics_.immediate_conflicts;
      return true;
    }
    ++context_.metrics_.float_certificate_failed;
    const ReplayVerdict verdict = syncAndCheckExact(false);
    if (verdict == ReplayVerdict::ConflictStaged)
      ++context_.metrics_.immediate_conflicts;
    else
      theory_dirty_ = true;
    return !failed();
  }
  catch (...)
  {
    context_.invalidate("unexpected failure asserting a float literal");
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
  try
  {
    float_level_marks_.emplace_back();
  }
  catch (...)
  {
    context_.invalidate("unexpected failure opening a float level");
    return;
  }
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
    if (context_.floatActive())
    {
      /* The exact mirror unwinds lazily, at the next sync.  The one thing
       * that cannot wait is a core left in Conflict by a staged conflict:
       * it must be Ready before anything consults it again, so that case
       * unwinds now -- still a single pop to the deepest dead batch. */
      unwind_low_level_ = std::min(unwind_low_level_, level);
      if (context_.core_->status() == CheckStatus::Conflict)
      {
        if (!unwindDeadBatches(unwind_low_level_))
          return;
        unwind_low_level_ = static_cast<std::size_t>(-1);
      }
      /* Mirror of the level_checkpoints_ walk below: the lowest popped
       * level carrying a mark is where the float trail rewinds to. */
      std::optional<std::size_t> restore;
      while (float_level_marks_.size() > level + 1)
      {
        if (float_level_marks_.back())
          restore = *float_level_marks_.back();
        float_level_marks_.pop_back();
      }
      if (restore)
        context_.float_core_->undoTo(*restore);
      /* The exact-path level vector still grows in notifyNewLevel; keep
       * its length honest.  Entries are empty here -- no exact level is
       * opened per decision level in float mode. */
      while (level_checkpoints_.size() > level + 1)
        level_checkpoints_.pop_back();
      return;
    }
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

void LraCandidateAdapter::maybeRequestFloatReroute() noexcept
{
  const unsigned budget = context_.floatRerouteBudget();
  if (budget == 0 || !context_.floatActive() || context_.float_core_ == nullptr ||
      solver_.theoryRerouteRequested())
    return;
  // liveNonzeros scans the rows, so sample the fill periodically rather than
  // on every check.
  constexpr unsigned kSampleEvery = 64;
  if (++float_reroute_sample_ < kSampleEvery)
    return;
  float_reroute_sample_ = 0;
  const std::uint64_t pristine = context_.float_core_->pristineNonzeros();
  if (pristine == 0)
    return;
  const std::uint64_t live = context_.float_core_->liveNonzeros();
  const std::uint64_t floor = context_.floatRerouteFloor();
  // Both tests: the fill is a pathological multiple of pristine, and the
  // tableau is large in absolute terms. The floor is what keeps a small
  // healthy problem -- whose fill trivially exceeds a multiple of its tiny
  // pristine -- from rerouting.
  if (live > static_cast<std::uint64_t>(budget) * pristine && live >= floor)
  {
    ++context_.metrics_.float_reroutes;
    solver_.requestTheoryReroute();
  }
}

void LraCandidateAdapter::checkPartialAssignment() noexcept
{
  if (!propagating_ || failed() || conflict_pending_ || !theory_dirty_ ||
      !partial_checks_enabled_ || pastTimeLimit())
    return;
  theory_dirty_ = false;
  if (context_.floatActive() && float_checks_degraded_)
  {
    /* The float tableau gave up on this instance; prune the exact way:
     * bring the mirror up to the trail and let the guarded exact check
     * below do what the flag-off path does. */
    switch (syncFloatTrailIntoExact())
    {
      case SyncOutcome::ConflictStaged:
        ++context_.metrics_.partial_conflicts;
        return;
      case SyncOutcome::Failed:
      case SyncOutcome::CoreBusy:
        return;
      case SyncOutcome::Clean:
        break;
    }
  }
  else if (context_.floatActive())
  {
    try
    {
      ++context_.metrics_.float_checks;
      const auto check_start = std::chrono::steady_clock::now();
      const std::uint64_t pivots_before = context_.float_core_->pivots();
      const FloatSimplex::Verdict verdict =
          context_.float_core_->check(context_.observer_);
      context_.metrics_.float_pivots +=
          context_.float_core_->pivots() - pivots_before;
      context_.metrics_.float_check_nanoseconds +=
          static_cast<std::uint64_t>(
              std::chrono::duration_cast<std::chrono::nanoseconds>(
                  std::chrono::steady_clock::now() - check_start)
                  .count());
      // The tableau grows across the incremental rebuilds these partial
      // checks drive; sample its fill here and reroute to the exact driver if
      // it has blown up.
      maybeRequestFloatReroute();
      if (verdict == FloatSimplex::Verdict::Feasible)
      {
        advice_source_ = AdviceSource::Float;
        return;
      }
      if (verdict == FloatSimplex::Verdict::Abandoned)
      {
        ++context_.metrics_.float_checks_abandoned;
        /* A tableau that keeps blowing the pivot or merge budget has
         * densified along its pivot history, not by the instance's
         * nature: restart the basis first -- pristine sparse rows, same
         * bounds -- and only degrade this solve to exact partial checks
         * over the mirror once restarts stop helping. */
        constexpr unsigned kFloatAbandonedBeforeDegrade = 3;
        /* Zeroth line: the tier tripped its infinitesimal cap a second
         * time.  A fresh factorized tier built from the same trail takes
         * over; only if it cannot be built, or this solve has already
         * been given its share of fresh tiers, does the cascade below
         * run -- a fresh tier that trips on its own first check has no
         * history to blame, and another identical one would trip the
         * same way (see float_promotions_). */
        unsigned const promotion_budget = context_.floatPromotionBudget();
        bool const budget_spent =
            promotion_budget != 0 && float_promotions_ >= promotion_budget;
        if (context_.float_core_->wantsPromotion() && !budget_spent &&
            context_.promoteFloatCore())
        {
          ++float_promotions_;
          partial_checks_abandoned_ = 0;
          theory_dirty_ = true;
          return;
        }
        if (++partial_checks_abandoned_ >= kFloatAbandonedBeforeDegrade)
        {
          if (float_restarts_ == 0)
          {
            /* First line: restart the substitution tableau's basis. */
            ++float_restarts_;
            ++context_.metrics_.float_restarts;
            partial_checks_abandoned_ = 0;
            context_.float_core_->restartBasis();
            theory_dirty_ = true;
          }
          else if (!context_.float_core_->factorized())
          {
            /* Second line: the factorized representation, where the
             * original rows are immutable and densification cannot
             * happen.  Its own budget (the pivot cap) feeds the same
             * abandonment counter. */
            ++float_restarts_;
            ++context_.metrics_.float_factorized;
            partial_checks_abandoned_ = 0;
            context_.float_core_->switchToFactorized();
            theory_dirty_ = true;
          }
          else
          {
            float_checks_degraded_ = true;
            ++context_.metrics_.partial_checks_disabled;
          }
        }
        return;
      }
      ++context_.metrics_.float_check_conflicts;
      if (stageCertificateConflict())
      {
        ++context_.metrics_.float_certified;
        ++context_.metrics_.partial_conflicts;
        return;
      }
      ++context_.metrics_.float_certificate_failed;
      const ReplayVerdict staged = syncAndCheckExact(false);
      if (staged == ReplayVerdict::ConflictStaged)
        ++context_.metrics_.partial_conflicts;
      else if (staged == ReplayVerdict::Consistent)
        context_.float_core_->dismissLastConflict();
    }
    catch (...)
    {
      context_.invalidate("unexpected failure in a float partial check");
    }
    return;
  }
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
        if (advice_source_ == AdviceSource::Float && context_.floatActive() &&
            !float_checks_degraded_)
          advice = context_.float_core_->preferredPolarity(mapped.float_atom);
        else if (advice_source_ == AdviceSource::Exact)
          advice = context_.core_->preferredPolarity(mapped.core_atom);
        if (advice)
        {
          ++context_.metrics_.polarity_advice;
          if (value != *advice)
            ++context_.metrics_.polarity_changes;
          if (advice_source_ == AdviceSource::Float)
            ++context_.metrics_.polarity_float;
          else
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
    if (context_.floatActive())
    {
      /* Cheap rejection first: a candidate model the float tier already
       * sees as infeasible, certified exactly, never pays the exact
       * replay.  Only float-feasible candidates -- which include every
       * model that is eventually accepted -- reach the exact core. */
      if (!float_checks_degraded_ &&
          context_.float_core_->check(context_.observer_,
                                      /*full_refresh=*/true) ==
              FloatSimplex::Verdict::InfeasibleCandidate &&
          stageCertificateConflict())
      {
        ++context_.metrics_.float_certified;
        return false;  // rejected; the clause follows
      }
      /* Refinement first: reconstruct the float assignment exactly and
       * have the core substitute an epsilon and verify it against the
       * trail's bounds. Keep the certified witness for publication. */
      std::optional<Model> witness;
      if (!float_checks_degraded_)
      {
        ModelRefinement refined = refineAndCertifyModel();
        if (refined.stop != StopReason::Continue)
        {
          if (refined.stop == StopReason::Interrupted && pastTimeLimit())
            return true;  // publication reports the deadline interruption
          context_.giveUp(refined.stop == StopReason::Interrupted
                              ? "model refinement was interrupted"
                              : "model refinement reached a resource limit");
          return true;
        }
        witness = std::move(refined.witness);
      }
      if (witness)
      {
        ++context_.metrics_.float_models_refined;
        context_.float_core_->dismissLastConflict();
        return retainPropagatedModel(std::move(*witness));
      }
      if (!float_checks_degraded_)
        ++context_.metrics_.float_model_refine_failed;
      /* The final verdict is always exact: bring the exact mirror up to
       * the float trail and keep the model produced by its final check. */
      const ReplayVerdict verdict = syncAndCheckExact(true, &witness);
      if (verdict == ReplayVerdict::Consistent)
      {
        context_.float_core_->dismissLastConflict();
        return retainPropagatedModel(std::move(*witness));
      }
      if (verdict == ReplayVerdict::ConflictStaged)
        return false;  // rejected; the clause follows
      if (!failed() && pastTimeLimit())
        return true;  // acceptPropagatedModel reports the interrupted search
      if (!failed())
        /* Inconclusive, which is not the same as wrong. syncAndCheckExact
         * reaches here when the exact mirror was busy, interrupted,
         * guard-stopped, or simply returned no verdict -- every one of them a
         * reason to stop rather than evidence that anything is broken. The
         * context still has to die, because returning true accepts a model
         * nothing verified and only a dead context stops that being read as
         * an answer; but dying as a fault made a query STP merely could not
         * decide come back as SOLVER_ERROR. */
        context_.giveUp("float final check produced no usable verdict");
      return true;
    }
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

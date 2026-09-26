#include "ExactLraCore.h"

#include "ExactLraRegistration.h"
#include "ExactLraVerificationData.h"
#include "BoundStore.h"
#include "ExactSimplex.h"
#include "VariableStore.h"
#include "Storage/StorageFailure.h"

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <limits>
#include <map>
#include <memory>
#include <new>
#include <optional>
#include <stdexcept>
#include <utility>
#include <vector>

namespace stp::lra {

namespace {

void increment(std::uint64_t& value) noexcept
{
  detail::saturatingIncrement(value);
}

void addMetric(std::uint64_t& destination, std::uint64_t value) noexcept
{
  destination = detail::saturatingAdd(destination, value);
}

void mergeStorageMetrics(StorageMetrics& destination,
                         StorageMetrics const& source) noexcept
{
#define STP_LRA_ADD_STORAGE_METRIC(field) \
  addMetric(destination.field, source.field)
  STP_LRA_ADD_STORAGE_METRIC(generations_created);
  STP_LRA_ADD_STORAGE_METRIC(generation_resets);
  STP_LRA_ADD_STORAGE_METRIC(ids_allocated);
  STP_LRA_ADD_STORAGE_METRIC(ordinal_exhaustions);
  STP_LRA_ADD_STORAGE_METRIC(arena_values);
  STP_LRA_ADD_STORAGE_METRIC(peak_arena_values);
  STP_LRA_ADD_STORAGE_METRIC(logical_arena_bytes);
  STP_LRA_ADD_STORAGE_METRIC(lookups);
  STP_LRA_ADD_STORAGE_METRIC(stale_lookup_rejections);
  STP_LRA_ADD_STORAGE_METRIC(invalid_ordinal_rejections);
  STP_LRA_ADD_STORAGE_METRIC(checkpoints_created);
  STP_LRA_ADD_STORAGE_METRIC(checkpoints_popped);
  STP_LRA_ADD_STORAGE_METRIC(stale_checkpoint_rejections);
  STP_LRA_ADD_STORAGE_METRIC(trail_appends);
  STP_LRA_ADD_STORAGE_METRIC(vector_growths);
  STP_LRA_ADD_STORAGE_METRIC(vector_resets);
  STP_LRA_ADD_STORAGE_METRIC(dense_membership_resizes);
  STP_LRA_ADD_STORAGE_METRIC(dense_membership_sets);
  STP_LRA_ADD_STORAGE_METRIC(dense_membership_queries);
  STP_LRA_ADD_STORAGE_METRIC(dense_membership_clears);
  STP_LRA_ADD_STORAGE_METRIC(value_mutations);
  STP_LRA_ADD_STORAGE_METRIC(presence_mutations);
  STP_LRA_ADD_STORAGE_METRIC(trail_restorations);
  STP_LRA_ADD_STORAGE_METRIC(sorts);
  STP_LRA_ADD_STORAGE_METRIC(sort_attempts);
  STP_LRA_ADD_STORAGE_METRIC(sort_successes);
  STP_LRA_ADD_STORAGE_METRIC(sort_failures);
  STP_LRA_ADD_STORAGE_METRIC(conversion_failures);
  STP_LRA_ADD_STORAGE_METRIC(allocation_failures);
#undef STP_LRA_ADD_STORAGE_METRIC
}

bool relationSupported(Relation relation) noexcept
{
  switch (relation)
  {
    case Relation::Less:
    case Relation::LessEqual:
    case Relation::Greater:
    case Relation::GreaterEqual:
      return true;
  }
  return false;
}

bool isSafeResource(NumberFailure const& failure) noexcept
{
  return failure.kind() == NumberFailureKind::ResourceLimit;
}

bool isSafeResource(StorageFailure const& failure) noexcept
{
  return failure.kind() == StorageFailureKind::ResourceLimit;
}

RegisteredBoundKind registeredKind(BoundSide side) noexcept
{
  return side == BoundSide::Upper ? RegisteredBoundKind::Upper
                                  : RegisteredBoundKind::Lower;
}

struct RelationBounds final
{
  BoundSide positive_side;
  DeltaRational positive_value;
  BoundSide negative_side;
  DeltaRational negative_value;
};

RelationBounds makeRelationBoundsOwned(
    BoundSide positive_side,
    ExactRational const& threshold,
    ExactRational const& positive_infinitesimal,
    BoundSide negative_side,
    ExactRational const& negative_infinitesimal)
{
  // Keep each completed DeltaRational in an independently active owner until its
  // complement has also been constructed.  In particular, do not place both
  // throwing constructions directly in one aggregate initializer: a failure
  // in the second initializer must unwind the first named owner.
  DeltaRational positive_value(threshold, positive_infinitesimal);
  DeltaRational negative_value(threshold, negative_infinitesimal);
  return RelationBounds{positive_side, std::move(positive_value),
                        negative_side, std::move(negative_value)};
}

RelationBounds makeRelationBounds(Relation relation,
                                  ExactRational const& threshold)
{
  ExactRational const minus_one(std::int64_t{-1});
  ExactRational const zero(std::int64_t{0});
  ExactRational const one(std::int64_t{1});
  switch (relation)
  {
    case Relation::Less:
      return makeRelationBoundsOwned(BoundSide::Upper, threshold, minus_one,
                                     BoundSide::Lower, zero);
    case Relation::LessEqual:
      return makeRelationBoundsOwned(BoundSide::Upper, threshold, zero,
                                     BoundSide::Lower, one);
    case Relation::Greater:
      return makeRelationBoundsOwned(BoundSide::Lower, threshold, one,
                                     BoundSide::Upper, zero);
    case Relation::GreaterEqual:
      return makeRelationBoundsOwned(BoundSide::Lower, threshold, zero,
                                     BoundSide::Upper, minus_one);
  }
  throw EngineInvariantFailure("unsupported relation reached mapper");
}

}  // namespace

class ExactLraCore::Impl final
{
 public:
  explicit Impl(NumberLimits limits, DirectBoundsMode direct_bounds);

  InputResult<VariableId> addVariable();
  InputResult<RowId> addRow(LinearTerm const* begin, LinearTerm const* end);
  InputResult<AtomId> addAtom(RowId row,
                              Relation relation,
                              ExactRational const& threshold,
                              OriginId positive_origin,
                              OriginId negative_origin);
  InputStatus initialize();
  InputResult<Checkpoint> push();
  InputStatus pop(Checkpoint checkpoint);
  AssertResult assertLiteral(AtomId atom, bool positive);
  CheckResult check(ExactLraResourceObserver& observer, bool verify_model);
  std::optional<bool> preferredPolarity(AtomId atom) const noexcept;

  VerificationResult verifyConflict(Conflict const&) const;
  VerificationResult verifyModel(Model const&) const;
  InputResult<Conflict> certifyCandidateConflict(
      ConflictCandidateTerm const* begin, ConflictCandidateTerm const* end,
      bool recover_weights, ExactLraResourceObserver* observer,
      std::size_t recovery_support_limit);
  InputResult<Model> certifyCandidateModel(
      ModelCandidateValue const* values_begin,
      ModelCandidateValue const* values_end,
      CandidateBound const* bounds_begin, CandidateBound const* bounds_end,
      CandidateBound const* pinned_begin, CandidateBound const* pinned_end,
      ExactLraResourceObserver* observer);

  CoreStatistics statistics() const noexcept;
  CheckStatus status() const noexcept;
  CoreGeneration generation() const noexcept
  {
    return generation_state_->engine->generation;
  }
  void reset() noexcept;
  InputStatus restartSearchState() noexcept;
  InputStatus beginExtension() noexcept
  {
    auto const& registration = generation_state_->engine->registration;
    if ((state_ != State::Ready && state_ != State::Consistent) ||
        registration.levelCount() != 0 || !registration.activeBounds().empty() ||
        registration.pendingConflictBound())
      return InputStatus::InvalidState;
    if (!prepareRevision())
      return InputStatus::InternalError;
    state_ = State::Building;
    return InputStatus::Accepted;
  }
  void setConflictVerification(bool enabled) noexcept
  {
    verify_conflicts_ = enabled;
  }
  void setSoi(bool enabled) noexcept
  {
    soi_ = enabled;
    generation_state_->engine->simplex.setSoi(enabled);
  }
  void setSeparateModelValues(bool enabled) noexcept
  {
    separate_model_values_ = enabled;
  }
  void setEarlyConflictDetection(bool enabled) noexcept
  {
    early_conflicts_ = enabled;
    generation_state_->engine->simplex.setEarlyConflictDetection(enabled);
  }

#if defined(STP_LRA_TEST_FAULT_INJECTION)
  void testCorruptVerificationRow(RowId);
  void testCorruptVerificationBound(AtomId, bool positive);
  void testForceNextConflictVerificationResource() noexcept
  {
    force_conflict_verification_resource_ = true;
  }
  void testForceNextModelVerificationResource() noexcept
  {
    force_model_verification_resource_ = true;
  }
  VerificationError testLastVerificationError() const noexcept
  {
    return last_verification_error_;
  }
#endif

 private:
  enum class State : std::uint8_t
  {
    Building,
    Ready,
    CandidateOpen,
    Consistent,
    Conflict,
    Interrupted,
    ResourceLimit,
    Invalid
  };

  struct Engine final
  {
    explicit Engine(CoreGeneration current)
        : generation(current),
          variables(current),
          bounds(current, variables),
          simplex(current, bounds),
          registration(current)
    {}

    CoreGeneration generation;
    VariableStore variables;
    BoundStore bounds;
    ExactSimplex simplex;
    ExactLraRegistration registration;
    std::uint64_t identity_rows = 0;
    std::uint64_t singleton_rows = 0;
    std::uint64_t direct_rows = 0;
  };

  struct GenerationState final
  {
    GenerationState(NumberLimits limits, CoreGeneration generation)
        : budget(limits)
    {
      NumberOperationScope scope(budget);
      engine = std::make_unique<Engine>(generation);
    }

    // C++ destroys members in reverse declaration order.  The budget is
    // deliberately first so every exact-value-bearing owner below is gone
    // before the budget's strict zero-live-state destructor guard runs.
    NumberBudget budget;
    std::unique_ptr<Engine> engine;
    ExactSimplex::Explanation pending_conflict_explanation;
  };

  class ObserverAdapter final : public ExactSimplexObserver
  {
   public:
    ObserverAdapter(Impl& owner, ExactLraResourceObserver& observer)
        : owner_(owner), observer_(observer)
    {}

    StopReason pollBeforePivot() noexcept override
    {
      return observer_.pollBeforePivot();
    }
    void accountPivot(bool bland) noexcept override
    {
      increment(owner_.statistics_.pivots);
      if (bland)
      {
        increment(owner_.statistics_.bland_pivots);
      }
      observer_.accountPivot(bland);
    }

   private:
    Impl& owner_;
    ExactLraResourceObserver& observer_;
  };

  bool prepareRevision() noexcept;
  void invalidate() noexcept;
  InputStatus inputFailure(NumberFailure const&, bool mutated) noexcept;
  InputStatus inputFailure(StorageFailure const&, bool mutated) noexcept;
  InputStatus inputFailure() noexcept;
  CheckResult checkFailure(NumberFailure const&) noexcept;
  CheckResult checkFailure(StorageFailure const&) noexcept;
  CheckResult checkFailure() noexcept;
  VerificationResult runConflictVerifier(Conflict const&) const;
  VerificationResult runModelVerifier(Model const&) const;

  Conflict exportConflict(ExactSimplex::Explanation const&) const;
  Model exportModel() const;
  Conflict publishConflict(Conflict const&) const;
  Model publishModel(Model const&) const;

  NumberLimits limits_;
  GenerationDomain generation_domain_;
  // Published DTO values may deliberately outlive a generation so callers
  // can receive StaleId on verification after reset.  They therefore use a
  // separate facade-lifetime budget rather than the replaceable generation
  // budget.  The existing facade contract requires DTOs to die before their
  // producing core; declaration order keeps the generation bundle shorter
  // lived than this budget during facade destruction.
  mutable NumberBudget witness_budget_;
  std::unique_ptr<GenerationState> generation_state_;
  State state_ = State::Building;
  std::uint64_t revision_ = 1;
  // The generation whose snapshot the candidate-certificate path last
  // audited in full.  Keyed on the generation, not the revision: asserts
  // bump the revision constantly (every certificate fallback syncs), but
  // the registration's rows, atoms and bounds only change with the
  // generation, and they are all the audit inspects.
  CoreGeneration certificate_audit_generation_{};
  mutable CoreStatistics statistics_{};
  // See ExactLraCore::setConflictVerification. Default on, so a core built
  // directly keeps the automatic check.
  bool verify_conflicts_ = true;
  bool early_conflicts_ = false;
  bool soi_ = false;
  bool separate_model_values_ = false;
  DirectBoundsMode direct_bounds_;
  mutable VerificationError last_verification_error_ =
      VerificationError::None;
#if defined(STP_LRA_TEST_FAULT_INJECTION)
  mutable bool force_conflict_verification_resource_ = false;
  mutable bool force_model_verification_resource_ = false;
#endif
};

ExactLraCore::Impl::Impl(NumberLimits limits, DirectBoundsMode direct_bounds)
    : limits_(limits),
      witness_budget_(limits_),
      generation_state_(std::make_unique<GenerationState>(
          limits_, generation_domain_.current())), direct_bounds_(direct_bounds)
{
  if (direct_bounds != DirectBoundsMode::Disabled &&
      direct_bounds != DirectBoundsMode::Identity &&
      direct_bounds != DirectBoundsMode::Singleton)
    throw std::invalid_argument("invalid direct bounds mode");
}

bool ExactLraCore::Impl::prepareRevision() noexcept
{
  if (revision_ == std::numeric_limits<std::uint64_t>::max())
  {
    invalidate();
    return false;
  }
  if (state_ == State::Consistent || state_ == State::Conflict)
  {
    increment(statistics_.witness_invalidations);
  }
  ++revision_;
  return true;
}

void ExactLraCore::Impl::invalidate() noexcept
{
  if (state_ == State::Consistent || state_ == State::Conflict)
  {
    increment(statistics_.witness_invalidations);
  }
  generation_state_->engine->registration.clearPendingConflictBound();
  generation_state_->pending_conflict_explanation.clear();
  state_ = State::Invalid;
  increment(statistics_.internal_errors);
}

InputStatus ExactLraCore::Impl::inputFailure(NumberFailure const& failure,
                                             bool mutated) noexcept
{
  if (!mutated && isSafeResource(failure))
  {
    increment(statistics_.resource_stops);
    return InputStatus::ResourceLimit;
  }
  invalidate();
  return InputStatus::InternalError;
}

InputStatus ExactLraCore::Impl::inputFailure(StorageFailure const& failure,
                                             bool mutated) noexcept
{
  if (!mutated && isSafeResource(failure))
  {
    increment(statistics_.resource_stops);
    return InputStatus::ResourceLimit;
  }
  invalidate();
  return InputStatus::InternalError;
}

InputStatus ExactLraCore::Impl::inputFailure() noexcept
{
  invalidate();
  return InputStatus::InternalError;
}

InputResult<VariableId> ExactLraCore::Impl::addVariable()
{
  if (state_ != State::Building)
  {
    return InputResult<VariableId>{InputStatus::InvalidState, std::nullopt};
  }
  if (!prepareRevision())
  {
    return InputResult<VariableId>{InputStatus::InternalError, std::nullopt};
  }
  bool mutated = false;
  try
  {
    NumberOperationScope scope(generation_state_->budget);
    VariableId const variable = generation_state_->engine->variables.allocate();
    mutated = true;
    generation_state_->engine->simplex.addVariable(variable);
    generation_state_->engine->registration.addBaseVariable(variable);
    return InputResult<VariableId>{InputStatus::Accepted, variable};
  }
  catch (NumberFailure const& failure)
  {
    return InputResult<VariableId>{inputFailure(failure, mutated),
                                   std::nullopt};
  }
  catch (StorageFailure const& failure)
  {
    return InputResult<VariableId>{inputFailure(failure, mutated),
                                   std::nullopt};
  }
  catch (...)
  {
    return InputResult<VariableId>{inputFailure(), std::nullopt};
  }
}

InputResult<RowId> ExactLraCore::Impl::addRow(LinearTerm const* begin,
                                              LinearTerm const* end)
{
  if (state_ != State::Building)
  {
    return InputResult<RowId>{InputStatus::InvalidState, std::nullopt};
  }
  if (begin == nullptr || end == nullptr || begin == end)
  {
    return InputResult<RowId>{InputStatus::Unsupported, std::nullopt};
  }

  VariableId previous = begin->variable;
  bool first = true;
  for (LinearTerm const* term = begin; term != end; ++term)
  {
    if (!generation_state_->engine->registration.containsBaseVariable(term->variable))
    {
      return InputResult<RowId>{InputStatus::InvalidId, std::nullopt};
    }
    if (term->coefficient.isZero())
    {
      return InputResult<RowId>{InputStatus::Unsupported, std::nullopt};
    }
    if (!first && !(previous < term->variable))
    {
      return InputResult<RowId>{InputStatus::Unsupported, std::nullopt};
    }
    first = false;
    previous = term->variable;
  }
  if (!prepareRevision())
  {
    return InputResult<RowId>{InputStatus::InternalError, std::nullopt};
  }

  bool mutated = false;
  try
  {
    NumberOperationScope scope(generation_state_->budget);
    std::vector<ExactSimplex::RowTerm> terms;
    std::vector<LinearTerm> canonical;
    for (LinearTerm const* term = begin; term != end; ++term)
    {
      terms.push_back(ExactSimplex::RowTerm{term->variable, term->coefficient});
      canonical.push_back(*term);
    }
    auto& engine = *generation_state_->engine;
    const bool singleton = terms.size() == 1;
    const bool identity = singleton && terms.front().coefficient.isOne();
    const bool direct = singleton &&
        (direct_bounds_ == DirectBoundsMode::Singleton ||
         (direct_bounds_ == DirectBoundsMode::Identity && identity));
    VariableId const auxiliary = direct ? terms.front().variable
                                        : engine.variables.allocate();
    mutated = true;
    if (!direct)
      engine.simplex.addRow(auxiliary, std::move(terms));
    RowId const row = engine.registration.addRow(
        auxiliary, std::move(canonical), direct);
    if (singleton)
      increment(engine.singleton_rows);
    if (identity)
      increment(engine.identity_rows);
    if (direct)
      increment(engine.direct_rows);
    return InputResult<RowId>{InputStatus::Accepted, row};
  }
  catch (NumberFailure const& failure)
  {
    return InputResult<RowId>{inputFailure(failure, mutated), std::nullopt};
  }
  catch (StorageFailure const& failure)
  {
    return InputResult<RowId>{inputFailure(failure, mutated), std::nullopt};
  }
  catch (...)
  {
    return InputResult<RowId>{inputFailure(), std::nullopt};
  }
}

InputResult<AtomId> ExactLraCore::Impl::addAtom(
    RowId row,
    Relation relation,
    ExactRational const& threshold,
    OriginId positive_origin,
    OriginId negative_origin)
{
  if (state_ != State::Building)
  {
    return InputResult<AtomId>{InputStatus::InvalidState, std::nullopt};
  }
  if (!generation_state_->engine->registration.containsRow(row))
  {
    return InputResult<AtomId>{InputStatus::InvalidId, std::nullopt};
  }
  if (!relationSupported(relation))
  {
    return InputResult<AtomId>{InputStatus::Unsupported, std::nullopt};
  }
  if (!prepareRevision())
  {
    return InputResult<AtomId>{InputStatus::InternalError, std::nullopt};
  }

  bool mutated = false;
  try
  {
    NumberOperationScope scope(generation_state_->budget);
    RelationBounds relation_bounds = makeRelationBounds(relation, threshold);
    ExactRational atom_threshold(threshold);
    ExactRational positive_main(relation_bounds.positive_value.rational());
    ExactRational positive_delta(relation_bounds.positive_value.infinitesimal());
    ExactRational negative_main(relation_bounds.negative_value.rational());
    ExactRational negative_delta(relation_bounds.negative_value.infinitesimal());

    const auto& registered_row = generation_state_->engine->registration.row(row);
    const auto positive_kind = registeredKind(relation_bounds.positive_side);
    const auto negative_kind = registeredKind(relation_bounds.negative_side);
    if (registered_row.direct_coefficient)
    {
      const auto& coefficient = *registered_row.direct_coefficient;
      // Divide the entire delta rational, including its infinitesimal. This
      // preserves the original strict-bound convention and certificate scale.
      if (!coefficient.isOne())
      {
        relation_bounds.positive_value /= coefficient;
        relation_bounds.negative_value /= coefficient;
      }
      if (coefficient.sign() < 0)
        std::swap(relation_bounds.positive_side, relation_bounds.negative_side);
    }

    AtomId const atom = generation_state_->engine->registration.allocateAtom();
    mutated = true;
    VariableId const auxiliary = registered_row.auxiliary;
    BoundStore::AtomBounds const pair =
        generation_state_->engine->bounds.allocatePair(
            auxiliary,
            BoundStore::BoundSpec{
                relation_bounds.positive_side,
                std::move(relation_bounds.positive_value), positive_origin,
                atom},
            BoundStore::BoundSpec{
                relation_bounds.negative_side,
                std::move(relation_bounds.negative_value), negative_origin,
                atom});
    BoundRef const positive_bound =
        relation_bounds.positive_side == BoundSide::Upper ? pair.upper
                                                          : pair.lower;
    BoundRef const negative_bound =
        relation_bounds.negative_side == BoundSide::Upper ? pair.upper
                                                          : pair.lower;

    generation_state_->engine->registration.addBound(RegisteredBound{
        positive_bound, row, positive_kind,
        std::move(positive_main), std::move(positive_delta), positive_origin,
        atom, true});
    generation_state_->engine->registration.addBound(RegisteredBound{
        negative_bound, row, negative_kind,
        std::move(negative_main), std::move(negative_delta), negative_origin,
        atom, false});
    generation_state_->engine->registration.addAtom(RegisteredAtom{
        atom, row, relation, std::move(atom_threshold), positive_origin,
        negative_origin, positive_bound, negative_bound});
    return InputResult<AtomId>{InputStatus::Accepted, atom};
  }
  catch (NumberFailure const& failure)
  {
    return InputResult<AtomId>{inputFailure(failure, mutated), std::nullopt};
  }
  catch (StorageFailure const& failure)
  {
    return InputResult<AtomId>{inputFailure(failure, mutated), std::nullopt};
  }
  catch (...)
  {
    return InputResult<AtomId>{inputFailure(), std::nullopt};
  }
}

InputStatus ExactLraCore::Impl::restartSearchState() noexcept
{
  const InputStatus opened = beginExtension();
  if (opened != InputStatus::Accepted)
    return opened;
  try
  {
    NumberOperationScope scope(generation_state_->budget);
    auto& engine = *generation_state_->engine;
    const auto& variables = engine.registration.baseVariables();
    const auto& rows = engine.registration.rows();
    const auto& originals = engine.registration.verificationRows();
    if (rows.size() != originals.size())
      throw EngineInvariantFailure("restart row coverage differs");
    engine.simplex.clearUnassertedTableau();
    // Structural columns and row auxiliaries may be interleaved by previous
    // extensions. Replay their allocation order so every identifier remains
    // identical; reconstructing all columns first would change pivot ties.
    std::size_t v = 0, r = 0;
    while (v < variables.size() || r < rows.size())
    {
      if (r < rows.size())
      {
        if (rows[r].id != originals[r].id)
          throw EngineInvariantFailure("restart row identity differs");
        // Aliases allocate no tableau variable or row. They can refer to an
        // older base ID, so exclude them from the allocation-order merge.
        if (rows[r].direct_coefficient)
        {
          ++r;
          continue;
        }
      }
      if (v < variables.size() &&
          (r == rows.size() || variables[v] < rows[r].auxiliary))
        engine.simplex.addVariable(variables[v++]);
      else
      {
        std::vector<ExactSimplex::RowTerm> terms;
        for (const auto& term : originals[r].terms)
          terms.push_back({term.variable, term.coefficient});
        engine.simplex.addRow(rows[r].auxiliary, std::move(terms));
        ++r;
      }
    }
    return initialize();
  }
  catch (NumberFailure const& failure)
  {
    return inputFailure(failure, true);
  }
  catch (StorageFailure const& failure)
  {
    return inputFailure(failure, true);
  }
  catch (...)
  {
    return inputFailure();
  }
}

InputStatus ExactLraCore::Impl::initialize()
{
  if (state_ != State::Building)
  {
    return InputStatus::InvalidState;
  }
  if (!prepareRevision())
  {
    return InputStatus::InternalError;
  }
  try
  {
    NumberOperationScope scope(generation_state_->budget);
    generation_state_->engine->simplex.initialize();
    if (!generation_state_->engine->simplex.invariantHolds())
    {
      throw EngineInvariantFailure(
                                   "simplex invariant failed at initialization");
    }
    state_ = State::Ready;
    return InputStatus::Accepted;
  }
  catch (NumberFailure const& failure)
  {
    return inputFailure(failure, false);
  }
  catch (StorageFailure const& failure)
  {
    return inputFailure(failure, false);
  }
  catch (...)
  {
    return inputFailure();
  }
}

InputResult<Checkpoint> ExactLraCore::Impl::push()
{
  // A consistent tableau can take a checkpoint too: that is a partial
  // assignment the search has checked and is about to extend.
  if (state_ != State::Ready && state_ != State::CandidateOpen &&
      state_ != State::Consistent && state_ != State::Interrupted)
  {
    return InputResult<Checkpoint>{InputStatus::InvalidState, std::nullopt};
  }
  if (!prepareRevision())
  {
    return InputResult<Checkpoint>{InputStatus::InternalError, std::nullopt};
  }
  bool mutated = false;
  try
  {
    NumberOperationScope scope(generation_state_->budget);
    Checkpoint const checkpoint = generation_state_->engine->simplex.push();
    mutated = true;
    generation_state_->engine->registration.push(checkpoint);
    state_ = State::CandidateOpen;
    increment(statistics_.pushes);
    return InputResult<Checkpoint>{InputStatus::Accepted, checkpoint};
  }
  catch (NumberFailure const& failure)
  {
    return InputResult<Checkpoint>{inputFailure(failure, mutated),
                                   std::nullopt};
  }
  catch (StorageFailure const& failure)
  {
    return InputResult<Checkpoint>{inputFailure(failure, mutated),
                                   std::nullopt};
  }
  catch (...)
  {
    return InputResult<Checkpoint>{inputFailure(), std::nullopt};
  }
}

InputStatus ExactLraCore::Impl::pop(Checkpoint checkpoint)
{
  if (state_ == State::Building || state_ == State::Ready ||
      state_ == State::Invalid ||
      !generation_state_->engine->registration.containsCheckpoint(checkpoint))
  {
    return state_ == State::Invalid ? InputStatus::InvalidState
                                    : InputStatus::InvalidId;
  }
  if (!prepareRevision())
  {
    return InputStatus::InternalError;
  }
  bool mutated = false;
  try
  {
    NumberOperationScope scope(generation_state_->budget);
    generation_state_->engine->simplex.pop(checkpoint);
    mutated = true;
    generation_state_->engine->registration.pop(checkpoint);
    generation_state_->pending_conflict_explanation.clear();
    state_ = generation_state_->engine->registration.levelCount() == 0
                 ? State::Ready
                 : State::CandidateOpen;
    increment(statistics_.pops);
    return InputStatus::Accepted;
  }
  catch (NumberFailure const& failure)
  {
    bool const unsafe = mutated || generation_state_->engine->simplex.pivotInProgress();
    return inputFailure(failure, unsafe);
  }
  catch (StorageFailure const& failure)
  {
    bool const unsafe = mutated || generation_state_->engine->simplex.pivotInProgress();
    return inputFailure(failure, unsafe);
  }
  catch (...)
  {
    return inputFailure();
  }
}

Conflict ExactLraCore::Impl::exportConflict(
    ExactSimplex::Explanation const& explanation) const
{
  if (explanation.empty())
  {
    throw EngineInvariantFailure("producer returned an empty conflict");
  }
  Conflict result{WitnessTag{generation_state_->engine->generation, revision_}, {}};
  result.terms.reserve(explanation.size());
  for (auto const& term : explanation)
  {
    if (!generation_state_->engine->registration.containsBound(term.bound) ||
        !generation_state_->engine->registration.isActive(term.bound) ||
        term.coefficient.sign() <= 0)
    {
      throw EngineInvariantFailure(
                                   "producer conflict contains invalid support");
    }
    RegisteredBound const& registered =
        generation_state_->engine->registration.bound(term.bound);
    EngineBound const& produced = generation_state_->engine->bounds[term.bound];
    if (!(registered.origin == produced.origin()))
    {
      throw EngineInvariantFailure(
                                   "producer and registration origins differ");
    }
    ExactRational weight = term.coefficient;
    const auto& row = generation_state_->engine->registration.row(registered.row);
    if (row.direct_coefficient && !row.direct_coefficient->isOne())
    {
      auto scale = *row.direct_coefficient;
      if (scale.sign() < 0)
        scale.negate();
      // The engine proved a combination of bounds divided by |a|. Export
      // weights over the original semantic a*x bounds for independent checking.
      weight /= scale;
    }
    result.terms.push_back(
        ConflictTerm{registered.origin, term.bound, std::move(weight)});
  }
  std::sort(result.terms.begin(), result.terms.end(),
            [](ConflictTerm const& lhs, ConflictTerm const& rhs) {
              return lhs.bound < rhs.bound;
            });
  for (std::size_t index = 1; index != result.terms.size(); ++index)
  {
    if (result.terms[index - 1U].bound == result.terms[index].bound)
    {
      throw EngineInvariantFailure(
                                   "producer conflict contains duplicate bounds");
    }
  }
  return result;
}

Model ExactLraCore::Impl::exportModel() const
{
  ExactRational const delta_substitution = generation_state_->engine->simplex.modelInfinitesimal();
  Model result{WitnessTag{generation_state_->engine->generation, revision_}, {}};
  std::vector<VariableId> const& base =
      generation_state_->engine->registration.baseVariables();
  std::vector<DeltaRational> symbolic;
  generation_state_->engine->simplex.values(base, symbolic);
  result.values.reserve(base.size());
  for (std::size_t index = 0; index != base.size(); ++index)
  {
    ExactRational concrete =
        symbolic[index].rational() + symbolic[index].infinitesimal() * delta_substitution;
    result.values.push_back(ModelValue{base[index], std::move(concrete)});
  }
  return result;
}

Conflict ExactLraCore::Impl::publishConflict(Conflict const& staged) const
{
  NumberOperationScope scope(witness_budget_);
  Conflict published{staged.tag, {}};
  published.terms.reserve(staged.terms.size());
  for (ConflictTerm const& term : staged.terms)
  {
    published.terms.push_back(
        ConflictTerm{term.origin, term.bound, term.weight});
  }
  return published;
}

Model ExactLraCore::Impl::publishModel(Model const& staged) const
{
  NumberOperationScope scope(witness_budget_);
  Model published{staged.tag, {}};
  published.values.reserve(staged.values.size());
  for (ModelValue const& value : staged.values)
  {
    published.values.push_back(ModelValue{value.variable, value.value});
  }
  return published;
}

VerificationResult ExactLraCore::Impl::runConflictVerifier(
    Conflict const& conflict) const
{
  // An explicit verification request always runs. Only the automatic
  // producer-side callers below may bypass this verifier.
  increment(statistics_.conflict_verifications);
#if defined(STP_LRA_TEST_FAULT_INJECTION)
  if (force_conflict_verification_resource_)
  {
    force_conflict_verification_resource_ = false;
    increment(statistics_.verification_failures);
    increment(statistics_.resource_stops);
    last_verification_error_ = VerificationError::ResourceLimit;
    return VerificationResult{VerificationError::ResourceLimit};
  }
#endif
  VerificationResult result{VerificationError::InternalError};
  try
  {
    NumberOperationScope scope(generation_state_->budget);
    result = verifyExactLraConflict(
        generation_state_->engine->registration.verificationData(
            WitnessTag{generation_state_->engine->generation, revision_}),
        conflict);
  }
  catch (NumberFailure const& failure)
  {
    result.error = isSafeResource(failure)
                       ? VerificationError::ResourceLimit
                       : VerificationError::InternalError;
  }
  catch (StorageFailure const& failure)
  {
    result.error = isSafeResource(failure)
                       ? VerificationError::ResourceLimit
                       : VerificationError::InternalError;
  }
  catch (...)
  {
    result.error = VerificationError::InternalError;
  }
  if (!result.verified())
  {
    increment(statistics_.verification_failures);
    if (result.error == VerificationError::ResourceLimit)
    {
      increment(statistics_.resource_stops);
    }
  }
  last_verification_error_ = result.error;
  return result;
}

VerificationResult ExactLraCore::Impl::runModelVerifier(
    Model const& model) const
{
  increment(statistics_.model_verifications);
#if defined(STP_LRA_TEST_FAULT_INJECTION)
  if (force_model_verification_resource_)
  {
    force_model_verification_resource_ = false;
    increment(statistics_.verification_failures);
    increment(statistics_.resource_stops);
    last_verification_error_ = VerificationError::ResourceLimit;
    return VerificationResult{VerificationError::ResourceLimit};
  }
#endif
  VerificationResult result{VerificationError::InternalError};
  try
  {
    NumberOperationScope scope(generation_state_->budget);
    result = verifyExactLraModel(
        generation_state_->engine->registration.verificationData(
            WitnessTag{generation_state_->engine->generation, revision_}),
        model);
  }
  catch (NumberFailure const& failure)
  {
    result.error = isSafeResource(failure)
                       ? VerificationError::ResourceLimit
                       : VerificationError::InternalError;
  }
  catch (StorageFailure const& failure)
  {
    result.error = isSafeResource(failure)
                       ? VerificationError::ResourceLimit
                       : VerificationError::InternalError;
  }
  catch (...)
  {
    result.error = VerificationError::InternalError;
  }
  if (!result.verified())
  {
    increment(statistics_.verification_failures);
    if (result.error == VerificationError::ResourceLimit)
    {
      increment(statistics_.resource_stops);
    }
  }
  last_verification_error_ = result.error;
  return result;
}

VerificationResult ExactLraCore::Impl::verifyConflict(
    Conflict const& conflict) const
{
  if (state_ != State::Conflict)
  {
    increment(statistics_.conflict_verifications);
    increment(statistics_.verification_failures);
    return VerificationResult{VerificationError::InternalError};
  }
  return runConflictVerifier(conflict);
}

VerificationResult ExactLraCore::Impl::verifyModel(Model const& model) const
{
  if (state_ != State::Consistent)
  {
    increment(statistics_.model_verifications);
    increment(statistics_.verification_failures);
    return VerificationResult{VerificationError::InternalError};
  }
  return runModelVerifier(model);
}

namespace
{
/* Recover a Farkas vector in the nullspace of the *original*, signed
 * support rows. Rounding its entries independently cannot preserve these
 * equations on dense, nonintegral inputs. The unknowns here are only the
 * proposed support's weights, not all variables/bounds in the tableau.
 *
 * Sparse echelon elimination uses short equations first. Free weights keep
 * the proposal's proportions; pivot weights are derived exactly. This is
 * advisory: missing support, negative weights, fill or arithmetic growth
 * all decline recovery, and the ordinary verifier judges every result. */
bool recoverConflictWeights(ExactLraRegistration const& registration,
                            Conflict& candidate,
                            ExactLraResourceObserver* observer,
                            std::size_t support_limit)
{
  const std::size_t max_support = std::min(support_limit, std::size_t{4096});
  const std::size_t max_cells = std::max(std::size_t{65536}, max_support * 128);
  const std::size_t max_work = max_support <= 512 ? 200000 : max_support * 512;
  constexpr std::uint64_t max_bits = 2048;
  const std::size_t count = candidate.terms.size();
  if (count == 0 || count > max_support)
    return false;
  std::size_t work = 0;
  const auto continuing = [&]()
  {
    return work <= max_work &&
           (observer == nullptr ||
            observer->pollBeforePivot() == StopReason::Continue);
  };
  const auto smallEnough = [&](ExactRational const& value)
  {
    return value.numeratorBits() <= max_bits &&
           value.denominatorBits() <= max_bits;
  };
  using Equation = std::map<std::size_t, ExactRational>;
  std::map<VariableId, Equation> equations;
  std::size_t cells = 0;
  for (std::size_t column = 0; column != count; ++column)
  {
    if (!continuing())
      return false;
    auto const& bound = registration.bound(candidate.terms[column].bound);
    auto const& row = registration.verificationRows().at(bound.row.ordinal());
    if (row.terms.size() > max_cells - cells)
      return false;
    cells += row.terms.size();
    for (auto const& term : row.terms)
    {
      if (!smallEnough(term.coefficient))
        return false;
      ExactRational coefficient = term.coefficient;
      if (bound.kind == RegisteredBoundKind::Lower)
        coefficient.negate();
      equations[term.variable].emplace(column, std::move(coefficient));
    }
  }
  std::vector<Equation*> order;
  order.reserve(equations.size());
  for (auto& entry : equations)
    order.push_back(&entry.second);
  std::stable_sort(order.begin(), order.end(),
                   [](Equation const* lhs, Equation const* rhs)
                   { return lhs->size() < rhs->size(); });
  std::vector<Equation> basis(count);
  std::size_t basis_cells = 0;
  for (Equation* equation : order)
  {
    while (!equation->empty())
    {
      if (!continuing())
        return false;
      const std::size_t column = equation->begin()->first;
      auto const& pivot = basis[column];
      if (pivot.empty())
      {
        if (equation->size() > max_cells - basis_cells)
          return false;
        const ExactRational divisor = equation->begin()->second;
        for (auto& term : *equation)
        {
          term.second /= divisor;
          if (++work > max_work || !smallEnough(term.second))
            return false;
        }
        basis_cells += equation->size();
        basis[column] = std::move(*equation);
        break;
      }
      const ExactRational factor = equation->begin()->second;
      equation->erase(equation->begin());
      for (auto term = std::next(pivot.begin()); term != pivot.end(); ++term)
      {
        if (++work > max_work || (work % 512 == 0 && !continuing()))
          return false;
        ExactRational contribution = factor * term->second;
        auto found = equation->find(term->first);
        if (found == equation->end())
        {
          contribution.negate();
          found = equation->emplace(term->first, std::move(contribution)).first;
        }
        else
          found->second -= contribution;
        if (!smallEnough(found->second))
          return false;
        if (found->second.isZero())
          equation->erase(found);
      }
    }
  }
  // Normalize by the largest free hint. In the usual one-dimensional
  // nullspace the sole free weight is one, avoiding the approximate
  // denominator in every reconstructed entry.
  ExactRational scale(std::int64_t{0});
  for (std::size_t column = 0; column != count; ++column)
    if (basis[column].empty() && scale < candidate.terms[column].weight)
      scale = candidate.terms[column].weight;
  if (scale.isZero())
    return false;
  std::vector<ExactRational> weights(count, ExactRational(std::int64_t{0}));
  for (std::size_t remaining = count; remaining != 0; --remaining)
  {
    if (!continuing())
      return false;
    const std::size_t column = remaining - 1;
    auto const& pivot = basis[column];
    if (pivot.empty())
      weights[column] = candidate.terms[column].weight / scale;
    else
      for (auto term = std::next(pivot.begin()); term != pivot.end(); ++term)
      {
        weights[column] -= term->second * weights[term->first];
        if (++work > max_work || !smallEnough(weights[column]))
          return false;
      }
    if (weights[column].sign() < 0 || !smallEnough(weights[column]))
      return false;
  }
  for (std::size_t column = 0; column != count; ++column)
    candidate.terms[column].weight = std::move(weights[column]);
  candidate.terms.erase(std::remove_if(candidate.terms.begin(),
                                       candidate.terms.end(),
                                       [](ConflictTerm const& term)
                                       { return term.weight.isZero(); }),
                        candidate.terms.end());
  return !candidate.terms.empty();
}
} // namespace

InputResult<Conflict> ExactLraCore::Impl::certifyCandidateConflict(
    ConflictCandidateTerm const* begin, ConflictCandidateTerm const* end,
    bool recover_weights, ExactLraResourceObserver* observer,
    std::size_t recovery_support_limit)
{
  /* Read-only judgement of an externally proposed Farkas certificate: no
   * state transition, no revision, no requirement that the cited bounds
   * are asserted here -- the caller's search asserts them, and the exact
   * combination is what makes the resulting clause theory-valid.  Any
   * post-build state may ask. */
  if (state_ == State::Building || state_ == State::Invalid ||
      state_ == State::ResourceLimit)
  {
    return InputResult<Conflict>{InputStatus::InvalidState, std::nullopt};
  }
  if (begin == end)
  {
    return InputResult<Conflict>{InputStatus::Unsupported, std::nullopt};
  }
  try
  {
    NumberOperationScope scope(witness_budget_);
    Conflict candidate{
        WitnessTag{generation_state_->engine->generation, revision_}, {}};
    candidate.terms.reserve(static_cast<std::size_t>(end - begin));
    for (ConflictCandidateTerm const* term = begin; term != end; ++term)
    {
      if (!generation_state_->engine->registration.containsAtom(term->atom))
      {
        return InputResult<Conflict>{InputStatus::InvalidId, std::nullopt};
      }
      RegisteredAtom const& atom =
          generation_state_->engine->registration.atom(term->atom);
      candidate.terms.push_back(ConflictTerm{
          term->positive ? atom.positive_origin : atom.negative_origin,
          term->positive ? atom.positive_bound : atom.negative_bound,
          term->weight});
    }
    std::sort(candidate.terms.begin(), candidate.terms.end(),
              [](ConflictTerm const& lhs, ConflictTerm const& rhs) {
                return lhs.bound < rhs.bound;
              });
    for (std::size_t index = 1; index != candidate.terms.size(); ++index)
    {
      if (candidate.terms[index - 1U].bound == candidate.terms[index].bound)
      {
        return InputResult<Conflict>{InputStatus::Duplicate, std::nullopt};
      }
    }
    increment(statistics_.conflict_verifications);
    bool const audit_snapshot = !(certificate_audit_generation_ ==
                                  generation_state_->engine->generation);
    VerificationResult verified = verifyExactLraConflictCandidate(
        generation_state_->engine->registration.verificationData(candidate.tag),
        candidate, audit_snapshot);
    if (recover_weights &&
        verified.error == VerificationError::NotContradictory)
    {
      // NotContradictory means the snapshot/IDs/weights passed the audit.
      // The reconstruction never edits registration or the warm tableau.
      if (audit_snapshot)
        certificate_audit_generation_ = generation_state_->engine->generation;
      increment(statistics_.conflict_recovery_attempts);
      const auto start = std::chrono::steady_clock::now();
      const bool recovered = recoverConflictWeights(
          generation_state_->engine->registration, candidate, observer,
          recovery_support_limit);
      if (recovered)
      {
        increment(statistics_.conflict_verifications);
        verified = verifyExactLraConflictCandidate(
            generation_state_->engine->registration.verificationData(
                candidate.tag),
            candidate, false);
        if (verified.verified())
          increment(statistics_.conflict_recoveries);
      }
      addMetric(statistics_.conflict_recovery_nanoseconds,
                static_cast<std::uint64_t>(
                    std::chrono::duration_cast<std::chrono::nanoseconds>(
                        std::chrono::steady_clock::now() - start)
                        .count()));
    }
    if (!verified.verified())
    {
      increment(statistics_.verification_failures);
      last_verification_error_ = verified.error;
      return InputResult<Conflict>{
          verified.error == VerificationError::ResourceLimit
              ? InputStatus::ResourceLimit
              : InputStatus::Unsupported,
          std::nullopt};
    }
    if (audit_snapshot)
      certificate_audit_generation_ = generation_state_->engine->generation;
    return InputResult<Conflict>{InputStatus::Accepted,
                                 std::move(candidate)};
  }
  catch (NumberFailure const& failure)
  {
    return InputResult<Conflict>{isSafeResource(failure)
                                     ? InputStatus::ResourceLimit
                                     : InputStatus::InternalError,
                                 std::nullopt};
  }
  catch (StorageFailure const& failure)
  {
    return InputResult<Conflict>{isSafeResource(failure)
                                     ? InputStatus::ResourceLimit
                                     : InputStatus::InternalError,
                                 std::nullopt};
  }
  catch (...)
  {
    return InputResult<Conflict>{InputStatus::InternalError, std::nullopt};
  }
}

namespace
{
// Repair must remain cheaper than an unbounded exact search. Count scans as
// well as arithmetic so sparse/zero cells cannot bypass the work allowance.
class ModelRepairBudget final
{
 public:
  explicit ModelRepairBudget(ExactLraResourceObserver* observer)
      : observer_(observer)
  {}

  bool poll()
  {
    stopped_ |= observer_ != nullptr &&
                observer_->pollBeforePivot() != StopReason::Continue;
    return !stopped_;
  }
  bool canSpend(std::size_t work) const { return work <= remaining_; }
  bool spend(std::size_t work = 1)
  {
    if (stopped_ || !canSpend(work))
      return false;
    std::size_t const previous = remaining_;
    remaining_ -= work;
    return previous / 256 == remaining_ / 256 || poll();
  }
  static bool small(ExactRational const& value)
  {
    return value.numeratorBits() <= 2048 && value.denominatorBits() <= 2048;
  }
  static bool subtractProduct(ExactRational& target,
                              ExactRational const& lhs,
                              ExactRational const& rhs)
  {
    ExactRational product = lhs * rhs;
    if (!small(product))
      return false;
    target -= product;
    return small(target);
  }

 private:
  ExactLraResourceObserver* observer_;
  std::size_t remaining_ = 200000;
  bool stopped_ = false;
};

/* The pinned equality system, dense over the columns the pinned rows
 * mention.  Solved by exact Gaussian elimination, first nonzero as
 * pivot; free columns keep the proposed coordinates; an inconsistent
 * system reports failure and the caller stays with the rejection. */
struct PinnedEquation final
{
  std::vector<std::pair<std::size_t, ExactRational>> terms;
  ExactRational value{std::int64_t{0}};
  ExactRational delta{std::int64_t{0}};
};

struct PinnedSystem final
{
  /* Dense column -> position in the base-variable order. */
  std::vector<std::size_t> columns;
  std::vector<PinnedEquation> equations;
};

bool solvePinnedSystem(PinnedSystem const& system,
                       std::vector<ModelCandidateValue>& refined,
                       ModelRepairBudget& budget)
{
  std::size_t const equation_count = system.equations.size();
  std::size_t const column_count = system.columns.size();
  if (equation_count == 0 || column_count == 0 || equation_count > 4096 ||
      column_count > 4096 ||
      equation_count * column_count > (std::size_t{1} << 22))
    return false;
  if (!budget.poll() || !budget.canSpend(equation_count * column_count))
    return false;
  std::vector<ExactRational> matrix;
  matrix.reserve(equation_count * column_count);
  for (std::size_t cell = 0; cell != equation_count * column_count; ++cell)
  {
    if (!budget.spend())
      return false;
    matrix.emplace_back(std::int64_t{0});
  }
  std::vector<ExactRational> side_value;
  std::vector<ExactRational> side_delta;
  side_value.reserve(equation_count);
  side_delta.reserve(equation_count);
  for (std::size_t row = 0; row != equation_count; ++row)
  {
    for (auto const& term : system.equations[row].terms)
    {
      if (!budget.spend())
        return false;
      matrix[row * column_count + term.first] += term.second;
      if (!budget.small(matrix[row * column_count + term.first]))
        return false;
    }
    if (!budget.spend(2))
      return false;
    side_value.push_back(system.equations[row].value);
    side_delta.push_back(system.equations[row].delta);
  }
  std::vector<std::size_t> pivot_column;
  std::size_t rank = 0;
  for (std::size_t column = 0;
       column != column_count && rank != equation_count; ++column)
  {
    if (!budget.poll())
      return false;
    std::size_t pivot = rank;
    while (pivot != equation_count)
    {
      if (!budget.spend())
        return false;
      if (!matrix[pivot * column_count + column].isZero())
        break;
      ++pivot;
    }
    if (pivot == equation_count)
      continue;
    if (pivot != rank)
    {
      for (std::size_t j = column; j != column_count; ++j)
      {
        if (!budget.spend())
          return false;
        std::swap(matrix[rank * column_count + j],
                  matrix[pivot * column_count + j]);
      }
      std::swap(side_value[rank], side_value[pivot]);
      std::swap(side_delta[rank], side_delta[pivot]);
    }
    for (std::size_t row = rank + 1; row != equation_count; ++row)
    {
      if (!budget.spend())
        return false;
      if (matrix[row * column_count + column].isZero())
        continue;
      ExactRational const factor = matrix[row * column_count + column] /
                                   matrix[rank * column_count + column];
      if (!budget.small(factor))
        return false;
      for (std::size_t j = column; j != column_count; ++j)
      {
        if (!budget.spend())
          return false;
        if (!matrix[rank * column_count + j].isZero() &&
            !budget.subtractProduct(matrix[row * column_count + j], factor,
                                    matrix[rank * column_count + j]))
          return false;
      }
      if (!budget.spend(2) ||
          !budget.subtractProduct(side_value[row], factor, side_value[rank]) ||
          !budget.subtractProduct(side_delta[row], factor, side_delta[rank]))
        return false;
    }
    pivot_column.push_back(column);
    ++rank;
  }
  /* Zero coefficients against a nonzero side: the pinned classification
   * was wrong. */
  for (std::size_t row = rank; row != equation_count; ++row)
    if (!budget.spend() || !side_value[row].isZero() ||
        !side_delta[row].isZero())
      return false;
  /* Free columns keep the proposals; pivot columns resolve bottom-up,
   * where everything to the right of a pivot is already known. */
  std::vector<ExactRational> solution_value;
  std::vector<ExactRational> solution_delta;
  solution_value.reserve(column_count);
  solution_delta.reserve(column_count);
  for (std::size_t column = 0; column != column_count; ++column)
  {
    if (!budget.spend())
      return false;
    ModelCandidateValue const& hint = refined[system.columns[column]];
    if (!budget.small(hint.value) || !budget.small(hint.delta))
      return false;
    solution_value.push_back(hint.value);
    solution_delta.push_back(hint.delta);
  }
  for (std::size_t solved = rank; solved != 0; --solved)
  {
    if (!budget.poll())
      return false;
    std::size_t const row = solved - 1;
    std::size_t const column = pivot_column[row];
    ExactRational value = side_value[row];
    ExactRational delta = side_delta[row];
    for (std::size_t j = column + 1; j != column_count; ++j)
    {
      if (!budget.spend())
        return false;
      ExactRational const& cell = matrix[row * column_count + j];
      if (cell.isZero())
        continue;
      if ((!solution_value[j].isZero() &&
           !budget.subtractProduct(value, cell, solution_value[j])) ||
          (!solution_delta[j].isZero() &&
           !budget.subtractProduct(delta, cell, solution_delta[j])))
        return false;
    }
    if (!budget.spend(2))
      return false;
    solution_value[column] = value / matrix[row * column_count + column];
    solution_delta[column] = delta / matrix[row * column_count + column];
    if (!budget.small(solution_value[column]) ||
        !budget.small(solution_delta[column]))
      return false;
  }
  for (std::size_t column = 0; column != column_count; ++column)
  {
    if (!budget.spend())
      return false;
    ModelCandidateValue& target = refined[system.columns[column]];
    target.value = solution_value[column];
    target.delta = solution_delta[column];
  }
  return budget.poll();
}
}  // namespace

InputResult<Model> ExactLraCore::Impl::certifyCandidateModel(
    ModelCandidateValue const* values_begin,
    ModelCandidateValue const* values_end,
    CandidateBound const* bounds_begin, CandidateBound const* bounds_end,
    CandidateBound const* pinned_begin, CandidateBound const* pinned_end,
    ExactLraResourceObserver* observer)
{
  /* Read-only, like the conflict counterpart: resolve the named atoms'
   * bounds, pick a concrete epsilon that keeps every strict margin, and
   * verify the substituted model exactly against exactly those bounds. */
  if (state_ == State::Building || state_ == State::Invalid ||
      state_ == State::ResourceLimit)
  {
    return InputResult<Model>{InputStatus::InvalidState, std::nullopt};
  }
  if (values_begin == values_end)
  {
    return InputResult<Model>{InputStatus::Unsupported, std::nullopt};
  }
  try
  {
    NumberOperationScope scope(witness_budget_);
    StopReason stopped = StopReason::Continue;
    auto const continuing = [&]() {
      if (stopped == StopReason::Continue && observer != nullptr)
        stopped = observer->pollBeforePivot();
      return stopped == StopReason::Continue;
    };
    if (!continuing())
      return InputResult<Model>{InputStatus::Unsupported, std::nullopt};
    auto const& registration = generation_state_->engine->registration;
    std::vector<VariableId> const& base = registration.baseVariables();
    std::size_t const value_count =
        static_cast<std::size_t>(values_end - values_begin);
    if (value_count != base.size())
    {
      return InputResult<Model>{InputStatus::InvalidId, std::nullopt};
    }
    for (std::size_t index = 0; index != value_count; ++index)
    {
      if (index % 256 == 0 && !continuing())
        return InputResult<Model>{InputStatus::Unsupported, std::nullopt};
      if (!(values_begin[index].variable == base[index]))
      {
        return InputResult<Model>{InputStatus::InvalidId, std::nullopt};
      }
    }
    std::vector<BoundRef> references;
    references.reserve(static_cast<std::size_t>(bounds_end - bounds_begin));
    for (CandidateBound const* bound = bounds_begin; bound != bounds_end;
         ++bound)
    {
      if (references.size() % 256 == 0 && !continuing())
        return InputResult<Model>{InputStatus::Unsupported, std::nullopt};
      if (!registration.containsAtom(bound->atom))
      {
        return InputResult<Model>{InputStatus::InvalidId, std::nullopt};
      }
      RegisteredAtom const& atom = registration.atom(bound->atom);
      references.push_back(bound->positive ? atom.positive_bound
                                           : atom.negative_bound);
    }
    /* Symbolic row values, evaluated on demand. */
    std::vector<ExactLraVerificationRow> const& rows =
        registration.verificationRows();
    for (BoundRef reference : references)
    {
      if (registration.bound(reference).row.ordinal() >= rows.size())
      {
        return InputResult<Model>{InputStatus::InvalidId, std::nullopt};
      }
    }
    auto const base_index = [&base](VariableId variable) {
      auto const found =
          std::lower_bound(base.begin(), base.end(), variable);
      if (found == base.end() || !(*found == variable))
        throw EngineInvariantFailure(
                                     "candidate model row references an unknown base");
      return static_cast<std::size_t>(found - base.begin());
    };
    /* One certification attempt over one symbolic assignment: the
     * concrete epsilon by the engine's modelInfinitesimal rule over the
     * certificate's bounds, substitution, exact verification. */
    InputStatus failure_status = InputStatus::Unsupported;
    auto const attempt =
        [&](ModelCandidateValue const* proposed) -> std::optional<Model> {
      if (!continuing())
        return std::nullopt;
      std::vector<char> row_ready(rows.size(), 0);
      std::vector<ExactRational> row_value;
      std::vector<ExactRational> row_delta;
      row_value.reserve(rows.size());
      row_delta.reserve(rows.size());
      for (std::size_t index = 0; index != rows.size(); ++index)
      {
        if (index % 256 == 0 && !continuing())
          return std::nullopt;
        row_value.emplace_back(std::int64_t{0});
        row_delta.emplace_back(std::int64_t{0});
      }
      std::size_t evaluation_work = 0;
      auto const eval_row = [&](std::size_t ordinal) {
        if (row_ready[ordinal] == 0)
        {
          for (LinearTerm const& term : rows[ordinal].terms)
          {
            if (++evaluation_work % 256 == 0 && !continuing())
              return false;
            std::size_t const index = base_index(term.variable);
            row_value[ordinal] +=
                term.coefficient * proposed[index].value;
            if (!proposed[index].delta.isZero())
              row_delta[ordinal] +=
                  term.coefficient * proposed[index].delta;
          }
          row_ready[ordinal] = 1;
        }
        return true;
      };
      /* The concrete epsilon: the engine's modelInfinitesimal rule, over the
       * certificate's bounds. */
      std::optional<ExactRational> limiting;
      for (BoundRef reference : references)
      {
        if (++evaluation_work % 256 == 0 && !continuing())
          return std::nullopt;
        RegisteredBound const& bound = registration.bound(reference);
        std::size_t const ordinal = bound.row.ordinal();
        if (!eval_row(ordinal))
          return std::nullopt;
        ExactRational const& value = row_value[ordinal];
        ExactRational const& delta = row_delta[ordinal];
        if (delta.isZero())
          continue;
        if (bound.kind == RegisteredBoundKind::Lower)
        {
          if (bound.threshold < value && bound.infinitesimal > delta)
          {
            ExactRational ratio = (value - bound.threshold) /
                                  (bound.infinitesimal - delta);
            if (!limiting || ratio < *limiting)
              limiting = std::move(ratio);
          }
        }
        else
        {
          if (value < bound.threshold && delta > bound.infinitesimal)
          {
            ExactRational ratio = (bound.threshold - value) /
                                  (delta - bound.infinitesimal);
            if (!limiting || ratio < *limiting)
              limiting = std::move(ratio);
          }
        }
      }
      ExactRational const one(std::int64_t{1});
      ExactRational epsilon(std::int64_t{1});
      if (limiting && !(one < *limiting))
        epsilon = *limiting / ExactRational(std::int64_t{2});
      Model candidate{
          WitnessTag{generation_state_->engine->generation, revision_}, {}};
      candidate.values.reserve(value_count);
      for (std::size_t index = 0; index != value_count; ++index)
      {
        if (index % 256 == 0 && !continuing())
          return std::nullopt;
        ExactRational concrete = proposed[index].value;
        if (!proposed[index].delta.isZero())
          concrete += proposed[index].delta * epsilon;
        candidate.values.push_back(
            ModelValue{proposed[index].variable, std::move(concrete)});
      }
      if (!continuing())
        return std::nullopt;
      increment(statistics_.model_verifications);
      bool const audit_snapshot = !(certificate_audit_generation_ ==
                                    generation_state_->engine->generation);
      VerificationResult const verified = verifyExactLraModelCandidate(
          generation_state_->engine->registration.verificationData(
              candidate.tag),
          candidate, references.data(),
          references.data() + references.size(), audit_snapshot);
      if (!continuing())
        return std::nullopt;
      if (!verified.verified())
      {
        increment(statistics_.verification_failures);
        last_verification_error_ = verified.error;
        failure_status = verified.error == VerificationError::ResourceLimit
                             ? InputStatus::ResourceLimit
                             : InputStatus::Unsupported;
        return std::nullopt;
      }
      if (audit_snapshot)
        certificate_audit_generation_ =
            generation_state_->engine->generation;
      return candidate;
    };
    if (std::optional<Model> direct = attempt(values_begin))
    {
      return InputResult<Model>{InputStatus::Accepted, std::move(*direct)};
    }
    if (failure_status == InputStatus::ResourceLimit ||
        pinned_begin == pinned_end || !continuing())
    {
      return InputResult<Model>{failure_status, std::nullopt};
    }
    /* The exact repair: each pinned bound is one equation -- its row's
     * terms against the threshold in the value coordinate and the
     * bound's infinitesimal in the delta coordinate -- and the solved
     * coordinates replace the proposals where the system determines
     * them.  A double cannot carry the vertices decimal instances
     * produce; the rows and thresholds here can. */
    ModelRepairBudget repair_budget(observer);
    std::size_t const pinned_count =
        static_cast<std::size_t>(pinned_end - pinned_begin);
    if (pinned_count > 4096 || !repair_budget.poll() ||
        !repair_budget.spend(base.size()))
      return InputResult<Model>{InputStatus::Unsupported, std::nullopt};
    PinnedSystem system;
    {
      std::size_t const kNoColumn = ~std::size_t{0};
      std::vector<std::size_t> column_of(base.size(), kNoColumn);
      for (CandidateBound const* pinned = pinned_begin; pinned != pinned_end;
           ++pinned)
      {
        if (!repair_budget.spend())
          return InputResult<Model>{InputStatus::Unsupported, std::nullopt};
        if (!registration.containsAtom(pinned->atom))
          return InputResult<Model>{InputStatus::InvalidId, std::nullopt};
        RegisteredAtom const& atom = registration.atom(pinned->atom);
        BoundRef const reference = pinned->positive ? atom.positive_bound
                                                    : atom.negative_bound;
        RegisteredBound const& bound = registration.bound(reference);
        if (bound.row.ordinal() >= rows.size())
          return InputResult<Model>{InputStatus::InvalidId, std::nullopt};
        if (!repair_budget.small(bound.threshold) ||
            !repair_budget.small(bound.infinitesimal))
          return InputResult<Model>{InputStatus::Unsupported, std::nullopt};
        PinnedEquation equation;
        for (LinearTerm const& term : rows[bound.row.ordinal()].terms)
        {
          if (!repair_budget.spend() || !repair_budget.small(term.coefficient))
            return InputResult<Model>{InputStatus::Unsupported, std::nullopt};
          std::size_t const position = base_index(term.variable);
          if (column_of[position] == kNoColumn)
          {
            column_of[position] = system.columns.size();
            system.columns.push_back(position);
          }
          equation.terms.emplace_back(column_of[position],
                                      term.coefficient);
        }
        equation.value = bound.threshold;
        equation.delta = bound.infinitesimal;
        system.equations.push_back(std::move(equation));
      }
    }
    if (!repair_budget.canSpend(value_count))
      return InputResult<Model>{InputStatus::Unsupported, std::nullopt};
    std::vector<ModelCandidateValue> refined;
    refined.reserve(value_count);
    for (ModelCandidateValue const* value = values_begin; value != values_end;
         ++value)
    {
      if (!repair_budget.spend() || !repair_budget.small(value->value) ||
          !repair_budget.small(value->delta))
        return InputResult<Model>{InputStatus::Unsupported, std::nullopt};
      refined.push_back(*value);
    }
    bool const solved = solvePinnedSystem(system, refined, repair_budget);
    if (!solved)
    {
      return InputResult<Model>{failure_status, std::nullopt};
    }
    increment(statistics_.model_repairs);
    if (std::optional<Model> repaired = attempt(refined.data()))
    {
      return InputResult<Model>{InputStatus::Accepted,
                                std::move(*repaired)};
    }
    return InputResult<Model>{failure_status, std::nullopt};
  }
  catch (NumberFailure const& failure)
  {
    return InputResult<Model>{isSafeResource(failure)
                                  ? InputStatus::ResourceLimit
                                  : InputStatus::InternalError,
                              std::nullopt};
  }
  catch (StorageFailure const& failure)
  {
    return InputResult<Model>{isSafeResource(failure)
                                  ? InputStatus::ResourceLimit
                                  : InputStatus::InternalError,
                              std::nullopt};
  }
  catch (...)
  {
    return InputResult<Model>{InputStatus::InternalError, std::nullopt};
  }
}

AssertResult ExactLraCore::Impl::assertLiteral(AtomId atom, bool positive)
{
  /* An interrupted check stops between pivots and rolls nothing back: the
   * pivots it made stand, as after any check, and the bounds are kept, so
   * the core takes input again: a driver that stops a partial check at a
   * budget goes on asserting. */
  if ((state_ != State::CandidateOpen && state_ != State::Consistent &&
       state_ != State::Interrupted) ||
      generation_state_->engine->registration.levelCount() == 0)
  {
    return AssertResult{InputStatus::InvalidState, std::nullopt};
  }
  if (!generation_state_->engine->registration.containsAtom(atom))
  {
    return AssertResult{InputStatus::InvalidId, std::nullopt};
  }
  std::optional<bool> const active =
      generation_state_->engine->registration.activePolarity(atom);
  if (active && *active == positive)
  {
    return AssertResult{InputStatus::Duplicate, std::nullopt};
  }
  if (!prepareRevision())
  {
    return AssertResult{InputStatus::InternalError, std::nullopt};
  }

  bool facade_mutated = false;
  try
  {
    RegisteredAtom const& atom_record =
        generation_state_->engine->registration.atom(atom);
    BoundRef const reference =
        positive ? atom_record.positive_bound : atom_record.negative_bound;
    ExactSimplex::Explanation explanation;
    {
      NumberOperationScope scope(generation_state_->budget);
      explanation = generation_state_->engine->simplex.assertBound(reference);
    }
    increment(statistics_.assertions);
    if (!explanation.empty())
    {
      generation_state_->engine->registration.setPendingConflictBound(
          reference);
      facade_mutated = true;
      Conflict staged{WitnessTag{}, {}};
      {
        NumberOperationScope scope(generation_state_->budget);
        staged = exportConflict(explanation);
      }
      Conflict conflict = publishConflict(staged);
      generation_state_->pending_conflict_explanation = std::move(explanation);
      VerificationResult const verification =
          verify_conflicts_ ? runConflictVerifier(conflict)
                            : VerificationResult{VerificationError::None};
      if (!verification.verified())
      {
        if (verification.error == VerificationError::ResourceLimit)
        {
          state_ = State::ResourceLimit;
          return AssertResult{InputStatus::ResourceLimit, std::nullopt};
        }
        invalidate();
        return AssertResult{InputStatus::InternalError, std::nullopt};
      }
      state_ = State::Conflict;
      increment(statistics_.immediate_conflicts);
      increment(statistics_.conflicts_produced);
      AssertResult result{InputStatus::Accepted, std::move(conflict)};
      if (!exactLraAssertResultShapeValid(result))
      {
        invalidate();
        return AssertResult{InputStatus::InternalError, std::nullopt};
      }
      return result;
    }
    generation_state_->engine->registration.activate(reference);
    state_ = State::CandidateOpen;
    return AssertResult{InputStatus::Accepted, std::nullopt};
  }
  catch (NumberFailure const& failure)
  {
    if (!facade_mutated && isSafeResource(failure) &&
        !generation_state_->engine->simplex.pivotInProgress())
    {
      increment(statistics_.resource_stops);
      return AssertResult{InputStatus::ResourceLimit, std::nullopt};
    }
    return AssertResult{inputFailure(failure, true), std::nullopt};
  }
  catch (StorageFailure const& failure)
  {
    if (!facade_mutated && isSafeResource(failure) &&
        !generation_state_->engine->simplex.pivotInProgress())
    {
      increment(statistics_.resource_stops);
      return AssertResult{InputStatus::ResourceLimit, std::nullopt};
    }
    return AssertResult{inputFailure(failure, true), std::nullopt};
  }
  catch (...)
  {
    return AssertResult{inputFailure(), std::nullopt};
  }
}

CheckResult ExactLraCore::Impl::checkFailure(
    NumberFailure const& failure) noexcept
{
  if (isSafeResource(failure) && !generation_state_->engine->simplex.pivotInProgress())
  {
    state_ = State::ResourceLimit;
    increment(statistics_.resource_stops);
    return CheckResult{CheckStatus::ResourceLimit, std::nullopt,
                       std::nullopt};
  }
  return checkFailure();
}

CheckResult ExactLraCore::Impl::checkFailure(
    StorageFailure const& failure) noexcept
{
  if (isSafeResource(failure) && !generation_state_->engine->simplex.pivotInProgress())
  {
    state_ = State::ResourceLimit;
    increment(statistics_.resource_stops);
    return CheckResult{CheckStatus::ResourceLimit, std::nullopt,
                       std::nullopt};
  }
  return checkFailure();
}

CheckResult ExactLraCore::Impl::checkFailure() noexcept
{
  invalidate();
  return CheckResult{CheckStatus::InternalError, std::nullopt, std::nullopt};
}

CheckResult ExactLraCore::Impl::check(ExactLraResourceObserver& observer,
                                      bool verify_model)
{
  if (state_ != State::CandidateOpen && state_ != State::Interrupted &&
      state_ != State::ResourceLimit && state_ != State::Consistent &&
      state_ != State::Conflict)
  {
    return CheckResult{CheckStatus::InternalError, std::nullopt,
                       std::nullopt};
  }
  if (!prepareRevision())
  {
    return CheckResult{CheckStatus::InternalError, std::nullopt,
                       std::nullopt};
  }
  increment(statistics_.checks);
  try
  {
    if (generation_state_->engine->registration.pendingConflictBound())
    {
      if (generation_state_->pending_conflict_explanation.empty())
      {
        throw EngineInvariantFailure(
                                     "pending conflict explanation is absent");
      }
      Conflict staged{WitnessTag{}, {}};
      {
        NumberOperationScope scope(generation_state_->budget);
        staged =
            exportConflict(generation_state_->pending_conflict_explanation);
      }
      Conflict conflict = publishConflict(staged);
      VerificationResult const verification =
          verify_conflicts_ ? runConflictVerifier(conflict)
                            : VerificationResult{VerificationError::None};
      if (!verification.verified())
      {
        if (verification.error == VerificationError::ResourceLimit)
        {
          state_ = State::ResourceLimit;
          return CheckResult{CheckStatus::ResourceLimit, std::nullopt,
                             std::nullopt};
        }
        return checkFailure();
      }
      state_ = State::Conflict;
      increment(statistics_.immediate_conflicts);
      increment(statistics_.conflicts_produced);
      CheckResult published{CheckStatus::Conflict, std::move(conflict),
                            std::nullopt};
      if (!exactLraCheckResultShapeValid(published))
      {
        return checkFailure();
      }
      return published;
    }

    ObserverAdapter adapter(*this, observer);
    ExactSimplex::Result result{ExactSimplex::ResultStatus::Interrupted,
                                    {}};
    {
      NumberOperationScope scope(generation_state_->budget);
      result = generation_state_->engine->simplex.check(adapter);
    }
    switch (result.status)
    {
      case ExactSimplex::ResultStatus::Interrupted:
        state_ = State::Interrupted;
        increment(statistics_.interruptions);
        return CheckResult{CheckStatus::Interrupted, std::nullopt,
                           std::nullopt};
      case ExactSimplex::ResultStatus::ResourceLimit:
        state_ = State::ResourceLimit;
        increment(statistics_.resource_stops);
        return CheckResult{CheckStatus::ResourceLimit, std::nullopt,
                           std::nullopt};
      case ExactSimplex::ResultStatus::Satisfied:
      {
        // A partial assignment's consistency is the whole of what its
        // caller wants: no model is exported, walked or verified for it.
        // The final check keeps all three.
        if (!verify_model)
        {
          state_ = State::Consistent;
          return CheckResult{CheckStatus::Consistent, std::nullopt,
                             std::nullopt};
        }
        Model staged{WitnessTag{}, {}};
        {
          NumberOperationScope scope(generation_state_->budget);
          // Break accidental value coincidences before the model is read
          // out, so that a reader which groups by value -- the lazy
          // congruence round does -- is not handed pairs the query never
          // asked for. Everything below still checks this model: the
          // invariant immediately, the verifier just after.
          if (separate_model_values_)
            generation_state_->engine->simplex.separateCoincidentValues();
          staged = exportModel();
          if (!generation_state_->engine->simplex.invariantHolds())
          {
            throw EngineInvariantFailure(
                                         "simplex invariant failed after model production");
          }
        }
        Model model = publishModel(staged);
        if (model.tag.generation != generation_state_->engine->generation)
        {
          throw EngineInvariantFailure(
                                       "published model generation changed during copy");
        }
        // A model nobody will read -- a partial assignment's -- is not
        // re-derived; the final one still is.
        VerificationResult const verification =
            verify_model ? runModelVerifier(model)
                         : VerificationResult{VerificationError::None};
        if (!verification.verified())
        {
          if (verification.error == VerificationError::ResourceLimit)
          {
            state_ = State::ResourceLimit;
            return CheckResult{CheckStatus::ResourceLimit, std::nullopt,
                               std::nullopt};
          }
          return checkFailure();
        }
        state_ = State::Consistent;
        increment(statistics_.models_produced);
        CheckResult published{CheckStatus::Consistent, std::nullopt,
                              std::move(model)};
        if (!exactLraCheckResultShapeValid(published))
        {
          return checkFailure();
        }
        return published;
      }
      case ExactSimplex::ResultStatus::Unsatisfied:
      {
        Conflict staged{WitnessTag{}, {}};
        {
          NumberOperationScope scope(generation_state_->budget);
          staged = exportConflict(result.explanation);
        }
        Conflict conflict = publishConflict(staged);
        VerificationResult const verification =
            verify_conflicts_ ? runConflictVerifier(conflict)
                              : VerificationResult{VerificationError::None};
        if (!verification.verified())
        {
          if (verification.error == VerificationError::ResourceLimit)
          {
            state_ = State::ResourceLimit;
            return CheckResult{CheckStatus::ResourceLimit, std::nullopt,
                               std::nullopt};
          }
          return checkFailure();
        }
        state_ = State::Conflict;
        increment(statistics_.tableau_conflicts);
        increment(statistics_.conflicts_produced);
        CheckResult published{CheckStatus::Conflict, std::move(conflict),
                              std::nullopt};
        if (!exactLraCheckResultShapeValid(published))
        {
          return checkFailure();
        }
        return published;
      }
    }
    throw EngineInvariantFailure("unknown simplex result status");
  }
  catch (NumberFailure const& failure)
  {
    return checkFailure(failure);
  }
  catch (StorageFailure const& failure)
  {
    return checkFailure(failure);
  }
  catch (...)
  {
    return checkFailure();
  }
}

CoreStatistics ExactLraCore::Impl::statistics() const noexcept
{
  CoreStatistics result = statistics_;
  result.variables = detail::saturatingSize(
      generation_state_->engine->registration.baseVariables().size());
  result.rows = detail::saturatingSize(generation_state_->engine->registration.rows().size());
  result.atoms = detail::saturatingSize(generation_state_->engine->registration.atoms().size());
  result.bounds = detail::saturatingSize(generation_state_->engine->registration.bounds().size());
  result.identity_rows = generation_state_->engine->identity_rows;
  result.singleton_rows = generation_state_->engine->singleton_rows;
  result.direct_rows = generation_state_->engine->direct_rows;
  result.numbers = generation_state_->budget.metrics();
  {
    ExactSimplexStats const& engine =
        generation_state_->engine->simplex.statistics();
    result.engine_pivots = engine.pivots;
    result.engine_bland_steps = engine.bland_steps;
    result.engine_activations = engine.activations;
    result.engine_deactivations = engine.deactivations;
    result.engine_normalised_cells = engine.normalised_cells;
    result.engine_early_conflicts = engine.early_conflicts;
    result.engine_soi_steps = engine.soi_steps;
    result.engine_soi_bound_flips = engine.soi_bound_flips;
    result.engine_soi_fallbacks = engine.soi_fallbacks;
  }
  result.storage = {};
  mergeStorageMetrics(result.storage, generation_state_->engine->bounds.arenaMetrics());
  return result;
}

CheckStatus ExactLraCore::Impl::status() const noexcept
{
  switch (state_)
  {
    case State::Building:
    case State::Ready:
    case State::CandidateOpen:
      return CheckStatus::Ready;
    case State::Consistent:
      return CheckStatus::Consistent;
    case State::Conflict:
      return CheckStatus::Conflict;
    case State::Interrupted:
      return CheckStatus::Interrupted;
    case State::ResourceLimit:
      return CheckStatus::ResourceLimit;
    case State::Invalid:
      return CheckStatus::InternalError;
  }
  return CheckStatus::InternalError;
}

void ExactLraCore::Impl::reset() noexcept
{
  try
  {
    CoreGeneration const current = generation_state_->engine->generation;
#if defined(STP_LRA_TEST_FAULT_INJECTION)
    force_conflict_verification_resource_ = false;
    force_model_verification_resource_ = false;
#endif
    if (state_ == State::Consistent || state_ == State::Conflict)
    {
      increment(statistics_.witness_invalidations);
    }
    generation_state_->engine->registration.clearPendingConflictBound();
    generation_state_->pending_conflict_explanation.clear();
    state_ = State::Invalid;

    if (current.epoch() == std::numeric_limits<std::uint32_t>::max() - 1U)
    {
      increment(statistics_.internal_errors);
      return;
    }
    CoreGeneration const proposed{current.value + 1U};
    if (!isImmediateSuccessor(current, proposed))
    {
      increment(statistics_.internal_errors);
      return;
    }

    std::unique_ptr<GenerationState> replacement =
        std::make_unique<GenerationState>(limits_, proposed);
    CoreGeneration const committed = generation_domain_.advance();
    if (committed != proposed)
    {
      increment(statistics_.internal_errors);
      return;
    }

    generation_state_.swap(replacement);
    generation_state_->engine->simplex.setEarlyConflictDetection(early_conflicts_);
    generation_state_->engine->simplex.setSoi(soi_);
    // The facade stays Invalid until every old exact value, native block,
    // registration snapshot, bound, tableau/model value, and the old budget
    // have been destroyed.  NumberBudget's destructor is the final zero-live
    // ownership proof for the retired bundle.
    replacement.reset();
    state_ = State::Building;
    revision_ = 1;
    increment(statistics_.resets);
  }
  catch (...)
  {
    generation_state_->engine->registration.clearPendingConflictBound();
    generation_state_->pending_conflict_explanation.clear();
    state_ = State::Invalid;
    increment(statistics_.internal_errors);
  }
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
void ExactLraCore::Impl::testCorruptVerificationRow(RowId row)
{
  try
  {
    NumberOperationScope scope(generation_state_->budget);
    ExactLraVerificationRow& snapshot =
        generation_state_->engine->registration.testMutableRow(row);
    if (snapshot.terms.empty())
    {
      invalidate();
      return;
    }
    snapshot.terms.front().coefficient = ExactRational(std::int64_t{0});
  }
  catch (...)
  {
    invalidate();
  }
}

void ExactLraCore::Impl::testCorruptVerificationBound(AtomId atom,
                                                       bool positive)
{
  try
  {
    RegisteredAtom const& record = generation_state_->engine->registration.atom(atom);
    BoundRef const reference = positive ? record.positive_bound
                                        : record.negative_bound;
    generation_state_->engine->registration.testMutableBound(reference).kind =
        static_cast<RegisteredBoundKind>(255);
  }
  catch (...)
  {
    invalidate();
  }
}
#endif

ExactLraCore::ExactLraCore(NumberLimits limits, DirectBoundsMode direct_bounds)
    : impl_(std::make_unique<Impl>(limits, direct_bounds))
{}

ExactLraCore::~ExactLraCore() noexcept = default;
ExactLraCore::ExactLraCore(ExactLraCore&&) noexcept = default;
ExactLraCore& ExactLraCore::operator=(ExactLraCore&&) noexcept = default;

InputResult<VariableId> ExactLraCore::addVariable()
{
  return impl_ ? impl_->addVariable()
               : InputResult<VariableId>{InputStatus::InvalidState,
                                         std::nullopt};
}

InputResult<RowId> ExactLraCore::addRow(LinearTerm const* begin,
                                        LinearTerm const* end)
{
  return impl_ ? impl_->addRow(begin, end)
               : InputResult<RowId>{InputStatus::InvalidState,
                                    std::nullopt};
}

InputResult<AtomId> ExactLraCore::addAtom(RowId row,
                                          Relation relation,
                                          ExactRational const& threshold,
                                          OriginId positive_origin,
                                          OriginId negative_origin)
{
  return impl_ ? impl_->addAtom(row, relation, threshold, positive_origin,
                                negative_origin)
               : InputResult<AtomId>{InputStatus::InvalidState,
                                     std::nullopt};
}

InputStatus ExactLraCore::initialize()
{
  return impl_ ? impl_->initialize() : InputStatus::InvalidState;
}

InputResult<Checkpoint> ExactLraCore::push()
{
  return impl_ ? impl_->push()
               : InputResult<Checkpoint>{InputStatus::InvalidState,
                                         std::nullopt};
}

InputStatus ExactLraCore::pop(Checkpoint checkpoint)
{
  return impl_ ? impl_->pop(checkpoint) : InputStatus::InvalidState;
}

AssertResult ExactLraCore::assertLiteral(AtomId atom, bool positive)
{
  return impl_ ? impl_->assertLiteral(atom, positive)
               : AssertResult{InputStatus::InvalidState, std::nullopt};
}

CheckResult ExactLraCore::check(ExactLraResourceObserver& observer,
                                bool verify_model)
{
  return impl_ ? impl_->check(observer, verify_model)
               : CheckResult{CheckStatus::InternalError, std::nullopt,
                             std::nullopt};
}

std::optional<bool> ExactLraCore::Impl::preferredPolarity(AtomId atom) const noexcept
{
  try
  {
    if (state_ != State::Consistent)
      return std::nullopt;
    auto const& registration = generation_state_->engine->registration;
    if (!registration.containsAtom(atom))
      return std::nullopt;
    NumberOperationScope scope(generation_state_->budget);
    auto const& record = registration.atom(atom);
    const auto& row = registration.row(record.row);
    auto value = generation_state_->engine->simplex.decisionValue(row.auxiliary);
    if (!value)
      return std::nullopt;
    if (row.direct_coefficient && !row.direct_coefficient->isOne())
      *value *= *row.direct_coefficient;
    DeltaRational const threshold(record.threshold, ExactRational(std::int64_t{0}));
    switch (record.positive_relation)
    {
      case Relation::Less: return *value < threshold;
      case Relation::LessEqual: return *value <= threshold;
      case Relation::Greater: return *value > threshold;
      case Relation::GreaterEqual: return *value >= threshold;
    }
  }
  catch (...)
  {
    // No tableau or witness was mutated; retain SAT's sign on failure.
  }
  return std::nullopt;
}

std::optional<bool> ExactLraCore::preferredPolarity(AtomId atom) const noexcept
{
  return impl_ ? impl_->preferredPolarity(atom) : std::nullopt;
}

VerificationResult ExactLraCore::verifyConflict(Conflict const& conflict) const
{
  return impl_ ? impl_->verifyConflict(conflict)
               : VerificationResult{VerificationError::InternalError};
}

VerificationResult ExactLraCore::verifyModel(Model const& model) const
{
  return impl_ ? impl_->verifyModel(model)
               : VerificationResult{VerificationError::InternalError};
}

InputResult<Conflict> ExactLraCore::certifyCandidateConflict(
    ConflictCandidateTerm const* begin, ConflictCandidateTerm const* end,
    bool recover_weights, ExactLraResourceObserver* observer,
    std::size_t recovery_support_limit)
{
  return impl_
             ? impl_->certifyCandidateConflict(begin, end, recover_weights,
                                               observer, recovery_support_limit)
             : InputResult<Conflict>{InputStatus::InternalError, std::nullopt};
}

InputResult<Model> ExactLraCore::certifyCandidateModel(
    ModelCandidateValue const* values_begin,
    ModelCandidateValue const* values_end,
    CandidateBound const* bounds_begin, CandidateBound const* bounds_end,
    CandidateBound const* pinned_begin, CandidateBound const* pinned_end,
    ExactLraResourceObserver* observer)
{
  return impl_ ? impl_->certifyCandidateModel(values_begin, values_end,
                                              bounds_begin, bounds_end,
                                              pinned_begin, pinned_end, observer)
               : InputResult<Model>{InputStatus::InternalError,
                                    std::nullopt};
}

void ExactLraCore::setConflictVerification(bool enabled) noexcept
{
  if (impl_)
    impl_->setConflictVerification(enabled);
}

void ExactLraCore::setSoi(bool enabled) noexcept
{
  if (impl_)
    impl_->setSoi(enabled);
}

void ExactLraCore::setSeparateModelValues(bool enabled) noexcept
{
  if (impl_)
    impl_->setSeparateModelValues(enabled);
}

InputStatus ExactLraCore::beginExtension() noexcept
{
  return impl_ ? impl_->beginExtension() : InputStatus::InternalError;
}

InputStatus ExactLraCore::restartSearchState() noexcept
{
  return impl_ ? impl_->restartSearchState() : InputStatus::InternalError;
}

void ExactLraCore::setEarlyConflictDetection(bool enabled) noexcept
{
  if (impl_)
    impl_->setEarlyConflictDetection(enabled);
}

CoreStatistics ExactLraCore::statistics() const noexcept
{
  return impl_ ? impl_->statistics() : CoreStatistics{};
}

CheckStatus ExactLraCore::status() const noexcept
{
  return impl_ ? impl_->status() : CheckStatus::InternalError;
}

CoreGeneration ExactLraCore::generation() const noexcept
{
  return impl_ ? impl_->generation() : CoreGeneration{0};
}

void ExactLraCore::reset() noexcept
{
  if (impl_)
  {
    impl_->reset();
  }
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
void ExactLraCore::testCorruptVerificationRow(RowId row)
{
  if (impl_)
  {
    impl_->testCorruptVerificationRow(row);
  }
}

void ExactLraCore::testCorruptVerificationBound(AtomId atom, bool positive)
{
  if (impl_)
  {
    impl_->testCorruptVerificationBound(atom, positive);
  }
}

void ExactLraCore::testForceNextConflictVerificationResource() noexcept
{
  if (impl_)
  {
    impl_->testForceNextConflictVerificationResource();
  }
}

void ExactLraCore::testForceNextModelVerificationResource() noexcept
{
  if (impl_)
  {
    impl_->testForceNextModelVerificationResource();
  }
}

VerificationError ExactLraCore::testLastVerificationError() const noexcept
{
  return impl_ ? impl_->testLastVerificationError()
               : VerificationError::InternalError;
}
#endif

}  // namespace stp::lra

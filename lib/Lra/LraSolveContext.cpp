#include "NumberBudget.h"
#include "LraSolveContext.h"
#include "stp/STPManager/STPManager.h"

#include "ExactLraVerificationData.h"

#include <algorithm>
#include <limits>
#include <new>
#include <set>
#include <sstream>
#include <utility>

namespace stp::lra {

namespace {

#if defined(STP_LRA_TEST_FAULT_INJECTION)
std::atomic<std::uint64_t> next_fault_origin_start{1};
#endif

std::uint64_t originStartForContext() noexcept
{
#if defined(STP_LRA_TEST_FAULT_INJECTION)
  return next_fault_origin_start.exchange(1, std::memory_order_relaxed);
#else
  return 1;
#endif
}

Relation coreRelation(FrontendRelation relation)
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
                            "an equality relation reached core registration");
}

void requireAccepted(InputStatus status, bool has_value,
                     const char* operation)
{
  if (status == InputStatus::Accepted && has_value)
    return;
  std::ostringstream out;
  out << operation << " returned status " << static_cast<unsigned>(status)
      << " with value=" << (has_value ? "present" : "absent");
  if (status == InputStatus::ResourceLimit)
    throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                              out.str());
  if (status == InputStatus::InternalError)
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              out.str());
  throw SolveContextFailure(SolveContextFailureKind::Invalid,
                            out.str());
}

[[noreturn]] void reportMissingMapping(const char* description)
{
  std::ostringstream out;
  out << "missing " << description;
  throw SolveContextFailure(SolveContextFailureKind::Invalid,
                            out.str());
}

// Position of every entry by the serial of the identifier `member` names.
// Serials are allocated one per entry, so a collision here is a registry that
// handed the same one out twice; the caller's full-identifier comparison would
// catch it as a miss, and building the index the same way keeps the first
// entry visible rather than the last.
template <class Entry, class Member>
SerialIndex buildSerialIndex(const std::vector<Entry>& entries, Member member,
                             const PreparationControl* preparation = nullptr)
{
  PreparationPoller poll(preparation, PreparationStage::LraCore);
  SerialIndex index;
  index.reserve(entries.size());
  for (std::size_t position = 0; position < entries.size(); ++position)
  {
    poll();
    index.emplace((entries[position].*member).serial, position);
  }
  return index;
}

// The lookup these tables exist for. It used to be a scan, which is O(n) per
// call inside loops that are themselves over every component -- quadratic in
// the atom count on every candidate, and the atom count is in the thousands.
//
// The identifier is still compared in full on the one entry the index offers,
// so a stale or foreign-domain identifier misses exactly as it did before, and
// so does a serial the index does not hold.
template <class Entry, class Id, class Member>
const Entry& findIndexed(const std::vector<Entry>& entries,
                         const SerialIndex& index, Id id, Member member,
                         const char* description)
{
  const auto found = index.find(id.serial);
  if (found == index.end() || found->second >= entries.size() ||
      !(entries[found->second].*member == id))
    reportMissingMapping(description);
  return entries[found->second];
}

} // namespace

SolveContextFailure::SolveContextFailure(SolveContextFailureKind kind,
                                         std::string detail)
    : std::runtime_error(std::move(detail)), kind_(kind)
{
}

LraResourceObserver::LraResourceObserver(
    SATSolver& solver, std::uint64_t maximum_pivots,
    const std::atomic<bool>* interrupted) noexcept
    : solver_(solver), maximum_pivots_(maximum_pivots),
      external_interrupt_(interrupted)
{
}

StopReason LraResourceObserver::pollBeforePivot() noexcept
{
  if (polls_ != std::numeric_limits<std::uint64_t>::max())
    ++polls_;
  if (local_interrupt_.load(std::memory_order_relaxed) ||
      (external_interrupt_ != nullptr &&
       external_interrupt_->load(std::memory_order_relaxed)) ||
      solver_.timeLimitExpired())
    return StopReason::Interrupted;
  if (check_guarded_)
  {
    // The check runs inside the core's number scope, so the active budget
    // is the tableau's; the first poll takes the baseline.
    void* const state = detail::BudgetAccess::active();
    if (state != nullptr)
    {
      const std::uint64_t made =
          detail::BudgetAccess::hot(state).metrics.big_operations;
      last_made_ = made;
      if (!have_baseline_)
      {
        materializations_baseline_ = made;
        have_baseline_ = true;
      }
      else if (check_pivots_ >= kGuardPivots &&
               made - materializations_baseline_ >= kGuardRatio * check_pivots_)
      {
        guard_stopped_ = true;
        return StopReason::Interrupted;
      }
    }
  }
  if (pivots_ >= maximum_pivots_)
    return StopReason::ResourceLimit;
  return StopReason::Continue;
}

void LraResourceObserver::accountPivot(bool bland) noexcept
{
  if (pivots_ != std::numeric_limits<std::uint64_t>::max())
    ++pivots_;
  if (check_pivots_ != std::numeric_limits<std::uint64_t>::max())
    ++check_pivots_;
  if (bland && bland_pivots_ != std::numeric_limits<std::uint64_t>::max())
    ++bland_pivots_;
}

void LraResourceObserver::requestInterrupt() noexcept
{
  local_interrupt_.store(true, std::memory_order_relaxed);
}

void LraResourceObserver::beginCandidate() noexcept
{
  // Interrupt state is owned by the query, not by a candidate attempt.  A
  // retry becomes eligible only when the outer owner clears its external
  // signal (or constructs a fresh solve context); beginning a candidate must
  // never silently consume an explicit stop request.
}

LraSolveContext::LraSolveContext(LraAtomRegistry& registry, SATSolver& solver,
                                 NumberLimits exact_limits,
                                 std::uint64_t maximum_pivots,
                                 const std::atomic<bool>* interrupted)
    : LraSolveContext(registry, solver, exact_limits, LraAssertionFrameId{},
                      maximum_pivots, interrupted)
{
}

LraSolveContext::LraSolveContext(LraAtomRegistry& registry, SATSolver& solver,
                                 NumberLimits exact_limits,
                                 LraAssertionFrameId solve_frame,
                                 std::uint64_t maximum_pivots,
                                 const std::atomic<bool>* interrupted)
    : registry_(registry), registry_frame_(solve_frame), solver_(solver),
      observer_(solver, maximum_pivots, interrupted),
      mapping_budget_(exact_limits)
{
  initializeSolveContext();
}


void LraSolveContext::initializeSolveContext() noexcept
{
  try
  {
    const auto* preparation = registry_.manager().preparation_control;
    registry_.manager().checkPreparation(PreparationStage::LraCore);
    solve_epoch_ = registry_.allocateSolveEpoch();
    if (solve_epoch_ == 0)
      throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                                "solve epoch zero is reserved");
    metrics_.solve_epoch = solve_epoch_;
    registry_snapshot_ = registry_frame_.valid()
                             ? registry_.frameSnapshot(registry_frame_, preparation)
                             : registry_.activeSnapshot(preparation);
    const bool snapshot_valid =
        registry_frame_.valid()
            ? registry_.validateFrameSnapshot(registry_snapshot_,
                                              registry_frame_)
            : registry_.validateSnapshot(registry_snapshot_);
    if (!snapshot_valid)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "registry changed while snapshotting solve");
    registry_row_index_ =
        buildSerialIndex(registry_snapshot_.rows, &RegistryRow::id, preparation);
    registry_component_index_ =
        buildSerialIndex(registry_snapshot_.components,
                         &RegistryComponent::id, preparation);
    registry_equality_index_ = buildSerialIndex(
        registry_snapshot_.equalities, &RegistryEqualityGroup::id, preparation);
    core_ = std::make_unique<ExactLraCore>(mapping_budget_.limits());
    // A context whose verification setting was chosen before the core existed
    // still has to reach it.
    core_->setConflictVerification(verify_conflicts_);
    buildCore(originStartForContext());
    status_ = SolveContextStatus::Ready;
  }
  catch (const PreparationInterrupted& stopped)
  {
    preparation_stop_ = stopped;
    status_ = SolveContextStatus::Interrupted;
    clearSemanticState();
  }
  catch (const SolveContextFailure& failure)
  {
    failure_detail_ = failure.what();
    status_ = failure.kind() == SolveContextFailureKind::ResourceLimit
                  ? SolveContextStatus::ResourceLimit
                  : SolveContextStatus::Invalid;
    clearSemanticState();
  }
  catch (const RegistryFailure& failure)
  {
    failure_detail_ = failure.what();
    status_ = failure.kind() == RegistryFailureKind::ResourceLimit
                  ? SolveContextStatus::ResourceLimit
                  : SolveContextStatus::Invalid;
    clearSemanticState();
  }
  catch (const NumberFailure& failure)
  {
    failure_detail_ = failure.what();
    status_ = failure.kind() == NumberFailureKind::ResourceLimit
                  ? SolveContextStatus::ResourceLimit
                  : SolveContextStatus::Invalid;
    clearSemanticState();
  }
  catch (const std::bad_alloc&)
  {
    failure_detail_ = "allocation failure creating LRA solve context";
    status_ = SolveContextStatus::Invalid;
    clearSemanticState();
  }
  catch (...)
  {
    failure_detail_ = "unexpected failure creating LRA solve context";
    status_ = SolveContextStatus::Invalid;
    clearSemanticState();
  }
}

LraSolveContext::~LraSolveContext() noexcept
{
  clearSemanticState();
  bindings_ready_ = false;
  component_bindings_.clear();
  equality_bindings_.clear();
}

void LraSolveContext::buildCore(std::uint64_t origin_serial_start)
{
  const auto* preparation = registry_.manager().preparation_control;
  PreparationPoller poll(preparation, PreparationStage::LraCore);
  if (core_ == nullptr || origin_serial_start == 0)
    throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                              "invalid solve-local origin serial start");
  next_origin_serial_ = origin_serial_start;
  const CoreGeneration generation = core_->generation();

  for (const RegistrySymbol& symbol : registry_snapshot_.symbols)
  {
    poll();
    if (!symbol.id.valid() || symbol.id.domain != registry_snapshot_.tag.domain ||
        symbol.frontend_id.value == 0 || symbol.symbol.IsNull() ||
        symbol.symbol.GetSourceSort().kind() != SourceSort::Kind::Real)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "invalid active registry symbol");
    const InputResult<VariableId> added = core_->addVariable();
    requireAccepted(added.status, added.value.has_value(), "addVariable");
    if (added.value->generation() != generation)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "core variable generation mismatch");
    variable_map_.push_back(CoreVariableMapEntry{
        symbol.id, symbol.frontend_id, *added.value, generation});
    ++metrics_.variables_registered;
  }
  variable_map_index_ = buildSerialIndex(
      variable_map_, &CoreVariableMapEntry::registry_symbol, preparation);

  for (const RegistryRow& row : registry_snapshot_.rows)
  {
    poll();
    if (!row.id.valid() || row.id.domain != registry_snapshot_.tag.domain ||
        row.terms.empty())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "invalid active canonical row");
    std::vector<LinearTerm> terms;
    {
      NumberOperationScope operation(mapping_budget_);
      terms.reserve(row.terms.size());
      for (const RegistryMonomial& term : row.terms)
      {
        poll();
        if (term.coefficient.isZero())
          throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                    "canonical row contains a zero term");
        const CoreVariableMapEntry& mapped = findIndexed(
            variable_map_, variable_map_index_, term.symbol,
            &CoreVariableMapEntry::registry_symbol,
            "registry-symbol to core-variable mapping");
        if (mapped.core_generation != generation)
          throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                    "core row variables are stale or unsorted");
        terms.push_back(LinearTerm{mapped.core_variable, term.coefficient});
      }
      std::sort(terms.begin(), terms.end(), [&poll](auto const& a, auto const& b) {
        poll();
        return a.variable < b.variable;
      });
    }
    const InputResult<RowId> added =
        core_->addRow(terms.data(), terms.data() + terms.size());
    requireAccepted(added.status, added.value.has_value(), "addRow");
    if (added.value->generation() != generation)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "core row generation mismatch");
    row_map_.push_back(CoreRowMapEntry{row.id, *added.value, generation});
    ++metrics_.rows_registered;
  }
  row_map_index_ =
      buildSerialIndex(row_map_, &CoreRowMapEntry::registry_row, preparation);

  for (const RegistryComponent& component : registry_snapshot_.components)
  {
    poll();
    if (!component.id.valid() ||
        component.id.domain != registry_snapshot_.tag.domain ||
        component.sources.empty())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "invalid active registry component");
    const CoreRowMapEntry& row = findIndexed(
        row_map_, row_map_index_, component.row,
        &CoreRowMapEntry::registry_row,
        "registry-row to core-row mapping");
    const OriginId positive{solve_epoch_, allocateOriginSerial()};
    const OriginId negative{solve_epoch_, allocateOriginSerial()};
    if (positive.serial == negative.serial)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "positive and negative origins alias");
    const Relation relation = coreRelation(component.relation);
    const InputResult<AtomId> added = core_->addAtom(
        row.core_row, relation, component.threshold, positive, negative);
    requireAccepted(added.status, added.value.has_value(), "addAtom");
    if (added.value->generation() != generation)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "core atom generation mismatch");
    component_map_.push_back(CoreComponentMapEntry{
        component.id, *added.value, relation, positive, negative, generation});
    origin_map_.push_back(OriginMapEntry{
        positive, component.id, *added.value, relation, true, generation});
    origin_map_.push_back(OriginMapEntry{
        negative, component.id, *added.value, relation, false, generation});
    ++metrics_.components_registered;
    metrics_.origins_registered += 2;
  }
  component_map_index_ = buildSerialIndex(
      component_map_, &CoreComponentMapEntry::registry_component, preparation);
  origin_map_index_ =
      buildSerialIndex(origin_map_, &OriginMapEntry::origin, preparation);

  for (const RegistryEqualityGroup& equality : registry_snapshot_.equalities)
  {
    poll();
    (void)findIndexed(component_map_, component_map_index_,
                      equality.less_equal_component,
                      &CoreComponentMapEntry::registry_component,
                      "equality less-equal component mapping");
    (void)findIndexed(component_map_, component_map_index_,
                      equality.greater_equal_component,
                      &CoreComponentMapEntry::registry_component,
                      "equality greater-equal component mapping");
    if (equality.id.domain != registry_snapshot_.tag.domain ||
        equality.less_equal_component == equality.greater_equal_component)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "invalid active equality group");
  }


  poll.check();
  const InputStatus initialized = core_->initialize();
  poll.check();
  ++metrics_.initialize_calls;
  if (initialized == InputStatus::ResourceLimit)
    throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                              "ExactLraCore::initialize reached a limit");
  if (initialized != InputStatus::Accepted ||
      core_->status() != CheckStatus::Ready)
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              "ExactLraCore::initialize failed");
}

CoreGeneration LraSolveContext::coreGeneration() const noexcept
{
  return core_ == nullptr ? CoreGeneration{0} : core_->generation();
}

bool LraSolveContext::bindOpaqueAtoms(
    const std::vector<LraSatBinding>& bindings,
    const std::vector<ASTNode>& omitted) noexcept
{
  try
  {
    if (!ready() || bindings_ready_ || !validateCurrentState())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "bindings require one current unbound context");
    if (!solver_.okay())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "SAT solver is not okay before LRA binding");
    const SATSolver::lbool true_value = solver_.true_literal();
    const SATSolver::lbool false_value = solver_.false_literal();
    const SATSolver::lbool undef_value = solver_.undef_literal();
    if (true_value == false_value || true_value == undef_value ||
        false_value == undef_value)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "SAT distinguished values are not distinct");

    struct Expected final
    {
      ASTNode atom;
      bool equality;
      std::uint64_t serial;
    };
    std::map<std::uint64_t, Expected> expected;
    for (const RegistryComponent& component : registry_snapshot_.components)
    {
      if (!expected
               .emplace(component.opaque_atom.GetNodeNum(),
                        Expected{component.opaque_atom, false,
                                 component.id.serial})
               .second)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "two components own one opaque AST atom");
    }
    for (const RegistryEqualityGroup& equality : registry_snapshot_.equalities)
    {
      if (!expected
               .emplace(equality.equality_atom.GetNodeNum(),
                        Expected{equality.equality_atom, true,
                                 equality.id.serial})
               .second)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "equality atom aliases another LRA atom");
    }
    /* An omitted atom is one the caller has established the Boolean formula
     * never mentions, so the CNF never named it. Counting those alongside
     * the bindings keeps this check exact: every registered atom is either
     * bound or accounted for, and a binding lost on the way to the CNF is
     * still caught. */
    std::set<std::uint64_t> omitted_nodes;
    for (const ASTNode& atom : omitted)
    {
      if (expected.find(atom.GetNodeNum()) == expected.end())
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "omitted atom was never registered");
      if (!omitted_nodes.insert(atom.GetNodeNum()).second)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "an atom was omitted twice");
    }
    if (bindings.size() + omitted_nodes.size() != expected.size())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "missing or extra opaque SAT binding");

    std::unordered_map<std::uint64_t, SATSolver::Lit> components;
    std::unordered_map<std::uint64_t, SATSolver::Lit> equalities;
    std::set<std::uint32_t> variables;
    std::set<std::uint64_t> seen_nodes;
    Frontend frontend(registry_.manager());
    for (const LraSatBinding& binding : bindings)
    {
      if (!frontend.ownsNode(binding.atom) ||
          !seen_nodes.insert(binding.atom.GetNodeNum()).second)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "foreign or duplicate opaque SAT binding");
      const auto found = expected.find(binding.atom.GetNodeNum());
      if (found == expected.end() || found->second.atom != binding.atom)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "binding names an unknown opaque atom");
      if (omitted_nodes.count(binding.atom.GetNodeNum()) != 0)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "an atom was both bound and omitted");
      if (SATSolver::sign(binding.literal))
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "opaque atom binding has the wrong sign");
      const std::uint32_t variable = SATSolver::var(binding.literal);
      if (!solver_.validVariable(variable))
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "opaque atom SAT variable is out of range");
      if (!variables.insert(variable).second)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "unrelated opaque atoms alias a SAT variable");
      (found->second.equality ? equalities : components)
          .emplace(found->second.serial, binding.literal);
    }
    if (components.size() + equalities.size() + omitted_nodes.size() !=
        registry_snapshot_.components.size() +
            registry_snapshot_.equalities.size())
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "opaque SAT binding coverage is incomplete");

    component_bindings_.swap(components);
    equality_bindings_.swap(equalities);
    bindings_ready_ = true;
    return true;
  }
  catch (const std::exception& failure)
  {
    invalidate(failure.what());
    return false;
  }
  catch (...)
  {
    invalidate("unexpected failure binding opaque LRA atoms");
    return false;
  }
}

VerificationResult LraSolveContext::verifyConflictChecked(
    const Conflict& conflict) const noexcept
{
  if (!verify_conflicts_ || core_ == nullptr)
  {
    return VerificationResult{VerificationError::None};
  }
  return core_->verifyConflict(conflict);
}

bool LraSolveContext::validateCurrentState() noexcept
{
  try
  {
    /* The identity half only.  Every registry mutation advances the
     * generation, so a context left behind by one is caught by the tag alone;
     * re-walking every symbol, row and component compares two copies of data
     * that no longer differ, on every candidate. The snapshot is still walked
     * in full where it is taken, and both independent verifiers still see
     * every conflict and every model. */
    if (!ready() || core_ == nullptr || solve_epoch_ == 0 ||
        !(registry_frame_.valid()
              ? registry_.validateFrameSnapshotIdentity(registry_snapshot_,
                                                        registry_frame_)
              : registry_.validateSnapshotIdentity(registry_snapshot_)) ||
        core_->generation() == CoreGeneration{0} ||
        core_->status() == CheckStatus::InternalError)
      throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                "solve context registry/core epoch is stale");
    const CoreGeneration generation = core_->generation();
    for (const CoreVariableMapEntry& entry : variable_map_)
      if (entry.core_generation != generation ||
          entry.core_variable.generation() != generation)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "stale core variable mapping");
    for (const CoreRowMapEntry& entry : row_map_)
      if (entry.core_generation != generation ||
          entry.core_row.generation() != generation)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "stale core row mapping");
    for (const CoreComponentMapEntry& entry : component_map_)
      if (entry.core_generation != generation ||
          entry.core_atom.generation() != generation ||
          entry.positive_origin.solve_epoch != solve_epoch_ ||
          entry.negative_origin.solve_epoch != solve_epoch_)
        throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                  "stale core component mapping");
    if (bindings_ready_)
    {
      for (const auto& binding : component_bindings_)
        if (!solver_.validVariable(SATSolver::var(binding.second)) ||
            SATSolver::sign(binding.second))
          throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                    "stale component SAT binding");
      for (const auto& binding : equality_bindings_)
        if (!solver_.validVariable(SATSolver::var(binding.second)) ||
            SATSolver::sign(binding.second))
          throw SolveContextFailure(SolveContextFailureKind::Invalid,
                                    "stale equality SAT binding");
    }
    return true;
  }
  catch (const std::exception& failure)
  {
    invalidate(failure.what());
    return false;
  }
  catch (...)
  {
    invalidate("unexpected solve-context validation failure");
    return false;
  }
}

PendingClauseState LraSolveContext::pendingClauseState() const noexcept
{
  return pending_clause_ ? pending_clause_->state
                         : PendingClauseState::NoPending;
}

const PendingLraClause* LraSolveContext::pendingClauseForTesting() const noexcept
{
  return pending_clause_ ? &*pending_clause_ : nullptr;
}

const StagedExactModel* LraSolveContext::stagedModelForTesting() const noexcept
{
  return staged_model_ ? &*staged_model_ : nullptr;
}

LraSolveMetrics LraSolveContext::metrics() const noexcept
{
  LraSolveMetrics result = metrics_;
  result.observer_polls = observer_.polls();
  result.observer_pivots = observer_.pivots();
  result.observer_bland_pivots = observer_.blandPivots();
  return result;
}

CoreStatistics LraSolveContext::coreStatistics() const noexcept
{
  return core_ ? core_->statistics() : CoreStatistics{};
}

bool LraSolveContext::beforeSolverCall() noexcept
{
  if (!validateCurrentState())
    return false;
  if (pending_clause_ &&
      pending_clause_->state == PendingClauseState::CandidateConflict)
  {
    invalidate("SAT call attempted before pending LRA clause encoding");
    return false;
  }
  staged_model_.reset();
  propagated_model_.reset();
  current_selection_.clear();
  current_equalities_.clear();
  current_selection_index_.clear();
  current_equalities_index_.clear();
  if (pending_clause_ && pending_clause_->state == PendingClauseState::ClauseEncoded)
    pending_clause_->state = PendingClauseState::Cleared;
  return true;
}

bool LraSolveContext::notifyContextMutation() noexcept
{
  invalidate("solve context invalidated by registry/public mutation");
  return false;
}

void LraSolveContext::giveUp(std::string detail) noexcept
{
  // A context already stopped as a fault stays one: this is here to say that
  // no verdict was reached, never to downgrade a failure someone else
  // diagnosed into one nobody has to look at.
  const bool already_failed = status_ != SolveContextStatus::Ready;
  invalidate(std::move(detail));
  if (!already_failed)
    status_ = SolveContextStatus::ResourceLimit;
}

void LraSolveContext::invalidate(std::string detail) noexcept
{
  status_ = SolveContextStatus::Invalid;
  failure_detail_ = std::move(detail);
  clearSemanticState();
  bindings_ready_ = false;
  component_bindings_.clear();
  equality_bindings_.clear();
}

void LraSolveContext::clearSemanticState() noexcept
{
  staged_model_.reset();
  propagated_model_.reset();
  pending_clause_.reset();
  current_selection_.clear();
  current_equalities_.clear();
  current_selection_index_.clear();
  current_equalities_index_.clear();
}

std::uint64_t LraSolveContext::allocateCandidateSerial()
{
  if (next_candidate_serial_ == 0 ||
      next_candidate_serial_ == std::numeric_limits<std::uint64_t>::max())
    throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                              "candidate serial space exhausted");
  return next_candidate_serial_++;
}

std::uint64_t LraSolveContext::allocateOriginSerial()
{
  if (next_origin_serial_ == 0 ||
      next_origin_serial_ == std::numeric_limits<std::uint64_t>::max())
    throw SolveContextFailure(SolveContextFailureKind::ResourceLimit,
                              "solve-local origin serial space exhausted");
  return next_origin_serial_++;
}

const RegistryRow& LraSolveContext::registryRow(LraCanonicalRowId id) const
{
  return findIndexed(registry_snapshot_.rows, registry_row_index_, id,
                     &RegistryRow::id, "active registry row");
}

const RegistryComponent& LraSolveContext::registryComponent(
    LraComponentId id) const
{
  return findIndexed(registry_snapshot_.components, registry_component_index_,
                     id, &RegistryComponent::id, "active registry component");
}

const RegistryEqualityGroup& LraSolveContext::registryEquality(
    LraEqualityGroupId id) const
{
  return findIndexed(registry_snapshot_.equalities, registry_equality_index_,
                     id, &RegistryEqualityGroup::id,
                     "active registry equality group");
}

const CoreVariableMapEntry& LraSolveContext::variableMap(
    LraRegistrySymbolId id) const
{
  return findIndexed(variable_map_, variable_map_index_, id,
                     &CoreVariableMapEntry::registry_symbol,
                     "registry-symbol to core-variable mapping");
}

const CoreRowMapEntry& LraSolveContext::rowMap(LraCanonicalRowId id) const
{
  return findIndexed(row_map_, row_map_index_, id,
                     &CoreRowMapEntry::registry_row,
                     "registry-row to core-row mapping");
}

const CoreComponentMapEntry& LraSolveContext::componentMap(
    LraComponentId id) const
{
  return findIndexed(component_map_, component_map_index_, id,
                     &CoreComponentMapEntry::registry_component,
                     "registry-component to core-atom mapping");
}

const OriginMapEntry& LraSolveContext::originMap(OriginId id) const
{
  return findIndexed(origin_map_, origin_map_index_, id,
                     &OriginMapEntry::origin,
                     "origin to signed-component mapping");
}

SATSolver::Lit LraSolveContext::componentBinding(LraComponentId id) const
{
  if (id.domain != registry_snapshot_.tag.domain)
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              "foreign component SAT binding lookup");
  const auto found = component_bindings_.find(id.serial);
  if (found == component_bindings_.end())
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              "missing component SAT binding");
  return found->second;
}

const SATSolver::Lit* LraSolveContext::componentBindingOrNull(
    LraComponentId id) const noexcept
{
  if (id.domain != registry_snapshot_.tag.domain)
  {
    return nullptr;
  }
  const auto found = component_bindings_.find(id.serial);
  return found == component_bindings_.end() ? nullptr : &found->second;
}

bool LraSolveContext::componentBound(LraComponentId id) const noexcept
{
  return id.domain == registry_snapshot_.tag.domain &&
         component_bindings_.count(id.serial) != 0;
}

bool LraSolveContext::equalityBound(LraEqualityGroupId id) const noexcept
{
  return id.domain == registry_snapshot_.tag.domain &&
         equality_bindings_.count(id.serial) != 0;
}

SATSolver::Lit LraSolveContext::equalityBinding(LraEqualityGroupId id) const
{
  if (id.domain != registry_snapshot_.tag.domain)
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              "foreign equality SAT binding lookup");
  const auto found = equality_bindings_.find(id.serial);
  if (found == equality_bindings_.end())
    throw SolveContextFailure(SolveContextFailureKind::Invalid,
                              "missing equality SAT binding");
  return found->second;
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
void LraSolveContext::testSetNextCandidateSerial(std::uint64_t next) noexcept
{
  next_candidate_serial_ = next;
}

void LraSolveContext::testSetOriginSerialStartForNextContext(
    std::uint64_t next) noexcept
{
  next_fault_origin_start.store(next, std::memory_order_relaxed);
}

void LraSolveContext::testCorruptPendingEpoch() noexcept
{
  if (pending_clause_)
    ++pending_clause_->solve_epoch;
}

void LraSolveContext::testCorruptPendingCandidate() noexcept
{
  if (pending_clause_)
    ++pending_clause_->candidate_serial;
}

void LraSolveContext::testCorruptPendingOrigin() noexcept
{
  if (pending_clause_ && !pending_clause_->support.empty())
    pending_clause_->support.front().origin.serial = 0;
}

void LraSolveContext::testCorruptPendingLiteralVariable() noexcept
{
  if (pending_clause_ && !pending_clause_->support.empty())
  {
    const std::uint32_t invalid =
        solver_.nVars() == std::numeric_limits<std::uint32_t>::max()
            ? 0
            : solver_.nVars() + 1;
    pending_clause_->support.front().asserting_literal =
        SATSolver::mkLit(invalid, false);
  }
}

void LraSolveContext::testCorruptPendingLiteralSign() noexcept
{
  if (pending_clause_ && !pending_clause_->support.empty())
    pending_clause_->support.front().asserting_literal.x ^= 1U;
}

void LraSolveContext::testDuplicatePendingSupport()
{
  if (pending_clause_ && !pending_clause_->support.empty())
  {
    NumberOperationScope operation(mapping_budget_);
    pending_clause_->support.push_back(pending_clause_->support.front());
  }
}

void LraSolveContext::testAddComplementaryPendingSupport()
{
  if (pending_clause_ && !pending_clause_->support.empty())
  {
    NumberOperationScope operation(mapping_budget_);
    PendingSupportEvidence duplicate = pending_clause_->support.front();
    duplicate.asserting_literal.x ^= 1U;
    pending_clause_->support.push_back(std::move(duplicate));
  }
}

void LraSolveContext::testClearPendingSupport() noexcept
{
  if (pending_clause_)
    pending_clause_->support.clear();
}
#endif

} // namespace stp::lra

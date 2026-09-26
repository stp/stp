#ifndef STP_LRA_SOLVE_CONTEXT_H
#define STP_LRA_SOLVE_CONTEXT_H

#include "ExactLraCore.h"
#include "LraAtomRegistry.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Util/PreparationControl.h"

#include <atomic>
#include <chrono>
#include <algorithm>
#include <cstdint>
#include <map>
#include <memory>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace stp {
class ToSATBase;
}

namespace stp::lra {


enum class CoreVariableRole : std::uint8_t
{
  PublicRealSymbol,
  BridgeResult,
  BridgeBit
};

enum class SolveOriginRole : std::uint8_t
{
  ExistingLraLiteral,
  BridgeBitLiteral,
  BridgeAxiom,
  InactiveComplement
};

enum class SolveContextStatus : std::uint8_t
{
  Ready,
  Interrupted,
  ResourceLimit,
  Invalid
};

/* Arithmetic resource refusals and invalid states use this exception.
 * Preparation cancellation retains its own typed interruption across the
 * noexcept constructor and extension boundary. */
enum class SolveContextFailureKind : std::uint8_t
{
  ResourceLimit,
  Invalid
};

class SolveContextFailure final : public std::runtime_error
{
public:
  SolveContextFailure(SolveContextFailureKind kind, std::string detail);
  SolveContextFailureKind kind() const noexcept { return kind_; }

private:
  SolveContextFailureKind kind_;
};

struct LraSatBinding final
{
  ASTNode atom;
  SATSolver::Lit literal;
};

struct CoreVariableMapEntry final
{
  CoreVariableMapEntry(LraRegistrySymbolId registry,
                       LraSymbolId frontend, VariableId variable,
                       CoreGeneration generation)
      : registry_symbol(registry), frontend_symbol(frontend),
        core_variable(variable), core_generation(generation)
  {
  }

  LraRegistrySymbolId registry_symbol;
  LraSymbolId frontend_symbol;
  VariableId core_variable;
  CoreGeneration core_generation;
  CoreVariableRole role = CoreVariableRole::PublicRealSymbol;
  std::uint32_t float_variable = 0xffffffffu;
};

struct CoreRowMapEntry final
{
  LraCanonicalRowId registry_row;
  RowId core_row;
  CoreGeneration core_generation;
  std::uint32_t float_variable = 0xffffffffu;
};

struct CoreComponentMapEntry final
{
  LraComponentId registry_component;
  AtomId core_atom;
  Relation relation;
  OriginId positive_origin;
  OriginId negative_origin;
  CoreGeneration core_generation;
  /* The advisory tier's atom for this component, when the float driver is
   * on; unset otherwise.  Float atoms are assigned in component order, so
   * this needs no map of its own. */
  std::uint32_t float_atom = 0xffffffffu;
};

struct OriginMapEntry final
{
  OriginMapEntry(OriginId source_origin, LraComponentId component,
                 AtomId atom, Relation source_relation,
                 bool source_positive, CoreGeneration generation)
      : origin(source_origin), registry_component(component), core_atom(atom),
        relation(source_relation), positive(source_positive),
        core_generation(generation)
  {
  }

  OriginId origin;
  LraComponentId registry_component;
  AtomId core_atom;
  Relation relation;
  bool positive = false;
  CoreGeneration core_generation;
  SolveOriginRole role = SolveOriginRole::ExistingLraLiteral;
};

struct CandidateComponentSelection final
{
  LraComponentId component;
  bool positive = false;
  SATSolver::Lit asserting_literal;
  // The literal this component is bound to, kept so that re-reading the
  // model does not have to look the binding up again.
  SATSolver::Lit binding;
};

struct CandidateEqualitySelection final
{
  LraEqualityGroupId group;
  bool equality_value = false;
  SATSolver::Lit equality_literal;
};

struct PendingSupportEvidence final
{
  PendingSupportEvidence(OriginId source_origin, BoundRef source_bound,
                         LraComponentId source_component,
                         bool source_positive,
                         SATSolver::Lit source_literal,
                         ExactRational source_weight,
                         ExactRational source_threshold,
                         std::vector<RegistryMonomial> source_row_terms)
      : origin(source_origin), bound(source_bound),
        component(source_component), positive(source_positive),
        asserting_literal(source_literal), weight(std::move(source_weight)),
        threshold(std::move(source_threshold)),
        row_terms(std::move(source_row_terms))
  {
  }

  OriginId origin;
  BoundRef bound;
  LraComponentId component;
  bool positive = false;
  SATSolver::Lit asserting_literal;
  ExactRational weight;
  ExactRational threshold;
  std::vector<RegistryMonomial> row_terms;
  SolveOriginRole role = SolveOriginRole::ExistingLraLiteral;
};

enum class PendingClauseState : std::uint8_t
{
  NoPending,
  CandidateConflict,
  ClauseEncoded,
  Cleared
};

struct PendingLraClause final
{
  PendingClauseState state = PendingClauseState::NoPending;
  std::uint64_t solve_epoch = 0;
  std::uint64_t candidate_serial = 0;
  bool final_verified = false;
  Conflict verified_conflict;
  std::vector<PendingSupportEvidence> support;
  std::vector<SATSolver::Lit> encoded_clause;
};

struct StagedRealValue final
{
  LraRegistrySymbolId registry_symbol;
  LraSymbolId frontend_symbol;
  ASTNode symbol;
  ExactRational value;
  std::string numerator_decimal;
  std::string denominator_decimal;
  CoreVariableRole role = CoreVariableRole::PublicRealSymbol;
};


struct StagedExactModel final
{
  std::uint64_t solve_epoch = 0;
  std::uint64_t candidate_serial = 0;
  std::vector<StagedRealValue> values;
};

struct LraSolveMetrics final
{
  std::uint64_t solve_epoch = 0;
  std::uint64_t variables_registered = 0;
  std::uint64_t rows_registered = 0;
  std::uint64_t components_registered = 0;
  std::uint64_t origins_registered = 0;
  std::uint64_t initialize_calls = 0;
  std::uint64_t persistent_extensions = 0;
  std::uint64_t float_extensions = 0;
  std::uint64_t candidates_started = 0;
  std::uint64_t complete_model_reads = 0;
  std::uint64_t exact_assertions = 0;
  std::uint64_t exact_checks = 0;
  std::uint64_t exact_pops = 0;
  // Theory levels opened while driving the search, as opposed to the one
  // push-per-candidate the full-lazy path performs.
  std::uint64_t exact_pushes = 0;
  std::uint64_t immediate_conflicts = 0;
  // Conflicts a partial assignment's tableau check found before a model.
  std::uint64_t partial_conflicts = 0;
  // Partial checks stopped at their pivot budget, and whether that turned
  // partial checks off for the rest of the solve.
  std::uint64_t partial_checks_abandoned = 0;
  std::uint64_t partial_checks_disabled = 0;
  std::uint64_t tableau_conflicts = 0;
  std::uint64_t clauses_encoded = 0;
  std::uint64_t clauses_inserted = 0;
  // Binary bound-ordering axioms handed to the SAT solver before the first
  // solve, so that candidates differing only in implied atoms never reach the
  // theory at all.
  std::uint64_t ordering_axioms = 0;
  std::uint64_t polarity_queries = 0;
  std::uint64_t polarity_advice = 0;
  std::uint64_t polarity_changes = 0;
  std::uint64_t polarity_abstentions = 0;
  std::uint64_t polarity_float = 0;
  std::uint64_t polarity_exact = 0;
  std::uint64_t models_staged = 0;
  std::uint64_t model_values_staged = 0;
  std::uint64_t observer_polls = 0;
  std::uint64_t observer_pivots = 0;
  std::uint64_t observer_bland_pivots = 0;
  std::uint64_t candidate_read_nanoseconds = 0;
  std::uint64_t exact_check_nanoseconds = 0;
  std::uint64_t model_mapping_nanoseconds = 0;
  std::uint64_t model_evaluation_nanoseconds = 0;
  // The advisory double tier, when the float driver is on: what it
  // absorbed, what it flagged, and how its candidates fared under exact
  // re-derivation.
  std::uint64_t float_assertions = 0;
  std::uint64_t float_checks = 0;
  std::uint64_t float_check_conflicts = 0;
  std::uint64_t float_local_conflicts = 0;
  std::uint64_t float_checks_abandoned = 0;
  // Times the float tier's fill blew past the reroute budget and the query
  // was handed to the exact driver. At most once per solve; see
  // UserDefinedFlags::lra_float_reroute.
  std::uint64_t float_reroutes = 0;
  std::uint64_t float_replays = 0;
  std::uint64_t float_replay_conflicts = 0;
  std::uint64_t float_replay_consistent = 0;
  std::uint64_t float_disabled = 0;
  std::uint64_t float_pivots = 0;
  std::uint64_t float_early_conflicts = 0;
  std::uint64_t float_soi_steps = 0;
  std::uint64_t float_soi_bound_flips = 0;
  std::uint64_t float_soi_fallbacks = 0;
  std::uint64_t float_check_nanoseconds = 0;
  std::uint64_t float_sync_nanoseconds = 0;
  // Certificate-first certification: conflicts staged straight from the
  // float tier's verified Farkas certificate, and certificates the exact
  // verifier rejected (each of those fell back to re-derivation).
  std::uint64_t float_certified = 0;
  std::uint64_t float_certificate_failed = 0;
  // Models accepted by refinement of the float assignment, and refinement
  // attempts the exact verifier rejected (each fell back to the core's
  // own check).
  std::uint64_t float_models_refined = 0;
  std::uint64_t float_model_refine_failed = 0;
  // Basis restarts taken before degrading a solve's float checks, and
  // switches into the factorized representation.
  std::uint64_t float_restarts = 0;
  std::uint64_t float_rebuilds = 0;
  std::uint64_t float_generalisations = 0;
  std::uint64_t float_factorized = 0;
  std::uint64_t float_complete_recoveries = 0;
  std::uint64_t float_cold_recoveries = 0;
  std::uint64_t float_refactor_failures = 0;
  std::uint64_t float_robust_refactors = 0;
  /* Times a solve continued in a fresh factorized tier built from the
   * trail after the double tier tripped twice. */
  std::uint64_t float_promotions = 0;
  /* Row dormancy in the float tier (UserDefinedFlags::lra_float_dormant_rows):
   * rows activated by a first bound, rows still dormant when the solve
   * ended, and assignment reads served for dormant basics by evaluation. */
  std::uint64_t float_row_activations = 0;
  std::uint64_t float_rows_dormant = 0;
  std::uint64_t float_dormant_evaluations = 0;
};


class LraResourceObserver final : public ExactLraResourceObserver
{
public:
  LraResourceObserver(SATSolver& solver, std::uint64_t maximum_pivots,
                      const std::atomic<bool>* interrupted = nullptr) noexcept;

  StopReason pollBeforePivot() noexcept override;
  void accountPivot(bool bland) noexcept override;
  void requestInterrupt() noexcept;
  void beginCandidate() noexcept;
  /* Guard the next check against runaway arithmetic: once it has pivoted
   * kGuardPivots times, a check whose pivots have taken the
   * arbitrary-precision route at kGuardRatio or more operations per pivot
   * is stopped as if interrupted -- the tableau keeps the pivots made, the
   * values go back to the saved assignment -- and guardStopped() says so,
   * as opposed to a stop the query asked for. On a tableau whose pivots
   * stay in word arithmetic the rate is zero; on a dense one whose
   * coefficients have grown it is in the thousands, and each pivot then
   * costs milliseconds.  The rate was once read from materialisations,
   * which the word representation performed once per big operation on a
   * word operand; a representation that keeps words as words makes that
   * proxy meaningless, and the operation count is what the cost is. */
  static constexpr std::uint64_t kGuardPivots = 10;
  static constexpr std::uint64_t kGuardRatio = 200;
  void beginCheck(bool guarded) noexcept
  {
    if (check_guarded_ && have_baseline_)
    {
      // Close the previous guarded check's account.
      guarded_pivots_ += check_pivots_;
      guarded_materializations_ += last_made_ - materializations_baseline_;
    }
    check_guarded_ = guarded;
    have_baseline_ = false;
    materializations_baseline_ = 0;
    last_made_ = 0;
    check_pivots_ = 0;
    guard_stopped_ = false;
  }
  bool guardStopped() const noexcept { return guard_stopped_; }
  /* The same rate over every guarded check so far: on a dense tableau each
   * check is short, and it is their sum that runs away. */
  bool guardedRateExceeded() const noexcept
  {
    return guarded_pivots_ >= kGuardPivots &&
           guarded_materializations_ >= kGuardRatio * guarded_pivots_;
  }

  std::uint64_t polls() const noexcept { return polls_; }
  std::uint64_t pivots() const noexcept { return pivots_; }
  std::uint64_t blandPivots() const noexcept { return bland_pivots_; }

private:
  SATSolver& solver_;
  std::uint64_t maximum_pivots_;
  const std::atomic<bool>* external_interrupt_;
  std::atomic<bool> local_interrupt_{false};
  std::uint64_t polls_ = 0;
  std::uint64_t pivots_ = 0;
  std::uint64_t bland_pivots_ = 0;
  bool check_guarded_ = false;
  bool have_baseline_ = false;
  std::uint64_t materializations_baseline_ = 0;
  std::uint64_t last_made_ = 0;
  std::uint64_t check_pivots_ = 0;
  std::uint64_t guarded_pivots_ = 0;
  std::uint64_t guarded_materializations_ = 0;
  bool guard_stopped_ = false;
};

class LraCandidateAdapter;
class LraCoordinator;

// One instance represents exactly one live SAT/refinement solve epoch.  The
// caller owns its SATSolver and must declare this context after the solver so
// normal reverse destruction releases the context first.
using SerialIndex = std::unordered_map<std::uint64_t, std::size_t>;

class FloatSimplex;

class LraSolveContext final
{
public:
  LraSolveContext(LraAtomRegistry& registry, SATSolver& solver,
                  NumberLimits exact_limits,
                  std::uint64_t maximum_pivots =
                      std::numeric_limits<std::uint64_t>::max(),
                  const std::atomic<bool>* interrupted = nullptr);
  LraSolveContext(LraAtomRegistry& registry, SATSolver& solver,
                  NumberLimits exact_limits,
                  LraAssertionFrameId solve_frame,
                  std::uint64_t maximum_pivots =
                      std::numeric_limits<std::uint64_t>::max(),
                  const std::atomic<bool>* interrupted = nullptr,
                  unsigned row_order = 0);
  ~LraSolveContext() noexcept;

  /* Whether each conflict certificate is independently re-derived before it
   * is trusted.  On by default, so anything constructing a context directly
   * -- every test that does -- keeps the check; the solver turns it off from
   * UserFlags, where it is off unless asked for. */
  void setConflictVerification(bool enabled) noexcept
  {
    verify_conflicts_ = enabled;
    // The core runs its own automatic pass over every conflict it produces,
    // which is a separate check from this context's and was not reachable
    // from the flag at all. One switch governs both: a caller asking for
    // conflicts to be verified means the whole path, and a caller not asking
    // should not be paying for either.
    if (core_ != nullptr)
      core_->setConflictVerification(enabled);
  }
  bool conflictVerification() const noexcept { return verify_conflicts_; }
  /* Route the propagator's asserts and partial checks through the advisory
   * double tier.  Enabling builds the float core from the maps the exact
   * build has already validated; a build whose numbers do not all convert
   * to finite doubles leaves the tier off and the exact path untouched. */
  void setFloatDriver(bool enabled) noexcept;
  void setConflictRecovery(bool enabled) noexcept
  {
    conflict_recovery_ = enabled;
  }
  void setEarlyConflictDetection(bool enabled) noexcept;
  void setSoi(bool enabled) noexcept;
  void setFloatDormantRows(bool enabled, std::int64_t min_cells = 0) noexcept;
  void setFloatPromotionBudget(std::int64_t budget) noexcept
  {
    float_promotion_budget_ = budget <= 0 ? 0U : static_cast<unsigned>(std::min<std::int64_t>(budget, 1U << 30));
  }
  unsigned floatPromotionBudget() const noexcept { return float_promotion_budget_; }
  void setSeparateModelValues(bool enabled) noexcept;
  void setDenseRecovery(bool enabled) noexcept;
  bool extendFromRegistry() noexcept;
  bool restartArithmeticState(bool float_basis_only) noexcept;
  bool refreshRegistryIdentity() noexcept;
  // The fill multiple past which the float tier is judged pathological and the
  // query rerouted to the exact driver; 0 disables it. Carried here so the
  // candidate adapter, which sees only the context, can read it. See
  // UserDefinedFlags::lra_float_reroute.
  void setFloatRerouteBudget(unsigned budget) noexcept
  {
    float_reroute_budget_ = budget;
  }
  unsigned floatRerouteBudget() const noexcept { return float_reroute_budget_; }
  void setFloatRerouteFloor(unsigned floor) noexcept
  {
    float_reroute_floor_ = floor;
  }
  unsigned floatRerouteFloor() const noexcept { return float_reroute_floor_; }
  // On, built, and every input converted finitely.
  bool floatActive() const noexcept;
  // The verifier, or an unconditional pass when it is switched off.
  VerificationResult verifyConflictChecked(
      const Conflict& conflict) const noexcept;

  LraSolveContext(const LraSolveContext&) = delete;
  LraSolveContext& operator=(const LraSolveContext&) = delete;
  LraSolveContext(LraSolveContext&&) = delete;
  LraSolveContext& operator=(LraSolveContext&&) = delete;

  SolveContextStatus status() const noexcept { return status_; }
  const std::string& failureDetail() const noexcept { return failure_detail_; }
  void rethrowPreparationInterruption() const
  {
    if (preparation_stop_)
      throw *preparation_stop_;
  }
  bool ready() const noexcept { return status_ == SolveContextStatus::Ready; }
  std::uint64_t solveEpoch() const noexcept { return solve_epoch_; }
  LraRegistryTag registryTag() const noexcept { return registry_snapshot_.tag; }
  CoreGeneration coreGeneration() const noexcept;

  /* Bind each opaque atom to its SAT literal.
   *
   * `omitted` names the atoms the caller has established the Boolean formula
   * does not mention, and which therefore have no SAT variable. Stating them
   * rather than simply leaving them out is what keeps the coverage check
   * exact: bound plus omitted must still account for every registered atom,
   * so a binding genuinely lost on the way to the CNF is still a fault. */
  bool bindOpaqueAtoms(const std::vector<LraSatBinding>& bindings,
                       const std::vector<ASTNode>& omitted = {}) noexcept;
  bool bindingsReady() const noexcept { return bindings_ready_; }
  bool validateCurrentState() noexcept;

  PendingClauseState pendingClauseState() const noexcept;
  const PendingLraClause* pendingClauseForTesting() const noexcept;
  const StagedExactModel* stagedModelForTesting() const noexcept;
  LraSolveMetrics metrics() const noexcept;
  CoreStatistics coreStatistics() const noexcept;

  // The outer owner calls this immediately before every SAT call.  It never
  // invokes SAT itself; it only enforces same-candidate state invalidation.
  // The public coordinator places the same hook.
  bool beforeSolverCall() noexcept;
  bool notifyContextMutation() noexcept;
  void requestInterrupt() noexcept { observer_.requestInterrupt(); }

#if defined(STP_LRA_TEST_FAULT_INJECTION)
  void testSetNextCandidateSerial(std::uint64_t next) noexcept;
  static void testSetOriginSerialStartForNextContext(
      std::uint64_t next) noexcept;
  void testCorruptPendingEpoch() noexcept;
  void testCorruptPendingCandidate() noexcept;
  void testCorruptPendingOrigin() noexcept;
  void testCorruptPendingLiteralVariable() noexcept;
  void testCorruptPendingLiteralSign() noexcept;
  void testDuplicatePendingSupport();
  void testAddComplementaryPendingSupport();
  void testClearPendingSupport() noexcept;
#endif

private:
  friend class LraCandidateAdapter;
  friend class LraCoordinator;

  void buildCore(std::uint64_t origin_serial_start);
  void buildFloatCore() noexcept;
  /* The float tier asked to be promoted (FloatSimplex::wantsPromotion):
   * build a fresh tier from the same registry, replay the trail into
   * it, switch it to the factorized representation and adopt it.  False
   * leaves the old tier in place. */
  bool promoteFloatCore() noexcept;
  std::unique_ptr<FloatSimplex> makeFloatCore();
  void bindFreshFloatMaps();
  void extendFloatCore() noexcept;
  void initializeSolveContext() noexcept;
  void invalidate(std::string detail) noexcept;
  /* Stop this context because a check could not reach a verdict, rather than
   * because its state is wrong. Same teardown as invalidate -- nothing here
   * may be read afterwards either way -- but the status says "no answer" and
   * not "a fault", which is the difference between the solve reporting
   * unknown and reporting an error. */
  void giveUp(std::string detail) noexcept;
  void clearSemanticState() noexcept;
  std::uint64_t allocateCandidateSerial();
  std::uint64_t allocateOriginSerial();
  const RegistryRow& registryRow(LraCanonicalRowId id) const;
  const RegistryComponent& registryComponent(LraComponentId id) const;
  const RegistryEqualityGroup& registryEquality(
      LraEqualityGroupId id) const;
  const CoreVariableMapEntry& variableMap(LraRegistrySymbolId id) const;
  const CoreRowMapEntry& rowMap(LraCanonicalRowId id) const;
  const CoreComponentMapEntry& componentMap(LraComponentId id) const;
  const OriginMapEntry& originMap(OriginId id) const;
  SATSolver::Lit componentBinding(LraComponentId id) const;
  /* Whether this component reached the CNF at all. A component the Boolean
   * formula never mentions has no SAT variable to read, is never asserted,
   * and cannot appear in a conflict; callers that walk every component skip
   * those rather than demanding a binding that was never possible. */
  bool componentBound(LraComponentId id) const noexcept;
  /* The binding, or nullptr when the component never reached the CNF.  One
   * lookup where asking whether it is bound and then asking for it is two --
   * which matters because the candidate reader asks for every component. */
  const SATSolver::Lit* componentBindingOrNull(
      LraComponentId id) const noexcept;
  bool equalityBound(LraEqualityGroupId id) const noexcept;
  SATSolver::Lit equalityBinding(LraEqualityGroupId id) const;

  LraAtomRegistry& registry_;
  LraAssertionFrameId registry_frame_;
  SATSolver& solver_;
  SolveContextStatus status_ = SolveContextStatus::Invalid;
  std::string failure_detail_;
  std::optional<PreparationInterrupted> preparation_stop_;
  std::uint64_t solve_epoch_ = 0;
  std::uint64_t current_candidate_serial_ = 0;
  std::uint64_t next_candidate_serial_ = 1;
  std::uint64_t next_origin_serial_ = 1;
  bool bindings_ready_ = false;
  bool verify_conflicts_ = true;
  LraSolveMetrics metrics_;
  LraResourceObserver observer_;

  // Destruction is reverse declaration order: staged/pending values and maps
  // disappear first, then the exact core, and finally the budget that owns
  // every context-side exact copy.
  NumberBudget mapping_budget_;
  std::unique_ptr<ExactLraCore> core_;
  /* The advisory tier and its replay mapping: float atoms are created in
   * component order, so float_atom_core_atoms_[float_atom] is the exact
   * atom to replay.  Doubles only; no budget involvement. */
  std::unique_ptr<FloatSimplex> float_core_;
  std::vector<AtomId> float_atom_core_atoms_;
  bool float_driver_ = false;
  unsigned float_reroute_budget_ = 0;
  unsigned float_reroute_floor_ = 0;
  bool conflict_recovery_ = true;
  bool early_conflicts_ = false;
  bool soi_ = false;
  bool float_dormant_rows_ = false;
  std::uint32_t float_dormant_min_cells_ = 0;
  unsigned float_promotion_budget_ = 4;
  bool dense_recovery_ = false;
  unsigned row_order_ = 0;
  LraRegistrySnapshot registry_snapshot_;
  std::vector<CoreVariableMapEntry> variable_map_;
  std::vector<CoreRowMapEntry> row_map_;
  std::vector<CoreComponentMapEntry> component_map_;
  std::vector<OriginMapEntry> origin_map_;
  // Serial-to-position for each of the vectors above and for the snapshot's
  // own tables. Every identifier here is a domain (or a solve epoch) and a
  // serial, and the serial alone separates the entries one context holds, so
  // it indexes them; the identifier is still compared in full on whatever the
  // index returns, which is what keeps a foreign-domain lookup missing.
  //
  // Built or extended at registration boundaries; immutable during search.
  SerialIndex registry_row_index_;
  SerialIndex registry_component_index_;
  SerialIndex registry_equality_index_;
  SerialIndex variable_map_index_;
  SerialIndex row_map_index_;
  SerialIndex component_map_index_;
  SerialIndex origin_map_index_;
  // Serial-keyed, and read once per atom on every candidate. Nothing iterates
  // either of these in order -- both walks are whole-table validation -- so
  // the tree they used to be bought nothing and cost a comparison chain and a
  // pointer chase per lookup.
  std::unordered_map<std::uint64_t, SATSolver::Lit> component_bindings_;
  std::unordered_map<std::uint64_t, SATSolver::Lit> equality_bindings_;
  std::vector<CandidateComponentSelection> current_selection_;
  std::vector<CandidateEqualitySelection> current_equalities_;
  // Rebuilt with the two tables above, once per candidate. The equality
  // cross-check walks every registered equality group and needs three
  // selections for each; finding them by scanning is quadratic in the atom
  // count, on every candidate.
  SerialIndex current_selection_index_;
  SerialIndex current_equalities_index_;
  std::optional<PendingLraClause> pending_clause_;
  std::optional<StagedExactModel> staged_model_;
  // A found-model callback owns its certified witness independently of the
  // search trail: some SAT backends unwind that trail before returning SAT.
  // New searches and context mutations discard it with the semantic state.
  // Declared after core_ so its exact values die before their owning budget.
  struct PropagatedModel final
  {
    std::uint64_t solve_epoch;
    std::uint64_t candidate_serial;
    Model witness;
  };
  std::optional<PropagatedModel> propagated_model_;
};

} // namespace stp::lra

#endif

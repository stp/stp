#ifndef STP_LRA_CANDIDATE_ADAPTER_H
#define STP_LRA_CANDIDATE_ADAPTER_H

#include "LraSolveContext.h"

#include <cstdint>
#include <string>

namespace stp::lra {

enum class AdapterOutcome : std::uint8_t
{
  ModelStaged,
  ConflictPending,
  Interrupted,
  ResourceLimit,
  ClauseInserted,
  InternalNoResult
};

struct AdapterResult final
{
  AdapterOutcome outcome = AdapterOutcome::InternalNoResult;
  std::uint64_t solve_epoch = 0;
  std::uint64_t candidate_serial = 0;
  std::string detail;
};

// SAT-facing production code for the atom registry.  This file includes only STP's common
// SATSolver abstraction through LraSolveContext.h.  It neither creates a SAT
// variable nor starts a SAT solve; the focused outer owner supplies one
// already-complete model and explicitly owns every re-solve.
/* The adapter is also the theory's seat in the SAT search when the backend
 * offers one. Both roles want the same three things -- the registry mapping,
 * the exact core, and the verified-conflict path -- so they live together
 * rather than duplicating that surface. Which role is active is decided once,
 * by the coordinator, from the backend's capability. */
class LraCandidateAdapter final : public SATSolver::TheoryPropagator
{
public:
  LraCandidateAdapter(LraSolveContext& context, SATSolver& solver);
  ~LraCandidateAdapter() noexcept = default;

  LraCandidateAdapter(const LraCandidateAdapter&) = delete;
  LraCandidateAdapter& operator=(const LraCandidateAdapter&) = delete;

  AdapterResult checkCompleteCandidate() noexcept;
  AdapterResult encodeAndInsertPendingClause() noexcept;
  // Emit the per-row bound-ordering axioms once, after the opaque atoms have
  // been bound and before the first solve.  See the implementation for what
  // they say and why the full-lazy loop needs them stated up front.
  AdapterResult emitBoundOrderingAxioms() noexcept;

  // --- SATSolver::TheoryPropagator -------------------------------------
  //
  // These run inside CaDiCaL's search, so none of them may throw: each one
  // catches everything and reports through failed(), after which the rest
  // go quiet and the coordinator discards the solve.
  void notifyAssigned(const std::vector<SATSolver::Lit>& literals) override;
  void notifyNewLevel() override;
  void notifyBacktrack(size_t level) override;
  bool checkFoundModel() override;
  bool takeClause(std::vector<SATSolver::Lit>& clause) override;
  bool pastTimeLimit() noexcept;
  bool failed() const override;
  void setDecisionPolarity(bool enabled) noexcept { decision_polarity_ = enabled; }
  bool wantsDecisionPolarity() const override { return decision_polarity_; }
  bool decisionPolarity(uint32_t variable, bool& value) noexcept override;

  // Prepare to drive the search rather than judge it: build the variable
  // map, open the root theory level, and report the variables the backend
  // must observe. False if the mapping is not current.
  bool beginTheoryPropagation(std::vector<uint32_t>& observed) noexcept;

  // Consume the model the search has already certified, checking it against
  // the final SAT selection even if the backend has unwound its trail.
  AdapterResult acceptPropagatedModel() noexcept;
  void endTheoryPropagation() noexcept;
#if defined(STP_LRA_TEST_FAULT_INJECTION)
  bool testValidateStagedModel() noexcept;
#endif

private:
  /* Theory-propagation state. Entry 0 is the root level the backend never
   * backtracks past; entry i belongs to decision level i.
   *
   * A level holds a checkpoint only once a bound has actually been asserted
   * at it. That is not an optimisation: Checkpoint is {generation, depth}
   * where depth is a position in the model trail, not a level index, so two
   * pushes with no bound between them produce the same checkpoint -- and
   * ExactLraRegistration::pop resolves a checkpoint to the first level
   * carrying it and resizes to there, which would unwind every level above
   * as well. Decision levels that assign no LRA atom are common, so this
   * matters immediately. */
  std::vector<std::optional<Checkpoint>> level_checkpoints_;
  std::vector<SATSolver::Lit> pending_theory_clause_;
  /* Float-driver state: the advisory tier's trail mark per decision level
   * (same lazy discipline as level_checkpoints_), and the lazy exact
   * mirror -- one batch per decision level that had asserts, each one
   * exact-core checkpoint covering that level's slice of the float trail,
   * built at sync time and popped exactly when the search leaves the
   * level.  Kept levels are never re-asserted. */
  std::vector<std::optional<std::size_t>> float_level_marks_;
  struct SyncBatch final
  {
    Checkpoint checkpoint;
    std::size_t level;
    std::size_t to;
  };
  std::vector<SyncBatch> sync_batches_;
  /* Unwinding is deferred to the next sync, so this records the lowest
   * level any backtrack reached since the last reconcile: a batch for
   * level 4 survives a sync at level 5 only if no backtrack dipped below
   * 4 in between -- comparing against the sync-time level alone would
   * keep batches whose entries a deeper backjump already undid. */
  std::size_t unwind_low_level_ = static_cast<std::size_t>(-1);
  std::map<uint32_t, LraComponentId> component_by_variable_;
  bool propagating_ = false;
  // Once a callback skips work at the deadline, re-arming the backend's
  // timer cannot make that incomplete propagation trail acceptable.
  bool deadline_interrupted_ = false;
  bool conflict_pending_ = false;
  // Bounds have been asserted since the tableau was last checked. Cleared by
  // the check the next clause poll runs, and by a backtrack, which pops back
  // to a state that was checked.
  bool theory_dirty_ = false;
  bool decision_polarity_ = false;
  enum class AdviceSource : std::uint8_t { None, Float, Exact };
  AdviceSource advice_source_ = AdviceSource::None;
  /* Partial checks run under the observer's arithmetic guard. On a tableau
   * whose pivots stay in word arithmetic it never fires; on a dense one
   * whose coefficients have grown wide, a partial check pivots for seconds
   * in big-number arithmetic, where the full-lazy loop decides the whole
   * file in a few checks. A check the guard stops is abandoned -- its
   * pivots are kept, so nothing is lost -- and after two of those, partial
   * checks are off for the rest of the solve: the propagator still catches
   * the immediate conflicts and judges complete assignments, which is the
   * full-lazy behaviour inside the search. */
  bool partial_checks_enabled_ = true;
  unsigned partial_checks_abandoned_ = 0;
  /* Fresh factorized tiers built from the trail in this solve, after the
   * double tier tripped its infinitesimal cap.  One such tier is the design
   * intent: a tableau whose pivot history blew up gets a factor over the
   * pristine rows instead.  A tier that trips on its own first check has
   * no history to blame, and building another identical one cannot end
   * differently -- measured as 18,094 promotions in one solve, each a full
   * trail replay and refactor, with SAT advancing a clause between them.
   * Past the budget the abandonment cascade below runs instead. */
  unsigned float_promotions_ = 0;
  /* Float-driver degrade, per solve: when the float tableau keeps blowing
   * its merge or pivot budget, its checks are hopeless for this instance
   * -- but pruning must not stop, or the search builds thousands of
   * doomed models that each pay a full exact replay.  Degraded means
   * partial checks run sync-plus-exact on the lazily maintained mirror
   * instead (as with --lra-float-driver=0), and the found-model float filter
   * steps aside. */
  bool float_checks_degraded_ = false;
  unsigned float_restarts_ = 0;
  unsigned complete_recoveries_ = 0;
  unsigned cold_factorized_restarts_ = 0;
  /* Sampling counter for the float-tier reroute check: liveNonzeros scans the
   * tableau, so the fill ratio is measured every few checks rather than every
   * one. */
  unsigned float_reroute_sample_ = 0;

  bool assertOneLiteral(SATSolver::Lit literal) noexcept;
  // Open a core checkpoint for the current level, if it has none yet.
  bool ensureLevelCheckpoint() noexcept;
  /* The float-driver counterparts: a trail mark for the current level, a
   * lazy sync that brings the exact core up to the float trail (popping
   * diverged batches, asserting only the new slice), and the exact check
   * over the synced state that certifies the advisory tier's candidates.
   * The synced bounds persist across calls; only rewinds below a batch
   * unwind it. */
  bool ensureFloatLevelMark() noexcept;
  /* Drop the mirror batches for levels above `level` and unwind the core
   * past all of them with one pop -- pops resolve a checkpoint to the
   * first level carrying it and unwind everything above, so the deepest
   * dead batch's checkpoint removes the whole dead suffix in one repair
   * pass instead of one per batch. */
  bool unwindDeadBatches(std::size_t level) noexcept;
  enum class SyncOutcome : std::uint8_t
  {
    Clean,
    ConflictStaged,
    /* A staged conflict's backtrack has not arrived yet: the core is in
     * Conflict and refuses pushes.  The backend may assert and poll in
     * that window; certifying nothing there is safe, the backtrack is
     * already forced. */
    CoreBusy,
    Failed
  };
  SyncOutcome syncFloatTrailIntoExact() noexcept;
  enum class ReplayVerdict : std::uint8_t
  {
    ConflictStaged,
    Consistent,
    Inconclusive
  };
  ReplayVerdict syncAndCheckExact(bool final_check,
                                 std::optional<Model>* witness = nullptr) noexcept;
  // Keep the certified value object, not a reference to the current tableau.
  bool retainPropagatedModel(Model witness);
  /* Certificate-first certification: hand the float tier's Farkas support
   * (atoms, polarities, dyadic weights) to the core's candidate verifier
   * and stage the returned exact Conflict.  False means no certificate,
   * an unverifiable one, or staging failed -- the caller falls back to
   * exact re-derivation. */
  bool stageCertificateConflict() noexcept;
  /* The certification middle of stageCertificateConflict: the float
   * tier's certificate, converted and judged by the core, as a verified
   * Conflict -- without any staging, so both the propagated path (theory
   * clause) and the full-lazy path (pending clause) can consume it. */
  std::optional<Conflict> certifyFloatCertificate() noexcept;
  /* The full-lazy candidate check, attempted on the float engine: scratch
   * -assert the selection, check, certify or refine, undo the scratch.
   * True means `out` carries the staged outcome; false means the caller
   * runs the exact path.  Throws only from staging, like that path. */
  bool floatCompleteCandidate(std::uint64_t candidate, AdapterResult& out);
  /* Model refinement off the float assignment: reconstruct every base
   * variable's (value, epsilon) pair as exact rationals, and have the
   * core substitute a concrete epsilon and verify against the float
   * trail's asserted bounds. A rejected proposal allows an exact re-check;
   * an observer stop ends the attempt before replaying the exact trail. */
  struct ModelRefinement final
  {
    std::optional<Model> witness;
    StopReason stop = StopReason::Continue;
  };
  ModelRefinement refineAndCertifyModel() noexcept;
  bool assertOneLiteralFloat(SATSolver::Lit literal,
                             const CoreComponentMapEntry& mapped) noexcept;
  bool stageTheoryConflict(const Conflict& conflict) noexcept;
  // The caller has already verified this witness against its support.
  bool stageVerifiedTheoryConflict(const Conflict& conflict) noexcept;
  // The tableau check on the bounds asserted so far, run at most once per
  // round of assignments: a conflict is staged for takeClause.
  void checkPartialAssignment() noexcept;

  // Sample the float tableau's fill and, if it has blown past the reroute
  // budget, ask the SAT backend to stop so the query can be redone on the
  // exact driver. Cheap and a no-op unless the budget is set and the float
  // tier is live. Verdict-preserving: the exact core certifies float results,
  // so the reroute only changes runtime. See UserDefinedFlags::lra_float_reroute.
  void maybeRequestFloatReroute() noexcept;

  bool readLiteral(SATSolver::Lit literal, bool& value,
                   std::string& detail) const;
  /* core_derived as in stageVerifiedModel: a candidate-certified conflict
   * does not require the core's own state to say Conflict. */
  void copyVerifiedConflict(const Conflict& conflict,
                            std::uint64_t candidate_serial,
                            bool core_derived = true);
  /* core_derived: the model came from the core's own check, whose state
   * must then still say Consistent; a candidate-certified model's
   * vouching is its verification, not the core's state. */
  void stageVerifiedModel(const Model& model, std::uint64_t candidate_serial,
                          bool core_derived = true);
  void independentlyCheckStagedModel() const;
  AdapterResult result(AdapterOutcome outcome, std::uint64_t candidate,
                       std::string detail = {}) const;
  /* The one place the driver's catch clauses decide which kind of refusal
   * they are holding. Every step of a candidate does exact arithmetic, and
   * the four layers that do it each refuse in their own currency when a
   * budget runs out -- none of which is a fault of ours. Taking the
   * exception apart here, while it is still in hand, is what keeps a spent
   * budget on the propagating path from being reported as an internal
   * error; without it the default path had no resource-limit outcome at
   * all. */
  AdapterResult refusal(const std::exception& failure,
                        std::uint64_t candidate) noexcept;
  // The one reader of the SAT assignment into the context's selection, for
  // both candidate paths. See the definition for `verify_stable`.
  void readSelectionFromSolver(bool verify_stable);

  LraSolveContext& context_;
  SATSolver& solver_;
};

} // namespace stp::lra

#endif

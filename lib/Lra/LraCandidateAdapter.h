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
  enum class AdviceSource : std::uint8_t { None, Exact };
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

  bool assertOneLiteral(SATSolver::Lit literal) noexcept;
  // Open a core checkpoint for the current level, if it has none yet.
  bool ensureLevelCheckpoint() noexcept;
  // Keep the certified value object, not a reference to the current tableau.
  bool retainPropagatedModel(Model witness);
  bool stageTheoryConflict(const Conflict& conflict) noexcept;
  // The caller has already verified this witness against its support.
  bool stageVerifiedTheoryConflict(const Conflict& conflict) noexcept;
  // The tableau check on the bounds asserted so far, run at most once per
  // round of assignments: a conflict is staged for takeClause.
  void checkPartialAssignment() noexcept;

  bool readLiteral(SATSolver::Lit literal, bool& value,
                   std::string& detail) const;
  void copyVerifiedConflict(const Conflict& conflict,
                            std::uint64_t candidate_serial);
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

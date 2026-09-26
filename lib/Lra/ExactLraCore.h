#ifndef STP_LRA_EXACT_LRA_CORE_H
#define STP_LRA_EXACT_LRA_CORE_H

#include "ExactLraTypes.h"

#include <memory>

namespace stp::lra {

class ExactLraResourceObserver
{
 public:
  virtual ~ExactLraResourceObserver() = default;
  virtual StopReason pollBeforePivot() noexcept = 0;
  virtual void accountPivot(bool bland) noexcept = 0;
};

class ExactLraCore final
{
 public:
  explicit ExactLraCore(NumberLimits,
                        DirectBoundsMode = DirectBoundsMode::Disabled);
  ~ExactLraCore() noexcept;

  ExactLraCore(ExactLraCore&&) noexcept;
  ExactLraCore& operator=(ExactLraCore&&) noexcept;
  ExactLraCore(ExactLraCore const&) = delete;
  ExactLraCore& operator=(ExactLraCore const&) = delete;

  InputResult<VariableId> addVariable();
  InputResult<RowId> addRow(LinearTerm const* begin,
                            LinearTerm const* end);
  InputResult<AtomId> addAtom(RowId,
                              Relation positive_relation,
                              ExactRational const& threshold,
                              OriginId positive_origin,
                              OriginId negative_origin);

  InputStatus initialize();

  InputResult<Checkpoint> push();
  InputStatus pop(Checkpoint);
  AssertResult assertLiteral(AtomId, bool positive);

  // `verify_model`: whether a consistent result is re-derived by the model
  // verifier before it is trusted. A check on a partial assignment, whose
  // model nobody will read, passes false; the final check keeps the default.
  CheckResult check(ExactLraResourceObserver&, bool verify_model = true);

  VerificationResult verifyConflict(Conflict const&) const;
  VerificationResult verifyModel(Model const&) const;

  /* Judge a conflict certificate proposed from outside -- atoms, asserted
   * polarities and positive Farkas weights:
   * the bounds are resolved from the registration, the exact combination
   * is verified (cancellation over every base variable, negative right
   * side), and only a verified certificate comes back as a Conflict
   * carrying this core's current witness tag.  Read-only: no state, no
   * revision, no requirement that the cited bounds are asserted here.
   * With recover_weights, a rejected combination can be reconstructed by
   * bounded sparse elimination over these same bounds. Free weights use
   * the proposal as a hint; cancellation, positivity and contradiction
   * are still verified exactly. The observer can interrupt recovery.
   * The optional support limit permits larger advisory LP proofs; it is
   * capped at 4096 and scales the bounded sparse work allowance. The default
   * preserves the ordinary float driver's existing 512-term recovery budget.
   * Rejected certificates return an unaccepted result; the caller falls
   * back to exact simplex. Neither path mutates the tableau or trail. */
  InputResult<Conflict>
  certifyCandidateConflict(ConflictCandidateTerm const* begin,
                           ConflictCandidateTerm const* end,
                           bool recover_weights = false,
                           ExactLraResourceObserver* observer = nullptr,
                           std::size_t recovery_support_limit = 512);

  /* Judge a model certificate proposed from outside: symbolic
   * value-plus-epsilon pairs for every base variable in ascending order,
   * and the asserted atoms whose bounds the model must satisfy.  The core
   * picks a concrete epsilon against those bounds, substitutes, verifies
   * the result exactly against the named bounds, and only a verified
   * model comes back, carrying this core's current witness tag.
   * Read-only, like the conflict counterpart.
   *
   * `pinned` names advisory bounds the proposing tier's point sits on
   * exactly.  When the proposed coordinates alone fail verification,
   * the core solves that equality system over its own exact rows --
   * decimal instances put vertices where no double-reconstructed
   * rational lands -- and verifies the solved model instead. Repair is
   * advisory: bounded work or coefficient growth declines it, as does an
   * observer stop. Neither changes the core or invalidates old witnesses.
   * Hints are inspected only if the direct model fails verification.
   * A caller that needs the stop reason should record its observer's result. */
  InputResult<Model> certifyCandidateModel(
      ModelCandidateValue const* values_begin,
      ModelCandidateValue const* values_end,
      CandidateBound const* bounds_begin, CandidateBound const* bounds_end,
      CandidateBound const* pinned_begin = nullptr,
      CandidateBound const* pinned_end = nullptr,
      ExactLraResourceObserver* observer = nullptr);

  // Whether the core re-derives every conflict it produces before returning
  // it. On by default, so a caller that builds a core directly keeps the
  // check; the solver turns it off unless --lra-verify-conflicts asks for it,
  // which is the same arrangement LraSolveContext already has. The two
  // verifyConflict/verifyModel entry points above are unaffected: those are a
  // caller asking, and this only governs what the core does on its own.
  //
  // It is not free. On a query that spends its time refuting candidates the
  // automatic pass was a sixth of the run.
  void setConflictVerification(bool enabled) noexcept;
  void setEarlyConflictDetection(bool enabled) noexcept;
  void setSoi(bool enabled) noexcept;
  /* Whether a model produced by check() has accidental value coincidences
   * broken before it is exported. See ExactSimplex::separateCoincidentValues. */
  void setSeparateModelValues(bool enabled) noexcept;
  // Heuristic evaluation of one atom at a checked assignment. Never a
  // deduction; failure or unavailable state simply declines advice.
  std::optional<bool> preferredPolarity(AtomId atom) const noexcept;

  CoreStatistics statistics() const noexcept;
  CheckStatus status() const noexcept;
  CoreGeneration generation() const noexcept;

  void reset() noexcept;
  // Reopen registration with no asserted bounds/checkpoints. Existing IDs,
  // assignments and basis survive; old witnesses are invalidated. Finish
  // the append with initialize(). Reset remains the destructive operation.
  InputStatus beginExtension() noexcept;
  // Reset assignments and basis at an unasserted boundary, keeping all IDs,
  // row insertion order, registrations and cumulative work statistics.
  InputStatus restartSearchState() noexcept;

#if defined(STP_LRA_TEST_FAULT_INJECTION)
  void testCorruptVerificationRow(RowId);
  void testCorruptVerificationBound(AtomId, bool positive);
  void testForceNextConflictVerificationResource() noexcept;
  void testForceNextModelVerificationResource() noexcept;
  VerificationError testLastVerificationError() const noexcept;
#endif

 private:
  class Impl;
  std::unique_ptr<Impl> impl_;
};

}  // namespace stp::lra

#endif

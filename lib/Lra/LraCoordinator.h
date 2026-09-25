#ifndef STP_LRA_COORDINATOR_H
#define STP_LRA_COORDINATOR_H

#include "LraAtomRegistry.h"
#include "LraCandidateAdapter.h"
#include "LraFrontend.h"
#include "RealModel.h"

#include <chrono>
#include <cstdint>
#include <iosfwd>
#include <memory>
#include <map>
#include <string>

namespace stp {
class AbsRefine_CounterExample;
class ToSATBase;

namespace lra {

enum class CoordinatorCandidateOutcome : std::uint8_t
{
  ModelStaged,
  ConflictPending,
  Interrupted,
  ResourceLimit,
  InternalNoResult
};

enum class StagedDiscardReason : std::uint8_t
{
  ArrayConflict,
  OrdinaryRefinement,
  LegacyArrayReadRefinement,
  SolverCall,
  StopOrError
};

/* What an in-place extension did, which is not the same question as
 * whether it succeeded.
 *
 * `Declined` is answered before anything is touched: the coordinator keeps
 * its registry, its arithmetic and the model it has committed, and the
 * caller's fallback -- solve the enlarged query again from the top -- can
 * still read all three.  The other two are answered after the extension has
 * begun to replace them, so that fallback is no longer available and no
 * verdict from this solve can stand. `Interrupted` preserves preparation
 * cancellation for the public query boundary. `ResourceLimit` says a budget refused
 * the work, which is a query STP cannot decide; `Failed` says the
 * coordinator is broken, which is a fault of ours. */
enum class ExtensionOutcome : std::uint8_t
{
  Extended,
  Declined,
  Interrupted,
  ResourceLimit,
  Failed
};

/* What publishing a verified model did. The same two-state distinction the
 * candidate outcomes carry, at the one boundary that used to drop it: a
 * budget refusal in the publication checks is a query this solve cannot
 * answer, not a fault to report as one. */
enum class CommitOutcome : std::uint8_t
{
  Committed,
  ResourceLimit,
  Failed
};

struct LraCoordinatorMetrics final
{
  std::uint64_t solve_epoch = 0;
  std::uint64_t candidates = 0;
  std::uint64_t lra_consistent = 0;
  std::uint64_t lra_conflicts = 0;
  std::uint64_t lra_clauses = 0;
  // Times the solve took on more of the query without starting over.
  std::uint64_t extensions = 0;
  // Actual arithmetic constructions, including the initial core.
  std::uint64_t core_rebuilds = 0;
  std::uint64_t conflict_support_literals = 0;
  std::uint64_t learned_clause_literals = 0;
  std::uint64_t maximum_conflict_support = 0;
  std::uint64_t maximum_learned_clause = 0;
  std::uint64_t equality_support_compressions = 0;
  std::uint64_t sat_resolves = 0;
  std::uint64_t array_consistent = 0;
  std::uint64_t array_conflicts = 0;
  std::uint64_t array_not_applicable = 0;
  std::uint64_t ordinary_consistent = 0;
  std::uint64_t ordinary_refinements = 0;
  std::uint64_t legacy_refinements = 0;
  std::uint64_t staged_models_discarded = 0;
  std::uint64_t discarded_for_array = 0;
  std::uint64_t discarded_for_ordinary = 0;
  std::uint64_t discarded_for_legacy = 0;
  std::uint64_t models_committed = 0;
  std::uint64_t committed_model_values = 0;
  std::uint64_t preregistration_nanoseconds = 0;
  std::uint64_t context_rebuild_nanoseconds = 0;
  std::uint64_t formula_evaluation_nanoseconds = 0;
  std::uint64_t publication_nanoseconds = 0;
};

// Arithmetic owner for one batch query. The outer STP loop owns SAT search
// and invokes the transition hooks between candidates and when the query
// is extended.
class LraCoordinator final
{
public:
  // `spread_symbols`: Real symbols whose free values every model keeps
  // apart -- the arguments of uninterpreted applications, which would
  // otherwise all sit at zero and be taken for equal. See the RealModel
  // constructor, and separateModelValuesEnabled, whose AUTO reads them.
  LraCoordinator(STPMgr& manager, SATSolver& solver,
                 const ASTNode& submitted_formula,
                 const std::vector<ASTNode>& spread_symbols =
                     std::vector<ASTNode>());
  ~LraCoordinator() noexcept;

  LraCoordinator(const LraCoordinator&) = delete;
  LraCoordinator& operator=(const LraCoordinator&) = delete;

  const ASTNode& booleanFormula() const noexcept
  {
    return registered_.boolean_formula;
  }
  const ASTNode& solveActivation() const noexcept
  {
    return solve_activation_;
  }
  const std::vector<ASTNode>& opaqueAtoms() const noexcept
  {
    return opaque_atoms_;
  }

  bool ready() const noexcept;
  const std::string& failureDetail() const noexcept { return failure_detail_; }
  void rethrowPreparationInterruption() const
  {
    if (preparation_stop_)
      throw *preparation_stop_;
  }
  /* What the last candidate check that stopped at a resource limit said;
   * a reason for an unknown answer, not a fault of the coordinator. */
  const std::string& resourceLimitDetail() const noexcept
  {
    return resource_limit_detail_;
  }
  /* True when this coordinator stopped because a budget refused the work,
   * rather than because something here is wrong. Every `ready()` test that
   * decides a verdict has to ask: not ready is the same bit for both, and
   * answering SOLVER_ERROR for the first is how a query STP merely could
   * not finish was reported as a fault of STP's. */
  bool gaveUp() const noexcept;
  std::uint64_t solveEpoch() const noexcept;
  std::uint64_t candidateSerial() const noexcept;

  bool beforeSolverCall() noexcept;

  // Take on more of the query between rounds, without a new solve. The
  // formula's Real predicates are registered into this solve's frame, the
  // exact core is rebuilt over the enlarged registry, and the Boolean
  // formula that results -- over opaque atoms, scalars the first encoding
  // already holds, and connectives -- is encoded as clauses into the SAT
  // solver this solve has been using, under its activation, which keeps
  // every clause that solver has learned. New atoms take fresh variables and
  // are entered in `tosat`'s symbol map, where the rebuilt context binds
  // them like the rest.
  //
  // `Declined` when the coordinator will not start: it is not ready, or the
  // formula is not one of this manager's Boolean nodes. Nothing has moved,
  // so the caller can fall back to solving again from the start.
  // `ResourceLimit` and `Failed` are refusals from inside the work, after
  // the registry, the arithmetic and the committed model have begun to be
  // replaced; the caller has no query left to fall back to and must give up
  // the solve. A connected theory propagator is disconnected first and
  // reconnected by the solve that follows.
  ExtensionOutcome extendWithFormula(const ASTNode& formula,
                                     ToSATBase& tosat) noexcept;
  CoordinatorCandidateOutcome checkCompleteCandidate(ToSATBase& tosat) noexcept;
  bool hasPendingLraClause() const noexcept;
  bool encodePendingLraClause() noexcept;
  bool hasStagedModel() const noexcept;

  void noteArrayOutcome(bool consistent) noexcept;
  void noteArrayNotApplicable() noexcept;
  void noteOrdinaryOutcome(bool consistent) noexcept;
  void setLegacyArrayRefinementEnabled(bool enabled) noexcept
  {
    legacy_array_refinement_enabled_ = enabled;
  }
  bool legacyArrayRefinementPending() const noexcept
  {
    return legacy_refinement_pending_;
  }
  void noteLegacyArrayRefinementEncoded() noexcept;
  void discardStagedModel(StagedDiscardReason reason) noexcept;

  // Re-evaluate the original mixed submitted formula, validate every source
  // predicate/equality against the same SAT assignment, then atomically move
  // a clean solve-independent RealModel into STPMgr.
  CommitOutcome verifyAndCommit(
      AbsRefine_CounterExample& counterexample) noexcept;
  void failClosed(std::string detail) noexcept;

  LraCoordinatorMetrics metrics() const noexcept;
  LraSolveMetrics solveMetrics() const noexcept;
  CoreStatistics coreStatistics() const noexcept;

#if defined(STP_LRA_TEST_FAULT_INJECTION)
  void testCorruptCandidateSerial() noexcept;
  void testCorruptStagedEpoch() noexcept;
  void testCorruptStagedCandidateSerial() noexcept;
  void testDropStagedValue() noexcept;
  void testDuplicateStagedValue();
  void testCorruptStagedSymbol() noexcept;
  void testCorruptStagedRegistryId() noexcept;
  void testCorruptStagedNumerator();
  void testCorruptStagedDenominator();
  void testReplaceStagedExactValue();
  bool testValidateStagedModel() noexcept;
#endif

private:
  bool decisionPolarityEnabled() const;
  bool separateModelValuesEnabled() const;
  bool bindOpaqueAtoms(ToSATBase& tosat) noexcept;
  bool prepareTheorySearch() noexcept;
  bool readOpaqueValue(const ASTNode& atom, bool& value) const noexcept;
  bool evaluateSubmittedFormula(const ASTNode& formula, const RealModel& model,
                                AbsRefine_CounterExample& counterexample) const;
  bool validateSourcePredicates(const RealModel& model) const;
  std::unique_ptr<RealModel> materializeStagedModel(
      ) const;
  ASTVec requiredRealSymbols() const;
  void addElapsed(std::uint64_t& destination,
                  std::chrono::steady_clock::time_point start) noexcept;
  void printMetrics(std::ostream& out) const;

  STPMgr& manager_;
  SATSolver& solver_;
  ASTNode submitted_formula_;
  ASTNode solve_activation_;
  Frontend frontend_;
  LraAtomRegistry registry_;
  LraAssertionFrameId frame_;
  PreregisteredFormula preregistered_;
  RegisteredLraFormula registered_;
  std::vector<ASTNode> opaque_atoms_;
  // Membership of opaque_atoms_, kept alongside it so an extension can
  // append without re-deriving what is already listed.
  std::set<ASTNode, ExprLess> opaque_atom_set_;
  std::map<ASTNode, ASTNode, ExprLess> source_atom_aliases_;
  std::map<ASTNode, SATSolver::Lit, ExprLess> opaque_bindings_;
  std::unique_ptr<LraSolveContext> context_;
  std::unique_ptr<LraCandidateAdapter> adapter_;
  // See the constructor. Handed to every model this coordinator commits.
  std::vector<ASTNode> spread_symbols_;
  bool frame_live_ = false;
  ASTNode base_submitted_;
  ASTNode base_registered_;
  ASTVec permanent_submitted_;
  ASTVec permanent_registered_;
  ExtensionOutcome extendInternal(const ASTNode& formula, ToSATBase& tosat,
                                  const ASTNode* frame_activation) noexcept;
  void rebuildLiveFormulas();
  void rebuildCoreAndContext();
  bool bindings_ready_ = false;
  // True once the theory has taken a seat inside the SAT search, which
  // replaces the candidate loop rather than supplementing it.
  bool propagating_ = false;
  // The per-row bound-ordering axioms are stated once, between the first and
  // second solve, and hold for the rest of the top-level solve.
  bool ordering_axioms_emitted_ = false;
  bool legacy_array_refinement_enabled_ = false;
  bool legacy_refinement_pending_ = false;
  std::string failure_detail_;
  std::optional<PreparationInterrupted> preparation_stop_;
  std::string resource_limit_detail_;
  LraCoordinatorMetrics metrics_;
};

} // namespace lra
} // namespace stp

#endif

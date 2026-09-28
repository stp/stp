#include "LraCoordinator.h"

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/ToSat/ToSATAIG.h"
#include "stp/UninterpretedFunctions/UFContext.h"

#if defined(USE_CADICAL)
#include "stp/Sat/Cadical.h"
#endif

#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using namespace stp;
using namespace stp::lra;

void require(bool condition, const std::string& detail)
{
  if (!condition)
    throw std::runtime_error(detail);
}

#if defined(USE_CADICAL)
void searchResetPreservesFormula()
{
  Cadical solver;
  const auto x = solver.newVar();
  const auto unused = solver.newVar();
  SATSolver::vec_literals clause;
  clause.push(SATSolver::mkLit(x, false));
  require(solver.addClause(clause), "assert reset control's unit");
  clause.clear();
  clause.push(SATSolver::mkLit(unused, false));
  clause.push(SATSolver::mkLit(unused, true));
  require(solver.addClause(clause), "declare an otherwise unconstrained variable");
  SATSolver::vec_literals assumptions;
  assumptions.push(SATSolver::mkLit(x, true));
  bool timeout = false;
  require(!solver.solveWithAssumptions(assumptions, timeout) && !timeout,
          "contradictory assumption is UNSAT");
  require(solver.resetSearch(), "reset after assumption UNSAT");
  require(solver.nVars() == unused && solver.solve(timeout) && !timeout,
          "reset keeps variable namespace and drops assumptions");
  require(solver.modelValue(x) == solver.true_literal(), "copied unit remains true");
  (void)solver.modelValue(unused);
  require(solver.resetSearch(), "reset after SAT");
  require(!solver.solveWithAssumptions(assumptions, timeout) && !timeout,
          "copied formula still refutes the opposite literal");
}

// Exercise capability fallback even when the test build has the advisor API.
class NoPolarityCadical final : public Cadical
{
public:
  bool supportsDecisionPolarity() const override { return false; }
  bool connectTheoryPropagator(TheoryPropagator* propagator,
                              const std::vector<uint32_t>& observed) override
  {
    require(!propagator->wantsDecisionPolarity(),
            "unsupported backend must receive a propagator without advice");
    return Cadical::connectTheoryPropagator(propagator, observed);
  }
};
#endif

enum class StageFault
{
  None,
  Epoch,
  StageSerial,
  CurrentSerial,
  MissingValue,
  DuplicateValue,
  ForeignSymbol,
  ForeignRegistryId,
  InconsistentNumerator,
  InvalidDenominator,
  WrongExactValue,
  ReconstructionValid,
  ReconstructionWrong,
  OriginalRejects
};

void applicationModelInvariants()
{
  STPMgr manager;
  manager.UserFlags.enable_uninterpreted_functions = true;
  const auto p = manager.CreateSourceSymbol("argument_p", SourceSort::boolean());
  const auto q = manager.CreateSourceSymbol("argument_q", SourceSort::boolean());
  const auto x = manager.CreateSourceSymbol("result_x", SourceSort::real());
  const auto y = manager.CreateSourceSymbol("result_y", SourceSort::real());
  std::string diagnostic;
  UFContext* context = manager.getUFContext();
  const UFDecl* f = context->declareFunction(
      "model_f", {SourceSort::boolean()}, SourceSort::real(), &diagnostic);
  require(f != nullptr, "model invariant function declaration");
  const auto fp = context->apply(f, ASTVec{p}, &diagnostic);
  const auto fq = context->apply(f, ASTVec{q}, &diagnostic);
  require(!fp.IsNull() && !fq.IsNull(), "model invariant applications");
  Frontend frontend(manager);
  RealModel conflicting(frontend.numberLimits(), {{x, "1", "1"}, {y, "2", "1"}},
                        ASTVec{x, y});
  conflicting.setScalarKeyOracle([](const ASTNode&) { return "same-value"; });
  bool rejected = false;
  try
  {
    conflicting.defineApplicationValues(ASTNodeMap{{fp, x}, {fq, y}});
  }
  catch (const std::exception&)
  {
    rejected = true;
  }
  require(rejected, "conflicting results for one argument tuple were published");

  RealModel unreadable(frontend.numberLimits(), {}, {});
  unreadable.markCommitted();
  unreadable.setScalarKeyOracle([](const ASTNode&) -> std::string {
    throw std::runtime_error("test unreadable scalar");
  });
  require(!unreadable.hasValue(fp), "unreadable argument silently became zero");
  unreadable.setScalarKeyOracle([](const ASTNode&) { return "unobserved-value"; });
  require(unreadable.stringsFor(fp).canonical_fraction == "0",
          "readable unmatched tuple lost its total-function default");
}

void reconstructionOrder()
{
  STPMgr manager;
  const auto x =
      manager.CreateSourceSymbol("reconstruct_x", SourceSort::real());
  const auto y =
      manager.CreateSourceSymbol("reconstruct_y", SourceSort::real());
  const auto z =
      manager.CreateSourceSymbol("reconstruct_z", SourceSort::real());
  const auto half = manager.CreateRealConst("1/2");
  const auto term = manager.CreateRealTerm(REAL_ADD, ASTVec{x, half});
  Frontend frontend(manager);
  RealModel model(frontend.numberLimits(), {{x, "3", "2"}}, ASTVec{x, y, z});
  require(model.stringsFor(y).canonical_fraction == "0", "unvalued default");
  model.reconstruct({{y, term}, {z, y}});
  require(model.stringsFor(y).canonical_fraction == "2" &&
              model.stringsFor(z).canonical_fraction == "2",
          "exact DAG replay");
  using ReconstructionKind = RealModelDefinition::Kind;
  RealModel monotone(frontend.numberLimits(), {{x, "3", "2"}}, ASTVec{x, y, z});
  monotone.reconstruct({{y, ASTVec{x, half}, ReconstructionKind::AboveMaximum},
                        {z, ASTVec{y, term}, ReconstructionKind::BelowMinimum}});
  require(monotone.stringsFor(y).canonical_fraction == "5/2" &&
              monotone.stringsFor(z).canonical_fraction == "1",
          "exact extrema and margins must share the model number budget");
  for (const std::vector<RealModelDefinition>& bad :
       {std::vector<RealModelDefinition>{{y, z}, {z, term}},
        std::vector<RealModelDefinition>{{y, y}},
        std::vector<RealModelDefinition>{{y, term}, {y, half}},
        std::vector<RealModelDefinition>{{half, term}},
        std::vector<RealModelDefinition>{
            {y, ASTVec{x, z}, ReconstructionKind::AboveMaximum}, {z, term}},
        std::vector<RealModelDefinition>{
            {y, ASTVec{x, y}, ReconstructionKind::BelowMinimum}},
        std::vector<RealModelDefinition>{
            {y, term}, {y, ASTVec{x}, ReconstructionKind::AboveMaximum}},
        std::vector<RealModelDefinition>{
            {y, ASTVec{}, ReconstructionKind::AboveMaximum}},
        std::vector<RealModelDefinition>{
            {y, ASTVec{ASTNode()}, ReconstructionKind::BelowMinimum}}})
  {
    RealModel candidate(frontend.numberLimits(), {{x, "3", "2"}},
                        ASTVec{x, y, z});
    bool rejected = false;
    try
    {
      candidate.reconstruct(bad);
    }
    catch (const std::exception&)
    {
      rejected = true;
    }
    require(rejected, "malformed reconstruction must fail closed");
  }
  model.markCommitted();
  bool rejected = false;
  try
  {
    model.reconstruct({{y, half}});
  }
  catch (const std::exception&)
  {
    rejected = true;
  }
  require(rejected, "published models cannot be reconstructed");
}

void runStageFault(StageFault fault)
{
  STPMgr manager;
  const ASTNode x =
      manager.CreateSourceSymbol("fault_x", SourceSort::real());
  const ASTNode formula = manager.CreateRealPredicate(
      EQ, x, manager.CreateRealConst("7/11"));
  std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
  require(solver != nullptr && solver->supportsAssumptions(),
          "configured common backend lacks solve assumptions");

  LraCoordinator coordinator(manager, *solver, formula);
  require(coordinator.ready(), coordinator.failureDetail());
  ArrayTransformer arrays(&manager, nullptr);
  ToSATAIG tosat(&manager, &arrays);
  for (const ASTNode& atom : coordinator.opaqueAtoms())
    tosat.protectSymbol(atom);
  require(tosat.setRequiredSolveAssumption(coordinator.solveActivation()),
          "solve activation setup failed");
  const ASTNode gated = manager.CreateNode(
      IMPLIES, coordinator.solveActivation(), coordinator.booleanFormula());
  require(coordinator.beforeSolverCall(), coordinator.failureDetail());
  require(tosat.CallSAT(*solver, gated, true) &&
              !tosat.hasInternalSolveFailure(),
          "candidate-producing SAT call failed");
  require(coordinator.checkCompleteCandidate(tosat) ==
              CoordinatorCandidateOutcome::ModelStaged &&
              coordinator.hasStagedModel(),
          "exact candidate did not stage a model");

  switch (fault)
  {
    case StageFault::None: break;
    case StageFault::Epoch: coordinator.testCorruptStagedEpoch(); break;
    case StageFault::StageSerial:
      coordinator.testCorruptStagedCandidateSerial();
      break;
    case StageFault::CurrentSerial:
      coordinator.testCorruptCandidateSerial();
      break;
    case StageFault::MissingValue: coordinator.testDropStagedValue(); break;
    case StageFault::DuplicateValue:
      coordinator.testDuplicateStagedValue();
      break;
    case StageFault::ForeignSymbol:
      coordinator.testCorruptStagedSymbol();
      break;
    case StageFault::ForeignRegistryId:
      coordinator.testCorruptStagedRegistryId();
      break;
    case StageFault::InconsistentNumerator:
      coordinator.testCorruptStagedNumerator();
      break;
    case StageFault::InvalidDenominator:
      coordinator.testCorruptStagedDenominator();
      break;
    case StageFault::WrongExactValue:
      coordinator.testReplaceStagedExactValue();
      break;
    case StageFault::OriginalRejects:
    {
      /* The query as it was written, before presolve rewrote it, with no
       * replay definitions at all: the commit has to evaluate it and refuse
       * a model that does not satisfy it. Were it evaluated only when a
       * reconstruction had been selected -- under HiGHS, or an explicit
       * --lra-model-reconstruction=on -- the five default-on presolve stages
       * would be the one part of the answer path no check covers, and a
       * wrong rewrite there would reach the answer unchecked. */
      LraReconstruction reconstruction;
      reconstruction.original = manager.CreateNode(
          AND, ASTVec{formula, manager.CreateRealPredicate(
                                   EQ, x, manager.CreateRealConst("13/17"))});
      require(reconstruction.definitions.empty(), "no replay for this case");
      coordinator.setReconstruction(std::move(reconstruction));
      AbsRefine_CounterExample counterexample(&manager, nullptr, &arrays);
      require(coordinator.verifyAndCommit(counterexample) !=
                  CommitOutcome::Committed,
              "a model the original query rejects must not be published");
      require(!manager.HasRealModel(),
              "a refused commit publishes nothing");
      return;
    }
    case StageFault::ReconstructionValid:
    case StageFault::ReconstructionWrong:
    {
      const auto y =
          manager.CreateSourceSymbol("reconstructed_y", SourceSort::real());
      const auto term = manager.CreateRealTerm(
          REAL_ADD, ASTVec{x, manager.CreateRealConst("1")});
      LraReconstruction reconstruction;
      reconstruction.original = manager.CreateNode(
          AND, ASTVec{formula, manager.CreateRealPredicate(EQ, y, term)});
      reconstruction.definitions.push_back(
          {y, fault == StageFault::ReconstructionValid
                  ? term
                  : manager.CreateRealConst("0")});
      coordinator.setReconstruction(std::move(reconstruction));
      AbsRefine_CounterExample counterexample(&manager, nullptr, &arrays);
      const bool accepted = coordinator.verifyAndCommit(counterexample) ==
                            CommitOutcome::Committed;
      require(accepted == (fault == StageFault::ReconstructionValid),
              "original formula must reject a corrupted reconstruction");
      require(manager.HasRealModel() == accepted,
              "only checked models are published");
      manager.InvalidateRealModel();
      return;
    }
  }

  const bool accepted = coordinator.testValidateStagedModel();
  if (fault == StageFault::None)
  {
    require(accepted && coordinator.ready() && !manager.HasRealModel(),
            "valid private stage did not validate without publication");
  }
  else
  {
    require(!accepted && !coordinator.ready() && !manager.HasRealModel(),
            "corrupt private stage did not fail closed");
  }
}

void arraySerialMismatchFailsClosed()
{
  STPMgr manager;
  const ASTNode x =
      manager.CreateSourceSymbol("array_serial_x", SourceSort::real());
  const ASTNode formula = manager.CreateRealPredicate(
      REAL_GE, x, manager.CreateRealConst("0"));
  std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
  LraCoordinator coordinator(manager, *solver, formula);
  ArrayTransformer arrays(&manager, nullptr);
  ToSATAIG tosat(&manager, &arrays);
  for (const ASTNode& atom : coordinator.opaqueAtoms())
    tosat.protectSymbol(atom);
  require(tosat.setRequiredSolveAssumption(coordinator.solveActivation()),
          "array serial activation setup failed");
  const ASTNode gated = manager.CreateNode(
      IMPLIES, coordinator.solveActivation(), coordinator.booleanFormula());
  require(coordinator.beforeSolverCall() &&
              tosat.CallSAT(*solver, gated, true) &&
              coordinator.checkCompleteCandidate(tosat) ==
                  CoordinatorCandidateOutcome::ModelStaged,
          "array serial fixture did not stage a model");
  coordinator.testCorruptCandidateSerial();
  coordinator.noteArrayOutcome(true);
  require(!coordinator.ready() && !manager.HasRealModel(),
          "array checker accepted a stale candidate serial");
}

void firstSearchIntegration(bool enabled, bool float_driver, bool corrupt_binding,
                            std::unique_ptr<SATSolver> solver = nullptr)
{
  STPMgr manager;
  manager.UserFlags.lra_first_search = enabled;
  manager.UserFlags.lra_float_driver = float_driver;
  manager.UserFlags.lra_early_conflicts = true;
  manager.UserFlags.lra_verify_conflicts = true;
  auto x = manager.CreateSourceSymbol("first_x", SourceSort::real());
  auto y = manager.CreateSourceSymbol("first_y", SourceSort::real());
  auto one = manager.CreateRealConst("1");
  auto sum = manager.CreateRealTerm(REAL_ADD, ASTVec{x, y});
  auto formula = manager.CreateNode(AND, ASTVec{
      manager.CreateRealPredicate(REAL_GE, x, one),
      manager.CreateRealPredicate(REAL_GE, y, one),
      manager.CreateRealPredicate(REAL_LE, sum, one)});
  if (!solver)
    solver.reset(createSATSolver(manager.UserFlags));
  LraCoordinator coordinator(manager, *solver, formula);
  require(coordinator.ready(), coordinator.failureDetail());
  ArrayTransformer arrays(&manager, nullptr);
  ToSATAIG tosat(&manager, &arrays);
  for (auto const& atom : coordinator.opaqueAtoms())
    tosat.protectSymbol(atom);
  require(tosat.setRequiredSolveAssumption(coordinator.solveActivation()),
          "first search activation");
  auto gated = manager.CreateNode(IMPLIES, coordinator.solveActivation(),
                                  coordinator.booleanFormula());
  require(coordinator.beforeSolverCall(), coordinator.failureDetail());
  bool called = false;
  if (enabled)
    tosat.setBeforeSearch([&]() {
      called = true;
      require(coordinator.candidateSerial() == 0, "hook precedes first candidate");
      auto& map = tosat.SATVar_to_SymbolIndexMap();
      require(!map.empty(), "hook follows CNF binding");
      if (corrupt_binding)
        map.at(coordinator.opaqueAtoms().front()).front() = ~0U;
      return coordinator.afterCnf(tosat);
    });
  bool sat = tosat.CallSAT(*solver, gated, true);
  tosat.clearBeforeSearch();
  require(called == enabled, "first search hook called as configured");
  if (corrupt_binding)
  {
    require(!sat && tosat.hasInternalSolveFailure() && !coordinator.ready(),
            "failed first binding is an error, not an UNSAT answer");
    return;
  }
  require(!tosat.hasInternalSolveFailure(), tosat.internalSolveFailureDetail());
  bool driven = enabled && solver->supportsTheoryPropagator();
  require(sat != driven, "theory contradiction is found within the first search");
  require(coordinator.metrics().first_search_connections == (driven ? 1U : 0U),
          "first search connection counted");
  if (driven)
    require(coordinator.solveMetrics().float_checks +
            coordinator.coreStatistics().checks > 0, "arithmetic checked during first search");
}

void persistentCoordinator(bool persistent, bool floating, bool propagation,
                           unsigned extension_mode = 0, unsigned row_order = 0,
                           bool reset_sat = false)
{
  STPMgr manager;
  manager.UserFlags.lra_persistent_state = persistent;
  manager.UserFlags.lra_extension_mode = extension_mode;
  manager.UserFlags.lra_row_order = row_order;
  manager.UserFlags.lra_extension_restart_sat = reset_sat;
  if (reset_sat)
  {
    manager.UserFlags.solver_to_use = UserDefinedFlags::CADICAL_SOLVER;
    manager.UserFlags.cadical_factor = UserDefinedFlags::BVAMode::OFF;
  }
  manager.UserFlags.lra_float_driver = floating;
  manager.UserFlags.lra_theory_propagation = propagation;
  manager.UserFlags.lra_early_conflicts = true;
  manager.UserFlags.lra_soi = true;
  manager.UserFlags.lra_verify_conflicts = true;
  auto x = manager.CreateSourceSymbol("persist_x", SourceSort::real());
  auto y = manager.CreateSourceSymbol("persist_y", SourceSort::real());
  auto z = manager.CreateSourceSymbol("persist_z", SourceSort::real());
  auto base = manager.CreateRealPredicate(REAL_GE, x, manager.CreateRealConst("1"));
  std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
  LraCoordinator coordinator(manager, *solver, base);
  ArrayTransformer arrays(&manager, nullptr);
  ToSATAIG tosat(&manager, &arrays);
  for (auto const& atom : coordinator.opaqueAtoms())
    tosat.protectSymbol(atom);
  auto gated = manager.CreateNode(IMPLIES, coordinator.solveActivation(), coordinator.booleanFormula());
  auto solve = [&](bool first) {
    require(tosat.setRequiredSolveAssumptions(coordinator.liveActivations()), "persistent activations");
    for (unsigned attempt = 0; attempt < 100; ++attempt)
    {
      require(coordinator.beforeSolverCall(), coordinator.failureDetail());
      tosat.setBeforeSearch([&]() { return coordinator.afterCnf(tosat); });
      bool sat = tosat.CallSAT(*solver, first ? gated : manager.ASTTrue, true);
      first = false;
      tosat.clearBeforeSearch();
      require(!tosat.hasInternalSolveFailure(), tosat.internalSolveFailureDetail());
      if (!sat)
        return false;
      auto outcome = coordinator.checkCompleteCandidate(tosat);
      if (outcome == CoordinatorCandidateOutcome::ModelStaged)
      {
        require(coordinator.testValidateStagedModel(), "persistent staged model validates");
        return true;
      }
      require(outcome == CoordinatorCandidateOutcome::ConflictPending &&
              coordinator.encodePendingLraClause(), coordinator.failureDetail());
    }
    throw std::runtime_error("persistent solve did not converge");
  };
  require(solve(true), "persistent base SAT");
  auto epoch = coordinator.solveEpoch();
  auto extra = manager.CreateNode(AND, ASTVec{
      manager.CreateRealPredicate(EQ, y, manager.CreateRealConst("2/3")),
      manager.CreateRealPredicate(REAL_GE,
          manager.CreateRealTerm(REAL_ADD, ASTVec{x, y}), manager.CreateRealConst("2"))});
  require(coordinator.extendWithFormula(extra, tosat) ==
              ExtensionOutcome::Extended, coordinator.failureDetail());
  require(!coordinator.hasStagedModel(), "extension discards old staged model");
  const bool reuse = persistent || extension_mode == 1 || extension_mode == 3;
  require((coordinator.solveEpoch() == epoch) == reuse, "context epoch reuse as configured");
  require(solve(false), "new structural variable after old row SAT");
  auto second = manager.CreateRealPredicate(EQ, z, manager.CreateRealConst("7/3"));
  coordinator.beginExtensionBatch();
  require(coordinator.extendWithFormula(second, tosat) ==
              ExtensionOutcome::Extended, coordinator.failureDetail());
  require(coordinator.endExtensionBatch(), coordinator.failureDetail());
  require(solve(false), "second persistent extension SAT");
  auto activation = manager.CreateSourceSymbol("persist_frame", SourceSort::boolean());
  auto bad = manager.CreateRealPredicate(REAL_LT, x, manager.CreateRealConst("0"));
  require(coordinator.extendFrame(bad, tosat, activation) ==
              ExtensionOutcome::Extended, coordinator.failureDetail());
  require(!solve(false), "pushed contradiction UNSAT");
  epoch = coordinator.solveEpoch();
  require(coordinator.retractFrame(activation), "retract contradictory frame");
  require((coordinator.solveEpoch() == epoch) == reuse, "pop keeps configured context");
  require(solve(false), "pop restores SAT");
  require(coordinator.metrics().core_rebuilds == (reuse ? 1U : 5U),
          "persistent mode constructs one core; baseline rebuilds on changes");
  require(coordinator.metrics().arithmetic_state_resets == (extension_mode == 3 ? 4U : 0U),
          "search reset preserves IDs through append and retraction");
  require(coordinator.metrics().sat_search_resets == (reset_sat ? 2U : 0U),
          "only the two permanent extensions reset SAT search");
  if (persistent)
  {
    require(coordinator.solveMetrics().persistent_extensions == 3, "three arithmetic extensions");
    require(coordinator.solveMetrics().float_extensions == (floating ? 3U : 0U),
            "float tableau extended as configured");
    require(coordinator.coreStatistics().variables == 3, "stable variable registration count");
    // A new exact threshold may stop fitting in the advisory tier. Keep
    // the persistent exact core and finish the query through it.
    auto huge = manager.CreateRealPredicate(REAL_GE, x,
        manager.CreateRealConst("1" + std::string(400, '0')));
    auto stable_epoch = coordinator.solveEpoch();
    require(coordinator.extendWithFormula(huge, tosat) ==
                ExtensionOutcome::Extended, coordinator.failureDetail());
    require(solve(false), "non-finite float extension falls back to exact arithmetic");
    require(coordinator.solveEpoch() == stable_epoch, "float fallback keeps exact context");
  }
}

/* A budget that refuses mid-check is a query this solve could not finish,
 * not a fault of ours -- and the two verdicts differ: one carries a reason a
 * caller can read, the other reaches a C boundary as a raw -100.  The
 * candidate driver used to decide this three times over, once per catch
 * clause, and each copy dropped the limit back to an internal fault whenever
 * the checkpoint pop that follows could not restore the core -- which is
 * exactly what a core stopped by a budget does. */
void budgetRefusalIsNotAnError()
{
  bool saw_limit = false;
  for (unsigned bits : {96U, 128U, 160U, 192U})
  {
    STPMgr manager;
    Frontend frontend(manager);
    frontend.configureNumberLimits(
        NumberLimits{bits, bits, UINT64_C(268435456), UINT64_C(16777216)});
    // Coprime denominators, so the substitutions a pivot performs grow the
    // coefficients until the result limit refuses one.
    static const char* const primes[] = {"3", "5",  "7",  "11",
                                         "13", "17", "19", "23"};
    std::vector<ASTNode> vars;
    for (std::size_t i = 0; i < 6; ++i)
      vars.push_back(manager.CreateSourceSymbol(
          ("budget_v" + std::to_string(i)).c_str(), SourceSort::real()));
    ASTVec conjuncts;
    for (std::size_t i = 0; i < 6; ++i)
    {
      ASTVec terms;
      for (std::size_t j = 0; j < 6; ++j)
        terms.push_back(manager.CreateRealTerm(
            REAL_MUL, ASTVec{manager.CreateRealConst(
                                 std::string(primes[(i + j) % 8]) + "/" +
                                 primes[(i * 3 + j) % 8]),
                             vars[j]}));
      conjuncts.push_back(manager.CreateRealPredicate(
          i % 2 ? REAL_GE : REAL_LE, manager.CreateRealTerm(REAL_ADD, terms),
          manager.CreateRealConst(i % 2 ? "1/29" : "-1/31")));
    }
    const ASTNode formula = manager.CreateNode(AND, conjuncts);
    std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
    LraCoordinator coordinator(manager, *solver, formula);
    if (!coordinator.ready())
      continue;  // refused while building; that path is covered elsewhere
    ArrayTransformer arrays(&manager, nullptr);
    ToSATAIG tosat(&manager, &arrays);
    for (const ASTNode& atom : coordinator.opaqueAtoms())
      tosat.protectSymbol(atom);
    require(tosat.setRequiredSolveAssumption(coordinator.solveActivation()),
            "budget solve activation setup failed");
    const ASTNode gated = manager.CreateNode(
        IMPLIES, coordinator.solveActivation(), coordinator.booleanFormula());
    if (!coordinator.beforeSolverCall())
      continue;
    if (!tosat.CallSAT(*solver, gated, true) ||
        tosat.hasInternalSolveFailure())
      continue;
    const CoordinatorCandidateOutcome outcome =
        coordinator.checkCompleteCandidate(tosat);
    if (outcome != CoordinatorCandidateOutcome::ResourceLimit)
      continue;
    saw_limit = true;
    require(!coordinator.resourceLimitDetail().empty(),
            "a refused budget says which limit refused");
    require(coordinator.failureDetail().empty(),
            "a refused budget is not recorded as a fault of the coordinator");
  }
  require(saw_limit,
          "no arithmetic budget refused a candidate: the classification this "
          "covers was not exercised");
}

/* A refusal from an extension means two different things and the caller has
 * to be able to tell them apart.
 *
 * `Declined` is answered before the coordinator touches itself, so the
 * caller's fallback -- state the lemma over a whole new solve -- still has
 * the registry and the committed model it re-derives from.  A refusal from
 * inside the work has already dropped both, and reporting it as a decline is
 * how a query whose congruence the solver has just refuted came back `sat`:
 * the restart loop re-derives its lemmas from the committed model, found it
 * gone, had nothing to state, and returned the round's own verdict. */
void extensionDeclineIsNotFailure()
{
  STPMgr manager;
  const auto x = manager.CreateSourceSymbol("decline_x", SourceSort::real());
  const auto base =
      manager.CreateRealPredicate(REAL_GE, x, manager.CreateRealConst("1"));
  std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
  LraCoordinator coordinator(manager, *solver, base);
  ArrayTransformer arrays(&manager, nullptr);
  ToSATAIG tosat(&manager, &arrays);
  require(coordinator.ready(), coordinator.failureDetail());

  const auto untouched = [&](const char* what) {
    require(coordinator.ready(), std::string(what) + " keeps the coordinator");
    require(coordinator.failureDetail().empty(),
            std::string(what) + " records no failure");
    require(coordinator.metrics().extensions == 0,
            std::string(what) + " counts no extension");
  };

  // Not a formula at all, and a formula of the wrong sort: answerable without
  // reading anything this coordinator owns.
  require(coordinator.extendWithFormula(ASTNode(), tosat) ==
              ExtensionOutcome::Declined, "a null formula declines");
  untouched("a null formula");
  require(coordinator.extendWithFormula(x, tosat) ==
              ExtensionOutcome::Declined, "a Real-sorted formula declines");
  untouched("a Real-sorted formula");

  // A frame activation that is not a Boolean symbol declines the same way.
  const auto activation =
      manager.CreateSourceSymbol("decline_frame", SourceSort::real());
  require(coordinator.extendFrame(base, tosat, activation) ==
              ExtensionOutcome::Declined, "a Real activation declines");
  untouched("a Real activation");

  // A Boolean formula this manager owns whose leaves the lemma encoder does
  // not cover. Everything before the encoder runs, so this refusal arrives
  // after the registry has grown and the model has been dropped -- which is
  // exactly the class that must not read as a decline.
  const auto a = manager.CreateSymbol("decline_a", 0, 8);
  const auto b = manager.CreateSymbol("decline_b", 0, 8);
  const auto unencodable = manager.CreateNode(BVLT, a, b);
  const ExtensionOutcome failed =
      coordinator.extendWithFormula(unencodable, tosat);
  require(failed == ExtensionOutcome::Failed ||
              failed == ExtensionOutcome::ResourceLimit,
          "an extension that begins and cannot finish is not a decline");
  require(!coordinator.ready(),
          "a failed extension leaves the coordinator unusable");
  require(!coordinator.failureDetail().empty(),
          "a failed extension says what happened");
}

void decisionPolarityState(bool floating)
{
  STPMgr manager;
  Frontend frontend(manager);
  LraAtomRegistry registry(manager);
  auto frame = registry.pushAssertionFrame();
  auto x = manager.CreateSourceSymbol("polarity_x", SourceSort::real());
  auto formula = manager.CreateNode(AND, ASTVec{
      manager.CreateRealPredicate(REAL_GE, x, manager.CreateRealConst("1")),
      manager.CreateRealPredicate(REAL_LT, x, manager.CreateRealConst("0")),
      manager.CreateRealPredicate(REAL_LE, x, manager.CreateRealConst("2"))});
  registry.registerFormula(frontend.preregister(formula), frame);
  auto snapshot = registry.frameSnapshot(frame);
  std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
  LraSolveContext context(registry, *solver, frontend.numberLimits(), frame);
  context.setFloatDriver(floating);
  std::vector<LraSatBinding> bindings;
  SATSolver::Lit lower{}, bad{}, upper{};
  for (auto const& c : snapshot.components)
  {
    auto literal = SATSolver::mkLit(solver->newVar(), false);
    bindings.push_back({c.opaque_atom, literal});
    if (c.relation == FrontendRelation::GreaterEqual)
      lower = literal;
    else if (c.relation == FrontendRelation::Less)
      bad = literal;
    else
      upper = literal;
  }
  require(context.bindOpaqueAtoms(bindings), "polarity bindings");
  LraCandidateAdapter adapter(context, *solver);
  adapter.setDecisionPolarity(true);
  std::vector<uint32_t> observed;
  require(adapter.beginTheoryPropagation(observed), "polarity adapter begins");
  bool value = true;
  require(!adapter.decisionPolarity(SATSolver::var(bad), value) && value,
          "unchecked assignment retains default polarity");
  adapter.notifyAssigned({lower});
  require(!adapter.decisionPolarity(SATSolver::var(bad), value),
          "dirty assignment retains default polarity");
  std::vector<SATSolver::Lit> clause;
  require(!adapter.takeClause(clause) && context.ready(), "root partial check feasible");
  auto before = context.metrics();
  require(adapter.decisionPolarity(SATSolver::var(bad), value) && !value,
          "false polarity reaches the bridge");
  require(adapter.decisionPolarity(SATSolver::var(upper), value) && value,
          "true polarity reaches the bridge");
  require(context.metrics().exact_checks == before.exact_checks &&
          context.metrics().float_checks == before.float_checks,
          "advice requests do not run arithmetic checks");
  require(context.metrics().polarity_advice == 2 &&
          context.metrics().polarity_changes == 2 &&
          (floating ? context.metrics().polarity_float : context.metrics().polarity_exact) == 2,
          "polarity counters report useful advice and its source");
  adapter.notifyNewLevel();
  adapter.notifyAssigned({bad});
  require(!adapter.decisionPolarity(SATSolver::var(upper), value),
          "conflicting state abstains");
  require(adapter.takeClause(clause), "conflict has a real explanation");
  adapter.notifyBacktrack(0);
  require(!adapter.decisionPolarity(SATSolver::var(bad), value),
          "backtracking does not claim an unchecked warm point is feasible");
  adapter.notifyNewLevel();
  adapter.notifyAssigned({upper});
  require(!adapter.takeClause(clause), "post-backtrack check feasible");
  require(adapter.decisionPolarity(SATSolver::var(bad), value) && !value,
          "advice resumes after a feasible check");
  adapter.setDecisionPolarity(false);
  auto queries = context.metrics().polarity_queries;
  require(!adapter.decisionPolarity(SATSolver::var(bad), value) &&
          context.metrics().polarity_queries == queries, "disabled advice is inert");
  adapter.endTheoryPropagation();
}

void decisionPolarityRequirements(SATSolver& solver)
{
  STPMgr manager;
  auto x = manager.CreateSourceSymbol("polarity_requirement_x", SourceSort::real());
  auto formula = manager.CreateRealPredicate(REAL_GE, x, manager.CreateRealConst("0"));
  {
    LraCoordinator coordinator(manager, solver, formula);
    require(coordinator.ready(), "default polarity tolerates unavailable support");
  }
  manager.UserFlags.lra_theory_propagation = false;
  {
    LraCoordinator coordinator(manager, solver, formula);
    require(coordinator.ready(), "default polarity tolerates disabled propagation");
  }
  manager.UserFlags.lra_decision_polarity_explicit = true;
  bool rejected = false;
  try { LraCoordinator coordinator(manager, solver, formula); }
  catch (std::exception const& e)
  {
    rejected = std::string(e.what()).find("--lra-theory-propagation=1") != std::string::npos;
  }
  require(rejected, "polarity without propagation is explicitly rejected");
  if (!solver.supportsDecisionPolarity())
  {
    manager.UserFlags.lra_theory_propagation = true;
    rejected = false;
    try { LraCoordinator coordinator(manager, solver, formula); }
    catch (std::exception const& e)
    {
      rejected = std::string(e.what()).find("cadical-decision-polarity.patch") != std::string::npos;
    }
    require(rejected, "unpatched backend cannot silently ignore requested advice");
  }
  manager.UserFlags.lra_decision_polarity = false;
  LraCoordinator disabled(manager, solver, formula);
  require(disabled.ready(), "explicit opt-out needs no polarity support");
}

} // namespace

int main()
{
  try
  {
    STPMgr manager;
    std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
    decisionPolarityRequirements(*solver);
    reconstructionOrder();
    applicationModelInvariants();
    budgetRefusalIsNotAnError();
    extensionDeclineIsNotFailure();
#if defined(USE_CADICAL)
    searchResetPreservesFormula();
    NoPolarityCadical unsupported;
    decisionPolarityRequirements(unsupported);
    for (bool floating : {false, true})
      firstSearchIntegration(true, floating, false,
                             std::make_unique<NoPolarityCadical>());
#endif
    for (bool floating : {false, true})
    {
      decisionPolarityState(floating);
      for (bool propagation : {false, true})
      {
        persistentCoordinator(false, floating, propagation);
        persistentCoordinator(true, floating, propagation);
        for (unsigned mode : {1U, 2U, 3U})
          for (unsigned order : {0U, 1U, 2U, 3U})
            persistentCoordinator(false, floating, propagation, mode, order);
#if defined(USE_CADICAL)
          for (unsigned mode : {1U, 2U, 3U})
            persistentCoordinator(false, floating, propagation, mode, 0, true);
#endif
      }
      firstSearchIntegration(false, floating, false);
      firstSearchIntegration(true, floating, false);
      firstSearchIntegration(true, floating, true);
    }
    runStageFault(StageFault::None);
    runStageFault(StageFault::Epoch);
    runStageFault(StageFault::StageSerial);
    runStageFault(StageFault::CurrentSerial);
    runStageFault(StageFault::MissingValue);
    runStageFault(StageFault::DuplicateValue);
    runStageFault(StageFault::ForeignSymbol);
    runStageFault(StageFault::ForeignRegistryId);
    runStageFault(StageFault::InconsistentNumerator);
    runStageFault(StageFault::InvalidDenominator);
    runStageFault(StageFault::WrongExactValue);
    runStageFault(StageFault::ReconstructionValid);
    runStageFault(StageFault::ReconstructionWrong);
    runStageFault(StageFault::OriginalRejects);
    arraySerialMismatchFailsClosed();
    std::cout << "PASS coordinator faults and first-search integration\n";
    return 0;
  }
  catch (const std::exception& failure)
  {
    std::cerr << "FAIL " << failure.what() << '\n';
    return 1;
  }
}

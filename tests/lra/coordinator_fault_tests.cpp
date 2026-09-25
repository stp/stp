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
      /* The query as it was written, before presolve rewrote it: the commit
       * has to evaluate it and refuse a model that does not satisfy it.
       * Were it not evaluated, the five default-on presolve stages
       * would be the one part of the answer path no check covers, and a
       * wrong rewrite there would reach the answer unchecked. */
      LraReconstruction reconstruction;
      reconstruction.original = manager.CreateNode(
          AND, ASTVec{formula, manager.CreateRealPredicate(
                                   EQ, x, manager.CreateRealConst("13/17"))});
      coordinator.setReconstruction(std::move(reconstruction));
      AbsRefine_CounterExample counterexample(&manager, nullptr, &arrays);
      require(coordinator.verifyAndCommit(counterexample) !=
                  CommitOutcome::Committed,
              "a model the original query rejects must not be published");
      require(!manager.HasRealModel(),
              "a refused commit publishes nothing");
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
    applicationModelInvariants();
    budgetRefusalIsNotAnError();
    extensionDeclineIsNotFailure();
#if defined(USE_CADICAL)
    searchResetPreservesFormula();
    NoPolarityCadical unsupported;
    decisionPolarityRequirements(unsupported);
#endif
    for (bool floating : {false, true})
    {
      decisionPolarityState(floating);
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
    runStageFault(StageFault::OriginalRejects);
    arraySerialMismatchFailsClosed();
    std::cout << "PASS coordinator faults\n";
    return 0;
  }
  catch (const std::exception& failure)
  {
    std::cerr << "FAIL " << failure.what() << '\n';
    return 1;
  }
}

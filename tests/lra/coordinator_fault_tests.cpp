#include "LraCoordinator.h"

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/ToSat/ToSATAIG.h"

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
};

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

void decisionPolarityState()
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
  require(context.metrics().exact_checks == before.exact_checks,
          "advice requests do not run arithmetic checks");
  require(context.metrics().polarity_advice == 2 &&
          context.metrics().polarity_changes == 2 &&
          context.metrics().polarity_exact == 2,
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
    budgetRefusalIsNotAnError();
#if defined(USE_CADICAL)
    searchResetPreservesFormula();
    NoPolarityCadical unsupported;
    decisionPolarityRequirements(unsupported);
#endif
    decisionPolarityState();
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

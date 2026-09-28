#include "LraAtomRegistry.h"
#include "LraCandidateAdapter.h"

#include "stp/STPManager/STPManager.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/ToSat/ToSATAIG.h"

#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#ifndef STP_BACKEND_LABEL
#define STP_BACKEND_LABEL "configured-common-backend"
#endif

namespace {

using namespace stp;
using namespace stp::lra;

[[noreturn]] void fail(const std::string& message)
{
  throw std::runtime_error(message);
}

void require(bool condition, const std::string& message)
{
  if (!condition)
    fail(message);
}

NumberLimits generousLimits()
{
  return NumberLimits{UINT64_C(65536), UINT64_C(65536),
                      UINT64_C(268435456), UINT64_C(16777216)};
}

std::vector<LraSatBinding> bindingsFromToSat(
    const LraRegistrySnapshot& snapshot, ToSATAIG& to_sat,
    SATSolver& solver)
{
  const ToSATBase::ASTNodeToSATVar& map =
      to_sat.SATVar_to_SymbolIndexMap();
  std::vector<LraSatBinding> result;
  auto append = [&](const ASTNode& atom) {
    const auto found = map.find(atom);
    require(found != map.end() && found->second.size() == 1,
            "ToSAT did not assign one live variable to an opaque atom");
    const unsigned raw = found->second.front();
    require(raw != std::numeric_limits<unsigned>::max(),
            "ToSAT returned its missing-variable sentinel");
    const std::uint32_t variable = static_cast<std::uint32_t>(raw);
    require(solver.validVariable(variable),
            "ToSAT opaque variable is outside the common solver range");
    result.push_back(
        LraSatBinding{atom, SATSolver::mkLit(variable, false)});
  };
  for (const RegistryComponent& component : snapshot.components)
    append(component.opaque_atom);
  for (const RegistryEqualityGroup& equality : snapshot.equalities)
    append(equality.equality_atom);
  return result;
}

struct BackendRun final
{
  std::uint64_t candidates = 0;
  std::uint64_t conflicts = 0;
  std::uint64_t clauses = 0;
  std::uint64_t models = 0;
  std::uint64_t immediate = 0;
  std::uint64_t tableau = 0;
  std::uint64_t pivots = 0;
};

BackendRun runFormula(const std::string& name,
                      bool equality_case,
                      bool tableau_case,
                      bool expect_model)
{
  STPMgr manager;
  Frontend frontend(manager);
  LraAtomRegistry registry(manager);
  const LraAssertionFrameId frame = registry.pushAssertionFrame();
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  ASTNode source;
  if (expect_model)
  {
    source = manager.CreateRealPredicate(
        REAL_GT, x,
        manager.CreateRealConst(
            "100000000000000000000000000000000000000000000000001/7"));
  }
  else if (equality_case)
  {
    source = manager.CreateNode(
        OR,
        manager.CreateRealPredicate(EQ, x, manager.CreateRealConst("0")),
        manager.CreateRealPredicate(REAL_GT, x, manager.CreateRealConst("0")));
  }
  else if (tableau_case)
  {
    const ASTNode twice = manager.CreateRealTerm(
        REAL_MUL, ASTVec{manager.CreateRealConst("2"), x});
    source = manager.CreateNode(
        OR,
        manager.CreateRealPredicate(REAL_LE, x, manager.CreateRealConst("0")),
        manager.CreateRealPredicate(REAL_GE, twice,
                                    manager.CreateRealConst("2")));
  }
  else
  {
    source = manager.CreateNode(
        OR,
        manager.CreateRealPredicate(REAL_LT, x, manager.CreateRealConst("0")),
        manager.CreateRealPredicate(REAL_GE, x, manager.CreateRealConst("0")));
  }

  const RegisteredLraFormula registered =
      registry.registerFormula(frontend.preregister(source), frame);
  require(!Frontend::containsRealSyntax(registered.boolean_formula),
          name + ": Real syntax crossed the pre-SAT barrier");
  const LraRegistrySnapshot snapshot = registry.activeSnapshot();

  std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
  require(solver != nullptr, name + ": common SAT factory returned null");
  ArrayTransformer array_transformer(&manager, nullptr);
  ToSATAIG to_sat(&manager, &array_transformer);
  const bool initial_sat =
      to_sat.CallSAT(*solver, registered.boolean_formula, false);
  require(initial_sat, name + ": Boolean abstraction unexpectedly UNSAT");
  const std::vector<LraSatBinding> bindings =
      bindingsFromToSat(snapshot, to_sat, *solver);

  LraSolveContext context(registry, *solver, generousLimits());
  require(context.ready(),
          name + ": core registration failed: " + context.failureDetail());
  require(context.bindOpaqueAtoms(bindings),
          name + ": ToSAT binding failed: " + context.failureDetail());
  LraCandidateAdapter adapter(context, *solver);

  BackendRun run;
  if (expect_model)
  {
    const AdapterResult checked = adapter.checkCompleteCandidate();
    ++run.candidates;
    require(checked.outcome == AdapterOutcome::ModelStaged,
            name + ": exact model was not privately staged");
    const StagedExactModel* stage = context.stagedModelForTesting();
    require(stage != nullptr && stage->values.size() == 1 &&
                !stage->values.front().numerator_decimal.empty() &&
                !stage->values.front().denominator_decimal.empty(),
            name + ": staged exact value is incomplete");
    run.models = 1;
  }
  else
  {
    // Force one deliberately conflicting but temporary Boolean candidate.
    // Assumptions disappear before addClause, so accepting the verified
    // no-good cannot be confused with discovering a root conflict while the
    // clause is submitted.
    require(solver->supportsAssumptions() && context.beforeSolverCall(),
            name + ": backend lacks the common assumption/re-solve path");
    SATSolver::vec_literals conflicting;
    for (const LraSatBinding& binding : bindings)
      conflicting.push(binding.literal);
    bool timeout = false;
    require(solver->solveWithAssumptions(conflicting, timeout) && !timeout,
            name + ": forced conflicting Boolean candidate was not SAT");
    const AdapterResult checked = adapter.checkCompleteCandidate();
    ++run.candidates;
    require(checked.outcome == AdapterOutcome::ConflictPending,
            name + ": exact conflict was not retained");
    const AdapterResult inserted = adapter.encodeAndInsertPendingClause();
    require(inserted.outcome == AdapterOutcome::ClauseInserted,
            name + ": common addClause rejected a verified no-good");
    require(solver->submittedClauses() > 0 && context.beforeSolverCall(),
            name + ": pending clause lifecycle did not reach Cleared");

    // Re-solve the same backend with a deterministic exact-consistent
    // assignment. For equality, E and its two components stay true while the
    // unrelated conflicting predicate becomes false. Ordinary fixtures keep
    // the first component true and make every later component false.
    SATSolver::vec_literals consistent;
    for (std::size_t i = 0; i < snapshot.components.size(); ++i)
    {
      bool positive = i == 0;
      if (equality_case)
      {
        const RegistryEqualityGroup& equality = snapshot.equalities.front();
        positive = snapshot.components[i].id ==
                       equality.less_equal_component ||
                   snapshot.components[i].id ==
                       equality.greater_equal_component;
      }
      SATSolver::Lit selected = bindings[i].literal;
      selected.x ^= positive ? 0U : 1U;
      consistent.push(selected);
    }
    for (std::size_t i = snapshot.components.size(); i < bindings.size(); ++i)
      consistent.push(bindings[i].literal);
    timeout = false;
    require(solver->solveWithAssumptions(consistent, timeout) && !timeout,
            name + ": same-solver clause re-solve made no progress");
    const AdapterResult refined = adapter.checkCompleteCandidate();
    ++run.candidates;
    require(refined.outcome == AdapterOutcome::ModelStaged &&
                context.stagedModelForTesting() != nullptr,
            name + ": refined same-solver candidate did not stage a model");
    run.conflicts = 1;
    run.clauses = 1;
    run.models = 1;
  }
  const LraSolveMetrics metrics = context.metrics();
  run.immediate = metrics.immediate_conflicts;
  run.tableau = metrics.tableau_conflicts;
  run.pivots = metrics.observer_pivots;
  if (tableau_case)
    require(run.tableau == 1 && run.pivots >= 1,
            name + ": expected tableau conflict did not pivot");
  if (!tableau_case && !expect_model)
    require(run.immediate == 1,
            name + ": expected immediate conflict was not recorded");
  return run;
}

} // namespace

int main()
{
  try
  {
    const BackendRun immediate =
        runFormula("immediate", false, false, false);
    const BackendRun tableau = runFormula("tableau", false, true, false);
    const BackendRun equality = runFormula("equality", true, false, false);
    const BackendRun model = runFormula("model", false, false, true);
    std::cout << "{\"backend\":\""
              << STP_BACKEND_LABEL
              << "\",\"adapter_source\":\"LraCandidateAdapter.cpp\","
                 "\"candidates\":"
              << immediate.candidates + tableau.candidates +
                     equality.candidates + model.candidates
              << ",\"conflicts\":"
              << immediate.conflicts + tableau.conflicts + equality.conflicts
              << ",\"clauses\":"
              << immediate.clauses + tableau.clauses + equality.clauses
              << ",\"models\":" << model.models
              + immediate.models + tableau.models + equality.models
              << ",\"immediate\":"
              << immediate.immediate + equality.immediate
              << ",\"tableau\":" << tableau.tableau
              << ",\"tableau_pivots\":" << tableau.pivots
              << ",\"same_solver_resolve\":true}"
              << std::endl;
    return 0;
  }
  catch (const std::exception& failure)
  {
    std::cerr << "configured backend test failure: " << failure.what()
              << std::endl;
    return 1;
  }
}

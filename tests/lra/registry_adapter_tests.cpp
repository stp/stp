#include "LraAtomRegistry.h"
#include "LraBudgetRefusal.h"
#include "LraSolveContext.h"
#include "LraCandidateAdapter.h"
#include "LraModelIndex.h"
#include "ImathAllocHooks.h"

#include "stp/STPManager/STPManager.h"

#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>
#include <vector>

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

class FakeSolver final : public SATSolver
{
public:
  enum class AddMode
  {
    Normal,
    FailStillOkay,
    FailAndNotOkay,
    AcceptButNotOkay
  };

  bool okay() const override { return okay_; }
  std::uint8_t modelValue(std::uint32_t variable) const override
  {
    if (!validVariable(variable))
      return undef_literal();
    ++read_count_;
    if (changing_model_ && read_count_ == change_on_read_)
      values_[change_variable_] = !values_[change_variable_];
    if (undef_variable_ && *undef_variable_ == variable)
      return undef_literal();
    return values_[variable] ? true_literal() : false_literal();
  }
  std::uint32_t newVar() override
  {
    values_.push_back(false);
    return static_cast<std::uint32_t>(values_.size() - 1U);
  }
  std::uint32_t nVars() const override
  {
    return static_cast<std::uint32_t>(values_.size());
  }
  void printStats() const override {}
  void setVerbosity(int) override {}
  lbool true_literal() const override { return UINT8_C(1); }
  lbool false_literal() const override { return UINT8_C(0); }
  lbool undef_literal() const override { return UINT8_C(2); }

  void set(std::uint32_t variable, bool value)
  {
    require(validVariable(variable), "fake assignment variable out of range");
    values_[variable] = value;
  }
  bool get(std::uint32_t variable) const
  {
    require(validVariable(variable), "fake model lookup out of range");
    return values_[variable];
  }
  void setUndef(std::optional<std::uint32_t> variable)
  {
    undef_variable_ = variable;
  }
  void changeOnRead(std::uint64_t read, std::uint32_t variable)
  {
    changing_model_ = true;
    change_on_read_ = read;
    change_variable_ = variable;
    read_count_ = 0;
  }
  void setAddMode(AddMode mode) { add_mode_ = mode; }
  const std::vector<std::vector<Lit>>& clauses() const { return clauses_; }

protected:
  bool addClauseInternal(const vec_literals& input) override
  {
    std::vector<Lit> clause;
    for (int i = 0; i < input.size(); ++i)
      clause.push_back(input[i]);
    if (add_mode_ == AddMode::FailStillOkay)
      return false;
    if (add_mode_ == AddMode::FailAndNotOkay)
    {
      okay_ = false;
      return false;
    }
    clauses_.push_back(std::move(clause));
    if (add_mode_ == AddMode::AcceptButNotOkay)
    {
      okay_ = false;
      return true;
    }
    if (clauses_.back().empty())
    {
      okay_ = false;
      return false;
    }
    return true;
  }

  bool solveInternal(bool& timeout_expired) override
  {
    timeout_expired = false;
    if (!okay_)
      return false;
    if (values_.size() >= 63)
      fail("fake solver brute-force domain too large");
    const std::uint64_t candidates = UINT64_C(1) << values_.size();
    for (std::uint64_t mask = 0; mask < candidates; ++mask)
    {
      bool all = true;
      for (const std::vector<Lit>& clause : clauses_)
      {
        bool satisfied = false;
        for (Lit literal : clause)
        {
          const bool variable =
              ((mask >> SATSolver::var(literal)) & UINT64_C(1)) != 0;
          satisfied = satisfied ||
                      (SATSolver::sign(literal) ? !variable : variable);
        }
        if (!satisfied)
        {
          all = false;
          break;
        }
      }
      if (!all)
        continue;
      for (std::size_t i = 0; i < values_.size(); ++i)
        values_[i] = ((mask >> i) & UINT64_C(1)) != 0;
      read_count_ = 0;
      return true;
    }
    okay_ = false;
    return false;
  }

private:
  mutable std::vector<bool> values_;
  std::vector<std::vector<Lit>> clauses_;
  bool okay_ = true;
  AddMode add_mode_ = AddMode::Normal;
  mutable std::optional<std::uint32_t> undef_variable_;
  mutable bool changing_model_ = false;
  mutable std::uint64_t read_count_ = 0;
  mutable std::uint64_t change_on_read_ = 0;
  mutable std::uint32_t change_variable_ = 0;
};

struct BindingSet final
{
  std::vector<LraSatBinding> bindings;
  std::map<LraComponentId, std::uint32_t> components;
  std::map<LraEqualityGroupId, std::uint32_t> equalities;
};

BindingSet makeBindings(const LraRegistrySnapshot& snapshot,
                        FakeSolver& solver)
{
  BindingSet result;
  for (const RegistryComponent& component : snapshot.components)
  {
    const std::uint32_t variable = solver.newVar();
    result.bindings.push_back(
        LraSatBinding{component.opaque_atom,
                      SATSolver::mkLit(variable, false)});
    result.components.emplace(component.id, variable);
  }
  for (const RegistryEqualityGroup& equality : snapshot.equalities)
  {
    const std::uint32_t variable = solver.newVar();
    result.bindings.push_back(
        LraSatBinding{equality.equality_atom,
                      SATSolver::mkLit(variable, false)});
    result.equalities.emplace(equality.id, variable);
  }
  return result;
}

void setAll(const BindingSet& bindings, FakeSolver& solver, bool value)
{
  for (const auto& entry : bindings.components)
    solver.set(entry.second, value);
  for (const auto& entry : bindings.equalities)
    solver.set(entry.second, value);
}

const RegistryComponent& componentWithRelation(
    const LraRegistrySnapshot& snapshot, FrontendRelation relation,
    std::size_t occurrence = 0)
{
  for (const RegistryComponent& component : snapshot.components)
  {
    if (component.relation == relation)
    {
      if (occurrence == 0)
        return component;
      --occurrence;
    }
  }
  fail("requested registry relation is absent");
}

RegisteredLraFormula registerNode(Frontend& frontend,
                                  LraAtomRegistry& registry,
                                  LraAssertionFrameId frame,
                                  const ASTNode& node)
{
  return registry.registerFormula(frontend.preregister(node), frame);
}

void registryScopeAndIdentity()
{
  STPMgr manager;
  Frontend frontend(manager);
  LraAtomRegistry registry(manager);
  LraAtomRegistry second_facade(manager);
  require(registry.tag().domain == second_facade.tag().domain,
          "facades over one manager did not share registry ownership");

  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode first = manager.CreateRealPredicate(
      REAL_LE, x, manager.CreateRealConst("1"));
  const ASTNode second = manager.CreateRealPredicate(
      REAL_LE, x, manager.CreateRealConst("2"));
  const LraAssertionFrameId frame1 = registry.pushAssertionFrame();
  const RegisteredLraFormula registered1 = registerNode(
      frontend, registry, frame1,
      manager.CreateNode(AND, ASTVec{first, first, second}));
  const LraRegistrySnapshot snapshot1 = registry.activeSnapshot();
  // Two occurrences, not three: the conjunction names `first` twice, and
  // the frontend gives a shared node one atom, so only two predicates ever
  // reach the registry. What this still pins is the row sharing -- x <= 1
  // and x <= 2 are two components over one row for one symbol -- and that
  // the occurrence list stays in step with what was registered, which is
  // the correspondence the coordinator indexes by position.
  require(snapshot1.symbols.size() == 1 && snapshot1.rows.size() == 1 &&
              snapshot1.components.size() == 2 &&
              registered1.component_occurrences.size() == 2 &&
              registered1.component_occurrences[0] !=
                  registered1.component_occurrences[1],
          "registry row/predicate hash-consing mismatch");
  // One row deduplication: x <= 2 reuses the row x <= 1 created. Component
  // deduplication needs a component to be registered twice, which no longer
  // happens within one formula now that a shared predicate node is walked
  // once -- it is checked below, where `first` is registered again under a
  // second frame.
  require(registry.metrics().row_deduplications >= 1,
          "registry row deduplication metric missing");
  const LraComponentId retained = registered1.component_occurrences.front();

  const LraAssertionFrameId frame2 = registry.pushAssertionFrame();
  const RegisteredLraFormula registered2 =
      registerNode(frontend, registry, frame2, first);
  require(registered2.component_occurrences.front() == retained,
          "shared predicate did not retain its stable registry ID");
  require(registry.metrics().component_deduplications >= 1,
          "registering a known predicate did not deduplicate its component");
  registry.popAssertionFrame(frame1);
  const LraRegistrySnapshot after_first_pop = registry.activeSnapshot();
  require(after_first_pop.components.size() == 1 &&
              after_first_pop.rows.size() == 1 &&
              after_first_pop.symbols.size() == 1,
          "shared entries were removed before their final frame pop");
  require(!registry.validateSnapshot(snapshot1),
          "popped registry generation accepted a stale snapshot");
  registry.popAssertionFrame(frame2);
  const LraRegistrySnapshot empty = registry.activeSnapshot();
  require(empty.components.empty() && empty.rows.empty() &&
              empty.symbols.empty(),
          "unreachable registry entries survived final frame pop");

  const LraAssertionFrameId frame3 = registry.pushAssertionFrame();
  const RegisteredLraFormula registered3 =
      registerNode(frontend, registry, frame3, first);
  require(registered3.component_occurrences.front().serial > retained.serial,
          "popped registry component ID was resurrected");
  const LraComponentId before_reset =
      registered3.component_occurrences.front();
  registry.destructiveReset();
  const LraAssertionFrameId frame4 = registry.pushAssertionFrame();
  const RegisteredLraFormula registered4 =
      registerNode(frontend, registry, frame4, first);
  require(registered4.component_occurrences.front().serial >
              before_reset.serial,
          "destructive reset reused a registry component ID");

  STPMgr peer_manager;
  LraAtomRegistry peer_registry(peer_manager);
  require(peer_registry.tag().domain != registry.tag().domain,
          "independent managers shared a registry ID domain");

  STPMgr exhausted_manager;
  LraAtomRegistry exhausted(exhausted_manager);
  exhausted.testSetNextFrameSerial(
      std::numeric_limits<std::uint64_t>::max());
  bool frame_exhausted = false;
  try
  {
    (void)exhausted.pushAssertionFrame();
  }
  catch (const RegistryFailure& failure)
  {
    frame_exhausted = failure.kind() == RegistryFailureKind::ResourceLimit;
  }
  require(frame_exhausted, "assertion-frame serial wrapped");
  exhausted.testSetNextSolveEpoch(
      std::numeric_limits<std::uint64_t>::max());
  bool epoch_exhausted = false;
  try
  {
    (void)exhausted.allocateSolveEpoch();
  }
  catch (const RegistryFailure& failure)
  {
    epoch_exhausted = failure.kind() == RegistryFailureKind::ResourceLimit;
  }
  require(epoch_exhausted, "solve epoch wrapped");

  // Reintroducing an old frontend symbol after its registry entry was popped
  // gives it a newer registry serial than a still-active peer. Canonical row
  // and core order must nevertheless remain the stable frontend-symbol order.
  STPMgr reordered_manager;
  Frontend reordered_frontend(reordered_manager);
  LraAtomRegistry reordered_registry(reordered_manager);
  const ASTNode reordered_x =
      reordered_manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode reordered_y =
      reordered_manager.CreateSourceSymbol("y", SourceSort::real());
  const LraAssertionFrameId x_frame =
      reordered_registry.pushAssertionFrame();
  (void)registerNode(
      reordered_frontend, reordered_registry, x_frame,
      reordered_manager.CreateRealPredicate(
          REAL_GE, reordered_x, reordered_manager.CreateRealConst("0")));
  const LraAssertionFrameId y_frame =
      reordered_registry.pushAssertionFrame();
  (void)registerNode(
      reordered_frontend, reordered_registry, y_frame,
      reordered_manager.CreateRealPredicate(
          REAL_GE, reordered_y, reordered_manager.CreateRealConst("0")));
  reordered_registry.popAssertionFrame(x_frame);
  const LraAssertionFrameId sum_frame =
      reordered_registry.pushAssertionFrame();
  const ASTNode reordered_sum = reordered_manager.CreateRealTerm(
      REAL_ADD, ASTVec{reordered_x, reordered_y});
  (void)registerNode(
      reordered_frontend, reordered_registry, sum_frame,
      reordered_manager.CreateRealPredicate(
          REAL_GE, reordered_sum, reordered_manager.CreateRealConst("0")));
  const LraRegistrySnapshot reordered_snapshot =
      reordered_registry.activeSnapshot();
  FakeSolver reordered_solver;
  const BindingSet reordered_bindings =
      makeBindings(reordered_snapshot, reordered_solver);
  setAll(reordered_bindings, reordered_solver, true);
  LraSolveContext reordered_context(
      reordered_registry, reordered_solver, generousLimits());
  require(reordered_context.ready() &&
              reordered_context.bindOpaqueAtoms(reordered_bindings.bindings),
          "reintroduced-symbol core mapping did not bind");
  LraCandidateAdapter reordered_adapter(reordered_context, reordered_solver);
  require(reordered_adapter.checkCompleteCandidate().outcome ==
              AdapterOutcome::ModelStaged,
          "reintroduced-symbol row lost canonical frontend/core order");
}

void coreRegistrationAndContexts()
{
  STPMgr manager;
  Frontend frontend(manager);
  LraAtomRegistry registry(manager);
  const LraAssertionFrameId frame = registry.pushAssertionFrame();
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode twice = manager.CreateRealTerm(
      REAL_MUL, ASTVec{manager.CreateRealConst("2"), x});
  const ASTNode p1 = manager.CreateRealPredicate(
      REAL_LE, x, manager.CreateRealConst("1"));
  const ASTNode p2 = manager.CreateRealPredicate(
      REAL_LE, x, manager.CreateRealConst("2"));
  const ASTNode p3 = manager.CreateRealPredicate(
      REAL_GE, twice, manager.CreateRealConst("-3"));
  (void)registerNode(frontend, registry, frame,
                     manager.CreateNode(AND, ASTVec{p1, p1, p2, p3}));
  const LraRegistrySnapshot snapshot = registry.activeSnapshot();
  require(snapshot.symbols.size() == 1 && snapshot.rows.size() == 2 &&
              snapshot.components.size() == 3,
          "core-registration fixture registry totals mismatch");

  FakeSolver solver;
  const BindingSet bindings = makeBindings(snapshot, solver);
  LraSolveContext first(registry, solver, generousLimits());
  require(first.ready(),
          "first solve context registration failed: " +
              first.failureDetail());
  require(first.bindOpaqueAtoms(bindings.bindings),
          "first solve context binding failed: " + first.failureDetail());
  const LraSolveMetrics first_metrics = first.metrics();
  require(first_metrics.variables_registered == 1 &&
              first_metrics.rows_registered == 2 &&
              first_metrics.components_registered == 3 &&
              first_metrics.origins_registered == 6 &&
              first_metrics.initialize_calls == 1 &&
              first.coreStatistics().variables == 1 &&
              first.coreStatistics().rows == 2 &&
              first.coreStatistics().atoms == 3,
          "deterministic frontend/core map totals mismatch");

  FakeSolver peer_solver;
  const BindingSet peer_bindings = makeBindings(snapshot, peer_solver);
  LraSolveContext second(registry, peer_solver, generousLimits());
  require(second.ready() && second.bindOpaqueAtoms(peer_bindings.bindings) &&
              second.solveEpoch() > first.solveEpoch() &&
              second.coreGeneration() != first.coreGeneration(),
          "interleaved solve contexts mixed epoch/core identities");

  LraSolveContext::testSetOriginSerialStartForNextContext(
      std::numeric_limits<std::uint64_t>::max());
  FakeSolver exhausted_solver;
  (void)makeBindings(snapshot, exhausted_solver);
  LraSolveContext exhausted(registry, exhausted_solver, generousLimits());
  require(exhausted.status() == SolveContextStatus::ResourceLimit,
          "solve-local OriginId exhaustion did not fail closed");

  const LraRegistryTag context_tag = first.registryTag();
  (void)registry.pushAssertionFrame();
  require(registry.tag() != context_tag && !first.validateCurrentState() &&
              first.status() == SolveContextStatus::Invalid,
          "registry mutation did not invalidate a stale solve context");
}

void zeroAtomCandidateAndSolverLifetime()
{
  STPMgr manager;
  Frontend frontend(manager);
  LraAtomRegistry registry(manager);
  const LraAssertionFrameId frame = registry.pushAssertionFrame();
  const RegisteredLraFormula constant = registerNode(
      frontend, registry, frame,
      manager.CreateRealPredicate(REAL_LT, manager.CreateRealConst("0"),
                                  manager.CreateRealConst("1")));
  require(constant.boolean_formula == manager.ASTTrue &&
              registry.activeSnapshot().components.empty(),
          "exact constant predicate was not handled without a SAT mapping");

  auto solver = std::make_unique<FakeSolver>();
  {
    // The solver is deliberately created before the solve context.  Leaving
    // this scope proves that every solver reference, pending clause, staged
    // value, and exact core is destroyed before the solver itself.
    LraSolveContext context(registry, *solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms({}),
            "zero-atom context or empty binding failed");
    LraCandidateAdapter adapter(context, *solver);
    const AdapterResult checked = adapter.checkCompleteCandidate();
    const StagedExactModel* stage = context.stagedModelForTesting();
    const LraSolveMetrics metrics = context.metrics();
    require(checked.outcome == AdapterOutcome::ModelStaged &&
                stage != nullptr && stage->values.empty() &&
                metrics.exact_assertions == 0 && metrics.exact_checks == 1 &&
                metrics.exact_pops == 1,
            "zero-atom candidate was not an exact no-op model stage");
  }
  solver.reset();
}

std::uint64_t concurrentManagersAndContexts()
{
  constexpr std::size_t manager_count = 8;
  std::array<std::uint64_t, manager_count> domains{};
  std::array<std::uint64_t, manager_count> epochs{};
  std::atomic<std::uint64_t> failures{0};
  std::vector<std::thread> workers;
  workers.reserve(manager_count);
  for (std::size_t index = 0; index < manager_count; ++index)
  {
    workers.emplace_back([&, index]() {
      try
      {
        STPMgr manager;
        Frontend frontend(manager);
        LraAtomRegistry registry(manager);
        const LraAssertionFrameId frame = registry.pushAssertionFrame();
        const ASTNode x =
            manager.CreateSourceSymbol("thread-x", SourceSort::real());
        (void)registerNode(
            frontend, registry, frame,
            manager.CreateRealPredicate(
                REAL_GT, x,
                manager.CreateRealConst(std::to_string(index + 1U))));
        const LraRegistrySnapshot snapshot = registry.activeSnapshot();
        FakeSolver solver;
        const BindingSet bindings = makeBindings(snapshot, solver);
        setAll(bindings, solver, true);
        LraSolveContext context(registry, solver, generousLimits());
        if (!context.ready() || !context.bindOpaqueAtoms(bindings.bindings))
          throw std::runtime_error("concurrent solve context did not bind");
        LraCandidateAdapter adapter(context, solver);
        if (adapter.checkCompleteCandidate().outcome !=
                AdapterOutcome::ModelStaged ||
            context.stagedModelForTesting() == nullptr)
          throw std::runtime_error("concurrent exact model did not stage");
        domains[index] = registry.tag().domain;
        epochs[index] = context.solveEpoch();
      }
      catch (...)
      {
        failures.fetch_add(1, std::memory_order_relaxed);
      }
    });
  }
  for (std::thread& worker : workers)
    worker.join();

  require(failures.load(std::memory_order_relaxed) == 0,
          "concurrent manager/context fixture failed");
  const std::set<std::uint64_t> unique_domains(domains.begin(), domains.end());
  require(unique_domains.size() == manager_count &&
              unique_domains.find(0) == unique_domains.end() &&
              std::all_of(epochs.begin(), epochs.end(),
                          [](std::uint64_t epoch) { return epoch != 0; }),
          "concurrent managers mixed registry domains or solve epochs");
  return manager_count;
}

std::uint64_t registrationOwnershipFaultGate()
{
  STPMgr manager;
  Frontend frontend(manager);
  LraAtomRegistry registry(manager);
  const LraAssertionFrameId frame = registry.pushAssertionFrame();
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode y = manager.CreateSourceSymbol("y", SourceSort::real());
  const ASTNode scaled = manager.CreateRealTerm(
      REAL_MUL, ASTVec{manager.CreateRealConst("17/19"), x});
  const ASTNode row = manager.CreateRealTerm(REAL_ADD, ASTVec{scaled, y});
  (void)registerNode(
      frontend, registry, frame,
      manager.CreateRealPredicate(
          REAL_LE, row,
          manager.CreateRealConst(
              "-123456789012345678901234567890/97")));
  const LraRegistrySnapshot snapshot = registry.activeSnapshot();
  require(snapshot.symbols.size() == 2 && snapshot.rows.size() == 1 &&
              snapshot.components.size() == 1 &&
              snapshot.components.front().canonical_key.find(
                  "b:-123456789012345678901234567890/97") !=
                  std::string::npos,
          "registration-path fixture changed identity");

  FakeSolver solver;
  const BindingSet bindings = makeBindings(snapshot, solver);
  solver.set(bindings.components.begin()->second, true);

  // A past-end control counts every intercepted native exact-number
  // allocation made while snapshotting, registering, and initializing the
  // fresh solve-local core.
  stp_lra_imath_test_fail_nth(
      std::numeric_limits<std::uint64_t>::max());
  {
    LraSolveContext control(registry, solver, generousLimits());
    require(control.ready() && control.bindOpaqueAtoms(bindings.bindings),
            "no-fault registration control failed");
  }
  const std::uint64_t allocation_points =
      stp_lra_imath_test_allocation_attempts();
  stp_lra_imath_test_disable_failures();
  require(allocation_points > 0,
          "registration ownership gate observed no native allocations");

  for (std::uint64_t index = 0; index < allocation_points; ++index)
  {
    stp_lra_imath_test_fail_nth(index);
    {
      LraSolveContext faulted(registry, solver, generousLimits());
      require(!faulted.ready() &&
                  faulted.stagedModelForTesting() == nullptr &&
                  faulted.pendingClauseForTesting() == nullptr,
              "faulted registration published a usable context");
    }
    require(index < stp_lra_imath_test_allocation_attempts(),
            "registration fault index was not reached");
    stp_lra_imath_test_disable_failures();
    require(registry.validateSnapshot(snapshot),
            "registration fault mutated the manager-owned registry");
  }

  LraSolveContext retry(registry, solver, generousLimits());
  require(retry.ready() && retry.bindOpaqueAtoms(bindings.bindings),
          "clean registration retry failed after ownership fault sweep");
  return allocation_points;
}

void relationPolarities()
{
  const std::vector<Kind> kinds = {REAL_LT, REAL_LE, REAL_GT, REAL_GE};
  for (Kind kind : kinds)
  {
    for (bool polarity : {false, true})
    {
      STPMgr manager;
      Frontend frontend(manager);
      LraAtomRegistry registry(manager);
      const LraAssertionFrameId frame = registry.pushAssertionFrame();
      const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
      (void)registerNode(frontend, registry, frame,
                         manager.CreateRealPredicate(
                             kind, x, manager.CreateRealConst("3/7")));
      const LraRegistrySnapshot snapshot = registry.activeSnapshot();
      FakeSolver solver;
      const BindingSet bindings = makeBindings(snapshot, solver);
      solver.set(bindings.components.begin()->second, polarity);
      LraSolveContext context(registry, solver, generousLimits());
      require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
              "relation fixture binding failed");
      LraCandidateAdapter adapter(context, solver);
      const AdapterResult checked = adapter.checkCompleteCandidate();
      require(checked.outcome == AdapterOutcome::ModelStaged &&
                  context.stagedModelForTesting() != nullptr &&
                  context.stagedModelForTesting()->values.size() == 1,
              "ordinary relation/polarity did not stage an exact model");
    }
  }
}

void immediateClausesAndProgress()
{
  STPMgr manager;
  Frontend frontend(manager);
  LraAtomRegistry registry(manager);
  const LraAssertionFrameId frame = registry.pushAssertionFrame();
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode less = manager.CreateRealPredicate(
      REAL_LT, x, manager.CreateRealConst("0"));
  const ASTNode greater_equal = manager.CreateRealPredicate(
      REAL_GE, x, manager.CreateRealConst("0"));
  (void)registerNode(frontend, registry, frame,
                     manager.CreateNode(AND, less, greater_equal));
  const LraRegistrySnapshot snapshot = registry.activeSnapshot();
  FakeSolver solver;
  const BindingSet bindings = makeBindings(snapshot, solver);
  setAll(bindings, solver, true);
  LraSolveContext context(registry, solver, generousLimits());
  require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
          "immediate-conflict binding failed");
  const CoreGeneration generation = context.coreGeneration();
  LraCandidateAdapter adapter(context, solver);

  std::uint64_t conflicts = 0;
  for (;;)
  {
    const AdapterResult checked = adapter.checkCompleteCandidate();
    if (checked.outcome == AdapterOutcome::ModelStaged)
      break;
    require(checked.outcome == AdapterOutcome::ConflictPending &&
                context.pendingClauseState() ==
                    PendingClauseState::CandidateConflict,
            "bad Boolean candidate did not retain a verified conflict");
    const AdapterResult inserted = adapter.encodeAndInsertPendingClause();
    require(inserted.outcome == AdapterOutcome::ClauseInserted &&
                context.pendingClauseState() == PendingClauseState::ClauseEncoded,
            "verified no-good was not inserted into the same solver");
    ++conflicts;
    require(context.beforeSolverCall(),
            "pending clause was not cleared before outer re-solve");
    bool timeout = false;
    require(solver.solve(timeout) && !timeout,
            "outer fake SAT re-solve failed to make progress");
    require(conflicts < 4, "refinement failed to reach a consistent candidate");
  }
  require(conflicts == 2 && solver.submittedClauses() == 2 &&
              context.coreGeneration() == generation &&
              context.stagedModelForTesting() != nullptr,
          "multiple-bad-candidate/same-core refinement totals mismatch");
  const LraSolveMetrics metrics = context.metrics();
  require(metrics.immediate_conflicts == 2 && metrics.clauses_inserted == 2 &&
              metrics.models_staged == 1 && metrics.exact_pops == 3,
          "immediate conflict/refinement metrics mismatch");
}

void tableauClause()
{
  STPMgr manager;
  Frontend frontend(manager);
  LraAtomRegistry registry(manager);
  const LraAssertionFrameId frame = registry.pushAssertionFrame();
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  const ASTNode twice = manager.CreateRealTerm(
      REAL_MUL, ASTVec{manager.CreateRealConst("2"), x});
  const ASTNode upper = manager.CreateRealPredicate(
      REAL_LE, x, manager.CreateRealConst("0"));
  const ASTNode lower = manager.CreateRealPredicate(
      REAL_GE, twice, manager.CreateRealConst("2"));
  (void)registerNode(frontend, registry, frame,
                     manager.CreateNode(AND, upper, lower));
  const LraRegistrySnapshot snapshot = registry.activeSnapshot();
  FakeSolver solver;
  const BindingSet bindings = makeBindings(snapshot, solver);
  setAll(bindings, solver, true);
  LraSolveContext context(registry, solver, generousLimits());
  require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
          "tableau fixture binding failed");
  LraCandidateAdapter adapter(context, solver);
  require(adapter.checkCompleteCandidate().outcome ==
              AdapterOutcome::ConflictPending &&
              context.metrics().tableau_conflicts == 1 &&
              context.metrics().observer_pivots >= 1,
          "tableau conflict did not pass the verified path");
  require(adapter.encodeAndInsertPendingClause().outcome ==
              AdapterOutcome::ClauseInserted,
          "tableau no-good insertion failed");
}

void equalityMapping()
{
  {
    STPMgr manager;
    Frontend frontend(manager);
    LraAtomRegistry registry(manager);
    const LraAssertionFrameId frame = registry.pushAssertionFrame();
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    const ASTNode equality = manager.CreateRealPredicate(
        EQ, x, manager.CreateRealConst("0"));
    const ASTNode greater = manager.CreateRealPredicate(
        REAL_GT, x, manager.CreateRealConst("0"));
    (void)registerNode(frontend, registry, frame,
                       manager.CreateNode(AND, equality, greater));
    const LraRegistrySnapshot snapshot = registry.activeSnapshot();
    require(snapshot.equalities.size() == 1,
            "positive equality registry group missing");
    FakeSolver solver;
    const BindingSet bindings = makeBindings(snapshot, solver);
    setAll(bindings, solver, true);
    LraSolveContext context(registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "positive equality binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ConflictPending,
            "positive equality conflict missing");
    const std::uint32_t equality_variable =
        bindings.equalities.begin()->second;
    const std::uint32_t less_variable = bindings.components.at(
        componentWithRelation(snapshot, FrontendRelation::LessEqual).id);
    require(adapter.encodeAndInsertPendingClause().outcome ==
                AdapterOutcome::ClauseInserted,
            "positive equality clause encoding failed");
    const std::vector<SATSolver::Lit>& clause = solver.clauses().back();
    bool has_negated_equality = false;
    bool has_less_component = false;
    for (SATSolver::Lit literal : clause)
    {
      has_negated_equality = has_negated_equality ||
                             (SATSolver::var(literal) == equality_variable &&
                              SATSolver::sign(literal));
      has_less_component = has_less_component ||
                           SATSolver::var(literal) == less_variable;
    }
    require(has_negated_equality && !has_less_component,
            "positive equality support was not compressed to source E");
  }

  {
    STPMgr manager;
    Frontend frontend(manager);
    LraAtomRegistry registry(manager);
    const LraAssertionFrameId frame = registry.pushAssertionFrame();
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    const ASTNode equality = manager.CreateRealPredicate(
        EQ, x, manager.CreateRealConst("0"));
    const ASTNode nonnegative = manager.CreateRealPredicate(
        REAL_GE, x, manager.CreateRealConst("1"));
    (void)registerNode(frontend, registry, frame,
                       manager.CreateNode(AND, equality, nonnegative));
    const LraRegistrySnapshot snapshot = registry.activeSnapshot();
    const RegistryEqualityGroup& group = snapshot.equalities.front();
    FakeSolver solver;
    const BindingSet bindings = makeBindings(snapshot, solver);
    for (const auto& entry : bindings.components)
      solver.set(entry.second, true);
    solver.set(bindings.equalities.at(group.id), false);
    solver.set(bindings.components.at(group.less_equal_component), true);
    solver.set(bindings.components.at(group.greater_equal_component), false);
    LraSolveContext context(registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "false equality branch binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ConflictPending,
            "false equality branch conflict missing");
    require(adapter.encodeAndInsertPendingClause().outcome ==
                AdapterOutcome::ClauseInserted,
            "false equality branch clause encoding failed");
    const std::uint32_t branch_variable =
        bindings.components.at(group.greater_equal_component);
    const std::uint32_t equality_variable = bindings.equalities.at(group.id);
    bool has_branch = false;
    bool has_equality = false;
    for (SATSolver::Lit literal : solver.clauses().back())
    {
      has_branch = has_branch || SATSolver::var(literal) == branch_variable;
      has_equality = has_equality ||
                     SATSolver::var(literal) == equality_variable;
    }
    require(has_branch && !has_equality,
            "false equality branch was unsafely collapsed to not-E");
  }
}

void exactModelCases()
{
  {
    STPMgr manager;
    Frontend frontend(manager);
    LraAtomRegistry registry(manager);
    const LraAssertionFrameId frame = registry.pushAssertionFrame();
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    const std::string huge =
        "100000000000000000000000000000000000000000000000001/7";
    (void)registerNode(frontend, registry, frame,
                       manager.CreateRealPredicate(
                           REAL_GT, x, manager.CreateRealConst(huge)));
    const LraRegistrySnapshot snapshot = registry.activeSnapshot();
    FakeSolver solver;
    const BindingSet bindings = makeBindings(snapshot, solver);
    setAll(bindings, solver, true);
    LraSolveContext context(registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "huge exact model binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ModelStaged,
            "huge strict model was not staged");
    const StagedExactModel* stage = context.stagedModelForTesting();
    require(stage != nullptr && stage->values.size() == 1 &&
                !stage->values.front().numerator_decimal.empty() &&
                stage->values.front().denominator_decimal != "0",
            "huge staged exact numerator/denominator missing");
  }

  {
    STPMgr manager;
    Frontend frontend(manager);
    LraAtomRegistry registry(manager);
    const LraAssertionFrameId frame = registry.pushAssertionFrame();
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    const ASTNode y = manager.CreateSourceSymbol("y", SourceSort::real());
    const ASTNode sum = manager.CreateRealTerm(REAL_ADD, ASTVec{x, y});
    (void)registerNode(frontend, registry, frame,
                       manager.CreateRealPredicate(
                           EQ, sum, manager.CreateRealConst("0")));
    const LraRegistrySnapshot snapshot = registry.activeSnapshot();
    require(snapshot.rows.size() == 1 && snapshot.symbols.size() == 2,
            "alias/free model fixture did not intern its equality row");
    FakeSolver solver;
    const BindingSet bindings = makeBindings(snapshot, solver);
    setAll(bindings, solver, true);
    LraSolveContext context(registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "alias/free model binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ModelStaged,
            "alias/free exact model was not staged");
    const StagedExactModel* stage = context.stagedModelForTesting();
    require(stage != nullptr && stage->values.size() == 2 &&
                stage->values[0].frontend_symbol <
                    stage->values[1].frontend_symbol,
            "staged model coverage/order is incomplete");
    require(context.beforeSolverCall() &&
                context.stagedModelForTesting() == nullptr,
            "solver-call boundary did not invalidate staged model");
    setAll(bindings, solver, true);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ModelStaged &&
                !context.notifyContextMutation() &&
                context.status() == SolveContextStatus::Invalid &&
                context.stagedModelForTesting() == nullptr,
            "public context mutation did not discard a staged model");
  }
}

void modelLookupIdentitiesAndBudget()
{
  NumberBudget budget(generousLimits());
  NumberOperationScope scope(budget);
  const CoreGeneration generation{UINT64_C(0x0000000100000001)};
  const CoreGeneration foreign{UINT64_C(0x0000000200000001)};
  // Sparse, permuted identifiers: neither ordinal nor vector position is an
  // identity, and building the lookup must not reorder the model itself.
  std::vector<ModelValue> values{
      {VariableId(generation, 42), ExactRational(std::int64_t{3})},
      {VariableId(generation, 2), ExactRational(std::int64_t{7})},
      {VariableId(generation, 19), ExactRational(std::int64_t{11})}};
  const LraModelIndex index(values, &ModelValue::variable, generousLimits(),
                            "test model variable");
  require(&index.at(VariableId(generation, 2)) == &values[1] &&
              &index.at(VariableId(generation, 42)) == &values[0] &&
              values[0].variable.ordinal() == 42,
          "model index changed the model order or selected the wrong value");
  const auto expect = [](SolveContextFailureKind kind, auto operation) {
    bool rejected = false;
    try { operation(); }
    catch (const SolveContextFailure& failure) { rejected = failure.kind() == kind; }
    require(rejected, "model index did not reject an invalid identity or allocation");
  };
  expect(SolveContextFailureKind::Invalid, [&] {
    (void)index.at(VariableId(generation, 3));
  });
  expect(SolveContextFailureKind::Invalid, [&] {
    (void)index.at(VariableId(foreign, 2));
  });
  auto duplicated = values;
  duplicated.push_back(duplicated.front());
  expect(SolveContextFailureKind::Invalid, [&] {
    (void)LraModelIndex(duplicated, &ModelValue::variable, generousLimits(),
                        "duplicate model variable");
  });
  NumberLimits tiny = generousLimits();
  tiny.maximum_allocation_bytes = sizeof(ModelValue const*) * values.size() - 1;
  expect(SolveContextFailureKind::ResourceLimit, [&] {
    (void)LraModelIndex(values, &ModelValue::variable, tiny, "limited model");
  });

  // Registry identities use domain/serial instead of generation/ordinal.
  std::vector<RegistrySymbol> symbols(2);
  symbols[0].id = LraRegistrySymbolId{7, 19};
  symbols[1].id = LraRegistrySymbolId{7, 2};
  const LraModelIndex registry_index(symbols, &RegistrySymbol::id,
                                     generousLimits(), "test registry symbol");
  require(&registry_index.at(LraRegistrySymbolId{7, 2}) == &symbols[1],
          "registry index selected the wrong sparse identity");
  expect(SolveContextFailureKind::Invalid, [&] {
    (void)registry_index.at(LraRegistrySymbolId{8, 2});
  });
  symbols[0].id = symbols[1].id;
  expect(SolveContextFailureKind::Invalid, [&] {
    (void)LraModelIndex(symbols, &RegistrySymbol::id, generousLimits(),
                        "duplicate registry symbol");
  });
}

struct SinglePredicateFixture final
{
  STPMgr manager;
  Frontend frontend;
  LraAtomRegistry registry;
  LraAssertionFrameId frame;
  LraRegistrySnapshot snapshot;

  SinglePredicateFixture()
      : frontend(manager), registry(manager), frame(registry.pushAssertionFrame())
  {
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    (void)registerNode(frontend, registry, frame,
                       manager.CreateRealPredicate(
                           REAL_GT, x, manager.CreateRealConst("0")));
    snapshot = registry.activeSnapshot();
  }
};

void satBindingAndCandidateFailures()
{
  {
    SinglePredicateFixture fixture;
    FakeSolver solver;
    const BindingSet bindings = makeBindings(fixture.snapshot, solver);
    LraSolveContext context(fixture.registry, solver, generousLimits());
    require(!context.bindOpaqueAtoms({}) &&
                context.status() == SolveContextStatus::Invalid,
            "missing SAT mapping was accepted");
  }
  {
    // An atom the Boolean formula never mentions has no SAT variable, and
    // the caller says so. Coverage still has to add up: declaring the
    // omission is accepted, declaring one that was never registered or one
    // that is also bound is not.
    SinglePredicateFixture fixture;
    FakeSolver solver;
    LraSolveContext context(fixture.registry, solver, generousLimits());
    const ASTNode dropped = fixture.snapshot.components.front().opaque_atom;
    require(context.bindOpaqueAtoms({}, {dropped}) &&
                context.status() != SolveContextStatus::Invalid,
            "a declared omission was refused");
  }
  {
    SinglePredicateFixture fixture;
    FakeSolver solver;
    const BindingSet bindings = makeBindings(fixture.snapshot, solver);
    LraSolveContext context(fixture.registry, solver, generousLimits());
    const ASTNode dropped = fixture.snapshot.components.front().opaque_atom;
    require(!context.bindOpaqueAtoms(bindings.bindings, {dropped}) &&
                context.status() == SolveContextStatus::Invalid,
            "an atom both bound and omitted was accepted");
    (void)bindings;
  }
  {
    STPMgr manager;
    Frontend frontend(manager);
    LraAtomRegistry registry(manager);
    const LraAssertionFrameId frame = registry.pushAssertionFrame();
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    (void)registerNode(
        frontend, registry, frame,
        manager.CreateNode(
            AND,
            manager.CreateRealPredicate(REAL_LT, x, manager.CreateRealConst("0")),
            manager.CreateRealPredicate(REAL_GT, x, manager.CreateRealConst("1"))));
    const LraRegistrySnapshot snapshot = registry.activeSnapshot();
    FakeSolver solver;
    const std::uint32_t shared = solver.newVar();
    std::vector<LraSatBinding> aliases;
    for (const RegistryComponent& component : snapshot.components)
      aliases.push_back(
          LraSatBinding{component.opaque_atom,
                        SATSolver::mkLit(shared, false)});
    LraSolveContext context(registry, solver, generousLimits());
    require(!context.bindOpaqueAtoms(aliases),
            "unexpected SAT-variable alias was accepted");
  }
  {
    SinglePredicateFixture fixture;
    FakeSolver solver;
    BindingSet bindings = makeBindings(fixture.snapshot, solver);
    bindings.bindings.front().literal.x ^= 1U;
    LraSolveContext context(fixture.registry, solver, generousLimits());
    require(!context.bindOpaqueAtoms(bindings.bindings),
            "wrong-sign opaque binding was accepted");
  }
  {
    SinglePredicateFixture fixture;
    FakeSolver solver;
    BindingSet bindings = makeBindings(fixture.snapshot, solver);
    bindings.bindings.front().literal =
        SATSolver::mkLit(solver.nVars() + 1U, false);
    LraSolveContext context(fixture.registry, solver, generousLimits());
    require(!context.bindOpaqueAtoms(bindings.bindings),
            "out-of-range opaque binding was accepted");
  }
  {
    SinglePredicateFixture fixture;
    FakeSolver solver;
    const BindingSet bindings = makeBindings(fixture.snapshot, solver);
    LraSolveContext context(fixture.registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "wrong-solver fixture binding failed");
    FakeSolver other_solver;
    (void)other_solver.newVar();
    LraCandidateAdapter wrong_solver_adapter(context, other_solver);
    (void)wrong_solver_adapter;
    require(context.status() == SolveContextStatus::Invalid,
            "adapter accepted a foreign SAT solver instance");
  }
  {
    SinglePredicateFixture fixture;
    FakeSolver solver;
    const BindingSet bindings = makeBindings(fixture.snapshot, solver);
    solver.setUndef(bindings.components.begin()->second);
    LraSolveContext context(fixture.registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "undef fixture binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::InternalNoResult &&
                context.stagedModelForTesting() == nullptr &&
                context.pendingClauseForTesting() == nullptr,
            "undef candidate published semantic state");
  }
  {
    SinglePredicateFixture fixture;
    FakeSolver solver;
    const BindingSet bindings = makeBindings(fixture.snapshot, solver);
    solver.set(bindings.components.begin()->second, true);
    solver.changeOnRead(2, bindings.components.begin()->second);
    LraSolveContext context(fixture.registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "changing-model fixture binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::InternalNoResult,
            "changing SAT model was accepted as one snapshot");
  }
  {
    SinglePredicateFixture fixture;
    FakeSolver solver;
    const BindingSet bindings = makeBindings(fixture.snapshot, solver);
    solver.set(bindings.components.begin()->second, true);
    LraSolveContext context(fixture.registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "candidate exhaustion fixture binding failed");
    context.testSetNextCandidateSerial(
        std::numeric_limits<std::uint64_t>::max());
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ResourceLimit &&
                context.stagedModelForTesting() == nullptr,
            "candidate serial exhaustion did not fail without publication");
  }
}

void propagatedModelOwnership()
{
  {
    STPMgr manager;
    Frontend frontend(manager);
    LraAtomRegistry registry(manager);
    const auto frame = registry.pushAssertionFrame();
    const auto x = manager.CreateSourceSymbol("retained_x", SourceSort::real());
    (void)registerNode(frontend, registry, frame, manager.CreateRealPredicate(
        EQ, x, manager.CreateRealConst("10000000001/30000000000")));
    const auto snapshot = registry.activeSnapshot();
    FakeSolver solver;
    const auto bindings = makeBindings(snapshot, solver);
    setAll(bindings, solver, true);
    LraSolveContext context(registry, solver, generousLimits());
    require(context.bindOpaqueAtoms(bindings.bindings), "retained model bindings");
    LraCandidateAdapter adapter(context, solver);
    std::vector<uint32_t> observed;
    require(adapter.beginTheoryPropagation(observed), "retained model setup");
    adapter.notifyNewLevel();
    std::vector<SATSolver::Lit> literals;
    for (const auto& binding : bindings.components)
      literals.push_back(SATSolver::mkLit(binding.second, false));
    adapter.notifyAssigned(literals);
    require(adapter.checkFoundModel() && !adapter.failed(),
            "retained model was not certified");
    const auto core_before = context.coreStatistics();
    const auto before = context.metrics();
    // CryptoMiniSat unwinds here before returning SAT. The empty notification
    // is also harmless: it conveys no new search activity.
    adapter.notifyBacktrack(0);
    adapter.notifyAssigned({});
    const auto accepted = adapter.acceptPropagatedModel();
    require(accepted.outcome == AdapterOutcome::ModelStaged &&
                accepted.candidate_serial != 0 &&
                context.stagedModelForTesting()->values.front().numerator_decimal == "10000000001" &&
                context.stagedModelForTesting()->values.front().denominator_decimal == "30000000000",
            "backend cleanup lost the certified exact witness");
    const auto core_after = context.coreStatistics();
    const auto after = context.metrics();
    require(core_after.checks == core_before.checks &&
                core_after.model_verifications == core_before.model_verifications &&
                core_after.model_repairs == core_before.model_repairs &&
                core_after.models_produced == core_before.models_produced &&
                after.candidates_started == before.candidates_started &&
                after.models_staged == before.models_staged + 1,
            "publication solved or certified the accepted model again");
    // A subsequent solve gets its own witness and candidate identity.
    require(context.beforeSolverCall(), "retained model next search");
    adapter.notifyNewLevel();
    adapter.notifyAssigned(literals);
    require(adapter.checkFoundModel() && !adapter.failed(), "next model certification");
    adapter.notifyBacktrack(0);
    const auto next = adapter.acceptPropagatedModel();
    require(next.outcome == AdapterOutcome::ModelStaged &&
                next.candidate_serial > accepted.candidate_serial,
            "next search reused an earlier candidate identity");
    require(adapter.acceptPropagatedModel().outcome == AdapterOutcome::InternalNoResult &&
                context.stagedModelForTesting() == nullptr,
            "publication reused a consumed witness");
    adapter.endTheoryPropagation();
  }

  enum class Change { NewSearch, NewLevel, Assignment, FinalSelection, Disconnect, Mutation };
    for (const auto change : {Change::NewSearch, Change::NewLevel,
                              Change::Assignment, Change::FinalSelection,
                              Change::Disconnect, Change::Mutation})
    {
      SinglePredicateFixture fixture;
      FakeSolver solver;
      const auto bindings = makeBindings(fixture.snapshot, solver);
      const auto variable = bindings.components.begin()->second;
      solver.set(variable, true);
      LraSolveContext context(fixture.registry, solver, generousLimits());
      require(context.bindOpaqueAtoms(bindings.bindings), "stale witness bindings");
      LraCandidateAdapter adapter(context, solver);
      std::vector<uint32_t> observed;
      require(adapter.beginTheoryPropagation(observed), "stale witness setup");
      adapter.notifyNewLevel();
      adapter.notifyAssigned({SATSolver::mkLit(variable, false)});
      require(adapter.checkFoundModel() && !adapter.failed(), "stale witness certification");
      adapter.notifyBacktrack(0);
      switch (change)
      {
        case Change::NewSearch:
          require(context.beforeSolverCall(), "stale witness next search");
          break;
        case Change::NewLevel:
          adapter.notifyNewLevel();
          break;
        case Change::Assignment:
          solver.set(variable, false);
          adapter.notifyAssigned({SATSolver::mkLit(variable, true)});
          break;
        case Change::FinalSelection:
          // No callback: publication must independently compare the saved
          // arithmetic witness with the model actually returned by SAT.
          solver.set(variable, false);
          break;
        case Change::Disconnect:
          adapter.endTheoryPropagation();
          require(adapter.beginTheoryPropagation(observed), "stale witness reconnect");
          break;
        case Change::Mutation:
          (void)context.notifyContextMutation();
          break;
      }
      require(adapter.acceptPropagatedModel().outcome == AdapterOutcome::InternalNoResult &&
                  context.stagedModelForTesting() == nullptr,
              "changed search or final selection reused a stale witness");
      adapter.endTheoryPropagation();
    }
}

void interruptionAndResource()
{
  // A backend can accept checkFoundModel's stop response before its own
  // deadline poll. No model may be recovered from the incomplete trail.
    for (bool skip_assignment : {false, true})
    {
      SinglePredicateFixture fixture;
      FakeSolver solver;
      const BindingSet bindings = makeBindings(fixture.snapshot, solver);
      const auto variable = bindings.components.begin()->second;
      solver.set(variable, true);
      LraSolveContext context(fixture.registry, solver, generousLimits());
      require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
              "propagation deadline fixture binding failed");
      LraCandidateAdapter adapter(context, solver);
      std::vector<uint32_t> observed;
      require(adapter.beginTheoryPropagation(observed),
              "propagation deadline fixture setup failed");
      if (skip_assignment)
        solver.setMaxTime(0);
      adapter.notifyAssigned({SATSolver::mkLit(variable, false)});
      if (!skip_assignment)
      {
        require(adapter.checkFoundModel(), "control candidate was rejected");
        solver.setMaxTime(0);
      }
      require(adapter.checkFoundModel(), "deadline did not end the search");
      if (skip_assignment)
        solver.setMaxTime(60); // the skipped assignment still poisons acceptance
      const auto result = adapter.acceptPropagatedModel();
      require(result.outcome == AdapterOutcome::Interrupted &&
                  context.ready() &&
                  context.pendingClauseForTesting() == nullptr &&
                  context.stagedModelForTesting() == nullptr,
              "expired propagated candidate was published or called a fault");
      adapter.endTheoryPropagation();
    }
  {
    SinglePredicateFixture fixture;
    FakeSolver solver;
    const BindingSet bindings = makeBindings(fixture.snapshot, solver);
    solver.set(bindings.components.begin()->second, true);
    std::atomic<bool> interrupted{true};
    LraSolveContext context(fixture.registry, solver, generousLimits(),
                            std::numeric_limits<std::uint64_t>::max(),
                            &interrupted);
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "interruption fixture binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::Interrupted &&
                context.pendingClauseForTesting() == nullptr &&
                context.stagedModelForTesting() == nullptr,
            "interrupted candidate published semantic state");
    interrupted.store(false, std::memory_order_relaxed);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ModelStaged,
            "safe retry after interruption failed on the same core");
  }
  {
    SinglePredicateFixture fixture;
    FakeSolver solver;
    const BindingSet bindings = makeBindings(fixture.snapshot, solver);
    solver.set(bindings.components.begin()->second, true);
    LraSolveContext context(fixture.registry, solver, generousLimits(), 0);
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "pivot resource fixture binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ResourceLimit &&
                context.pendingClauseForTesting() == nullptr &&
                context.stagedModelForTesting() == nullptr,
            "pivot resource stop published semantic state");
  }
}

using Corruptor = void (*)(LraSolveContext&);

void corruptEpoch(LraSolveContext& context) { context.testCorruptPendingEpoch(); }
void corruptCandidate(LraSolveContext& context)
{
  context.testCorruptPendingCandidate();
}
void corruptOrigin(LraSolveContext& context)
{
  context.testCorruptPendingOrigin();
}
void corruptVariable(LraSolveContext& context)
{
  context.testCorruptPendingLiteralVariable();
}
void corruptSign(LraSolveContext& context)
{
  context.testCorruptPendingLiteralSign();
}
void corruptComplement(LraSolveContext& context)
{
  context.testAddComplementaryPendingSupport();
}
void corruptEmpty(LraSolveContext& context)
{
  context.testClearPendingSupport();
}

void runPendingCorruption(Corruptor corruptor)
{
  STPMgr manager;
  Frontend frontend(manager);
  LraAtomRegistry registry(manager);
  const LraAssertionFrameId frame = registry.pushAssertionFrame();
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  (void)registerNode(
      frontend, registry, frame,
      manager.CreateNode(
          AND,
          manager.CreateRealPredicate(REAL_LT, x, manager.CreateRealConst("0")),
          manager.CreateRealPredicate(REAL_GE, x, manager.CreateRealConst("0"))));
  const LraRegistrySnapshot snapshot = registry.activeSnapshot();
  FakeSolver solver;
  const BindingSet bindings = makeBindings(snapshot, solver);
  setAll(bindings, solver, true);
  LraSolveContext context(registry, solver, generousLimits());
  require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
          "corruption fixture binding failed");
  LraCandidateAdapter adapter(context, solver);
  require(adapter.checkCompleteCandidate().outcome ==
              AdapterOutcome::ConflictPending,
          "corruption fixture did not produce pending conflict");
  corruptor(context);
  require(adapter.encodeAndInsertPendingClause().outcome ==
              AdapterOutcome::InternalNoResult &&
              solver.submittedClauses() == 0,
          "corrupt pending conflict reached SAT");
}

void corruptionAndClauseFailures()
{
  for (Corruptor corruptor : {corruptEpoch, corruptCandidate, corruptOrigin,
                              corruptVariable, corruptSign, corruptComplement,
                              corruptEmpty})
    runPendingCorruption(corruptor);

  // An exact duplicate support record is harmless and is deduplicated only at
  // the signed-literal boundary.
  {
    STPMgr manager;
    Frontend frontend(manager);
    LraAtomRegistry registry(manager);
    const LraAssertionFrameId frame = registry.pushAssertionFrame();
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    (void)registerNode(
        frontend, registry, frame,
        manager.CreateNode(
            AND,
            manager.CreateRealPredicate(REAL_LT, x, manager.CreateRealConst("0")),
            manager.CreateRealPredicate(REAL_GE, x, manager.CreateRealConst("0"))));
    const LraRegistrySnapshot snapshot = registry.activeSnapshot();
    FakeSolver solver;
    const BindingSet bindings = makeBindings(snapshot, solver);
    setAll(bindings, solver, true);
    LraSolveContext context(registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "duplicate-support fixture binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ConflictPending,
            "duplicate-support fixture conflict missing");
    context.testDuplicatePendingSupport();
    require(adapter.encodeAndInsertPendingClause().outcome ==
                AdapterOutcome::ClauseInserted,
            "exact duplicate signed support was not deduplicated");
  }

  for (FakeSolver::AddMode mode : {FakeSolver::AddMode::FailStillOkay,
                                   FakeSolver::AddMode::FailAndNotOkay,
                                   FakeSolver::AddMode::AcceptButNotOkay})
  {
    STPMgr manager;
    Frontend frontend(manager);
    LraAtomRegistry registry(manager);
    const LraAssertionFrameId frame = registry.pushAssertionFrame();
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    (void)registerNode(
        frontend, registry, frame,
        manager.CreateNode(
            AND,
            manager.CreateRealPredicate(REAL_LT, x, manager.CreateRealConst("0")),
            manager.CreateRealPredicate(REAL_GE, x, manager.CreateRealConst("0"))));
    const LraRegistrySnapshot snapshot = registry.activeSnapshot();
    FakeSolver solver;
    const BindingSet bindings = makeBindings(snapshot, solver);
    setAll(bindings, solver, true);
    solver.setAddMode(mode);
    LraSolveContext context(registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "addClause fault fixture binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ConflictPending &&
                adapter.encodeAndInsertPendingClause().outcome ==
                    AdapterOutcome::InternalNoResult &&
                context.stagedModelForTesting() == nullptr,
            "addClause anomaly did not fail closed");
  }

  {
    STPMgr manager;
    Frontend frontend(manager);
    LraAtomRegistry registry(manager);
    const LraAssertionFrameId frame = registry.pushAssertionFrame();
    const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
    (void)registerNode(
        frontend, registry, frame,
        manager.CreateNode(
            AND,
            manager.CreateRealPredicate(REAL_LT, x,
                                        manager.CreateRealConst("0")),
            manager.CreateRealPredicate(REAL_GE, x,
                                        manager.CreateRealConst("0"))));
    const LraRegistrySnapshot snapshot = registry.activeSnapshot();
    FakeSolver solver;
    const BindingSet bindings = makeBindings(snapshot, solver);
    setAll(bindings, solver, true);
    LraSolveContext context(registry, solver, generousLimits());
    require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
            "pending nested-solve fixture binding failed");
    LraCandidateAdapter adapter(context, solver);
    require(adapter.checkCompleteCandidate().outcome ==
                AdapterOutcome::ConflictPending &&
                !context.beforeSolverCall() &&
                context.status() == SolveContextStatus::Invalid &&
                context.pendingClauseForTesting() == nullptr,
            "nested solver call was accepted while a clause was pending");
  }
}

void equalitySnapshotRejection()
{
  STPMgr manager;
  Frontend frontend(manager);
  LraAtomRegistry registry(manager);
  const LraAssertionFrameId frame = registry.pushAssertionFrame();
  const ASTNode x = manager.CreateSourceSymbol("x", SourceSort::real());
  (void)registerNode(frontend, registry, frame,
                     manager.CreateRealPredicate(
                         EQ, x, manager.CreateRealConst("0")));
  const LraRegistrySnapshot snapshot = registry.activeSnapshot();
  const RegistryEqualityGroup& equality = snapshot.equalities.front();
  FakeSolver solver;
  const BindingSet bindings = makeBindings(snapshot, solver);
  solver.set(bindings.components.at(equality.less_equal_component), true);
  solver.set(bindings.components.at(equality.greater_equal_component), true);
  solver.set(bindings.equalities.at(equality.id), false);
  LraSolveContext context(registry, solver, generousLimits());
  require(context.ready() && context.bindOpaqueAtoms(bindings.bindings),
          "equality snapshot-rejection binding failed");
  LraCandidateAdapter adapter(context, solver);
  require(adapter.checkCompleteCandidate().outcome ==
              AdapterOutcome::InternalNoResult &&
              context.pendingClauseForTesting() == nullptr &&
              context.stagedModelForTesting() == nullptr,
          "inconsistent equality definition reached the exact core");
}

} // namespace

// Every layer that does exact arithmetic while building the LRA problem
// refuses in its own currency, and the top of the solver and the C interface
// each decided for themselves which currencies counted.  They disagreed:
// STP.cpp knew all four, c_interface.cpp knew NumberFailure and
// FrontendFailure only, so a RegistryFailure or SolveContextFailure carrying
// ResourceLimit was a budget refusal at one layer and a fatal error -- an
// aborted host process -- one layer down.  One predicate now answers for all
// of them, and this pins that it recognises each, and that it does not
// mistake a wrong state for a budget.
void budgetRefusalIsRecognisedFromEveryLayer()
{
  using stp::lra::gaveUpOnABudget;

  require(gaveUpOnABudget(stp::lra::NumberFailure(
              stp::lra::NumberFailureKind::ResourceLimit, "n")),
          "NumberFailure ResourceLimit is a budget refusal");
  require(gaveUpOnABudget(stp::lra::FrontendFailure(
              stp::lra::FrontendFailureKind::ResourceLimit, "f")),
          "FrontendFailure ResourceLimit is a budget refusal");
  require(gaveUpOnABudget(stp::lra::RegistryFailure(
              stp::lra::RegistryFailureKind::ResourceLimit, "r")),
          "RegistryFailure ResourceLimit is a budget refusal");
  require(gaveUpOnABudget(stp::lra::SolveContextFailure(
              stp::lra::SolveContextFailureKind::ResourceLimit, "s")),
          "SolveContextFailure ResourceLimit is a budget refusal");

  require(!gaveUpOnABudget(stp::lra::RegistryFailure(
              stp::lra::RegistryFailureKind::Invalid, "r")),
          "a wrong registry state is not a budget refusal");
  require(!gaveUpOnABudget(stp::lra::SolveContextFailure(
              stp::lra::SolveContextFailureKind::Invalid, "s")),
          "a wrong context state is not a budget refusal");
  require(!gaveUpOnABudget(std::runtime_error("unrelated")),
          "an untyped failure is not a budget refusal");
}

int main()
{
  try
  {
    registryScopeAndIdentity();
    coreRegistrationAndContexts();
    zeroAtomCandidateAndSolverLifetime();
    const std::uint64_t concurrent_managers = concurrentManagersAndContexts();
    const std::uint64_t registration_fault_points =
        registrationOwnershipFaultGate();
    relationPolarities();
    immediateClausesAndProgress();
    budgetRefusalIsRecognisedFromEveryLayer();
    tableauClause();
    equalityMapping();
    exactModelCases();
    modelLookupIdentitiesAndBudget();
    satBindingAndCandidateFailures();
    propagatedModelOwnership();
    interruptionAndResource();
    corruptionAndClauseFailures();
    equalitySnapshotRejection();
    std::cout
        << "{\"suite\":\"registry-adapter\","
           "\"registry\":true,\"core_mapping\":true,"
           "\"candidate\":true,\"clauses\":true,"
           "\"model_stage\":true,\"faults\":true,"
           "\"zero_atom\":true,\"concurrent_managers\":"
        << concurrent_managers << ",\"registration_fault_points\":"
        << registration_fault_points << "}"
        << std::endl;
    return 0;
  }
  catch (const std::exception& failure)
  {
    std::cerr << "registry/adapter test failure: " << failure.what()
              << std::endl;
    return 1;
  }
}

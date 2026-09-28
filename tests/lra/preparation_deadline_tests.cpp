#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/PreparationControl.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/ToSat/ToSATAIG.h"
#include "Lra/LraFrontend.h"
#include "Lra/LraAtomRegistry.h"
#include "Lra/LraSolveContext.h"

#include <iostream>
#include <limits>
#include <memory>
#include <numeric>
#include <sstream>
#include <stdexcept>

namespace
{
using namespace stp;

void require(bool condition, const char* detail)
{
  if (!condition)
    throw std::runtime_error(detail);
}

std::uint64_t timing_ticks = 0;
QueryTiming::Clock::time_point timingNow()
{
  return QueryTiming::Clock::time_point(std::chrono::nanoseconds(timing_ticks));
}

void queryTiming()
{
  timing_ticks = 0;
  QueryTiming timing(timingNow(), timingNow);
  QueryTiming* slot = nullptr;
  std::ostringstream output;
  {
    QueryTimingReport report(slot, &timing, output);
    timing_ticks = 2;
    try
    {
      QueryPhaseScope outer(slot, QueryPhase::EncodingOther);
      struct Owner
      {
        ~Owner() { timing_ticks += 5; }
      } owner;
      QueryCleanupOnExit cleanup(slot, QueryPhase::EncodingCleanup);
      timing_ticks += 3;
      QueryPhaseScope inner(slot, QueryPhase::ClauseLoading);
      timing_ticks += 7;
      throw std::runtime_error("unwind the measured owners");
    }
    catch (const std::runtime_error&) {}
    timing_ticks += 11;
    const auto totals = timing.totals();
    require(totals[static_cast<unsigned>(QueryPhase::Other)] == 13 &&
                totals[static_cast<unsigned>(QueryPhase::EncodingOther)] == 3 &&
                totals[static_cast<unsigned>(QueryPhase::ClauseLoading)] == 7 &&
                totals[static_cast<unsigned>(QueryPhase::EncodingCleanup)] == 5 &&
                std::accumulate(totals.begin(), totals.end(), std::uint64_t{0}) == 28,
            "nested query timers double-counted work or missed unwinding");
    {
      QueryTimingReport disabled(slot, nullptr, output);
      require(slot == nullptr, "disabled query timing retained an outer clock");
    }
    require(slot == &timing, "nested timing report did not restore its owner");
  }
  require(slot == nullptr && output.str().find("Query phases: total_ns=28 ") == 0,
          "query timing report lost its total or escaped its query");
}

struct StopAfter
{
  PreparationStage stage;
  unsigned limit;
  unsigned calls = 0;
  STPMgr* lowering_manager = nullptr;
  std::uint64_t lowered_before = 0;
  static bool observe(void* opaque, PreparationStage stage)
  {
    auto& self = *static_cast<StopAfter*>(opaque);
    if (stage != self.stage)
      return false;
    ++self.calls;
    if (self.lowering_manager)
      return self.lowering_manager->UserFlags.coverage.uf_applications_lowered >=
             self.lowered_before + 16;
    return self.calls >= self.limit;
  }
};

void control()
{
  const PreparationControl expired(PreparationControl::Clock::time_point::min());
  bool stopped = false;
  try { expired.check(PreparationStage::Boundary); }
  catch (const PreparationInterrupted&) { stopped = true; }
  require(stopped, "expired preparation deadline did not stop");
  const PreparationControl unlimited;
  unlimited.check(PreparationStage::Boundary);

  StopAfter stop{PreparationStage::LraRegistry, 3};
  const PreparationControl observed(PreparationControl::Clock::time_point::max(),
                                    nullptr, StopAfter::observe, &stop);
  PreparationPoller poll(&observed, stop.stage);
  unsigned work = 0;
  stopped = false;
  try { for (; work != 1024; ++work) poll(); }
  catch (const PreparationInterrupted&) { stopped = true; }
  require(stopped && work == 511 && stop.calls == 3,
          "preparation polling missed its bounded work interval");
  stop.calls = 0;
  stopped = false;
  try { observed.check(PreparationStage::Boundary); }
  catch (const PreparationInterrupted&) { stopped = true; }
  require(stopped && stop.calls == 0, "preparation stop was not latched");

  const PreparationControl* slot = nullptr;
  {
    PreparationScope outer(slot, unlimited);
    {
      PreparationScope inner(slot, observed);
      require(slot == &observed, "nested preparation scope was not installed");
    }
    require(slot == &unlimited, "nested preparation scope was not restored");
  }
  require(slot == nullptr, "preparation scope escaped its query");
}

ASTNode manyRows(STPMgr& manager)
{
  ASTVec rows;
  for (unsigned i = 0; i != 1024; ++i)
  {
    const auto symbol = manager.CreateSourceSymbol(
        ("row_" + std::to_string(i)).c_str(), SourceSort::real());
    rows.push_back(manager.CreateRealPredicate(
        REAL_GE, symbol, manager.CreateRealConst(std::to_string(i))));
  }
  return manager.CreateNode(AND, rows);
}

void transactionRecovery()
{
  using namespace stp::lra;
  STPMgr manager;
  const ASTNode formula = manyRows(manager);
  Frontend frontend(manager);
  const auto generation = frontend.registryGeneration();
  StopAfter frontend_stop{PreparationStage::LraPreregistration, 3};
  const PreparationControl frontend_control(PreparationControl::Clock::time_point::max(),
                                            nullptr, StopAfter::observe, &frontend_stop);
  bool stopped = false;
  {
    PreparationScope scope(manager.preparation_control, frontend_control);
    try { (void)frontend.preregister(formula); }
    catch (const PreparationInterrupted&) { stopped = true; }
  }
  require(stopped && frontend.registryGeneration() == generation,
          "interrupted frontend registration did not roll back");
  const auto preregistered = frontend.preregister(formula);
  require(preregistered.predicates.size() == 1024,
          "frontend retry lost predicates after cancellation");
  LraAtomRegistry registry(manager);
  const auto frame = registry.pushAssertionFrame();
  const auto tag = registry.tag();
  StopAfter registry_stop{PreparationStage::LraRegistry, 3};
  const PreparationControl registry_control(PreparationControl::Clock::time_point::max(),
                                            nullptr, StopAfter::observe, &registry_stop);
  stopped = false;
  {
    PreparationScope scope(manager.preparation_control, registry_control);
    try { (void)registry.registerFormula(preregistered, frame); }
    catch (const PreparationInterrupted&) { stopped = true; }
  }
  const auto empty = registry.frameSnapshot(frame);
  require(stopped && registry.tag() == tag && empty.symbols.empty() &&
              empty.rows.empty() && empty.components.empty(),
          "interrupted atom registration retained partial ownership");
  (void)registry.registerFormula(preregistered, frame);
  const auto complete = registry.frameSnapshot(frame);
  require(complete.symbols.size() == 1024 && complete.rows.size() == 1024 &&
              complete.components.size() == 1024,
          "registry retry lost or duplicated rows after cancellation");

  std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
  StopAfter counter{PreparationStage::LraCore, std::numeric_limits<unsigned>::max()};
  const PreparationControl counting(PreparationControl::Clock::time_point::max(),
                                    nullptr, StopAfter::observe, &counter);
  {
    PreparationScope scope(manager.preparation_control, counting);
    LraSolveContext core(registry, *solver, frontend.numberLimits(), frame);
    require(core.ready(), "uncancelled core construction failed");
  }
  require(counter.calls > 10, "core construction did not poll inside its loops");
  for (unsigned point = 1; point <= counter.calls; ++point)
  {
    StopAfter stop{PreparationStage::LraCore, point};
    const PreparationControl control(PreparationControl::Clock::time_point::max(),
                                     nullptr, StopAfter::observe, &stop);
    PreparationScope scope(manager.preparation_control, control);
    LraSolveContext core(registry, *solver, frontend.numberLimits(), frame);
    require(!core.ready() && core.status() == SolveContextStatus::Interrupted,
            "interrupted core construction became an internal error");
    stopped = false;
    try { core.rethrowPreparationInterruption(); }
    catch (const PreparationInterrupted&) { stopped = true; }
    require(stopped && registry.validateFrameSnapshot(complete, frame),
            "interrupted core lost the timeout or damaged its registry");
  }
  {
    LraSolveContext core(registry, *solver, frontend.numberLimits(), frame);
    require(core.ready(), "fresh core did not recover after cancellation sweep");
  }
  registry.popAssertionFrame(frame);
  std::cout << "core preparation cancellation points=" << counter.calls << '\n';
}

void queryRecovery(PreparationStage stage, unsigned stop_after = 1)
{
  STPMgr manager;
  STP engine(&manager);
  struct RestoreGlobal
  {
    STP* saved = GlobalSTP;
    ~RestoreGlobal() { GlobalSTP = saved; }
  } restore_global;
  GlobalSTP = &engine;
  manager.UserFlags.enable_uninterpreted_functions = true;
  const auto x = manager.CreateSourceSymbol("deadline_x", SourceSort::real());
  auto assertion = manager.CreateRealPredicate(
      EQ, x, manager.CreateRealConst("1"));
  if (stop_after > 1)
  {
    ASTVec terms{assertion, manyRows(manager)};
    auto* context = manager.getUFContext();
    std::string diagnostic;
    const auto real = SourceSort::real();
    const auto* function = context->declareFunction("deadline_f", {real}, real,
                                                     &diagnostic);
    require(function != nullptr, "could not declare UF cancellation control");
    for (unsigned i = 0; i != 512; ++i)
    {
      const auto value = manager.CreateRealConst(std::to_string(i));
      const auto application = context->apply(function, {value}, &diagnostic);
      terms.push_back(manager.CreateRealPredicate(EQ, application, value));
    }
    assertion = manager.CreateNode(AND, terms);
  }
  require(engine.TopLevelSTP(assertion, manager.ASTFalse) == SOLVER_SATISFIABLE
              && manager.HasRealModel(), "control query did not build a model");
  engine.ClearAllTables();
  manager.ClearAllTables();
  const bool ack = manager.UserFlags.ackermannisation;
  const bool abstraction = manager.UserFlags.bv_term_abstraction;
  const bool optimize = manager.UserFlags.optimize_flag;
  StopAfter stop{stage, stop_after};
  if (stage == PreparationStage::UFLowering && stop_after > 1)
  {
    // Interrupt after the rewrite has minted actual result symbols, rather
    // than only during its read-only narrowing analysis.
    stop.lowering_manager = &manager;
    stop.lowered_before = manager.UserFlags.coverage.uf_applications_lowered;
  }
  const PreparationControl observed(PreparationControl::Clock::time_point::max(),
                                    nullptr, StopAfter::observe, &stop);
  {
    PreparationScope scope(manager.preparation_control, observed);
    require(engine.TopLevelSTP(assertion, manager.ASTFalse) == SOLVER_UNKNOWN,
            "preparation cancellation was not unknown");
    require(manager.getUnknownReason() == UnknownReason::Timeout &&
                manager.soft_timeout_expired && !manager.HasRealModel(),
            "preparation cancellation lost its reason or retained a model");
    require(manager.preparation_control == &observed,
            "public query did not restore its outer preparation observer");
  }
  if (stop.lowering_manager)
    require(manager.UserFlags.coverage.uf_applications_lowered >= stop.lowered_before + 16 &&
                manager.UserFlags.coverage.uf_applications_lowered < stop.lowered_before + 512,
            "UF cancellation did not interrupt a partially populated lowering view");
  else
    require(stop.calls == stop_after, "requested preparation stage was not reached");
  const auto active = lra::LraAtomRegistry(manager).metrics();
  require(active.active_frames == 0 && active.active_rows == 0 &&
              active.active_components == 0,
          "cancelled public query retained an active preparation frame");
  // The CLI's quick-statistics printer rejects an unbalanced timer stack.
  // Cancellation must leave diagnostics usable as well as the next solve.
  manager.GetRunTimes()->print();
  require(manager.UserFlags.ackermannisation == ack &&
              manager.UserFlags.bv_term_abstraction == abstraction &&
              manager.UserFlags.optimize_flag == optimize,
          "cancelled preparation retained query-local flags");
  require(engine.TopLevelSTP(assertion, manager.ASTFalse) == SOLVER_SATISFIABLE &&
              manager.HasRealModel() && manager.GetRealModelValue(x) == "1" &&
              manager.getUnknownReason() == UnknownReason::None,
          "fresh query did not recover after preparation cancellation");
  require(manager.preparation_control == nullptr,
          "fresh query retained a borrowed preparation control");
}

ASTNode encodingFormula(STPMgr& manager)
{
  ASTVec clauses;
  for (unsigned i = 0; i != 1024; ++i)
  {
    const auto a = manager.CreateSourceSymbol(
        ("encoding_a_" + std::to_string(i)).c_str(), SourceSort::boolean());
    const auto b = manager.CreateSourceSymbol(
        ("encoding_b_" + std::to_string(i)).c_str(), SourceSort::boolean());
    clauses.push_back(manager.CreateNode(OR, a, b));
  }
  return manager.CreateNode(AND, clauses);
}

void partialEncoding(UserDefinedFlags::CNFEffort effort, PreparationStage stage)
{
  STPMgr manager;
  STP engine(&manager);
  manager.UserFlags.cnf_effort = effort;
  const auto formula = encodingFormula(manager);
  struct StopPartway
  {
    PreparationStage stage;
    ToSATAIG& encoder;
    SATSolver& solver;
    unsigned calls = 0;
    static bool observe(void* opaque, PreparationStage stage)
    {
      auto& self = *static_cast<StopPartway*>(opaque);
      if (stage != self.stage)
        return false;
      ++self.calls;
      if (stage == PreparationStage::CNFConversion)
        return self.encoder.SATVar_to_SymbolIndexMap().size() >= 16;
      return self.solver.submittedClauses() >= 16;
    }
  };
  {
    std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
    ToSATAIG encoder(&manager, engine.arrayTransformer);
    StopPartway stop{stage, encoder, *solver};
    const PreparationControl control(PreparationControl::Clock::time_point::max(),
                                      nullptr, StopPartway::observe, &stop);
    bool interrupted = false;
    {
      PreparationScope scope(manager.preparation_control, control);
      try { (void)encoder.CallSAT(*solver, formula, false); }
      catch (const PreparationInterrupted& error)
      {
        interrupted = error.stage == stage;
      }
    }
    require(interrupted && stop.calls > 1, "encoding did not stop after partial work");
    if (stage == PreparationStage::CNFConversion)
      require(encoder.SATVar_to_SymbolIndexMap().size() >= 16 &&
                  encoder.SATVar_to_SymbolIndexMap().size() < 2048,
              "CNF cancellation did not interrupt a partial symbol projection");
    else
      require(solver->submittedClauses() >= 16 && solver->submittedClauses() < 1024,
              "clause cancellation did not interrupt partial insertion");
    manager.GetRunTimes()->print();
  }
  manager.ClearAllTables();
  std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
  ToSATAIG fresh(&manager, engine.arrayTransformer);
  require(fresh.CallSAT(*solver, formula, false),
          "fresh encoding did not recover after partial cancellation");
}

void constantBitOwnership()
{
  STPMgr manager;
  STP engine(&manager);
  const auto formula = encodingFormula(manager);
  manager.UserFlags.optimize_flag = false;
  manager.UserFlags.enable_unconstrained = false;
  manager.UserFlags.enable_pure_literals = false;
  manager.UserFlags.bitConstantProp_flag = true;
  StopAfter stop{PreparationStage::CNFConversion, 1};
  const PreparationControl control(PreparationControl::Clock::time_point::max(),
                                    nullptr, StopAfter::observe, &stop);
  {
    PreparationScope scope(manager.preparation_control, control);
    require(engine.TopLevelSTP(formula, manager.ASTFalse) == SOLVER_UNKNOWN &&
                manager.getUnknownReason() == UnknownReason::Timeout,
            "cancellation after consuming constant-bit data lost its timeout");
  }
  require(stop.calls == 1 && manager.UserFlags.bitConstantProp_flag,
          "constant-bit ownership control did not reach CNF conversion");
  manager.GetRunTimes()->print();
  require(engine.TopLevelSTP(formula, manager.ASTFalse) == SOLVER_SATISFIABLE,
          "fresh query failed after constant-bit ownership handoff");
}

void congruenceRecovery(PreparationStage target = PreparationStage::LraRegistry)
{
  STPMgr manager;
  STP engine(&manager);
  manager.UserFlags.enable_uninterpreted_functions = true;
  manager.UserFlags.uf_propagate_equalities = UserDefinedFlags::OptionMode::OFF;
  manager.UserFlags.uf_eager_mode = UserDefinedFlags::UFEagerMode::OFF;
  manager.UserFlags.lra_float_driver = false;
  const auto real = SourceSort::real();
  const auto a = manager.CreateSourceSymbol("congruence_a", real);
  const auto b = manager.CreateSourceSymbol("congruence_b", real);
  auto* uf = manager.getUFContext();
  std::string diagnostic;
  const auto* f = uf->declareFunction("congruence_f", {real}, real, &diagnostic);
  require(f != nullptr, "could not declare congruence control");
  const auto fa = uf->apply(f, {a}, &diagnostic);
  const auto fb = uf->apply(f, {b}, &diagnostic);
  const auto formula = manager.CreateNode(AND, ASTVec{
      manager.CreateRealPredicate(EQ, a, b),
      manager.CreateRealPredicate(EQ, fa, manager.CreateRealConst("0")),
      manager.CreateRealPredicate(EQ, fb, manager.CreateRealConst("1"))});
  struct StopDuringRefinement
  {
    PreparationStage target;
    bool encoded = false;
    unsigned registrations = 0;
    static bool observe(void* opaque, PreparationStage stage)
    {
      auto& self = *static_cast<StopDuringRefinement*>(opaque);
      if (stage == PreparationStage::Encoding)
        self.encoded = true;
      return self.encoded && stage == self.target &&
             ++self.registrations == 2;
    }
  } stop{target};
  const PreparationControl observed(PreparationControl::Clock::time_point::max(),
                                    nullptr, StopDuringRefinement::observe, &stop);
  {
    PreparationScope scope(manager.preparation_control, observed);
    require(engine.TopLevelSTP(formula, manager.ASTFalse) == SOLVER_UNKNOWN &&
                manager.getUnknownReason() == UnknownReason::Timeout &&
                !manager.HasRealModel() && stop.registrations == 2,
            "interrupted congruence preparation lost its timeout outcome");
  }
  require(engine.TopLevelSTP(formula, manager.ASTFalse) == SOLVER_UNSATISFIABLE,
          "congruence query did not recover after interrupted registration");
}

// The candidate pass proves its equalities with sub-solves that go through
// the same encoder, so a cancellation can land inside one. The pass's timer
// and the manager state it sets aside for the sub-solve are both restored.
void congruenceCandidateRecovery(PreparationStage stage)
{
  STPMgr manager;
  STP engine(&manager);
  manager.UserFlags.enable_congruence_candidates = true;
  const auto bv8 = SourceSort::bitVector(8);
  const auto x = manager.CreateSourceSymbol("candidate_x", bv8);
  const auto y = manager.CreateSourceSymbol("candidate_y", bv8);
  const auto z = manager.CreateSourceSymbol("candidate_z", bv8);
  const auto c = manager.CreateSourceSymbol("candidate_c", bv8);
  // x*y and x*z share the slot beside c, so x*y = x*z is a candidate.
  const auto formula = manager.CreateNode(
      AND,
      manager.CreateNode(
          EQ,
          manager.CreateTerm(BVPLUS, 8, manager.CreateTerm(BVMULT, 8, x, y), c),
          manager.CreateBVConst(8, 1)),
      manager.CreateNode(
          EQ,
          manager.CreateTerm(BVPLUS, 8, manager.CreateTerm(BVMULT, 8, x, z), c),
          manager.CreateBVConst(8, 2)));
  // A candidate's sub-solve runs with the manager's query set aside, which
  // is what places the stop inside one rather than in the main encoding.
  struct StopInCandidate
  {
    STPMgr& manager;
    PreparationStage stage;
    bool stopped = false;
    static bool observe(void* opaque, PreparationStage stage)
    {
      auto& self = *static_cast<StopInCandidate*>(opaque);
      if (stage != self.stage ||
          self.manager.GetQuery() != self.manager.ASTUndefined)
        return false;
      self.stopped = true;
      return true;
    }
  } stop{manager, stage};
  const PreparationControl control(PreparationControl::Clock::time_point::max(),
                                    nullptr, StopInCandidate::observe, &stop);
  manager.SetQuery(manager.ASTFalse);
  {
    PreparationScope scope(manager.preparation_control, control);
    require(engine.TopLevelSTP(formula, manager.ASTFalse) == SOLVER_UNKNOWN &&
                manager.getUnknownReason() == UnknownReason::Timeout,
            "cancelled candidate sub-solve lost its timeout outcome");
  }
  require(stop.stopped, "no candidate sub-solve reached the stage");
  require(manager.GetQuery() == manager.ASTFalse,
          "cancelled candidate sub-solve did not restore the query");
  manager.GetRunTimes()->print();
  require(engine.TopLevelSTP(formula, manager.ASTFalse) == SOLVER_SATISFIABLE &&
              manager.getUnknownReason() == UnknownReason::None,
          "fresh query failed after a cancelled candidate sub-solve");
}

} // namespace

int main()
{
  try
  {
    queryTiming();
    control();
    transactionRecovery();
    for (auto stage : {PreparationStage::Boundary, PreparationStage::UFLowering,
                       PreparationStage::LraPresolve,
                       PreparationStage::LraPreregistration,
                       PreparationStage::LraRegistry,
                       PreparationStage::LraCore, PreparationStage::Encoding})
      queryRecovery(stage);
    for (auto stage : {PreparationStage::UFLowering, PreparationStage::LraPresolve,
                       PreparationStage::LraPreregistration,
                       PreparationStage::LraRegistry, PreparationStage::LraCore,
                       PreparationStage::BitBlasting, PreparationStage::CNFConversion,
                       PreparationStage::ClauseLoading})
      queryRecovery(stage, 3);
    congruenceRecovery();
    congruenceRecovery(PreparationStage::RefinementEncoding);
    constantBitOwnership();
    for (auto stage : {PreparationStage::BitBlasting, PreparationStage::ClauseLoading})
      congruenceCandidateRecovery(stage);
    for (auto effort : {UserDefinedFlags::CNF_EFFORT_LOW,
                        UserDefinedFlags::CNF_EFFORT_NEW_MEDIUM,
                        UserDefinedFlags::CNF_EFFORT_GIA_LOW})
      for (auto stage : {PreparationStage::CNFConversion, PreparationStage::ClauseLoading})
        partialEncoding(effort, stage);
    std::cout << "PASS preparation deadline and query recovery\n";
    return 0;
  }
  catch (const std::exception& error)
  {
    std::cerr << error.what() << '\n';
    return 1;
  }
}

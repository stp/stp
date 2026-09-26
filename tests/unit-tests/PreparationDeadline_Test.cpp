/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Sep, 2026
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

// Deterministic cancellation at public preparation boundaries, and the
// exclusive per-query timers that account for it. Every case here is over
// bit-vectors, Booleans and bit-vector UFs.

#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/PreparationControl.h"
#include "stp/Util/QueryTiming.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/ToSat/ToSATAIG.h"
#include <gtest/gtest.h>

#include <memory>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>

namespace
{
using namespace stp;

std::uint64_t timing_ticks = 0;
QueryTiming::Clock::time_point timingNow()
{
  return QueryTiming::Clock::time_point(std::chrono::nanoseconds(timing_ticks));
}

TEST(QueryTiming, NestedPhasesAreExclusiveAndCloseOnUnwind)
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
    EXPECT_EQ(13u, totals[static_cast<unsigned>(QueryPhase::Other)]);
    EXPECT_EQ(3u, totals[static_cast<unsigned>(QueryPhase::EncodingOther)]);
    EXPECT_EQ(7u, totals[static_cast<unsigned>(QueryPhase::ClauseLoading)]);
    EXPECT_EQ(5u, totals[static_cast<unsigned>(QueryPhase::EncodingCleanup)]);
    EXPECT_EQ(28u, std::accumulate(totals.begin(), totals.end(),
                                   std::uint64_t{0}));
    {
      QueryTimingReport disabled(slot, nullptr, output);
      EXPECT_EQ(nullptr, slot) << "disabled query timing retained an outer clock";
    }
    EXPECT_EQ(&timing, slot) << "nested timing report did not restore its owner";
  }
  EXPECT_EQ(nullptr, slot);
  EXPECT_EQ(0u, output.str().find("Query phases: total_ns=28 "))
      << output.str();
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

TEST(PreparationControl, DeadlinePollingLatchAndScopes)
{
  const PreparationControl expired(PreparationControl::Clock::time_point::min());
  EXPECT_THROW(expired.check(PreparationStage::Boundary), PreparationInterrupted);
  const PreparationControl unlimited;
  EXPECT_NO_THROW(unlimited.check(PreparationStage::Boundary));

  StopAfter stop{PreparationStage::CNFConversion, 3};
  const PreparationControl observed(PreparationControl::Clock::time_point::max(),
                                    nullptr, StopAfter::observe, &stop);
  PreparationPoller poll(&observed, stop.stage);
  unsigned work = 0;
  bool stopped = false;
  try { for (; work != 1024; ++work) poll(); }
  catch (const PreparationInterrupted&) { stopped = true; }
  EXPECT_TRUE(stopped);
  EXPECT_EQ(511u, work) << "preparation polling missed its bounded work interval";
  EXPECT_EQ(3u, stop.calls);
  stop.calls = 0;
  EXPECT_THROW(observed.check(PreparationStage::Boundary), PreparationInterrupted);
  EXPECT_EQ(0u, stop.calls) << "preparation stop was not latched";

  const PreparationControl* slot = nullptr;
  {
    PreparationScope outer(slot, unlimited);
    {
      PreparationScope inner(slot, observed);
      EXPECT_EQ(&observed, slot) << "nested preparation scope was not installed";
    }
    EXPECT_EQ(&unlimited, slot) << "nested preparation scope was not restored";
  }
  EXPECT_EQ(nullptr, slot) << "preparation scope escaped its query";
}

// Enough independent bit-vector rows that bit-blasting, CNF conversion and
// clause loading each reach several polling intervals.
ASTNode manyRows(STPMgr& manager)
{
  ASTVec rows;
  for (unsigned i = 0; i != 1024; ++i)
  {
    const auto symbol = manager.CreateSourceSymbol(
        ("row_" + std::to_string(i)).c_str(), SourceSort::bitVector(16));
    rows.push_back(manager.CreateNode(BVGE, symbol, manager.CreateBVConst(16, i)));
  }
  return manager.CreateNode(AND, rows);
}

void queryRecovery(PreparationStage stage, unsigned stop_after = 1)
{
  SCOPED_TRACE(std::string("stage ") + preparationStageName(stage) +
               ", stop after " + std::to_string(stop_after));
  STPMgr manager;
  STP engine(&manager);
  struct RestoreGlobal
  {
    STP* saved = GlobalSTP;
    ~RestoreGlobal() { GlobalSTP = saved; }
  } restore_global;
  GlobalSTP = &engine;
  manager.UserFlags.enable_uninterpreted_functions = true;
  manager.UserFlags.produce_models = true;
  const auto bv16 = SourceSort::bitVector(16);
  const auto x = manager.CreateSourceSymbol("deadline_x", bv16);
  const auto one = manager.CreateBVConst(16, 1);
  auto assertion = manager.CreateNode(EQ, x, one);
  if (stop_after > 1)
  {
    // Keep every row and application through to the encoding: the word-level
    // simplifiers would otherwise dispose of this formula before it is blasted.
    manager.UserFlags.optimize_flag = false;
    manager.UserFlags.enable_unconstrained = false;
    manager.UserFlags.enable_pure_literals = false;
    ASTVec terms{assertion, manyRows(manager)};
    auto* context = manager.getUFContext();
    std::string diagnostic;
    const auto* function = context->declareFunction("deadline_f", {bv16}, bv16,
                                                     &diagnostic);
    ASSERT_NE(nullptr, function) << diagnostic;
    for (unsigned i = 0; i != 512; ++i)
    {
      const auto value = manager.CreateBVConst(16, i);
      const auto application = context->apply(function, {value}, &diagnostic);
      ASSERT_FALSE(application.IsNull()) << diagnostic;
      terms.push_back(manager.CreateNode(EQ, application, value));
    }
    assertion = manager.CreateNode(AND, terms);
  }
  ASSERT_EQ(SOLVER_SATISFIABLE, engine.TopLevelSTP(assertion, manager.ASTFalse))
      << "control query did not build a model";
  EXPECT_EQ(one, engine.Ctr_Example->GetCounterExample(x));
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
    EXPECT_EQ(SOLVER_UNKNOWN, engine.TopLevelSTP(assertion, manager.ASTFalse))
        << "preparation cancellation was not unknown";
    EXPECT_EQ(UnknownReason::Timeout, manager.getUnknownReason());
    EXPECT_TRUE(manager.soft_timeout_expired);
    EXPECT_EQ(&observed, manager.preparation_control)
        << "public query did not restore its outer preparation observer";
  }
  if (stop.lowering_manager)
  {
    const auto lowered = manager.UserFlags.coverage.uf_applications_lowered;
    EXPECT_GE(lowered, stop.lowered_before + 16);
    EXPECT_LT(lowered, stop.lowered_before + 512)
        << "UF cancellation did not interrupt a partially populated lowering view";
  }
  else
    EXPECT_EQ(stop_after, stop.calls)
        << "requested preparation stage was not reached";
  // The CLI's quick-statistics printer rejects an unbalanced timer stack.
  // Cancellation must leave diagnostics usable as well as the next solve.
  manager.GetRunTimes()->print();
  EXPECT_EQ(ack, manager.UserFlags.ackermannisation);
  EXPECT_EQ(abstraction, manager.UserFlags.bv_term_abstraction);
  EXPECT_EQ(optimize, manager.UserFlags.optimize_flag)
      << "cancelled preparation retained query-local flags";
  EXPECT_EQ(SOLVER_SATISFIABLE, engine.TopLevelSTP(assertion, manager.ASTFalse))
      << "fresh query did not recover after preparation cancellation";
  EXPECT_EQ(one, engine.Ctr_Example->GetCounterExample(x));
  EXPECT_EQ(UnknownReason::None, manager.getUnknownReason());
  EXPECT_EQ(nullptr, manager.preparation_control)
      << "fresh query retained a borrowed preparation control";
}

TEST(PreparationDeadline, PublicQueryRecoversAtEachStage)
{
  for (auto stage : {PreparationStage::Boundary, PreparationStage::UFLowering,
                     PreparationStage::Encoding})
    queryRecovery(stage);
}

TEST(PreparationDeadline, PublicQueryRecoversPartwayThroughAStage)
{
  for (auto stage : {PreparationStage::UFLowering, PreparationStage::BitBlasting,
                     PreparationStage::CNFConversion,
                     PreparationStage::ClauseLoading})
    queryRecovery(stage, 3);
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
  SCOPED_TRACE(std::string("stage ") + preparationStageName(stage) +
               ", CNF effort " + std::to_string(static_cast<int>(effort)));
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
    EXPECT_TRUE(interrupted);
    EXPECT_GT(stop.calls, 1u) << "encoding did not stop after partial work";
    if (stage == PreparationStage::CNFConversion)
    {
      EXPECT_GE(encoder.SATVar_to_SymbolIndexMap().size(), 16u);
      EXPECT_LT(encoder.SATVar_to_SymbolIndexMap().size(), 2048u)
          << "CNF cancellation did not interrupt a partial symbol projection";
    }
    else
    {
      EXPECT_GE(solver->submittedClauses(), 16u);
      EXPECT_LT(solver->submittedClauses(), 1024u)
          << "clause cancellation did not interrupt partial insertion";
    }
    manager.GetRunTimes()->print();
  }
  manager.ClearAllTables();
  std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
  ToSATAIG fresh(&manager, engine.arrayTransformer);
  EXPECT_TRUE(fresh.CallSAT(*solver, formula, false))
      << "fresh encoding did not recover after partial cancellation";
}

TEST(PreparationDeadline, EncodingStopsPartwayAndRecovers)
{
  for (auto effort : {UserDefinedFlags::CNF_EFFORT_LOW,
                      UserDefinedFlags::CNF_EFFORT_NEW_MEDIUM,
                      UserDefinedFlags::CNF_EFFORT_GIA_LOW})
    for (auto stage : {PreparationStage::CNFConversion, PreparationStage::ClauseLoading})
      partialEncoding(effort, stage);
}

TEST(PreparationDeadline, ConstantBitOwnershipSurvivesCancellation)
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
    EXPECT_EQ(SOLVER_UNKNOWN, engine.TopLevelSTP(formula, manager.ASTFalse));
    EXPECT_EQ(UnknownReason::Timeout, manager.getUnknownReason())
        << "cancellation after consuming constant-bit data lost its timeout";
  }
  EXPECT_EQ(1u, stop.calls);
  EXPECT_TRUE(manager.UserFlags.bitConstantProp_flag)
      << "constant-bit ownership control did not reach CNF conversion";
  manager.GetRunTimes()->print();
  EXPECT_EQ(SOLVER_SATISFIABLE, engine.TopLevelSTP(formula, manager.ASTFalse))
      << "fresh query failed after constant-bit ownership handoff";
}

// The candidate pass proves its equalities with sub-solves that go through
// the same encoder, so a cancellation can land inside one. The pass's timer
// and the manager state it sets aside for the sub-solve are both restored.
void congruenceCandidateRecovery(PreparationStage stage)
{
  SCOPED_TRACE(std::string("stage ") + preparationStageName(stage));
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
    EXPECT_EQ(SOLVER_UNKNOWN, engine.TopLevelSTP(formula, manager.ASTFalse));
    EXPECT_EQ(UnknownReason::Timeout, manager.getUnknownReason());
  }
  EXPECT_TRUE(stop.stopped) << "no candidate sub-solve reached the stage";
  EXPECT_EQ(manager.ASTFalse, manager.GetQuery())
      << "cancelled candidate sub-solve did not restore the query";
  manager.GetRunTimes()->print();
  EXPECT_EQ(SOLVER_SATISFIABLE, engine.TopLevelSTP(formula, manager.ASTFalse))
      << "fresh query failed after a cancelled candidate sub-solve";
  EXPECT_EQ(UnknownReason::None, manager.getUnknownReason());
}

TEST(PreparationDeadline, CongruenceCandidateSubSolveRecovers)
{
  for (auto stage : {PreparationStage::BitBlasting, PreparationStage::ClauseLoading})
    congruenceCandidateRecovery(stage);
}

} // namespace

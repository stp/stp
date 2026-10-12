/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
 * Copyright (c) 2026 Vector Informatik GmbH
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, subject to the conditions of the MIT
 * license carried by the rest of STP.
 ********************************************************************/

/* A persistent Real solve across check-sats.
 *
 * The batch path builds a coordinator, an exact core, a Boolean skeleton's
 * CNF and a SAT solver for one check-sat and destroys them all. An
 * incremental client asserts, pushes, checks and pops in a loop; rebuilding
 * everything per check costs the whole stack each time. This keeps those
 * objects alive between checks. The base level is encoded once under the
 * coordinator's solve activation; each pushed level is an extension frame
 * under an activation of its own; a check assumes the live activations; a pop
 * retracts a frame with a permanent unit on its activation, its clauses
 * staying satisfied in the solver. Learned clauses, atom bindings, exact
 * registrations all survive.
 *
 * It does not touch the batch solve loop. Uninterpreted functions and every
 * bit-vector / array / floating-point / DISTINCT construct are declined to
 * the batch path (UF needs a persistent deterministic lowering, a step of
 * its own); a declined stack solves exactly as before. */

#include "stp/STPManager/STP.h"

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/ToSat/ToSATAIG.h"
#include "stp/Util/PreparationControl.h"
#include "Lra/ASTRealConst.h"
#include "Lra/LraCoordinator.h"
#include "Lra/LraFrontend.h"

#include <algorithm>
#include <iostream>
#include <memory>
#include <set>
#include <vector>

namespace stp
{

struct RealSessionState final
{
  std::unique_ptr<SATSolver> solver;
  std::unique_ptr<ToSATAIG> tosat;
  std::unique_ptr<lra::LraCoordinator> coordinator;
  struct Frame
  {
    std::vector<ASTNode> encoded;
    ASTNode activation;
  };
  std::vector<Frame> frames; // frames[i] is level i + 1
  std::vector<ASTNode> base_encoded;
  bool base_unsat = false;
  uint64_t checks = 0;
  std::vector<size_t> failed_assumptions;
};

namespace
{

// An assertion can itself be a conjunction, and older callers may have
// conjoined an entire level through getVectorOfAsserts(). Reconcile atomic
// conjuncts so growth reads as a superset, independently of that grouping.
void decomposeLevel(const ASTVec& level, std::vector<ASTNode>& out)
{
  std::vector<ASTNode> work(level.rbegin(), level.rend());
  while (!work.empty())
  {
    const ASTNode node = work.back();
    work.pop_back();
    if (node.IsNull() || node.GetKind() == TRUE)
      continue;
    if (node.GetKind() == AND)
    {
      const auto kids = node.GetChildren();
      for (size_t j = kids.size(); j > 0; --j)
        work.push_back(kids[j - 1]);
      continue;
    }
    out.push_back(node);
  }
}

enum class LevelRel
{
  Equal,    // same conjunct set: reuse the frame unchanged
  Superset, // grew: `diff` holds the conjuncts to append
  Changed   // a previously-encoded conjunct is gone: retract and re-encode
};

LevelRel classifyLevel(const std::vector<ASTNode>& encoded,
                       const std::vector<ASTNode>& current, ASTVec& diff)
{
  const std::set<ASTNode, ExprLess> cur(current.begin(), current.end());
  for (const ASTNode& e : encoded)
    if (cur.find(e) == cur.end())
      return LevelRel::Changed;
  const std::set<ASTNode, ExprLess> enc(encoded.begin(), encoded.end());
  std::set<ASTNode, ExprLess> added;
  diff.clear();
  for (const ASTNode& c : current)
    if (enc.find(c) == enc.end() && added.insert(c).second)
      diff.push_back(c);
  return diff.empty() ? LevelRel::Equal : LevelRel::Superset;
}

ASTNode conjoin(STPMgr* bm, const ASTVec& conjuncts)
{
  if (conjuncts.empty())
    return bm->ASTTrue;
  if (conjuncts.size() == 1)
    return conjuncts[0];
  return bm->CreateNode(AND, conjuncts);
}

} // namespace

bool STP::realSessionCanHandle(const ASTVec& assertions) const
{
  if (bm->has_distinct || bm->has_floating_point_theory)
    return false;
  std::set<ASTNode, ExprLess> seen;
  std::vector<ASTNode> work(assertions.begin(), assertions.end());
  while (!work.empty())
  {
    const ASTNode node = work.back();
    work.pop_back();
    if (node.IsNull() || !seen.insert(node).second)
      continue;
    switch (node.GetSourceSort().kind())
    {
      case SourceSort::Kind::Bool:
      case SourceSort::Kind::Real:
        break;
      default:
        return false;
    }
    switch (node.GetKind())
    {
      case READ:
      case WRITE:
      case DISTINCT:
      case UF_APPLY:
        return false;
      default:
        break;
    }
    for (const ASTNode& child : node.GetChildren())
      work.push_back(child);
  }
  return true;
}

void STP::discardRealSession()
{
  delete realSession;
  realSession = nullptr;
}

std::vector<size_t> STP::realSessionUnsatAssumptionIndices() const
{
  return realSession ? realSession->failed_assumptions : std::vector<size_t>{};
}

SOLVER_RETURN_TYPE STP::checkSatRealSession(const std::vector<ASTVec*>& levels,
                                            bool& handled,
                                            size_t assumption_levels)
{
  handled = false;
  if (levels.empty() || assumption_levels >= levels.size())
    return SOLVER_ERROR;
  const auto deadline = bm->UserFlags.hasQueryTimeLimit()
      ? bm->UserFlags.queryDeadline(PreparationControl::Clock::now())
      : PreparationControl::Clock::time_point::max();
  const PreparationControl preparation(deadline, bm->preparation_control);
  const PreparationScope preparation_scope(bm->preparation_control, preparation);
  const bool fresh = realSession == nullptr;
  if (fresh)
    realSession = new RealSessionState();
  RealSessionState& session = *realSession;
  session.failed_assumptions.clear();
  // A check that ran out of its own time or conflict budget has its answer:
  // unknown, as the batch path answers when its budget runs out. Declining
  // would hand the batch path the same check with a fresh budget of its own,
  // spending --max-time twice. The session ends here all the same -- a
  // coordinator stopped by a timeout has failed closed -- and the next check
  // starts a new one.
  const auto budgetSpent = [&]() {
    return bm->soft_timeout_expired &&
           (bm->getUnknownReason() == UnknownReason::Timeout ||
            bm->getUnknownReason() == UnknownReason::ConflictBudget);
  };
  const auto giveUp = [&]() -> SOLVER_RETURN_TYPE {
    discardRealSession();
    handled = true;
    return bm->unknownResult();
  };
  const auto preparationStopped = [&](const PreparationInterrupted& stopped) {
    bm->soft_timeout_expired = true;
    if (bm->getUnknownReason() == UnknownReason::None)
      bm->noteUnknown(UnknownReason::Timeout,
                      std::string("during ") + preparationStageName(stopped.stage));
    return giveUp();
  };
  const auto decline = [&]() -> SOLVER_RETURN_TYPE {
    // Coordinator extensions report interruptions through their return
    // values. Preserve those stops before discarding the session: a batch
    // retry would otherwise arm a fresh budget for the same check.
    try
    {
      if (session.coordinator)
        session.coordinator->rethrowPreparationInterruption();
      bm->checkPreparation(PreparationStage::Boundary);
    }
    catch (const PreparationInterrupted& stopped)
    {
      return preparationStopped(stopped);
    }
    discardRealSession();
    handled = false;
    return SOLVER_ERROR;
  };

  // Every check starts the way a batch query does. The batch path clears the
  // manager's formula-computation and counterexample caches before the solve
  // (bm->ClearAllTables etc.); the ordinary model re-evaluation reads them,
  // so a stale entry from an earlier check would misjudge the candidate.
  bm->InvalidateRealModel();
  Ctr_Example->setFpEncodingContext(NULL);
  bm->clearInjectivityAssumed();
  bm->soft_timeout_expired = false;
  bm->UserFlags.cnf_auto_real_path = true;
  // An active LRA solve builds a candidate model for the ordinary
  // re-evaluation the coordinator checks against; the batch path forces
  // this on for every LRA solve (STP.cpp), and without it the model reads
  // as empty and every candidate is judged a mismatch.
  bm->UserFlags.construct_counterexample_flag = true;

  try
  {
    bm->checkPreparation(PreparationStage::Boundary);
    SATSolver* solver = nullptr;
    ToSATAIG* tosat = nullptr;
    lra::LraCoordinator* coordinator = nullptr;

    if (fresh)
    {
      // Encode the base first, then install every live frame before searching.
      // A harder base must not spend the check's budget before a contradictory
      // pushed assertion or assumption is installed.
      session.solver.reset(get_new_sat_solver());
      if (bm->UserFlags.stats_flag)
        session.solver->setVerbosity(1);
      solver = session.solver.get();
      applySolveBudgets(*solver, bm->UserFlags, deadline);
      session.tosat = std::make_unique<ToSATAIG>(bm, nullptr, arrayTransformer);
      tosat = session.tosat.get();

      const ASTNode base = conjoin(bm, *levels[0]);
      session.base_encoded.clear();
      decomposeLevel(*levels[0], session.base_encoded);
      session.coordinator =
          std::make_unique<lra::LraCoordinator>(*bm, *solver, base,
                                                std::vector<ASTNode>{});
      coordinator = session.coordinator.get();
      if (!coordinator->ready())
        return decline();
      for (const ASTNode& atom : coordinator->opaqueAtoms())
        tosat->protectSymbol(atom);
      coordinator->setLegacyArrayRefinementEnabled(false);
      const ASTNode& activation = coordinator->solveActivation();
      ASTNode inputToSat = coordinator->booleanFormula();
      if (!inputToSat.isConstant())
        inputToSat = bm->CreateNode(IMPLIES, activation, inputToSat);
      if (!solver->supportsAssumptions() ||
          !tosat->setRequiredSolveAssumption(activation))
        return decline();
      solver->enableRefinement(true);
      bm->ClearAllTables();
      bm->TermsAlreadySeenMap_Clear();
      Ctr_Example->ClearAllTables();
      if (inputToSat == bm->ASTFalse)
        session.base_unsat = true;
      else
      {
        // Reserve the theory interface before the backend receives clauses;
        // CaDiCaL's elimination options cannot be changed after that point.
        if (!coordinator->beforeSolverCall())
          return decline();
        const bool encoded = tosat->encodeWithoutSearch(
            *solver, inputToSat, /*needAbsRef=*/true);
        if (budgetSpent())
          return giveUp();
        if (!encoded || bm->soft_timeout_expired ||
            !coordinator->afterCnf(*tosat))
          return decline();
      }
    }
    else
    {
      // Budgets are per check-sat, as the batch path arms them per query.
      // The solver outlives the check that created it, so every later
      // check arms it again rather than inheriting a deadline already
      // spent; a check that spends its budget answers unknown (giveUp
      // above) rather than being solved a second time on the batch path.
      applySolveBudgets(*session.solver, bm->UserFlags, deadline);
    }
    solver = session.solver.get();
    tosat = session.tosat.get();
    coordinator = session.coordinator.get();

    if (session.base_unsat)
    {
      ++session.checks;
      handled = true;
      return SOLVER_VALID;
    }

    // One core rebuild for the whole reconciliation, not one per mutation.
    coordinator->beginExtensionBatch();

    // Decompose every level to its conjunct set once, up front.
    std::vector<std::vector<ASTNode>> current(levels.size());
    for (size_t i = 0; i < levels.size(); ++i)
      decomposeLevel(*levels[i], current[i]);

    // Level 0 is the base; it only ever grows. A superset appends the new
    // conjuncts; a non-monotone change is beyond what an in-session base can
    // represent, so decline (the batch path will take it).
    {
      ASTVec diff;
      switch (classifyLevel(session.base_encoded, current[0], diff))
      {
        case LevelRel::Equal:
          break;
        case LevelRel::Superset:
          if (coordinator->extendWithFormula(conjoin(bm, diff), *tosat) !=
              lra::ExtensionOutcome::Extended)
            return decline();
          session.base_encoded = current[0];
          break;
        case LevelRel::Changed:
          return decline();
      }
    }

    // Pushed levels: keep every frame still equal or grown, retract from the
    // first that diverged (everything above it sits on that frame), then
    // append growth to the survivors and encode the newly pushed levels.
    size_t keep = 0;
    for (; keep < session.frames.size() && keep + 1 < levels.size(); ++keep)
    {
      ASTVec diff;
      if (classifyLevel(session.frames[keep].encoded, current[keep + 1],
                        diff) == LevelRel::Changed)
        break;
    }
    for (size_t i = session.frames.size(); i > keep; --i)
      if (!session.frames[i - 1].activation.IsNull())
        if (!coordinator->retractFrame(session.frames[i - 1].activation))
          return decline();
    session.frames.resize(keep);
    for (size_t i = 1; i < levels.size(); ++i)
    {
      const std::vector<ASTNode>& level = current[i];
      if (i - 1 < session.frames.size())
      {
        RealSessionState::Frame& frame = session.frames[i - 1];
        ASTVec diff;
        if (classifyLevel(frame.encoded, level, diff) == LevelRel::Superset)
        {
          if (frame.activation.IsNull())
            frame.activation = CreateFreshSessionActivation();
          if (coordinator->extendFrame(conjoin(bm, diff), *tosat,
                                       frame.activation) !=
              lra::ExtensionOutcome::Extended)
            return decline();
          frame.encoded = level;
        }
      }
      else
      {
        RealSessionState::Frame frame;
        if (!level.empty())
        {
          frame.activation = CreateFreshSessionActivation();
          if (coordinator->extendFrame(conjoin(bm, level), *tosat,
                                       frame.activation) !=
              lra::ExtensionOutcome::Extended)
            return decline();
          frame.encoded = level;
        }
        session.frames.push_back(std::move(frame));
      }
    }

    if (!coordinator->endExtensionBatch())
      return decline();

    if (!tosat->setRequiredSolveAssumptions(coordinator->liveActivations()))
      return decline();

    bm->ClearAllTables();
    bm->TermsAlreadySeenMap_Clear();
    Ctr_Example->ClearAllTables();
    SOLVER_RETURN_TYPE res = lraSessionSolve(*solver, *tosat, *coordinator);
    if (budgetSpent())
      return giveUp();
    if (res == SOLVER_ERROR || bm->soft_timeout_expired)
      return decline();
    if (res == SOLVER_VALID && assumption_levels)
    {
      // Capture the backend core immediately, before any further mutation.
      // Each API assumption has its own activation frame, so the proof can
      // omit irrelevant predicates. The permanent and user-pushed frames
      // remain part of the query against which this core is valid.
      auto& bindings = tosat->SATVar_to_SymbolIndexMap();
      SATSolver::vec_literals live;
      for (const ASTNode& activation : coordinator->liveActivations())
      {
        const auto found = bindings.find(activation);
        if (found == bindings.end() || found->second.size() != 1 ||
            !solver->validVariable(found->second.front()))
          return decline();
        live.push(SATSolver::mkLit(found->second.front(), false));
      }
      std::vector<int> failed;
      solver->unsatAssumptions(live, failed);
      const size_t first = levels.size() - assumption_levels;
      for (size_t i = 0; i < assumption_levels; ++i)
      {
        const ASTNode& activation = session.frames[first + i - 1].activation;
        if (activation.IsNull()) // an empty/constant-true assumption frame
          continue;
        const auto found = bindings.find(activation);
        if (found == bindings.end() || found->second.size() != 1)
          return decline();
        const int literal = SATSolver::toInt(
            SATSolver::mkLit(found->second.front(), false));
        if (std::find(failed.begin(), failed.end(), literal) != failed.end())
          session.failed_assumptions.push_back(i);
      }
    }
    if (bm->UserFlags.stats_flag)
      std::cerr << "Real session: check " << session.checks + 1 << ", levels "
                << levels.size() << ", frames " << session.frames.size()
                << std::endl;
    ++session.checks;
    handled = true;
    return res;
  }
  catch (const PreparationInterrupted& stopped)
  {
    return preparationStopped(stopped);
  }
  catch (...)
  {
    // A run that ended at the session's first CNF ends here too: declining
    // would hand the check to the batch path, which would generate the CNF
    // again.
    if (bm->run_ended_after_cnf)
    {
      handled = true;
      return bm->unknownResult();
    }
    return decline();
  }
}

ASTNode STP::CreateFreshSessionActivation()
{
  return bm->CreateFreshInternalSourceVariable(SourceSort::boolean(),
                                               "lra_frame");
}

SOLVER_RETURN_TYPE STP::lraSessionSolve(SATSolver& solver, ToSATAIG& tosat,
                                        lra::LraCoordinator& coordinator)
{
  const ASTNode& skeleton = coordinator.booleanFormula();
  SOLVER_RETURN_TYPE res = Ctr_Example->CallSAT_ResultCheck(
      solver, bm->ASTTrue, skeleton, skeleton, &tosat, true, &coordinator);
  while (res == SOLVER_UNDECIDED)
  {
    if (bm->soft_timeout_expired)
      return bm->unknownResult();
    if (!coordinator.hasPendingLraClause())
    {
      coordinator.failClosed("session refinement reached no pending clause");
      return SOLVER_ERROR;
    }
    if (!coordinator.encodePendingLraClause())
      return SOLVER_ERROR;
    Ctr_Example->ClearAllTables();
    res = Ctr_Example->CallSAT_ResultCheck(solver, bm->ASTTrue, skeleton,
                                           skeleton, &tosat, true,
                                           &coordinator);
  }
  return res;
}

} // namespace stp

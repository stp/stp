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
#include "Lra/ASTRealConst.h"
#include "Lra/LraCoordinator.h"
#include "Lra/LraFrontend.h"

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
};

namespace
{

// getVectorOfAsserts() collapses every assertion level to a single node
// before each check: TRUE for an empty level, the lone assertion for one, an
// AND(...) for several. Its identity therefore changes whenever the level's
// contents change -- growing the base from {a>=1} to {a>=1,b>=2} turns node
// `a>=1` into node `AND(a>=1,b>=2)`. Reconciling on that node is what made
// the session decline a monotonically growing base. Flatten it back to the
// set of atomic conjuncts so growth reads as a superset instead.
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

SOLVER_RETURN_TYPE STP::checkSatRealSession(const std::vector<ASTVec*>& levels,
                                            bool& handled)
{
  handled = false;
  if (levels.empty())
    return SOLVER_ERROR;
  const bool fresh = realSession == nullptr;
  if (fresh)
    realSession = new RealSessionState();
  RealSessionState& session = *realSession;
  const auto decline = [&]() -> SOLVER_RETURN_TYPE {
    discardRealSession();
    handled = false;
    return SOLVER_ERROR;
  };
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
    SATSolver* solver = nullptr;
    ToSATAIG* tosat = nullptr;
    lra::LraCoordinator* coordinator = nullptr;

    if (fresh)
    {
      // Level 0 is the base; every deeper level is a frame. The base is
      // encoded and solved once, here.
      session.solver.reset(get_new_sat_solver());
      if (bm->UserFlags.stats_flag)
        session.solver->setVerbosity(1);
      solver = session.solver.get();
      applySolveBudgets(*solver, bm->UserFlags);
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
      SOLVER_RETURN_TYPE base_res = lraSessionSolve(
          *solver, *tosat, *coordinator, inputToSat, /*first=*/true);
      if (budgetSpent())
        return giveUp();
      if (base_res == SOLVER_ERROR || base_res == SOLVER_UNKNOWN ||
          bm->soft_timeout_expired)
        return decline();
      if (base_res == SOLVER_VALID)
        session.base_unsat = true;
    }
    else
    {
      // Budgets are per check-sat, as the batch path arms them per query.
      // The solver outlives the check that created it, so every later
      // check arms it again rather than inheriting a deadline already
      // spent; a check that spends its budget answers unknown (giveUp
      // above) rather than being solved a second time on the batch path.
      applySolveBudgets(*session.solver, bm->UserFlags);
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
    SOLVER_RETURN_TYPE res = lraSessionSolve(
        *solver, *tosat, *coordinator, bm->ASTTrue, /*first=*/false);
    if (budgetSpent())
      return giveUp();
    if (res == SOLVER_ERROR || bm->soft_timeout_expired)
      return decline();
    if (bm->UserFlags.stats_flag)
      std::cerr << "Real session: check " << session.checks + 1 << ", levels "
                << levels.size() << ", frames " << session.frames.size()
                << std::endl;
    ++session.checks;
    handled = true;
    return res;
  }
  catch (...)
  {
    return decline();
  }
}

ASTNode STP::CreateFreshSessionActivation()
{
  return bm->CreateFreshInternalSourceVariable(SourceSort::boolean(),
                                               "lra_frame");
}

SOLVER_RETURN_TYPE STP::lraSessionSolve(SATSolver& solver, ToSATAIG& tosat,
                                        lra::LraCoordinator& coordinator,
                                        const ASTNode& modified_input,
                                        bool first)
{
  (void)first;
  const ASTNode& skeleton = coordinator.booleanFormula();
  SOLVER_RETURN_TYPE res = Ctr_Example->CallSAT_ResultCheck(
      solver, modified_input, skeleton, skeleton, &tosat, true, &coordinator);
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

/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#include "IncrementalSolverImpl.h"

namespace stp
{


IncrementalSolver::IncrementalSolver(STPMgr* bm, AbsRefine_CounterExample* ce,
                                     Simplifier* batchSimp,
                                     ArrayTransformer* batchAT)
    : impl(new Impl(bm, ce, batchSimp, batchAT))
{
}

std::vector<std::pair<ASTNode, ASTNode>>
IncrementalSolver::seededReadsForTesting() const
{
  std::vector<std::pair<ASTNode, ASTNode>> out;
  for (std::map<std::pair<ASTNode, ASTNode>, size_t>::const_iterator it =
           impl->seededRowRef.begin();
       it != impl->seededRowRef.end(); ++it)
  {
    const ArrayTransformer::ArrType::const_iterator array =
        impl->arrayRegistry.reads.find(it->first.first);
    if (array != impl->arrayRegistry.reads.end() &&
        array->second.find(it->first.second) != array->second.end())
      out.push_back(it->first);
  }
  return out;
}

IncrementalSolver::EncodingEpochStats
IncrementalSolver::encodingEpochStatsForTesting() const
{
  EncodingEpochStats out;
  out.generation = impl->encodingEpochGeneration;
  out.aigAndNodes = impl->encoding.aigAndNodes();
  out.rootEncodings = impl->rootLitOf.size();
  out.bitBlastedSymbols =
      impl->encoding.nodes().symbolToBBNode.size();
  out.semanticCacheEntries = impl->semanticCacheEntryCount();
  for (ArrayTransformer::ArrType::const_iterator it =
           impl->arrayRegistry.reads.begin();
       it != impl->arrayRegistry.reads.end(); ++it)
    out.arrayReadRows += it->second.size();
  return out;
}

bool IncrementalSolver::lastSolveWasUnsat() const
{
  return impl->lastUnsat;
}

bool IncrementalSolver::lastUnsatHasAssumptionGranularity() const
{
  return impl->lastUnsat && !impl->lastUnsatCoarse &&
         impl->lastLevelIndividual;
}

std::vector<ASTNode> IncrementalSolver::lastUnsatAssumptionConjuncts() const
{
  std::vector<ASTNode> out;
  if (!lastUnsatHasAssumptionGranularity())
    return out;
  const std::unordered_set<int> failed(impl->lastFailedLits.begin(),
                                       impl->lastFailedLits.end());
  for (const std::pair<int, ASTNode>& lc : impl->lastLevelLitConjuncts)
  {
    if (failed.count(lc.first))
      out.push_back(lc.second);
  }
  return out;
}

std::vector<size_t> IncrementalSolver::lastUnsatCoreLevels() const
{
  std::vector<size_t> out;
  if (!impl->lastUnsat)
    return out;
  if (impl->lastUnsatCoarse)
  {
    for (size_t i = 1; i < impl->lastLevelCount; i++)
      out.push_back(i);
    return out;
  }
  const std::unordered_set<int> failed(impl->lastFailedLits.begin(),
                                       impl->lastFailedLits.end());
  std::unordered_set<size_t> seen;
  // A promoted level is asserted unconditionally, so every refutation
  // may rest on it without any assumption failing: the core is floored
  // at the promoted prefix, and the caller's verdict cache can never
  // record an unsat above a level that may have carried it.
  for (size_t i = 1;
       i <= impl->scopes.promotedDepth() && i < impl->lastLevelCount; i++)
  {
    if (seen.insert(i).second)
      out.push_back(i);
  }
  for (const std::pair<int, size_t>& ll : impl->assumedLitLevels)
  {
    if (failed.count(ll.first) && seen.insert(ll.second).second)
      out.push_back(ll.second);
  }
  std::sort(out.begin(), out.end());
  return out;
}

IncrementalSolver::~IncrementalSolver()
{
  if (impl->ce->getUFTheoryAdapter() == impl->ufAdapter.get())
    impl->ce->setUFTheoryAdapter(NULL);
  // The counterexample machinery may still point at our floating-point
  // encoding context; whoever solves next installs their own before any
  // model is read (and model_valid already refuses stale reads).
  if (impl->fpCtx)
    impl->ce->setFpEncodingContext(NULL);

  // Withdraw what this driver seeded into the batch Simplifier's SolverMap.
  // That channel is shared and is never cleared between solves -- the batch
  // pipeline owns entries of its own in it -- which is why
  // seedEliminatedIntoModelChannel withdraws at the START of every solve: a
  // stale entry from a popped branch SHADOWS a live one, because insert()
  // does not overwrite. The protocol covered every transition except the
  // last one, so this object could be destroyed leaving its entries in a map
  // that outlives it.
  //
  // Be exact about what this is worth. No reachable wrong answer is being
  // fixed: both frontends clear the map first -- reset() and
  // resetAssertions() call resetSolver() before resetIncrementalSolver(),
  // and ~STP() calls ClearAllTables() before deleteObjects() -- so in-tree
  // the entries are already gone by the time we get here, and there is no
  // test that can fail without this. It is here because IncrementalSolver is
  // public API an embedder constructs and destroys directly, and a class
  // whose invariant holds only because its caller tidies up first is one
  // refactor away from not holding. Defence, not a fix.
  //
  // Ordering is safe on both teardown paths: deleteObjects() destroys this
  // driver before it deletes the Simplifier, and resetIncrementalSolver()
  // runs while the whole STP object is alive.
  if (impl->batchSimp != NULL)
  {
    DenseNodeMap* channel = impl->batchSimp->Return_SolverMap();
    for (const ASTNode& k : impl->seededModelKeys)
      channel->erase(k);
    impl->seededModelKeys.clear();
  }
}

bool IncrementalSolver::forcedFirstSolve(bool forcedFromStart,
                                        size_t solvesRun)
{
  return forcedFromStart && solvesRun == 0;
}

bool IncrementalSolver::automaticEngagementReady(int64_t configuredThreshold,
                                                bool delayedBvLogic,
                                                size_t solvesRun)
{
  // A targeted 107-session sweep found solve 32 the best finite compromise
  // for pure QF_BV/QF_ABV: engaging later or never made common batch-friendly
  // cases faster but lost incremental-friendly long sessions. Everything else
  // -- floating point, arrays outside QF_ABV, unknown logics -- engages on the
  // third, keeping two batch warm-ups.
  int64_t engageAt = configuredThreshold;
  if (engageAt < 0)
    engageAt = delayedBvLogic ? 32 : 3;
  if (engageAt <= 0)
    return false;
  return solvesRun >= static_cast<size_t>(engageAt - 1);
}

bool IncrementalSolver::canHandle(const ASTVec& assertionsSMT2)
{
  // Every construct the SMT-LIB frontend can produce is covered: plain
  // bit-vectors, arrays (lazy or --ackermanize), floating point, and
  // whole-array equality. The method remains the seam for any future
  // exclusion.
  (void)assertionsSMT2;
  return true;
}

SOLVER_RETURN_TYPE IncrementalSolver::checkSat(const ASTVec& assertionsSMT2,
                                               bool assumeLastLevelPerConjunct,
                                               bool firstForcedIncrementalSolve)
{
  if (impl->bm->UserFlags.aig_node_budget >= 0 && !budgetNotEnforcedWarned)
  {
    budgetNotEnforcedWarned = true;
    std::cerr << "Warning: --aig-node-budget is not enforced on the "
                 "incremental encoder; the cap covers batch solves only."
              << std::endl;
  }

  impl->beginProfile(assertionsSMT2.size());
  const SOLVER_RETURN_TYPE result = checkSatBody(
      assertionsSMT2, assumeLastLevelPerConjunct, firstForcedIncrementalSolve);
  impl->finishProfile();
  // The driver has its own encoding path and never enters the batch
  // refinement loop, so the batch pipeline's report never runs here;
  // without this the checker's rounds are invisible in exactly the mode
  // that accumulates the most of them.
  if (ExtensionalityContext* ext = impl->bm->getExtensionalityIfAny())
    ext->reportLemmaStats();
  return result;
}

void IncrementalSolver::materializePendingModel()
{
  if (!impl->modelPending)
    return;
  impl->modelPending = false;
  buildPendingModel();
}

void IncrementalSolver::buildPendingModel()
{
  STPMgr* bm = impl->bm;
  bm->GetRunTimes()->start(RunTimes::CounterExampleGeneration);
  impl->ce->ClearCounterExampleMap();
  impl->ce->ClearComputeFormulaMap();

  impl->seedEliminatedIntoModelChannel();
  // The solve that deferred this model may not have wired the context
  // itself (the plain exact-stack route does not); lowered floating-point
  // terms evaluate through the context that lowered them.
  impl->publishFpContext();

  ToSATBase::ASTNodeToSATVar symbolMap;
  impl->buildSymbolMap(symbolMap);
  impl->ce->ConstructCounterExample(*impl->solver, symbolMap);
  bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);

  if (bm->UserFlags.stats_flag)
    std::cerr << "Incremental: model materialized on demand" << std::endl;
}

SOLVER_RETURN_TYPE
IncrementalSolver::checkSatBody(const ASTVec& assertionsSMT2,
                                bool assumeLastLevelPerConjunct,
                                bool firstForcedIncrementalSolve)
{
  STPMgr* bm = impl->bm;
  UserDefinedFlags& uf = bm->UserFlags;

  assert(!assertionsSMT2.empty());
  // A frontend may claim a forced FIRST solve only before this driver has
  // engaged at all; otherwise the first-solve policies the stages below key
  // on the flag would be applied to a solve which already had
  // batch-preprocessed predecessors. Checked here, where the claim arrives
  // and before maintenance counts the solve, so the stages can take the
  // flag's honesty for granted -- and maintenance, which never acts on the
  // flag, need not take it at all.
  assert((!firstForcedIncrementalSolve || impl->engagedSolves == 0) &&
         "a forced first solve was claimed after the driver had engaged");

  impl->maintainBackendForCheck(assertionsSMT2);

  // No stale equality state may survive into this round: the consistency
  // checker keys off ext->active(), and a previous round's solve-local
  // records would send this round's candidate to a checker expecting values
  // for symbols this round never encoded. active() deliberately outlives the
  // solve that set it -- the model surfaces read the frozen graph after the
  // solve returns -- so only the next round can retire it, and the SMT-LIB2
  // pop is the only caller that does so itself: the C API's vc_pop
  // deliberately clears nothing (its model outlives the bracket), and
  // check-sat-assuming's frame pop keeps the model too.
  //
  // This is ahead of the routing because every route materializes candidates.
  // The exact-stack route begins a solve of its own only for an
  // array-equality round, yet it also owns rounds that merely apply an
  // uninterpreted function, and those would otherwise run the previous
  // round's checker over the current round's assignment.
  ExtensionalityContext* staleExt = bm->getExtensionalityIfAny();
  if (staleExt != NULL && staleExt->active())
    staleExt->beginSolve();

  SOLVER_RETURN_TYPE exactResult;
  if (impl->tryExactStackRoute(assertionsSMT2,
                               assumeLastLevelPerConjunct,
                               firstForcedIncrementalSolve, exactResult))
    return exactResult;

  UFContext* staleUF = bm->getUFContextIfAny();
  if (staleUF != NULL)
    staleUF->releaseSolveProtection();
  impl->activeUFView = LoweredApplicationView();
  impl->ufAdapter->clearActiveBlock();
  if (impl->ce->getUFTheoryAdapter() == impl->ufAdapter.get())
    impl->ce->setUFTheoryAdapter(NULL);

  const uint64_t clausesBefore = impl->lifetimeClauseSubmissions();
  impl->encodesThisCall = 0;

  ProfileClock::time_point semanticStarted;
  if (impl->profile.enabled)
    semanticStarted = ProfileClock::now();

  impl->synchronizeCbpPrefix(assertionsSMT2,
                             firstForcedIncrementalSolve);

  impl->encodeBaseLevel(assertionsSMT2, firstForcedIncrementalSolve);

  SATSolver::vec_literals assumptions;
  const size_t contextEntries = impl->prepareAndEncodePushedLevels(
      assertionsSMT2, assumeLastLevelPerConjunct, assumptions);

  // Every route bit-blasts before it solves, and the abstractions the
  // blaster made are this driver's to refine. Taken across here, once all
  // of this call's encoding is done and before any search.
  impl->syncAbstractions();

  const ASTVec& activeEncodedKeys = impl->scopes.activeSemanticKeys();
  impl->hintRetractedLevels(assumptions);

  ASTNode ordinaryOwner;
  if (assertionsSMT2.size() > 1)
    ordinaryOwner = bm->CreateNode(AND, assertionsSMT2);
  else
    ordinaryOwner = assertionsSMT2[0];

  // This solve's live clause mass -- what the assumed stack actually
  // uses -- feeds the relief valve's deadness measure on LATER solves.
  // The peak since the last rebuild is the valve's denominator.
  uint64_t ordinaryLiveMass = impl->baseLiveMass;
  std::vector<Aig_Obj_t*> ordinaryCurrentRoots;
  const bool trackOrdinaryRoots =
      impl->profile.enabled || impl->clauseReliefSizeReached();
  if (trackOrdinaryRoots)
    ordinaryCurrentRoots.reserve(activeEncodedKeys.size());
  const uint64_t activationMass = impl->activeActivationMass(assumptions);
  const uint64_t oldRefinementMass = impl->refinementMass(ordinaryOwner);
  {
    for (const ASTNode& k : activeEncodedKeys)
    {
      std::map<ASTNode, uint64_t>::const_iterator mit =
          impl->clauseMassOf.find(k);
      if (mit != impl->clauseMassOf.end())
        ordinaryLiveMass = Impl::addMass(ordinaryLiveMass, mit->second);
      if (trackOrdinaryRoots)
        ordinaryCurrentRoots.push_back(impl->aigRoot(k));
    }
    ordinaryLiveMass = Impl::addMass(ordinaryLiveMass, activationMass);
    ordinaryLiveMass = Impl::addMass(ordinaryLiveMass, oldRefinementMass);
    uint64_t nonStructuralMass =
        Impl::addMass(impl->permanentUnitMass, activationMass);
    nonStructuralMass =
        Impl::addMass(nonStructuralMass, oldRefinementMass);
    impl->stageLiveConeMass(ordinaryCurrentRoots, ordinaryLiveMass,
                            nonStructuralMass);
    impl->stageSemanticLiveStack(assertionsSMT2, activeEncodedKeys);
  }

  if (impl->profile.enabled)
  {
    impl->profile.semanticNs +=
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            ProfileClock::now() - semanticStarted)
            .count();
    impl->profile.activeKeys = activeEncodedKeys.size();
    impl->profile.assumptions = assumptions.size();
    impl->profile.contextEntries = contextEntries;
  }

  if (uf.stats_flag)
  {
    std::cerr << "Incremental: encoded " << impl->encodesThisCall
              << " new conjuncts, added "
              << (impl->lifetimeClauseSubmissions() - clausesBefore)
              << " clauses, assumed "
              << assumptions.size() << " literals, solver has "
              << impl->solver->nVars() << " variables, " << impl->sigma0.size()
              << " base-level and " << contextEntries
              << " pushed substitutions, "
              << impl->scopes.activeEliminations().size() << " eliminated"
              << std::endl;
    if (impl->callCbpAdopted > 0 || impl->callCbpReplayed > 0)
      std::cerr << "Incremental: cbp adopted " << impl->callCbpAdopted
                << " rewrites (" << impl->callCbpReplayed << " replayed) from "
                << impl->callCbpSubst.size() << " fixed nodes" << std::endl;
  }

  // Array refinement needs a candidate model to find violated axioms, so
  // arrays force counterexample construction, exactly as in the batch
  // pipeline (TopLevelSTPAux). Under --ackermanize the transform compiles
  // arrays away eagerly -- each new read carries its if-then-else over the
  // existing reads -- so there is nothing to refine and the lean path
  // solves it like plain bit-vectors.
  bool activeHasArrays = false;
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    if (impl->fragment(levelConjunction).arrays)
    {
      activeHasArrays = true;
      break;
    }
  }
  const bool needRefinement = activeHasArrays && !uf.ackermannisation;

  // Derived afresh from the genuine inputs -- including the C API's direct
  // request, which now has its own field -- so that a check needing a
  // candidate model for refinement cannot leave construction switched on
  // for every later check, and with it the frontend's shortcut for a
  // repeated query whose model nobody wants.
  const bool construct = uf.modelConstructionRequired(needRefinement);
  uf.construct_counterexample_flag = construct;

  // Model evaluation of floating-point terms needs the encoding context
  // that lowered them. Batch fallback rounds install their own per solve;
  // this keeps the driver's rounds coherent the same way.
  impl->publishFpContext();

  // Budgets are per check-sat, as solve_by_sat_solver arms them per query.
  applySolveBudgets(*impl->solver, uf);
  bm->soft_timeout_expired = false;

  if (needRefinement)
  {
    ScopedProfileTimer refinementTimer(impl->profile.enabled,
                                       impl->profile.refinementNs);
    // The batch pipeline's own CEGAR: candidate model, violated congruence
    // axioms as direct (permanent -- they are tautologies of the canonical
    // read abstraction) clauses, solve again. The adapter re-solves under
    // this check-sat's assumptions, and the batch-side tables the
    // machinery reads are seeded from the driver's persistent stores.
    IncrementalToSAT* adapter =
        static_cast<IncrementalToSAT*>(impl->ensureAdapter());

    // Restrict the batch tables to the active cone's reads; stale rows
    // from popped scopes must not reach model construction or
    // refinement. Base keys have already queued themselves as they were
    // first asserted; only the pushed cone is passed per solve.
    impl->seedActiveReads(activeEncodedKeys);
    impl->seedEliminatedIntoModelChannel();

    // Idempotent when nothing changed; essential after a re-encode, when
    // registry symbols from earlier sessions have no variables yet and the
    // axiom encoder reads their bits unconditionally.
    impl->totalizeRegistrySymbols();

    const ASTNode& activeConjunction = ordinaryOwner;

    adapter->setAssumptions(&assumptions);
    const uint64_t refinementClausesBefore =
        impl->solver->submittedClauses();
    size_t refinementRounds = 0;
    ArrayReadRefinementProgress refinementProgress;
    uint64_t abstractionsRefined = impl->bvAbstraction.refinements();
    SOLVER_RETURN_TYPE res = impl->ce->CallSAT_ResultCheck(
        *impl->solver, bm->ASTTrue, activeConjunction, activeConjunction,
        adapter, true);
    while (res == SOLVER_UNDECIDED)
    {
      refinementRounds++;
      // A candidate rejected because it contradicted a bit-vector
      // abstraction has already been ruled out, inside the call above and
      // ahead of everything else that reads a candidate. Nothing is owed
      // to the array axioms for it -- it was never a model of the reads
      // either -- so the round is just the next search.
      const uint64_t refinedNow = impl->bvAbstraction.refinements();
      if (refinedNow != abstractionsRefined)
      {
        abstractionsRefined = refinedNow;
        res = impl->ce->CallSAT_ResultCheck(*impl->solver, bm->ASTTrue,
                                            activeConjunction,
                                            activeConjunction, adapter, true);
        continue;
      }
      res = impl->runGuardedReadRefinementRound(
          activeConjunction, adapter, refinementProgress,
          "IncrementalSolver: an array refinement round rejected "
          "the candidate but emitted no new logical axiom -- the "
          "encoding and model evaluation disagree");
    }
    adapter->setAssumptions(NULL);

    if (uf.stats_flag && refinementRounds > 0)
      std::cerr << "Incremental: array refinement converged after "
                << refinementRounds << " rounds" << std::endl;
    if (impl->profile.enabled)
      impl->profile.refinementRounds += refinementRounds;

    const uint64_t newRefinementMass = impl->accountRefinementClauses(
        ordinaryOwner, refinementClausesBefore);
    uint64_t refinedNonStructuralMass =
        Impl::addMass(impl->permanentUnitMass, activationMass);
    refinedNonStructuralMass = Impl::addMass(
        refinedNonStructuralMass, impl->refinementMass(ordinaryOwner));
    impl->stageLiveConeMass(
        ordinaryCurrentRoots,
        Impl::addMass(ordinaryLiveMass, newRefinementMass),
        refinedNonStructuralMass);

    if (uf.stats_flag)
      impl->solver->printStats();

    if (res == SOLVER_UNSATISFIABLE)
      impl->recordUnsat(assumptions, assertionsSMT2.size(), false);

    // SOLVER_INVALID and SOLVER_SATISFIABLE (resp. VALID/UNSATISFIABLE)
    // are the same enum values, so this is already in check-sat terms.
    return res;
  }

  bm->GetRunTimes()->start(RunTimes::Solving);
  if (impl->profile.enabled)
    impl->profile.satCalls++;
  bool sat;
  {
    ScopedProfileTimer satTimer(impl->profile.enabled, impl->profile.satNs);
    ScopedProfileTimer initialSatTimer(impl->profile.enabled,
                                       impl->profile.initialSatNs);
    if (assumptions.size() == 0)
      sat = impl->solver->solve(bm->soft_timeout_expired);
    else
      sat = impl->solver->solveWithAssumptions(assumptions,
                                               bm->soft_timeout_expired);
  }
  bm->GetRunTimes()->stop(RunTimes::Solving);

  // No candidate leaves this route until every bit-vector abstraction in it
  // agrees with the operands it stands for. The refinement loops above reach
  // that through CallSAT_ResultCheck; this route never enters it, so the loop
  // is written out. It terminates because every round either rules out the
  // candidate it was shown -- each term family, congruence clause and
  // said-unequal equality round adds a clause that candidate violates -- or
  // strictly grows an equality's refined prefix, which its width bounds; a
  // ruled-out candidate never returns, and the solver's models are finite.
  // The working bounds per record: one round for a comparison, addition or
  // if-then-else, log2(width) for an equality, and the blocking allowance
  // plus one exact encoding for a multiplication, division or remainder --
  // whose enumeration, with the allowance set to zero, is instead bounded
  // by the operand pairs the search can propose.
  const uint64_t abstractionClausesBefore = impl->solver->submittedClauses();
  while (sat && !bm->soft_timeout_expired &&
         impl->refineAbstractions(*impl->solver) > 0)
  {
    bm->GetRunTimes()->start(RunTimes::Solving);
    if (impl->profile.enabled)
    {
      impl->profile.satCalls++;
      impl->profile.refinementSatCalls++;
      impl->profile.refinementRounds++;
    }
    {
      ScopedProfileTimer satTimer(impl->profile.enabled, impl->profile.satNs);
      ScopedProfileTimer refineSatTimer(impl->profile.enabled,
                                        impl->profile.refinementSatNs);
      if (assumptions.size() == 0)
        sat = impl->solver->solve(bm->soft_timeout_expired);
      else
        sat = impl->solver->solveWithAssumptions(assumptions,
                                                 bm->soft_timeout_expired);
    }
    bm->GetRunTimes()->stop(RunTimes::Solving);
  }

  // Say which budget stopped the search while the solver is still here to be
  // asked, the way the batch pipeline does in ToSATAIG::runSolver. The
  // SOLVER_TIMEOUT below is all that survives this frame, and it is the same
  // value a clock expiry returns, so a reason not taken here is one
  // (get-info :reason-unknown) can never give.
  if (bm->soft_timeout_expired)
    bm->noteBudgetExhausted(*impl->solver);

  // Whatever the loop pinned is part of what this stack costs from now on;
  // re-stage the mass over it, as the refinement branch above does for its
  // axioms.
  {
    const uint64_t pinnedMass = impl->accountRefinementClauses(
        ordinaryOwner, abstractionClausesBefore);
    if (pinnedMass > 0)
    {
      uint64_t nonStructuralMass =
          Impl::addMass(impl->permanentUnitMass, activationMass);
      nonStructuralMass = Impl::addMass(nonStructuralMass,
                                        impl->refinementMass(ordinaryOwner));
      impl->stageLiveConeMass(
          ordinaryCurrentRoots,
          Impl::addMass(ordinaryLiveMass, pinnedMass), nonStructuralMass);
    }
  }

  if (uf.stats_flag)
    impl->solver->printStats();

  if (bm->soft_timeout_expired)
    return SOLVER_TIMEOUT;

  if (!sat)
  {
    impl->recordUnsat(assumptions, assertionsSMT2.size(), false);
    return SOLVER_UNSATISFIABLE;
  }

  // resetSolver() clears the batch transformer's tables before every
  // check-sat.  Eager Ackermannisation does not need them for refinement,
  // but counterexample construction still uses the active read rows to
  // evaluate source-level READ terms.  A round whose encodings are all cache
  // hits otherwise leaves that table empty and can report an arbitrary array
  // value even though the reused SAT encoding has the right read symbol.
  // Materialise only after a satisfiable solve, and only when a model can be
  // observed; the table then also remains available to deferred get-model /
  // get-value construction.
  if (construct && activeHasArrays && uf.ackermannisation)
    impl->seedActiveReads(activeEncodedKeys);

  if (construct)
  {
    // Unless the model is read at solve time -- the self-check below is
    // such a reader -- construction is deferred to the first model query
    // and never happens for answers nobody samples. The SAT model this
    // materializes from stays live: the driver adds no clause and runs
    // no solve between user commands.
    if (!uf.check_counterexample_flag)
    {
      impl->modelPending = true;
      return SOLVER_SATISFIABLE;
    }

    bm->GetRunTimes()->start(RunTimes::CounterExampleGeneration);
    impl->ce->ClearCounterExampleMap();
    impl->ce->ClearComputeFormulaMap();

    impl->seedEliminatedIntoModelChannel();

    ToSATBase::ASTNodeToSATVar symbolMap;
    impl->buildSymbolMap(symbolMap);
    impl->ce->ConstructCounterExample(*impl->solver, symbolMap);
    bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);

    if (uf.check_counterexample_flag)
      impl->checkModelSatisfiesRawStack(assertionsSMT2);
  }

  return SOLVER_SATISFIABLE;
}

} // namespace stp

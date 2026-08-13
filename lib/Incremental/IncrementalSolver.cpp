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

// A plain-BV exact block is already fully encoded and has no theory model to
// refine. Solve it like the ordinary array-free driver: construct a model only
// when a caller can observe one, and defer that construction until its first
// reader unless --check-sanity needs it immediately. In particular, do not
// create the refinement adapter or force construct_counterexample_flag merely
// because cross-level preprocessing chose the exact-block representation.
SOLVER_RETURN_TYPE IncrementalSolver::Impl::solvePlainExactStack(
    const ASTVec& assertionsSMT2,
    const SATSolver::vec_literals& assumptions, const ASTNode& inputToSat,
    Aig_Obj_t* blockRegular)
{
  UserDefinedFlags& uf = bm->UserFlags;

  const bool construct = observableModelRequested(uf);
  uf.construct_counterexample_flag = construct;

  bm->GetRunTimes()->start(RunTimes::Solving);
  if (profile.enabled)
    profile.satCalls++;
  bool sat;
  {
    ScopedProfileTimer satTimer(profile.enabled, profile.satNs);
    ScopedProfileTimer initialSatTimer(profile.enabled, profile.initialSatNs);
    sat = solver->solveWithAssumptions(assumptions, bm->soft_timeout_expired);
  }
  bm->GetRunTimes()->stop(RunTimes::Solving);

  const uint64_t cheapLiveMass =
      addMass(baseLiveMass, clauseMassOf[inputToSat]);
  std::vector<Aig_Obj_t*> currentRoots(1, blockRegular);
  stageLiveConeMass(currentRoots, cheapLiveMass, permanentUnitMass);
  stageSemanticLiveStack(assertionsSMT2, ASTVec(1, inputToSat));

  if (uf.stats_flag)
    solver->printStats();

  if (bm->soft_timeout_expired)
    return SOLVER_TIMEOUT;

  if (!sat)
  {
    // The complete stack rode one assumption, so its core is deliberately
    // coarse even though this solve did not need the refinement adapter.
    recordUnsat(assumptions, assertionsSMT2.size(), true);
    return SOLVER_UNSATISFIABLE;
  }

  if (!construct)
    return SOLVER_SATISFIABLE;

  if (!uf.check_counterexample_flag)
  {
    modelPending = true;
    return SOLVER_SATISFIABLE;
  }

  bm->GetRunTimes()->start(RunTimes::CounterExampleGeneration);
  ce->ClearCounterExampleMap();
  ce->ClearComputeFormulaMap();
  seedEliminatedIntoModelChannel();
  // Eagerly instantiated array-equality rounds land here with lowered
  // floating-point terms in the block; model evaluation needs the context
  // that lowered them, exactly as the refinement paths wire it.
  if (fpCtx)
    ce->setFpEncodingContext(fpCtx.get());

  ToSATBase::ASTNodeToSATVar symbolMap;
  buildSymbolMap(symbolMap);
  ce->ConstructCounterExample(*solver, symbolMap);
  bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);

  checkModelSatisfiesRawStack(assertionsSMT2);

  return SOLVER_SATISFIABLE;
}

// Encode the complete active stack as one assumption-scoped block. Whole-array
// equality always needs this route: extensionality owns the complete array
// graph, so every active read must be lowered and checked together. Explicit
// first engagement can also use it for a plain-BV stack, but only after the
// whole-stack preprocessing trial has at least halved the DAG; that narrowly
// recovers cases where a deep fact collapses a huge shallow root before the
// ordinary per-level driver would encode it. Generated names and the block
// root are deterministic, so retained clauses remain reusable. A rejected BV
// trial returns before any clause or model definition is committed and the
// caller continues through the ordinary path.
SOLVER_RETURN_TYPE
IncrementalSolver::Impl::exactStackCheckSat(
    const ASTVec& assertionsSMT2, bool firstForcedIncrementalSolve,
    bool requireScopedCollapse, bool* scopedAccepted)
{
  UserDefinedFlags& uf = bm->UserFlags;

  bool arrayEqualityRound = false;
  bool activeHasFp = false;
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    const Fragment& f = fragment(levelConjunction);
    arrayEqualityRound = arrayEqualityRound || f.arrayEq;
    activeHasFp = activeHasFp || f.fp;
  }
  profile.extensionality = arrayEqualityRound;
  ScopedProfileTimer extensionalityTimer(
      profile.enabled && arrayEqualityRound, profile.extensionalityNs);

  // Eager Ackermannization expands reads into if-then-else chains,
  // destroying the array structure the lazy procedure works on. As in the
  // batch pipeline, active equalities over plain bit-vector sorts are
  // instantiated pointwise over the solve's access indexes (below, once
  // the records are conjoined) and the round stays on the caller's eager
  // path; quotiented floating-point cells have no sound pointwise bit
  // instantiation and fall back to lemmas on demand for this round, with
  // the flag disabled and the batch pipeline's warning.
  const bool savedAck = uf.ackermannisation;

  ASTNode activeConjunction;
  if (assertionsSMT2.size() > 1)
    activeConjunction = bm->CreateNode(AND, assertionsSMT2);
  else
    activeConjunction = assertionsSMT2[0];

  // Plain-BV exact blocks have no extensionality state at all. Avoid creating
  // a context for them; besides the allocation, an empty context makes this
  // representation look needlessly like a theory-refinement solve.
  ExtensionalityContext* ext = NULL;
  if (arrayEqualityRound)
  {
    ext = bm->getExtensionality();
    ext->beginSolve();
  }

  ASTNodeMap arrayEqualityRewrites;
  ASTNode prepared = activeConjunction;
  if (activeHasFp)
  {
    prepared = fpContext()->prepare(prepared);
    fpContext()->copyArrayEqualityRewrites(arrayEqualityRewrites);
  }

  ASTNode semantic = prepared;
  if (arrayEqualityRound)
    semantic =
        ext->lowerArrayEqualities(prepared, arrayEqualityRewrites);
  ASTNode inputToSat = semantic;

  bool extActive = arrayEqualityRound && ext->active();
  // Releases the record-table seal on every exit from this function.
  ExtensionalityContext::SolveScope extScope(ext);

  if (extActive)
    inputToSat = ext->conjoinRecordConstraints(inputToSat);

  if (extActive && uf.ackermannisation)
  {
    const ASTNode eager = ext->instantiateEagerAckermann(inputToSat);
    if (!eager.IsNull())
    {
      // The equalities are now ordinary conjuncts of the block and the
      // records are retired: the round continues exactly as an eager
      // array round, reads expanded through the transform below, nothing
      // left for the lazy checker.
      inputToSat = eager;
      extActive = false;
      bm->ASTNodeStats("after eager equality instantiation: ", inputToSat);
    }
    else
    {
      std::cerr << "Warning: --ackermanize is disabled for queries with "
                   "array equality over floating-point sorts."
                << std::endl;
      uf.ackermannisation = false;
    }
  }

  // Automatic engagement already received two batch-preprocessed solves, so
  // its first persistent exact-stack block keeps the raw search shape and a
  // genuinely new later stack takes this pass. Explicit first engagement has
  // no such batch work to fall back on: preprocess its first block too, which
  // removes the broad forced-first ABV tail. The decision is fixed per raw
  // active conjunction above, so a repeated or re-pushed stack never flips
  // encoding strategy underneath the block cache.
  bool scopedPreprocess = false;
  if (policy.semanticPreprocessing())
    scopedPreprocess =
        exactScopedPreprocessOf
            .insert(std::make_pair(activeConjunction,
                                   engagedSolves > 1 ||
                                       firstForcedIncrementalSolve))
            .first->second;
  PreprocessingTransaction stackTransaction(PreprocessingMode::ExactStack,
                                             inputToSat);
  stackTransaction.conjuncts.push_back(inputToSat);
  if (scopedPreprocess)
  {
    stackTransaction =
        preprocessExactStackBlock(inputToSat, requireScopedCollapse);
    inputToSat = stackTransaction.conjuncts.front();
    if (!stackTransaction.accepted)
    {
      if (profile.enabled)
        profile.firstStackRejected++;
      exactScopedPreprocessOf.erase(activeConjunction);
      uf.ackermannisation = savedAck;
      if (scopedAccepted != NULL)
        *scopedAccepted = false;
      return SOLVER_UNDECIDED;
    }
    if (profile.enabled)
    {
      const size_t eliminated = stackTransaction.eliminatedSymbolCount();
      if (requireScopedCollapse)
      {
        profile.firstStackPreprocesses++;
        profile.firstStackEliminations += eliminated;
      }
      else
      {
        profile.extPreprocesses++;
        profile.extEliminations += eliminated;
      }
    }
  }

  if (scopedAccepted != NULL)
    *scopedAccepted = true;

  // Formula output and eliminated-definition replay become active together.
  // A rejected speculative block returned above without committing either.
  scopes.commitWholeStack(stackTransaction);

  if (activeHasFp)
    inputToSat = fpContext()->lowerPrepared(inputToSat);

  const bool extPrepared = extActive && !inputToSat.isConstant();
  if (extPrepared)
    inputToSat = ext->prepare(inputToSat);

  exactStackKeepAlive.insert(activeConjunction);
  exactStackKeepAlive.insert(prepared);
  exactStackKeepAlive.insert(semantic);
  exactStackKeepAlive.insert(inputToSat);
  chargeSemanticRoot(activeConjunction);
  chargeSemanticRoot(prepared);
  chargeSemanticRoot(semantic);
  chargeSemanticRoot(inputToSat);

  if (uf.enable_array_equality && containsArrayEquality(inputToSat))
    FatalError("IncrementalSolver: an opaque array equality reached the "
               "final array transformation boundary",
               inputToSat);

  // A fresh per-round registry: the whole-graph transform must neither see
  // the persistent lazy rows (it refuses reused legacy rows) nor leak its
  // own solve-local rows into them. The rows are left in place afterwards
  // -- model construction reads them -- until the next solve or pop clears
  // the batch tables as usual.
  batchAT->arrayToIndexToRead.clear();
  batchAT->ack_pair.clear();

  const bool arrayops = containsArrayOps(inputToSat, bm) || extActive;
  if (arrayops)
    inputToSat = batchAT->TransformFormula_TopLevel(inputToSat);
  if (extPrepared)
    ext->bindAfterTransform(batchAT);

  // Encode the block; its root is assumed, never asserted -- the block
  // spans every level, including the base. Every generated symbol in the
  // block (witnesses, scalar names, read abstractions) is named
  // deterministically by what it stands for, so an identical stack lowers
  // to the identical node and this cache hit makes the repeat round's
  // encoding free -- and the recycled names keep previously encoded
  // checker lemmas attached to the right SAT variables.
  // The block encodes the RAW stack -- the base's defining equations
  // included -- so it can mint bits for variables sigma0 eliminated. Those
  // equations hold inside the block only under its retractable literal; a
  // later ordinary round would read the then-unconstrained bits into
  // models and into the refinement loop's raw-stack evaluation. Restore
  // them as permanent units first (see restoreDroppedSigma0) -- always
  // sound, since the base only grows.
  restoreDroppedSigma0(inputToSat);

  int blockLit;
  Aig_Obj_t* blockRegular = NULL;
  bool blockReused = false;
  {
    NodeToLitMap::const_iterator hit = rootLitOf.find(inputToSat);
    if (hit != rootLitOf.end())
    {
      if (profile.enabled)
        profile.rootHits++;
      blockLit = hit->second;
      blockReused = true;
      blockRegular = aigRoot(inputToSat);
    }
    else
    {
      if (profile.enabled)
        profile.rootMisses++;
      ScopedProfileTimer encodingTimer(profile.enabled, profile.encodeNs);
      const uint64_t submittedBefore = solver->submittedClauses();
      bm->GetRunTimes()->start(RunTimes::BitBlasting);
      BBNodeAIG root = encoding.blaster().BBForm(inputToSat);
      bm->GetRunTimes()->stop(RunTimes::BitBlasting);
      bm->GetRunTimes()->start(RunTimes::CNFConversion);
      blockRegular = Aig_Regular(root.n);
      ensureEncoded(blockRegular);
      blockLit =
          2 * varOfAig(blockRegular) + (Aig_IsComplement(root.n) ? 1 : 0);
      bm->GetRunTimes()->stop(RunTimes::CNFConversion);
      rootLitOf[inputToSat] = blockLit;
      aigRootOf[inputToSat] = blockRegular;
      clauseMassOf[inputToSat] =
          solver->submittedClauses() - submittedBefore;
    }
  }
  assert(blockRegular != NULL);

  // Refinement lemmas are encoded over the abstraction/witness/scalar
  // names; give every bit of every such symbol a variable before the
  // first solve, fresh and unconstrained where the blasted block never
  // needed it -- the meaning ToSATAIG's lemma-only path assigns.
  if (extActive)
  {
    for (const ASTNode& s : ext->getFrozenSymbols())
      totalizeSymbol(s);
    for (const ASTNode& s : ext->getLemmaOnlySymbols())
      totalizeSymbol(s);
  }

  if (uf.stats_flag)
  {
    std::cerr << "Incremental: "
              << (arrayEqualityRound ? "array-equality" : "first scoped BV")
              << " round, block of "
              << assertionsSMT2.size() << " levels "
              << (blockReused ? "reused" : "encoded") << ", solver has "
              << solver->nVars() << " variables" << std::endl;
  }

  applySolveBudgets(*solver, uf);
  bm->soft_timeout_expired = false;

  SATSolver::vec_literals assumptions;
  if (policy.retractionSearchHints())
    everAssumedLits[blockLit] = engagedSolves;
  assumptions.push(SATSolver::mkLit(blockLit >> 1, blockLit & 1));
  hintRetractedLevels(assumptions);
  if (profile.enabled)
  {
    profile.activeKeys = 1;
    profile.assumptions = assumptions.size();
  }

  // An array-equality round whose equalities were eagerly instantiated --
  // or simplified away before lowering -- while --ackermanize remains in
  // force has been compiled onto the ordinary eager path: reads expanded
  // by the transform above, nothing for the lazy checker or read
  // refinement to do. Solve it like the plain block it now is.
  if (!arrayEqualityRound || (uf.ackermannisation && !extActive))
    return solvePlainExactStack(assertionsSMT2, assumptions, inputToSat,
                                blockRegular);

  // Array equality needs a candidate model on every refinement round. Keep
  // that internal requirement distinct from whether this query's caller is
  // entitled to observe the resulting model. In particular, the incoming
  // derived flag may still describe an earlier query (and is false before a
  // session's first query), so restoring it would lose :produce-models.
  const bool constructForCaller = observableModelRequested(uf);
  uf.construct_counterexample_flag = true;

  if (fpCtx)
    ce->setFpEncodingContext(fpCtx.get());

  seedEliminatedIntoModelChannel();

  IncrementalToSAT* tosat = static_cast<IncrementalToSAT*>(ensureAdapter());
  tosat->setAssumptions(&assumptions);

  // Congruence axioms are encoded straight over the bit variables of the
  // round registry's read symbols, and the block's cone may have needed
  // only some of a symbol's bits (the frozen/lemma-only totalisation
  // above covers the checker's symbols, not the registry rows). This
  // matters most for the hybrid below: a round routed here for an array
  // equality that simplified away runs ordinary read refinement with the
  // checker inactive.
  totalizeBatchRegistrySymbols();
  ArrayReadRefinementProgress readRefinementProgress;

  const uint64_t refinementClausesBefore = solver->submittedClauses();
  ScopedProfileTimer refinementTimer(profile.enabled, profile.refinementNs);
  SOLVER_RETURN_TYPE res = ce->CallSAT_ResultCheck(
      *solver, bm->ASTTrue, semantic, prepared, tosat, true);

  // The refinement driver, as in TopLevelSTPAux: with an active equality
  // the checker owns every read, so each undecided candidate must carry a
  // pending theory lemma; without one, ordinary read refinement runs.
  size_t refinementRounds = 0;
  while (res == SOLVER_UNDECIDED)
  {
    refinementRounds++;
    // Re-totalize: the checker's lemma encodings can introduce new reads,
    // whose rows joined the table after the pass above. Memoised, so a
    // round that added nothing pays nothing.
    totalizeBatchRegistrySymbols();
    if (extActive)
    {
      if (!ext->hasPendingLemma())
        FatalError("IncrementalSolver: an active array-equality refinement "
                   "round has neither a decision nor a pending lemma");
      ext->encodePendingLemmas(*solver, tosat);
      res = ce->CallSAT_ResultCheck(*solver, bm->ASTTrue, semantic, prepared,
                                    tosat, true);
    }
    else
    {
      // The hybrid case: routed here for an array equality that simplified
      // away, so ordinary read refinement runs.
      res = runGuardedReadRefinementRound(
          semantic, tosat, readRefinementProgress,
          "IncrementalSolver: an array-equality round fell back to "
          "read refinement, rejected the candidate and emitted no "
          "new logical axiom -- the encoding and model evaluation "
          "disagree");
    }
  }

  tosat->setAssumptions(NULL);
  uf.ackermannisation = savedAck;
  uf.construct_counterexample_flag = constructForCaller;

  if (uf.stats_flag && refinementRounds > 0)
    std::cerr << "Incremental: array-equality refinement converged after "
              << refinementRounds << " rounds" << std::endl;
  if (profile.enabled)
    profile.refinementRounds += refinementRounds;

  accountRefinementClauses(inputToSat, refinementClausesBefore);
  const uint64_t theoryMass = refinementMass(inputToSat);
  uint64_t cheapLiveMass = addMass(baseLiveMass, clauseMassOf[inputToSat]);
  cheapLiveMass = addMass(cheapLiveMass, theoryMass);
  std::vector<Aig_Obj_t*> currentRoots(1, blockRegular);
  stageLiveConeMass(currentRoots, cheapLiveMass,
                    addMass(permanentUnitMass, theoryMass));
  stageSemanticLiveStack(assertionsSMT2, ASTVec(1, inputToSat));

  // The whole round rode one block literal, so an unsat answer has no
  // per-level or per-assumption granularity: the core is everything.
  if (res == SOLVER_UNSATISFIABLE)
    recordUnsat(assumptions, assertionsSMT2.size(), true);

  return res;
}

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
    if (impl->myReads.find(it->first.first) != impl->myReads.end() &&
        impl->myReads.find(it->first.first)
                ->second.find(it->first.second) !=
            impl->myReads.find(it->first.first)->second.end())
      out.push_back(it->first);
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
  for (ArrayTransformer::ArrType::const_iterator it = impl->myReads.begin();
       it != impl->myReads.end(); ++it)
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
  impl->beginProfile(assertionsSMT2.size());
  const SOLVER_RETURN_TYPE result = checkSatBody(
      assertionsSMT2, assumeLastLevelPerConjunct, firstForcedIncrementalSolve);
  impl->finishProfile();
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
  if (impl->fpCtx)
    impl->ce->setFpEncodingContext(impl->fpCtx.get());

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

  impl->currentLiveClauseMass = 0;

  // The unsat story is per solve; a stale one must not answer for this
  // call.
  impl->lastUnsat = false;
  impl->lastUnsatCoarse = false;
  impl->lastLevelIndividual = false;
  impl->modelPending = false;
  impl->assumedLitLevels.clear();
  impl->lastLevelLitConjuncts.clear();
  impl->lastFailedLits.clear();
  // Scope reconciliation below can change the eliminated-variable filter
  // the adapter's cached symbol map was built under.
  impl->symbolMapCacheValid = false;
  {
    ScopedProfileTimer maintenanceTimer(impl->profile.enabled,
                                        impl->profile.maintenanceNs);

    // Promoted-prefix bookkeeping first: if a promoted level changed or
    // vanished, its units no longer describe the stack and the solver
    // restarts here, before any routing can touch it.
    impl->updateStackStability(assertionsSMT2);

    // The relief valve: once the solver is past the configured size and most
    // of its encodings belong to content no longer on the stack, start it
    // over from the live stack. Checked before routing so extensionality
    // rounds benefit too. Deadness is measured by CLAUSE MASS against the
    // peak live mass any solve has used since the last rebuild -- conjunct
    // counts, the original proxy, missed variant-push sessions whose few
    // dozen distinct conjuncts each carry a huge circuit (a million
    // variables of ~95% popped content never tripped the count ratio) --
    // and comparing with the PEAK is the hysteresis: after a rebuild the
    // tracked mass restarts at the working set, so firing again takes
    // another fourfold growth.
    if (impl->clauseReliefSizeReached() && impl->reliefRatioReached())
      impl->expandPendingLiveConeMass();

    const bool clauseRelief =
        impl->clauseReliefSizeReached() && impl->reliefRatioReached();
    // Semantic caches have an independent DAG-node floor. Their cheap charge
    // only stages the decision; semanticReliefReached walks exact retained
    // and live unions, so a monotonically growing stack whose snapshots share
    // almost everything is not mistaken for dead churn.
    const bool semanticRelief = impl->semanticReliefReached();
    if (clauseRelief || semanticRelief)
    {
      if (uf.stats_flag)
        std::cerr << "Incremental: re-encoded from scratch (solver had "
                  << impl->solver->nVars() << " variables, "
                  << impl->retainedClauseMass()
                  << " retained clauses for a "
                  << impl->maxLiveClauseMass << " clause working set, "
                  << impl->lastRetainedSemanticNodes
                  << " retained semantic DAG nodes for a "
                  << impl->maxLiveSemanticNodes << " node working set)"
                  << std::endl;
      impl->rebuildEncodings(assertionsSMT2, Impl::RebuildReason::Relief);
    }

    // Probe-based inprocessing is the opposite trade to the valve above:
    // it re-runs over the WHOLE persistent encoding at every solve, so on
    // many-solve sessions its recurring cost dominates what it earns
    // (measured 2x of the total runtime on generated variant-push
    // corpora), while a session that is one or two big searches genuinely
    // profits from it. The option is configuration-window-only, so
    // retirement -- once the session qualifies, or immediately under an
    // explicit 'off' -- means one bounded rebuild onto a fresh solver
    // configured without it. AUTO additionally requires a base which has
    // stayed fixed throughout the observation window: new permanent clauses
    // give inprocessing new work, and disabling elimination on that shape
    // made later VexRiscv proofs time out. Trail reuse must also have been
    // retired already: a session still riding the trail is the
    // many-small-queries shape whose accumulated search state a rebuild
    // would throw away for a technique that measured neutral there. The
    // capability is probed without touching the live solver, and a backend
    // that cannot control it simply never retires.
    // A frontend may claim a forced FIRST solve only before this driver has
    // engaged at all: four preprocessing policies below read that claim and
    // would otherwise apply to a solve that DID have batch-preprocessed
    // predecessors. The driver cannot derive the fact -- it is a session
    // fact, not an object one -- but it can check the one direction that
    // must hold, which is exactly the mis-plumbing a new frontend would
    // introduce by passing its forced flag and forgetting the ordinal.
    assert((!firstForcedIncrementalSolve || impl->engagedSolves == 0) &&
           "a forced first solve was claimed after the driver had engaged");
    impl->engagedSolves++;
    if (!impl->inprobingRetired &&
        ((uf.incremental_inprobing == UserDefinedFlags::BVAMode::OFF &&
          impl->solver->supportsInprobingControl()) ||
         (impl->inprobingRetirementEarned() && !impl->trailReuseAllowed)))
    {
      impl->inprobingRetired = true;
      if (uf.stats_flag)
        std::cerr << "Incremental: inprobing retired (" << impl->engagedSolves
                  << " solves), solver restarted without it" << std::endl;
      impl->rebuildEncodings(assertionsSMT2, Impl::RebuildReason::Inprobing);
    }

    // Early FP is still strong evidence to start without trail reuse. The
    // ambiguous late-transition policy is specific to source array+FP
    // sessions: observe up to three FP checks before classifying one, then
    // retire a still-small state or let a growing state reach the existing
    // inprobing boundary so both configuration changes cost one rebuild.
    // Array-free QF_BVFP retains its established trail; applying the array
    // policy there lost five measured solves. Arrays introduced internally by
    // FP totalisation do not change that classification. Refinement-heavy
    // array state gets the old size belt instead.
    if (impl->policy.adaptiveBackendConfiguration() &&
        impl->trailReuseAllowed)
    {
      bool retire = impl->solver->nVars() >= Impl::trailReuseVarLimit;
      bool hasFp = false;
      for (size_t i = 0; !hasFp && i < assertionsSMT2.size(); i++)
        hasFp = impl->fragment(assertionsSMT2[i]).fp;
      if (!retire && hasFp)
      {
        const bool earlyFp =
            impl->engagedSolves < Impl::trailReuseFpRetireSolves;
        const bool refinementHeavy =
            impl->currentRefinementClauseMass >=
            Impl::trailReuseRefinementClauseFloor;
        const bool canRetireInprobingWithTrail =
            impl->inprobingRetirementEarned();
        const bool smallLateFpState =
            impl->lateArrayFpSolvesWithTrail >=
                Impl::trailReuseLateArrayFpProbeSolves &&
            impl->solver->nVars() < Impl::trailReuseEstablishedVarFloor;

        retire = earlyFp ||
                 (impl->sourceArraysSeen && !refinementHeavy &&
                  (canRetireInprobingWithTrail || smallLateFpState));
        if (!retire && impl->sourceArraysSeen)
          impl->lateArrayFpSolvesWithTrail++;
      }
      if (retire)
      {
        impl->trailReuseAllowed = false;
        if (uf.stats_flag)
          std::cerr << "Incremental: trail reuse retired ("
                    << impl->solver->nVars()
                    << " variables after " << impl->engagedSolves
                    << " solves), solver restarted without it" << std::endl;
        // If the session already qualifies for inprobing retirement --
        // whose AUTO gate waits for exactly this trail retirement -- take
        // both in ONE rebuild. Left to its own block, the retirement
        // would fire on the NEXT solve and rebuild a freshly re-encoded
        // solver all over again; a session whose trail died at fifty
        // thousand variables measured 2x slower from that double rebuild.
        if (!impl->inprobingRetired && impl->inprobingRetirementEarned())
        {
          impl->inprobingRetired = true;
          if (uf.stats_flag)
            std::cerr << "Incremental: inprobing retired with it ("
                      << impl->engagedSolves << " solves)" << std::endl;
        }
        impl->rebuildEncodings(assertionsSMT2, Impl::RebuildReason::Trail);
      }
    }

    // The backend's configuration window closes at its first clause; take
    // the bounded-variable-addition decision while it is still open. This
    // must precede the extensionality routing below: an equality round
    // encodes into the same persistent solver.
    impl->decideBVA(assertionsSMT2);

    // Retire stale retraction bookkeeping here, inside the maintenance block,
    // rather than after the routing below: an all-array-equality session
    // returns through the extensionality path and never reached it, so its
    // hint list grew one entry per distinct block root for the life of the
    // epoch and every solve hinted all of them. The precondition is the
    // configuration window, which decideBVA has just closed -- the pins are
    // clauses.
    if (impl->policy.aggregateLevelAssumptions())
      impl->retireStaleActivation();
  }

  // Whole-array equality routes the entire check-sat through the
  // extensionality block: the procedure owns the round's complete array
  // graph, so no conjunct may be encoded separately this round. New
  // base-level conjuncts stay out of level0Asserted and simply become
  // permanent units in a later equality-free round; this round the block
  // covers them.
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    if (impl->fragment(levelConjunction).arrayEq)
      return impl->exactStackCheckSat(assertionsSMT2,
                                      firstForcedIncrementalSolve);
  }

  // Explicit first engagement has no earlier batch solve to collapse facts
  // across level boundaries. Try the same exact-stack preprocessing used by
  // array-equality blocks for a plain-BV stack, but adopt it only when the
  // complete DAG at least halves. This catches the CPAchecker shape where a
  // deep unit makes a huge shallow disjunction trivial; modest rewrites fall
  // through to the ordinary per-level driver, preserving its reusable roots
  // and search shape. check-sat-assuming stays per-conjunct so its failed
  // assumptions remain reportable. An explicitly aggressive relief threshold
  // also keeps ordinary ownership from the outset; a provisional block would
  // otherwise hide the live-root accounting that configuration asks to use.
  const bool provisionalBlockAllowed =
      uf.incremental_reencode_limit == 0 ||
      uf.incremental_reencode_limit >= Impl::firstStackMinReencodeLimit;
  if (impl->policy.firstSolveShortcuts() && firstForcedIncrementalSolve &&
      !assumeLastLevelPerConjunct &&
      provisionalBlockAllowed && assertionsSMT2.size() > 1)
  {
    bool plainBv = true;
    for (const ASTNode& levelConjunction : assertionsSMT2)
    {
      const Fragment& f = impl->fragment(levelConjunction);
      if (f.arrays || f.arrayEq || f.fp)
      {
        plainBv = false;
        break;
      }
    }
    if (plainBv)
    {
      bool accepted = false;
      const SOLVER_RETURN_TYPE result =
          impl->exactStackCheckSat(assertionsSMT2,
                                   firstForcedIncrementalSolve, true,
                                   &accepted);
      if (accepted)
        return result;
    }
  }

  // No active equality this round, so no stale equality state may survive
  // into it: the consistency checker keys off ext->active(), and a
  // previous round's solve-local records would send this round's model to
  // a checker expecting values for symbols it never encoded. The SMT-LIB2
  // pop clears this itself, but the C API's vc_pop deliberately clears
  // nothing (its model outlives the bracket), and check-sat-assuming's
  // frame pop keeps the model too -- so the round boundary is here.
  ExtensionalityContext* staleExt = bm->getExtensionalityIfAny();
  if (staleExt != NULL && staleExt->active())
    staleExt->beginSolve();

  const uint64_t clausesBefore = impl->lifetimeClauseSubmissions();
  impl->encodesThisCall = 0;

  ProfileClock::time_point semanticStarted;
  if (impl->profile.enabled)
    semanticStarted = ProfileClock::now();

  // Constant-bit propagation state persists across calls. A pop, changed
  // level, or base growth rolls the engine and caller overlay back to their
  // longest common prefix; the diagnostic reset mode rebuilds that prefix
  // instead. The rewrite/fact memo has its own matching-prefix watermark
  // (see cbpFeedLevel/cbpAdopt and IncrementalScopeState::CbpMemo).
  bool cbpBootstrapDeferred = false;
  if (impl->policy.crossLevelPropagation())
  {
    ScopedProfileTimer cbpTimer(impl->profile.enabled, impl->profile.cbpNs);
    ScopedProfileTimer syncTimer(impl->profile.enabled,
                                 impl->profile.cbpSyncNs);

    // A forced first solve has no CBP prefix to reuse yet. Building a large
    // engine for that one solve was the dominant remaining cost on the
    // CPAchecker QF_BV first-check family, usually with no adoption at all.
    // Leave the engine genuinely empty for this call; if another real solve
    // follows, its ordinary prefix feed builds the complete current state.
    // Automatic sessions never request this flag: it specifically identifies
    // a first solve forced through the driver by explicit --incremental.
    const int64_t configuredBootstrapLimit =
        uf.incremental_cbp_bootstrap_limit;
    if (firstForcedIncrementalSolve && configuredBootstrapLimit > 0 &&
        uf.optimize_flag && uf.bitConstantProp_flag &&
        assertionsSMT2.size() > 1 && impl->scopes.cbpFedDepth() == 0 &&
        impl->scopes.cbpMemoDepth() == 0)
    {
      const size_t limit =
          clampToSize(static_cast<uint64_t>(configuredBootstrapLimit));
      cbpBootstrapDeferred = impl->cbpStackExceeds(assertionsSMT2, limit);
      if (cbpBootstrapDeferred)
      {
        if (impl->profile.enabled)
          impl->profile.cbpBootstrapDeferred++;
        if (uf.stats_flag)
          std::cerr << "Incremental: deferred large first-solve cbp "
                       "bootstrap"
                    << std::endl;
      }
    }

    const size_t lcp = impl->scopes.cbpFedCommonPrefix();
    if (impl->profile.enabled)
      impl->profile.stablePrefix = lcp;
    const bool diverged = lcp < impl->scopes.cbpFedDepth();
    if (diverged)
    {
      if (impl->profile.enabled)
        impl->profile.cbpDivergences++;
      // Futility accounting: an epoch (the span since the last
      // divergence) that adopted nothing lengthens the barren run;
      // one fresh adoption clears it.
      if (impl->cbpEpochAdopted == 0)
      {
        impl->cbpBarrenDivergences++;
        const size_t leash = impl->cbpEverFixed
                                 ? Impl::cbpRetireBarrenFixed
                                 : Impl::cbpRetireBarrenNeverFixed;
        if (!impl->cbpSessionRetired && impl->cbpBarrenDivergences >= leash)
        {
          impl->cbpSessionRetired = true;
          if (uf.stats_flag)
            std::cerr << "Incremental: cbp retired for the session ("
                      << impl->cbpBarrenDivergences
                      << " adoption-free stack divergences)" << std::endl;
        }
      }
      else
      {
        impl->cbpBarrenDivergences = 0;
      }
      impl->cbpEpochAdopted = 0;

      const size_t fedLevelsBefore = impl->scopes.cbpFedDepth();
      const bool aligned =
          impl->callCbp.get() != NULL &&
          impl->callCbp->levelCount() == fedLevelsBefore &&
          impl->cbpCallerCheckpoints.size() == fedLevelsBefore &&
          !impl->cbpCallerLevelOpen && impl->callCbpDeferred.empty();
      const bool useRollback =
          !impl->cbpSessionRetired && !uf.incremental_cbp_reset && aligned;
      if (useRollback)
      {
        ScopedProfileTimer rollbackTimer(impl->profile.enabled,
                                         impl->profile.cbpRollbackNs);
        const IncrementalCBP::RollbackStats stats =
            impl->callCbp->rollbackTo(lcp);
        const size_t callerEntries = impl->cbpRollbackCallerTo(lcp);
        assert(stats.levels == fedLevelsBefore - lcp);
        assert(impl->callCbp->levelCount() == lcp);
        assert(impl->cbpCallerCheckpoints.size() == lcp);
        assert(impl->scopes.cbpFedDepth() == lcp);
        if (impl->profile.enabled)
        {
          impl->profile.cbpRollbacks++;
          impl->profile.cbpRolledLevels += stats.levels;
          impl->profile.cbpRollbackFixed += stats.fixedStates;
          impl->profile.cbpRollbackCreated += stats.createdFixedStates;
          impl->profile.cbpRollbackDependencies += stats.dependencyNodes;
          impl->profile.cbpRollbackMultiplications +=
              stats.multiplicationStates;
          impl->profile.cbpRollbackCallerEntries += callerEntries;
        }
      }
      else
      {
        ScopedProfileTimer resetTimer(impl->profile.enabled,
                                      impl->profile.cbpResetNs);
        if (impl->profile.enabled)
          impl->profile.cbpResets++;
        impl->cbpReset();
      }
    }

    impl->cbpMemoStable = impl->scopes.trimCbpMemoToCurrent();
  }
  else
  {
    impl->cbpMemoStable = 0;
    if (impl->profile.enabled)
      impl->profile.stablePrefix = impl->scopes.lastCommonPrefix();
  }
  impl->callCbpAdopted = 0;
  impl->callCbpReplayed = 0;
  impl->callCbpOff = !impl->policy.crossLevelPropagation() ||
                     impl->cbpSessionRetired || cbpBootstrapDeferred ||
                     impl->cbpOverFeedCap();
  impl->callCbpConflict = false;

  // Base level: every conjunct becomes a permanent unit clause, once. The
  // base level only grows (reset destroys this object), so this is monotone
  // and sound even though the level's conjunction node is re-collapsed --
  // and possibly re-simplified -- on every call.
  // A rebuild left the re-simplified base waiting for this point: the
  // backend's configuration window is decided and equality-free rounds
  // reach here, so the replacements encode as this round's units.
  // (level0Asserted kept the RAW keys, so the loop below skips them.)
  if (!impl->pendingRebuiltBase.empty())
  {
    for (const ASTNode& c : impl->pendingRebuiltBase)
    {
      const int lit = impl->rootLit(c);
      SATSolver::vec_literals unit;
      unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
      impl->addClause(unit);
      impl->baseLiveMass = Impl::addMass(
          impl->baseLiveMass, Impl::addMass(impl->clauseMassOf[c], 1));
      impl->recordPermanentRoot(c);
    }
    impl->pendingRebuiltBase.clear();
  }

  ASTVec conjuncts;
  splitConjuncts(assertionsSMT2[0], bm->ASTTrue, conjuncts);

  ASTVec newLevel0;
  for (const ASTNode& c : conjuncts)
  {
    if (!impl->level0Asserted.insert(c).second)
      continue;
    impl->pendingBaseSeed.push_back(c);
    newLevel0.push_back(c);
    // New content first invalidates any cached level whose elimination it
    // contradicts, and joins the base symbol set the privacy check
    // consults -- both before anything is harvested or encoded.
    if (impl->policy.semanticPreprocessing())
    {
      ScopedProfileTimer screenTimer(impl->profile.enabled,
                                     impl->profile.screenNs);
      impl->screenNewContent(c);
    }
    if (impl->policy.semanticPreprocessing())
    {
      const ASTNodeSet& syms = impl->symbolsOf(c);
      impl->baseSymbols.insert(syms.begin(), syms.end());
      if (uf.optimize_flag)
        impl->harvestSigma0(c);
    }
  }

  if (impl->policy.firstSolveShortcuts() && firstForcedIncrementalSolve &&
      assertionsSMT2.size() == 1 &&
      !newLevel0.empty())
  {
    ASTVec reducedBase;
    if (impl->preprocessForcedFirstBase(newLevel0, reducedBase))
      newLevel0.swap(reducedBase);
  }

  for (const ASTNode& c : newLevel0)
  {
    const int lit = impl->rootLit(c);
    SATSolver::vec_literals unit;
    unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
    impl->addClause(unit);
    impl->baseLiveMass = Impl::addMass(
        impl->baseLiveMass, Impl::addMass(impl->clauseMassOf[c], 1));
    impl->recordPermanentRoot(c);
  }

  // Screening must see the WHOLE stack's new raw content before any level
  // is prepared or encoded: a later level's mention of a variable an
  // earlier level's cached preparation eliminated invalidates that cache
  // entry now, not after the stale entry was already used.
  if (impl->policy.semanticPreprocessing())
  {
    ScopedProfileTimer screenTimer(impl->profile.enabled,
                                   impl->profile.screenNs);
    for (size_t level = 1; level < assertionsSMT2.size(); level++)
      impl->screenNewContent(assertionsSMT2[level]);
  }

  // The base level seeds the constant-bit engine: its conjuncts are
  // permanent units, so their truth is sound for every fact any
  // deeper level draws from them. The base itself never adopts (it is
  // already encoded), so its parked fixings flush straight back --
  // and with no pushed level in the stack there is no adopter at all,
  // so a session that never pushes never pays for the feed (a huge
  // single-check formula measured two minutes of fixpoint and harvest
  // with nothing downstream to spend it on).
  if (impl->policy.crossLevelPropagation() && uf.optimize_flag &&
      uf.bitConstantProp_flag && assertionsSMT2.size() > 1)
  {
    impl->cbpFeedLevel(0, assertionsSMT2[0]);
    impl->cbpFinishLevel();
  }

  // Pushed levels: each is prepared in pieces -- substituted under the
  // context, run through the batch equality-propagation and
  // simplification passes, private definitions eliminated and everything
  // else re-conjoined (see PreparedPiece) -- then encoded against the
  // epoch-persistent caches and assumed through one literal per level. The
  // assumption set is recomputed from the current stack on every call,
  // so popped levels vanish by simply no longer being here.
  SATSolver::vec_literals assumptions;
  std::vector<int> levelRoots;
  // The context carries only RETRACTABLE definitions -- harvested from
  // the live pushed levels this call, plus this call's eliminations --
  // and is part of every piece's cache key. sigma0 is deliberately NOT
  // here: it is applied inside the (cached) preparation, where its
  // permanence makes staleness sound, so base growth never churns the
  // piece cache.
  // The pushed-definition context accumulates BY LEVEL PREFIX: before a
  // level is prepared, its own raw definitions join the map, so level L
  // is substituted under the definitions of levels 1..L -- uniformly
  // with every level below it (shared subterms keep rewriting
  // identically, and a definition reaches its same-level uses), but
  // NEVER under deeper levels' definitions. That last part is what keeps
  // a conjunct's substituted form STABLE as the stack grows underneath
  // it: a whole-stack map changed shallow conjuncts on every deepening,
  // so one semantic array read took a fresh syntactic index per query
  // and the refinement loop drowned in aliased read pairs (measured as
  // entire check-sats spent inside SATBased_ArrayReadRefinement).
  ASTNodeMap ctx;
  ASTNodeSet ctxSources;
  bool ctxHasFp = false;
  // Pinning facts emitted by CBP are real, scoped conjuncts.  Their symbols
  // must participate in private-definition decisions just like symbols in
  // the raw assertion stack: eliminating a definition and then appending a
  // fact that still mentions its variable leaves that fact unconstrained.
  // Accumulate the facts of shallower live levels for the deeper levels'
  // privacy checks.
  ASTNodeSet activeCbpFactSymbols;
  // Both eliminability questions below are constant-time lookups into an
  // occurrence index rather than stack scans; it is built on first use, so a
  // stack that asks neither pays nothing (see LevelOccurrence).
  impl->invalidateLevelOccurrences();
  for (size_t level = 1; level < assertionsSMT2.size(); level++)
  {
    const bool individually =
        assumeLastLevelPerConjunct && level + 1 == assertionsSMT2.size();
    PreprocessingTransaction levelTransaction(PreprocessingMode::PerLevel,
                                              assertionsSMT2[level]);

    ASTVec levelDefiningConjuncts;
    if (impl->policy.semanticPreprocessing() && uf.optimize_flag)
    {
      const size_t contextBefore = ctx.size();
      conjuncts.clear();
      splitConjuncts(assertionsSMT2[level], bm->ASTTrue, conjuncts);
      for (const ASTNode& c : conjuncts)
        impl->harvestPushed(c, ctx, ctxSources, ctxHasFp);
      if (impl->profile.enabled)
        impl->profile.contextDefinitions += ctx.size() - contextBefore;
      // A defining conjunct must never be rewritten under its own entry:
      // substituting x -> t into (= x t) yields TRUE and the constraint
      // silently vanishes -- with no replay record, so the model channel
      // answers a default, the raw-stack model check calls every
      // candidate bogus, and array refinement spins forever with no
      // violated axiom to add. The definers are re-presented to the
      // preparation unreplaced; its own harvest then either eliminates
      // them WITH bookkeeping (privacy rules, model replay) or keeps the
      // equation asserted.
      for (const ASTNode& c : conjuncts)
        if (ctxSources.find(c) != ctxSources.end())
          levelDefiningConjuncts.push_back(c);
    }

    // Constant-bit propagation over the live prefix: feed this
    // level's raw conjunction (a no-op for the persisting session's
    // stable prefix), then rewrite its conjuncts below under the
    // constants accumulated from levels up to and including this one
    // (see cbpFeedLevel/cbpAdopt). Never on the per-assumption path,
    // whose conjunct-to-assumption mapping a cross-conjunct fact
    // would blur.
    if (impl->policy.crossLevelPropagation() && uf.optimize_flag &&
        !individually && uf.bitConstantProp_flag)
      impl->cbpFeedLevel(level, assertionsSMT2[level]);

    conjuncts.clear();
    if (!impl->policy.semanticPreprocessing() || !uf.optimize_flag ||
        individually)
    {
      // check-sat-assuming wants per-assumption granularity: merging the
      // assumptions through a level-wide preparation would destroy the
      // conjunct-to-assumption mapping, so that level encodes raw.
      splitConjuncts(assertionsSMT2[level], bm->ASTTrue, conjuncts);
    }
    else
    {
      const bool levelHasFp = impl->fragment(assertionsSMT2[level]).fp;

      // Preparation granularity is a size call. A level of moderate size
      // is prepared as ONE formula -- full cross-conjunct simplification,
      // which is what collapses generated queries whose conjuncts only
      // shrink together. A huge level (the deep define-fun families)
      // prepares per conjunct instead: the whole-level pass would rerun
      // over the entire level for every pushed variant, while per-conjunct
      // preparation reuses every already-prepared piece and loses only
      // cross-conjunct effects beyond definition chaining.
      ASTVec rawConjuncts;
      if (impl->dagSizeUpToBigMemo(assertionsSMT2[level],
                                   Impl::bigFormulaCap) <=
          Impl::bigFormulaCap)
        rawConjuncts.push_back(assertionsSMT2[level]);
      else
        splitConjuncts(assertionsSMT2[level], bm->ASTTrue, rawConjuncts);

      // How many of this level's raw conjuncts mention each symbol; a
      // definition is only eliminable if its variable stays inside one.
      // At whole-level granularity there is exactly one raw conjunct, so
      // every count would be one and the test this feeds can never fire --
      // building it would be a walk over the level's symbols for nothing.
      std::map<ASTNode, size_t> conjunctCountOf;
      if (rawConjuncts.size() > 1)
        for (const ASTNode& rc : rawConjuncts)
          for (const ASTNode& s : impl->symbolsOf(rc))
            conjunctCountOf[s]++;

      // Totalisation order matters more than it looks. Totalising the
      // RAW conjunct and substituting after keeps the symfpu circuits
      // raw-keyed and shared across the session's variants; totalising
      // the substituted form builds novel circuits per variant, and a
      // family the batch pipeline solves in a second ran to timeout on
      // their shapes. The late order exists for exactly one reason --
      // a context entry with a floating-point BODY can splice partial
      // operations into the conjunct, which only the totaliser may
      // lower -- so it is used only when the context actually carries
      // floating point.
      const bool totaliseEarly = levelHasFp && !ctxHasFp;
      // A level inside the memo's stable prefix REPLAYS its recorded
      // rewrites -- outputs frozen at build time, when the
      // accumulated substitution held exactly this level's prefix --
      // and a level being fed this call records its own. A level that
      // is neither (a retired session's new levels, a lookup miss)
      // takes the plain path with no constant-fixing adoption: the
      // live map may hold deeper levels' fixings by now, and prefix
      // discipline forbids folding those into a shallower conjunct.
      const bool cbpHit = level < impl->cbpMemoStable;
      const bool cbpBuild = !cbpHit && impl->scopes.hasCbpMemo(level);
      ASTNodeSet cbpProtectedSymbols = activeCbpFactSymbols;
      const auto protectSymbols = [&](const ASTNode& n)
      {
        const ASTNodeSet& symbols = impl->symbolsOf(n);
        cbpProtectedSymbols.insert(symbols.begin(), symbols.end());
      };
      if (cbpHit)
      {
        for (const ScopedFact& f : impl->scopes.cbpMemo(level).facts)
          protectSymbols(f.assertion);
      }
      else if (cbpBuild)
      {
        // The facts this level will emit are discovered while its pieces are
        // being prepared.  Protect the symbols of every eligible fixed
        // domain up front, so a fact discovered by a later piece cannot make
        // an earlier piece's definition elimination unsound.  This is a
        // conservative superset: cbpAdopt emits only reachable domains.
        ASTVec eligibleDomains;
        eligibleDomains.reserve(impl->callCbpSubst.size());
        for (ASTNodeMap::const_iterator it = impl->callCbpSubst.begin();
             it != impl->callCbpSubst.end(); ++it)
        {
          if (impl->callCbpFedConjuncts.find(it->first) ==
              impl->callCbpFedConjuncts.end())
            eligibleDomains.push_back(it->first);
        }
        impl->addSymbolsOf(eligibleDomains, cbpProtectedSymbols);
      }
      size_t cbpMemoIdx = 0;
      std::vector<ScopedFact> cbpFacts;
      for (const ASTNode& rc : rawConjuncts)
      {
        ASTNode replaced = rc;
        bool replayed = false;
        if (cbpHit)
        {
          ScopedProfileTimer cbpTimer(impl->profile.enabled,
                                      impl->profile.cbpNs);
          ScopedProfileTimer replayTimer(impl->profile.enabled,
                                         impl->profile.cbpReplayNs);
          if (impl->profile.enabled)
            impl->profile.cbpReplayAttempts++;
          const std::vector<std::pair<ASTNode, ASTNode>>& rw =
              impl->scopes.cbpMemo(level).rewrites;
          if (cbpMemoIdx < rw.size() && rw[cbpMemoIdx].first == rc)
          {
            replaced = rw[cbpMemoIdx].second;
            cbpMemoIdx++;
            replayed = true;
            impl->callCbpReplayed++;
            if (impl->profile.enabled)
              impl->profile.cbpReplays++;
          }
        }
        if (!replayed)
        {
          if (totaliseEarly)
            replaced = impl->fpContext()->prepare(replaced);
          const bool isDefiner = ctxSources.find(rc) != ctxSources.end();
          if (!ctx.empty() && !isDefiner)
          {
            ASTNodeMap cache;
            const ASTNode substituted = SubstitutionMap::replace(
                replaced, ctx, cache, bm->defaultNodeFactory);
            // Adopt the substituted form only if it builds no novel
            // floating-point circuit (see introducesNovelFpOperations): a
            // fold is the collapse this context exists for, a variant is a
            // duplicate of a raw-keyed circuit and strictly harder to
            // search than the raw conjunct it replaces. The refused
            // conjunct encodes raw-keyed, sharing everything it always
            // shared; its definers stay asserted, so nothing is lost but
            // the rewrite.
            if (!impl->introducesNovelFpOperations(replaced, substituted))
              replaced = substituted;
          }
          // The whole-level piece contains its definers INSIDE the node
          // just substituted; restore them alongside the replaced form
          // (totalised the same way the piece was).
          if (rc == assertionsSMT2[level] && !levelDefiningConjuncts.empty())
          {
            ASTVec parts;
            for (const ASTNode& d : levelDefiningConjuncts)
              parts.push_back(totaliseEarly
                                  ? impl->fpContext()->prepare(d)
                                  : d);
            parts.push_back(replaced);
            replaced = bm->defaultNodeFactory->CreateNode(AND, parts);
          }

          // Rewrite under the prefix's accumulated constant fixings
          // BEFORE granularity is judged and the piece is prepared: a
          // conjunct this collapses flows into the piece machinery (and
          // from there to the transformer and the read registry) in its
          // folded form, content-keyed like every other conjunct.
          if (!cbpHit)
          {
            const size_t factsBefore = cbpFacts.size();
            replaced = impl->cbpAdopt(replaced, cbpFacts);
            for (size_t i = factsBefore; i < cbpFacts.size(); ++i)
              protectSymbols(cbpFacts[i].assertion);
          }
          if (cbpBuild)
            impl->scopes.cbpMemo(level).rewrites.push_back(
                std::make_pair(rc, replaced));
        }

        // An oversize conjunct (the deep define-fun chains) skips the
        // TRIAL passes -- their novel rewritten forms forfeit the
        // bit-blast memo's sharing wholesale -- but keeps the context
        // substitution: these conjuncts collapse under their levels'
        // definitions, and encoding one unsubstituted measured ten
        // million clauses against the substituted form's thousands.
        // rootLit's raw-keyed preparation (sigma0 and the plain
        // simplifier inside the cache) does the rest, as it always has.
        if (impl->dagSizeUpToBigMemo(replaced, Impl::bigFormulaCap) >
            Impl::bigFormulaCap)
        {
          conjuncts.push_back(replaced);
          continue;
        }

        // The late totalisation, for the context-carries-floating-point
        // case only (see totaliseEarly above): the substitution may have
        // spliced partial operations in, and lowering only accepts
        // totalised forms. A level with no floating point of its own can
        // acquire some the same way.
        if (!totaliseEarly &&
            (levelHasFp ||
             (ctxHasFp && containsFloatingPointTheory(replaced, bm))))
          replaced = impl->fpContext()->prepare(replaced);
        const Impl::PreparedPiece* pp =
            &impl->preparePiece(replaced, level, assertionsSMT2,
                                conjunctCountOf, cbpProtectedSymbols, ctx);
        // The other half of the elimination decision, settled once. The
        // expansion computed here is exactly what the join below installs,
        // so deciding it at the point of use costs one substitution per
        // definition per check rather than two. A CACHED piece was decided
        // under whatever context it was first prepared under, which may no
        // longer inline; re-preparing decides again under this one, and
        // preparePiece's own creation-time check makes the retry inlinable
        // by construction.
        std::vector<std::pair<ASTNode, ASTNode>> ctxInlines;
        bool inlinesHold = true;
        for (const ScopedElimination& d : pp->eliminated)
        {
          ASTNode expanded;
          if (!impl->ctxInlinable(d.symbol, d.value, ctx, expanded))
          {
            inlinesHold = false;
            break;
          }
          ctxInlines.push_back(std::make_pair(d.symbol, expanded));
        }
        if (!inlinesHold)
        {
          impl->dropPreparedLevel(replaced);
          pp = &impl->preparePiece(replaced, level, assertionsSMT2,
                                   conjunctCountOf, cbpProtectedSymbols, ctx);
          ctxInlines.clear();
          for (const ScopedElimination& d : pp->eliminated)
          {
            ASTNode expanded;
            const bool held =
                impl->ctxInlinable(d.symbol, d.value, ctx, expanded);
            assert(held && "a re-prepared piece refuses its own inlining");
            (void)held;
            ctxInlines.push_back(std::make_pair(d.symbol, expanded));
          }
        }
        for (const ASTNode& pc : pp->conjuncts)
          conjuncts.push_back(pc);
        // Eliminated definitions are recorded for the model, and joined
        // onto the context so DEEPER levels' uses collapse under them --
        // this is the only route by which a definition the raw harvest
        // refuses on content (a floating-point body, say) still reaches
        // its uses; without it those levels keep every symbolic read and
        // the refinement loop pays for the aliases. Joining obeys the
        // SAME discipline as harvestPushed: the body is expanded under
        // the current context and refused if its own variable reappears
        // or it grows past the inlining cap. A definer conjunct's piece
        // sees RAW content (it is never rewritten under its own entry),
        // so its propagator can harvest a definition in terms of a
        // variable another context entry defines -- feeding that
        // unexpanded made the map cyclic, and the next replacement
        // recursed until the worker stack died. The elimination itself
        // stays (it is sound for the piece and its replay); only the
        // context entry is withheld.
        for (const ScopedElimination& d : pp->eliminated)
          levelTransaction.addElimination(d.symbol, d.value, d.witness);
        for (const std::pair<ASTNode, ASTNode>& ci : ctxInlines)
        {
          // A null expansion means the context already binds the variable,
          // so its occurrences are already substituted away.
          if (ci.second.IsNull())
            continue;
          ctx[ci.first] = ci.second;
          if (impl->profile.enabled)
            impl->profile.contextDefinitions++;
          if (!ctxHasFp && bm->has_floating_point_theory &&
              containsFloatingPointTheory(ci.second, bm))
            ctxHasFp = true;
        }
      }

      // The pinning facts justifying this level's adoptions are its
      // conjuncts too: asserted under the same assumption, retracted
      // with the same pop, and content-keyed like everything else. A
      // replaying level re-asserts the facts it recorded.
      if (cbpHit)
      {
        for (const ScopedFact& f : impl->scopes.cbpMemo(level).facts)
        {
          // A retired session will never adopt again and creates no new
          // caller checkpoints. Its memo still supplies already-recorded
          // assertions, but there is no scoped fact-emission state to seed.
          if (!f.domain.IsNull() && !impl->cbpSessionRetired)
            impl->cbpInsertFactDomain(f.domain);
          conjuncts.push_back(f.assertion);
          levelTransaction.facts.push_back(f);
        }
      }
      else
      {
        // Append rather than assign: a refuted level's memo already
        // carries its FALSE.
        if (cbpBuild)
          for (const ScopedFact& f : cbpFacts)
            impl->scopes.cbpMemo(level).facts.push_back(f);
        for (const ScopedFact& f : cbpFacts)
        {
          conjuncts.push_back(f.assertion);
          levelTransaction.facts.push_back(f);
        }
      }

      const std::vector<ScopedFact>& activeFacts =
          cbpHit ? impl->scopes.cbpMemo(level).facts : cbpFacts;
      for (const ScopedFact& f : activeFacts)
      {
        const ASTNodeSet& symbols = impl->symbolsOf(f.assertion);
        activeCbpFactSymbols.insert(symbols.begin(), symbols.end());
      }
    }

    // A feed that refuted the live prefix by bit-level reasoning alone
    // asserts FALSE at the refuting level.
    if (impl->callCbpConflict)
    {
      conjuncts.push_back(bm->ASTFalse);
      levelTransaction.facts.push_back(
          ScopedFact(ASTNode(), bm->ASTFalse));
      impl->callCbpConflict = false;
    }
    // This level is past rewriting; its own parked fixings now serve
    // the deeper levels.
    impl->cbpFinishLevel();

    levelTransaction.conjuncts = conjuncts;
    impl->scopes.commitLevel(level, levelTransaction);

    if (conjuncts.empty())
      continue;

    levelRoots.clear();
    for (const ASTNode& c : conjuncts)
      levelRoots.push_back(impl->rootLit(c));

    // A level inside the promoted prefix is already asserted as units;
    // nothing to assume. (Its preparation above still ran: deeper
    // levels need its definitions in the context either way.)
    //
    // Only while it still prepares to what promotion pinned, though. The
    // raw conjunction updateStackStability compares is unchanged in the
    // case that matters: later content retracts a private elimination, the
    // level re-prepares with its defining equation restored -- and skipping
    // here would encode that stronger form and then drop it, leaving the
    // variable unconstrained behind the older, weaker units. Fall through
    // instead, so this solve assumes what the level now says, and hand the
    // epoch to the next call's maintenance block, which can rebuild safely.
    if (level <= impl->scopes.promotedDepth())
    {
      if (!impl->scopes.promotedConjunctsChanged(level, conjuncts))
        continue;
      impl->scopes.notePromotionDrift();
      if (uf.stats_flag)
        std::cerr << "Incremental: promoted level " << level
                  << " re-prepared differently, assumed for this solve "
                     "and demoted at the next"
                  << std::endl;
    }

    // Promote the next prefix level once it has sat identical long
    // enough. Never the deepest level: it is the churn point, and
    // check-sat-assuming's per-assumption frame must stay assumed.
    // Only once trail reuse has been retired -- the same session split
    // as inprobing retirement, for the same reason: a session still
    // riding the trail re-descends its stable assumptions nearly for
    // free and only pays promotion's recurring root-level preprocessing
    // over the new units (measured ~10% on the KLEE-class b64), while
    // the sessions that shed the trail pay the full assumption descent
    // every solve, which is exactly what promotion removes (measured
    // ~16% on f84c6e97).
    if (impl->policy.unitPromotion() && !individually &&
        uf.incremental_promote_units &&
        !impl->trailReuseAllowed &&
        level == impl->scopes.promotedDepth() + 1 &&
        level + 1 < assertionsSMT2.size() &&
        level < impl->scopes.size() &&
        impl->scopes.stableSolves(level) >= impl->promoteAfterSolves)
    {
      for (const int r : levelRoots)
      {
        SATSolver::vec_literals unit;
        unit.push(SATSolver::mkLit(r >> 1, r & 1));
        impl->addClause(unit);
      }
      impl->baseLiveMass = Impl::addMass(impl->baseLiveMass,
                                         levelRoots.size());
      assert(conjuncts.size() == levelRoots.size());
      for (const ASTNode& c : conjuncts)
        impl->recordPermanentRoot(c);
      // Remember the form that was pinned, not just how deep promotion
      // reached: the skip above is only sound while the level still
      // prepares to exactly this.
      impl->scopes.promote(level, conjuncts);
      if (uf.stats_flag)
        std::cerr << "Incremental: promoted level " << level << " ("
                  << levelRoots.size() << " conjuncts) to units after "
                  << impl->scopes.stableSolves(level) << " stable solves"
                  << std::endl;
      continue;
    }

    if (individually || !impl->policy.aggregateLevelAssumptions())
    {
      // The per-assumption route needs one root per source conjunct for
      // reporting. Core-only mode deliberately uses the same direct-root
      // mechanism for every level, avoiding the optional activation-literal
      // aggregation policy while retaining the assumption core itself.
      if (individually)
        impl->lastLevelIndividual = true;
      for (size_t k = 0; k < conjuncts.size(); k++)
      {
        const int r = levelRoots[k];
        if (impl->policy.retractionSearchHints())
          impl->everAssumedLits[r] = impl->engagedSolves;
        impl->assumedLitLevels.push_back(std::make_pair(r, level));
        if (individually)
          impl->lastLevelLitConjuncts.push_back(
              std::make_pair(r, conjuncts[k]));
        assumptions.push(SATSolver::mkLit(r >> 1, r & 1));
      }
      continue;
    }

    const int lit = impl->levelAssumption(levelRoots);
    if (impl->policy.retractionSearchHints())
      impl->everAssumedLits[lit] = impl->engagedSolves;
    impl->assumedLitLevels.push_back(std::make_pair(lit, level));
    assumptions.push(SATSolver::mkLit(lit >> 1, lit & 1));
  }

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
    impl->profile.contextEntries = ctx.size();
  }

  if (uf.stats_flag)
  {
    std::cerr << "Incremental: encoded " << impl->encodesThisCall
              << " new conjuncts, added "
              << (impl->lifetimeClauseSubmissions() - clausesBefore)
              << " clauses, assumed "
              << assumptions.size() << " literals, solver has "
              << impl->solver->nVars() << " variables, " << impl->sigma0.size()
              << " base-level and " << ctx.size() << " pushed substitutions, "
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
  const bool construct = observableModelRequested(uf) || needRefinement;
  uf.construct_counterexample_flag = construct;

  // Model evaluation of floating-point terms needs the encoding context
  // that lowered them. Batch fallback rounds install their own per solve;
  // this keeps the driver's rounds coherent the same way.
  if (impl->fpCtx)
    impl->ce->setFpEncodingContext(impl->fpCtx.get());

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
    SOLVER_RETURN_TYPE res = impl->ce->CallSAT_ResultCheck(
        *impl->solver, bm->ASTTrue, activeConjunction, activeConjunction,
        adapter, true);
    while (res == SOLVER_UNDECIDED)
    {
      refinementRounds++;
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

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

// The exact-stack route: the whole active stack encoded as one
// assumption-scoped block. Whole-array equality always takes it (the
// lazy checker owns the complete array graph), eagerly instantiated
// equality rounds and the first-engagement plain-BV shortcut solve the
// block like an ordinary formula. Route-specific preprocessing, the
// block solve, and the array-equality refinement driver live here;
// everything they share with the per-level route stays on Impl
// (IncrementalSolverImpl.h).

#include "IncrementalSolverImpl.h"

namespace stp
{

PreprocessingTransaction
IncrementalSolver::Impl::preprocessExactStackBlock(const ASTNode& input,
                                                 bool requireCollapse)
{
  PreprocessingTransaction result(PreprocessingMode::ExactStack, input);
  if (!bm->UserFlags.optimize_flag || input.isConstant())
  {
    result.accepted = !requireCollapse;
    result.conjuncts.push_back(input);
    return result;
  }

  // `requireCollapse` is part of the key: it changes both the acceptance
  // rule and the size gate, so the two callers must not share an entry.
  const std::pair<ASTNode, bool> memoKey(input, requireCollapse);
  std::map<std::pair<ASTNode, bool>,
           PreprocessingTransaction>::const_iterator memo =
      scopedBlockOf.find(memoKey);
  if (memo != scopedBlockOf.end())
    return memo->second;

  size_t before = 0;
  if (requireCollapse)
  {
    if (dagSizeUpTo(input, firstStackCollapseMinNodes - 1) <
        firstStackCollapseMinNodes)
    {
      PreprocessingTransaction& rejected = scopedBlockOf[memoKey];
      rejected = PreprocessingTransaction(PreprocessingMode::ExactStack,
                                          input);
      rejected.conjuncts.push_back(input);
      rejected.accepted = false;
      return rejected;
    }
    before = dagSizeUpTo(input, std::numeric_limits<size_t>::max());
  }

  SubstitutionMap scopedMap(bm);
  Simplifier scoped(bm, &scopedMap);
  ASTNode out = input;

  if (bm->UserFlags.bitConstantProp_flag)
  {
    simplifier::constantBitP::ConstantBitPropagation cb(
        bm, &scoped, bm->defaultNodeFactory, out);
    out = cb.topLevelBothWays(out);
    if (cb.isUnsatisfiable())
      out = bm->ASTFalse;
  }

  if (!out.isConstant() && bm->UserFlags.propagate_equalities)
  {
    PropagateEqualities pe(&scoped, bm->defaultNodeFactory, bm);
    out = pe.topLevel(out);
  }
  if (scoped.hasUnappliedSubstitutions())
    out = scoped.applySubstitutionMapAtTopLevel(out);

  if (!out.isConstant() && bm->UserFlags.enable_unconstrained)
  {
    RemoveUnconstrained remove(*bm);
    out = remove.topLevel(out, &scoped);
  }

  if (!out.isConstant() && bm->UserFlags.enable_pure_literals)
  {
    FindPureLiterals pure;
    if (pure.topLevel(out, &scoped, bm))
      out = scoped.applySubstitutionMapAtTopLevel(out);
  }

  if (scoped.hasUnappliedSubstitutions())
    out = scoped.applySubstitutionMapAtTopLevel(out);

  // Plain-BV first engagement uses this path only as a high-yield escape
  // from cross-level collapse cliffs. A modest rewrite can make the SAT
  // search shape worse while forfeiting the ordinary per-level roots, so
  // keep the raw exact-stack block unless the scoped trial at least halves
  // the DAG. No definitions have entered the model channel yet.
  if (requireCollapse && dagSizeUpTo(out, before / 2) > before / 2)
  {
    // A rejected trial commits no definitions (they would be model state
    // for a formula that is not being encoded), so the entry records only
    // the refusal.
    PreprocessingTransaction& rejected = scopedBlockOf[memoKey];
    rejected =
        PreprocessingTransaction(PreprocessingMode::ExactStack, input);
    rejected.conjuncts.push_back(input);
    rejected.accepted = false;
    return rejected;
  }

  PreprocessingTransaction& done = scopedBlockOf[memoKey];
  done = PreprocessingTransaction(PreprocessingMode::ExactStack, input);
  done.conjuncts.push_back(out);
  done.accepted = true;
  const ASTNodeSet retainedSymbols = symbolsOf(out);
  for (DenseNodeMap::const_iterator it = scoped.Return_SolverMap()->begin();
       it != scoped.Return_SolverMap()->end(); ++it)
  {
    if (it->first.GetKind() == SYMBOL &&
        retainedSymbols.find(it->first) != retainedSymbols.end())
      continue;
    done.addElimination(it->first, it->second);
  }
#ifndef NDEBUG
  // The third statement of the invariant preparePiece and
  // resimplifyBaseAtRebuild assert. Here it is true by construction -- the
  // loop above skips any key still present in the output, and this pass
  // keeps no definitions -- but that is a property of the `continue` three
  // lines up, not of the design, and it is what makes this pass's
  // unconstrained call safe without an untouchable set at all. Say so where
  // it can be checked rather than where it can be argued.
  for (const ScopedElimination& e : done.eliminated)
    assert(retainedSymbols.find(e.symbol) == retainedSymbols.end() &&
           "scoped block output mentions a variable it eliminated");
#endif
  bm->ASTNodeStats("Incremental exact stack after preprocessing: ", out);
  return done;
}

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

  const bool construct = uf.modelConstructionRequired();
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

  // No candidate leaves this route until every bit-vector abstraction in it
  // agrees with the operands it stands for. The refinement routes reach that
  // through CallSAT_ResultCheck; this one never enters it, so the loop is
  // written out. It terminates because every round either rules out the
  // candidate it was shown -- each term family, congruence clause and
  // said-unequal equality round adds a clause that candidate violates -- or
  // strictly grows an equality's refined prefix, which its width bounds; a
  // ruled-out candidate never returns, and the solver's models are finite.
  // The working bounds per record: one round for a comparison, addition or
  // if-then-else, log2(width) for an equality, and the blocking allowance
  // plus one exact encoding for a multiplication, division or remainder --
  // whose enumeration, with the allowance set to zero, is instead bounded
  // by the operand pairs the search can propose.
  const uint64_t refinementClausesBefore = solver->submittedClauses();
  while (sat && !bm->soft_timeout_expired && refineAbstractions(*solver) > 0)
  {
    bm->GetRunTimes()->start(RunTimes::Solving);
    if (profile.enabled)
    {
      profile.satCalls++;
      profile.refinementSatCalls++;
      profile.refinementRounds++;
    }
    {
      ScopedProfileTimer satTimer(profile.enabled, profile.satNs);
      ScopedProfileTimer refineSatTimer(profile.enabled,
                                        profile.refinementSatNs);
      sat = solver->solveWithAssumptions(assumptions, bm->soft_timeout_expired);
    }
    bm->GetRunTimes()->stop(RunTimes::Solving);
  }

  // As in IncrementalSolver::checkSat: the SOLVER_TIMEOUT below is the same
  // value a clock expiry returns, so which budget it was has to be taken from
  // the solver here or not at all.
  if (bm->soft_timeout_expired)
    bm->noteBudgetExhausted(*solver);

  // Whatever the loop pinned is part of what this stack costs from now on,
  // so it is accounted before the mass is staged -- the same treatment the
  // array-equality route gives its lemmas.
  const uint64_t theoryMass =
      accountRefinementClauses(inputToSat, refinementClausesBefore);
  uint64_t cheapLiveMass = addMass(baseLiveMass, clauseMassOf[inputToSat]);
  cheapLiveMass = addMass(cheapLiveMass, theoryMass);
  std::vector<Aig_Obj_t*> currentRoots(1, blockRegular);
  stageLiveConeMass(currentRoots, cheapLiveMass,
                    addMass(permanentUnitMass, theoryMass));
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
  publishFpContext();

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
  bool ufRound = false;
  bool activeHasFp = false;
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    const Fragment& f = fragment(levelConjunction);
    arrayEqualityRound = arrayEqualityRound || f.arrayEq;
    ufRound = ufRound || f.ufApply;
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

  // The exact stack has now been fully assembled, including every frontend
  // substitution and let expansion. Lower its durable applications before FP
  // totalisation, opaque array equality, or scoped preprocessing. Retain the
  // public conjunction separately in activeUFView.
  activeUFView = LoweredApplicationView();
  ASTNode ufSemantic = activeConjunction;
  if (ufRound)
  {
    UFLowering lowerer(bm);
    activeUFView = lowerer.lowerCompletedRoot(
        activeConjunction,
        UFSolveScope::persistent(activeConjunction.GetNodeNum(),
                                 encodingEpochGeneration));
    ufSemantic = activeUFView.semanticRootWithDefinitions(bm);
    if (containsKind(ufSemantic, UF_APPLY))
      FatalError("UF_APPLY crossed the persistent completed-block lowering "
                 "barrier",
                 ufSemantic);
  }
  else if (bm->getUFContextIfAny() != NULL)
    bm->getUFContextIfAny()->releaseSolveProtection();

  // Scope the solve-local UF indexes across every persistent preprocessing,
  // encoding, candidate and refinement path, including early rejection.
  UFContext* ufSolveContext =
      activeUFView.active() ? bm->getUFContextIfAny() : NULL;
  UFContext::SolveScope ufSolveScope(ufSolveContext);

  // A UF leaf actual is a solve scalar even when scoped preprocessing removes
  // every occurrence of it from the block formula.  If an earlier ordinary
  // solve dropped that symbol's sigma0 base definition, totalization would
  // otherwise mint unconstrained SAT bits which neither the formula walk nor
  // encodePrepared() can discover.  Restore these definitions before the
  // block's preprocessing trial records any new eliminations.
  if (activeUFView.active())
    for (const ASTNode& scalar : activeUFView.solveScalars)
      restoreDroppedSigma0Symbol(scalar);

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
  ASTNode prepared = ufSemantic;
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
  {
    inputToSat = ext->prepareInitialFormula(inputToSat);
    extActive = ext->active();
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
  exactStackKeepAlive.insert(ufSemantic);
  exactStackKeepAlive.insert(prepared);
  exactStackKeepAlive.insert(semantic);
  exactStackKeepAlive.insert(inputToSat);
  chargeSemanticRoot(activeConjunction);
  chargeSemanticRoot(ufSemantic);
  chargeSemanticRoot(prepared);
  chargeSemanticRoot(semantic);
  chargeSemanticRoot(inputToSat);

  if (uf.enable_array_equality && containsKind(inputToSat, ARRAY_EQ))
    FatalError("IncrementalSolver: an opaque array equality reached the "
               "final array transformation boundary",
               inputToSat);
  if (uf.enable_uninterpreted_functions && containsKind(inputToSat, UF_APPLY))
    FatalError("IncrementalSolver: UF_APPLY reached bit-blast", inputToSat);

  // A fresh per-round registry: the whole-graph transform must neither see
  // the persistent lazy rows (it refuses reused legacy rows) nor leak its
  // own solve-local rows into them. The rows are left in place afterwards
  // -- model construction reads them -- until the next solve or pop clears
  // the batch tables as usual.
  batchAT->ClearAllTables();

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
  if (activeUFView.active())
    for (const ASTNode& s : activeUFView.solveScalars)
      totalizeSymbol(s);

  if (uf.stats_flag)
  {
    std::cerr << "Incremental: "
              << (arrayEqualityRound ? "array-equality" : "first scoped BV")
              << " round, block of "
              << assertionsSMT2.size() << " levels "
              << (blockReused ? "reused" : "encoded") << ", solver has "
              << solver->nVars() << " variables" << std::endl;
  }

  // Every route bit-blasts before it solves, and the abstractions the
  // blaster made are this driver's to refine. Taken across here, once this
  // round's block is encoded and before any search.
  syncAbstractions();

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
  if ((!arrayEqualityRound && !ufRound) ||
      (!ufRound && uf.ackermannisation && !extActive))
    return solvePlainExactStack(assertionsSMT2, assumptions, inputToSat,
                                blockRegular);

  // Array equality needs a candidate model on every refinement round. Keep
  // that internal requirement distinct from whether this query's caller is
  // entitled to observe the resulting model. In particular, the incoming
  // derived flag may still describe an earlier query (and is false before a
  // session's first query), so restoring it would lose :produce-models.
  const bool constructForCaller = uf.callerRequestedModel();
  uf.construct_counterexample_flag = true;

  if (activeUFView.active())
  {
    ufAdapter->beginBlock(&activeUFView, encodingEpochGeneration,
                          satBackendGeneration, activeUFView.scope.id,
                          blockLit);
    ce->setUFTheoryAdapter(ufAdapter.get());
  }
  else
  {
    ufAdapter->clearActiveBlock();
    if (ce->getUFTheoryAdapter() == ufAdapter.get())
      ce->setUFTheoryAdapter(NULL);
  }

  publishFpContext();

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
  // Snapshotted before the first solve: that call refines the bit-vector
  // abstractions too, and the loop below reads the count to decide whether
  // the round it is looking at made progress.
  uint64_t abstractionsRefined = bvAbstraction.refinements();
  SOLVER_RETURN_TYPE res = ce->CallSAT_ResultCheck(
      *solver, bm->ASTTrue, semantic, prepared, tosat, true);

  // The refinement driver, as in TopLevelSTPAux: with an active equality
  // the checker owns every read, so each undecided candidate must carry a
  // pending theory lemma; without one, ordinary read refinement runs.
  size_t refinementRounds = 0;
  while (res == SOLVER_UNDECIDED)
  {
    refinementRounds++;
    // A candidate rejected because it contradicted a bit-vector abstraction
    // has already been ruled out, inside the call above and ahead of
    // everything else that reads a candidate. No theory owes a lemma for it
    // -- it was never a model of the reads either -- so the round is just
    // the next search.
    const uint64_t refinedNow = bvAbstraction.refinements();
    if (refinedNow != abstractionsRefined)
    {
      abstractionsRefined = refinedNow;
      res = ce->CallSAT_ResultCheck(*solver, bm->ASTTrue, semantic, prepared,
                                    tosat, true);
      continue;
    }
    // Re-totalize: the checker's lemma encodings can introduce new reads,
    // whose rows joined the table after the pass above. Memoised, so a
    // round that added nothing pays nothing.
    totalizeBatchRegistrySymbols();
    if (extActive && ext->hasPendingLemma())
    {
      // The lemmas persist in this session's solver, but their symbols
      // mean what THIS block's anchor and naming equations say they
      // mean -- and the whole-block preprocessing above may have
      // rewritten those equations under a retractable conjunct (a
      // check-sat-assuming level substituted into the anchors, say).
      // Each lemma clause therefore carries the negated block literal:
      // inert once this block is retracted, active again whenever the
      // identical stack re-assumes it. Without the guard, a lemma whose
      // atoms folded under such a substitution survives as an
      // unconditional fact -- concretely, a refuted index-equality
      // assumption left a permanent NOT-proxy unit behind, turning the
      // next assumption-free solve of the satisfiable base stack unsat.
      ext->encodePendingLemmas(*solver, tosat, blockLit ^ 1);
      res = ce->CallSAT_ResultCheck(*solver, bm->ASTTrue, semantic, prepared,
                                    tosat, true);
    }
    else if (activeUFView.active() && ufAdapter->hasPendingLemma())
    {
      ufAdapter->encodePendingLemmas(*solver, tosat);
      res = ce->CallSAT_ResultCheck(*solver, bm->ASTTrue, semantic, prepared,
                                    tosat, true);
    }
    else
    {
      if (!arrayops)
        FatalError("IncrementalSolver: UF refinement rejected a candidate "
                   "without retaining a block-scoped lemma");
      if (extActive)
        FatalError("IncrementalSolver: EXTCHK accepted no ordinary read "
                   "refinement owner for its complete graph");
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

  // UF certification necessarily materialized an internal candidate, but
  // that is distinct from publishing the caller-visible model. Preserve the
  // persistent driver's ordinary deferred-reader contract: after the seed
  // and durable-handle map have been certified, get-model/get-value performs
  // the public materialization on demand. The adapter state remains the
  // certified pending interpretation throughout.
  if (activeUFView.active() && res == SOLVER_SATISFIABLE && constructForCaller &&
      !uf.check_counterexample_flag)
    modelPending = true;

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

} // namespace stp

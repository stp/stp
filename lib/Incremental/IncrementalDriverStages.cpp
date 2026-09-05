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

void IncrementalSolver::Impl::maintainBackendForCheck(
    const ASTVec& assertionsSMT2, const ASTNode& classificationRoot)
{
  UserDefinedFlags& uf = bm->UserFlags;

  currentLiveClauseMass = 0;

  // The unsat story is per solve; a stale one must not answer for this call.
  lastUnsat = false;
  lastUnsatCoarse = false;
  lastLevelIndividual = false;
  modelPending = false;
  if (ufAdapter)
    ufAdapter->invalidateCertifiedModel();
  assumedLitLevels.clear();
  lastLevelLitConjuncts.clear();
  lastFailedLits.clear();
  // Scope reconciliation below can change the eliminated-variable filter the
  // adapter's cached symbol map was built under.
  symbolMapCache.invalidate();

  ScopedProfileTimer maintenanceTimer(profile.enabled, profile.maintenanceNs);

  // Promoted-prefix bookkeeping first: if a promoted level changed or
  // vanished, its units no longer describe the stack and the solver restarts
  // here, before any routing can touch it.
  updateStackStability(assertionsSMT2);

  // The relief valve: once the solver is past the configured size and most of
  // its encodings belong to content no longer on the stack, start it over from
  // the live stack. Deadness is measured by CLAUSE MASS: conjunct counts, the
  // original proxy, missed variant-push sessions whose few dozen distinct
  // conjuncts each carry a huge circuit (a million variables of ~95% popped
  // content never tripped the count ratio). Expand the exact live cone only
  // after the cheap clause-mass gate says a rebuild might be due.
  if (clauseReliefSizeReached() && reliefRatioReached())
    expandPendingLiveConeMass();

  const bool clauseRelief =
      clauseReliefSizeReached() && reliefRatioReached();
  // Semantic caches have an independent DAG-node floor. Their cheap charge
  // only stages the decision; semanticReliefReached walks exact retained and
  // live unions, so a monotonically growing stack whose snapshots share almost
  // everything is not mistaken for dead churn.
  const bool semanticRelief = semanticReliefReached();
  if (clauseRelief || semanticRelief)
  {
    if (uf.stats_flag)
      std::cerr << "Incremental: re-encoded from scratch (solver had "
                << solver->nVars() << " variables, " << retainedClauseMass()
                << " retained clauses for a " << maxLiveClauseMass
                << " clause working set, "
                << semanticEpoch.lastRetainedNodeCount()
                << " retained semantic DAG nodes for a "
                << semanticEpoch.maxLiveNodeCount() << " node working set)"
                << std::endl;
    rebuildEncodings(assertionsSMT2, RebuildReason::Relief);
  }

  // Probe-based inprocessing re-runs over the whole persistent encoding at
  // every solve. Retiring it is configuration-window-only, so the transition
  // is one bounded rebuild onto a fresh solver configured without it.
  engagedSolves++;
  if (!inprobingRetired &&
      ((uf.incremental_inprobing == UserDefinedFlags::BVAMode::OFF &&
        solver->supportsInprobingControl()) ||
       (inprobingRetirementEarned() && !trailReuseAllowed)))
  {
    inprobingRetired = true;
    if (uf.stats_flag)
      std::cerr << "Incremental: inprobing retired (" << engagedSolves
                << " solves), solver restarted without it" << std::endl;
    rebuildEncodings(assertionsSMT2, RebuildReason::Inprobing);
  }

  // Early FP is strong evidence to start without trail reuse. The ambiguous
  // late transition is specific to source array+FP sessions: observe a few FP
  // checks, then retire a still-small state or combine the transition with the
  // existing inprobing boundary. Array-free QF_BVFP retains its trail.
  if (policy.adaptiveBackendConfiguration() && trailReuseAllowed)
  {
    bool retire = solver->nVars() >= trailReuseVarLimit;
    bool hasFp = false;
    if (!classificationRoot.IsNull())
      hasFp = fragment(classificationRoot).fp;
    else
      for (size_t i = 0; !hasFp && i < assertionsSMT2.size(); i++)
        hasFp = fragment(assertionsSMT2[i]).fp;
    if (!retire && hasFp)
    {
      const bool earlyFp = engagedSolves < trailReuseFpRetireSolves;
      const bool refinementHeavy =
          currentRefinementClauseMass >= trailReuseRefinementClauseFloor;
      const bool canRetireInprobingWithTrail = inprobingRetirementEarned();
      const bool smallLateFpState =
          lateArrayFpSolvesWithTrail >= trailReuseLateArrayFpProbeSolves &&
          solver->nVars() < trailReuseEstablishedVarFloor;

      retire = earlyFp ||
               (sourceArraysSeen && !refinementHeavy &&
                (canRetireInprobingWithTrail || smallLateFpState));
      if (!retire && sourceArraysSeen)
        lateArrayFpSolvesWithTrail++;
    }
    if (retire)
    {
      trailReuseAllowed = false;
      if (uf.stats_flag)
        std::cerr << "Incremental: trail reuse retired (" << solver->nVars()
                  << " variables after " << engagedSolves
                  << " solves), solver restarted without it" << std::endl;
      // If the session already qualifies for inprobing retirement, take both
      // transitions in one rebuild rather than rebuilding again next solve.
      if (!inprobingRetired && inprobingRetirementEarned())
      {
        inprobingRetired = true;
        if (uf.stats_flag)
          std::cerr << "Incremental: inprobing retired with it ("
                    << engagedSolves << " solves)" << std::endl;
      }
      rebuildEncodings(assertionsSMT2, RebuildReason::Trail);
    }
  }

  // The backend's configuration window closes at its first clause. This must
  // precede extensionality routing because an equality round encodes into the
  // same persistent solver.
  decideBVA(assertionsSMT2, classificationRoot);

  // Activation-literal pins are clauses, so stale retraction bookkeeping may
  // be retired only after the configuration window has closed.
  if (policy.aggregateLevelAssumptions())
    retireStaleActivation();
}

bool IncrementalSolver::Impl::tryExactStackRoute(
    const ASTVec& assertionsSMT2, bool assumeLastLevelPerConjunct,
    bool firstForcedIncrementalSolve, const ASTNode& assumptionScopedRoot,
    size_t orderedDistincts, SOLVER_RETURN_TYPE& result)
{
  UserDefinedFlags& uf = bm->UserFlags;

  // DISTINCT ordering is an equisatisfiable whole-formula rewrite, not a
  // permanent fact. Encode its completed root as the same retractable block
  // used by the other whole-stack routes: this check assumes the block's root,
  // and a later check whose occurrence survey no longer earns the ordering
  // simply does not assume it. In particular, do this before the ordinary
  // per-level route can turn a base-level chain into an irrevocable unit.
  if (!assumptionScopedRoot.IsNull())
  {
    result = exactStackCheckSat(assertionsSMT2,
                                firstForcedIncrementalSolve, false, NULL,
                                assumptionScopedRoot, orderedDistincts);
    return true;
  }

  // Whole-array equality and UF completed-root lowering each own the round's
  // complete active stack, so no conjunct may be encoded separately.
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    const Fragment& f = fragment(levelConjunction);
    if (f.arrayEq || f.ufApply)
    {
      result = exactStackCheckSat(assertionsSMT2,
                                  firstForcedIncrementalSolve);
      return true;
    }
  }

  // Explicit first engagement has no earlier batch solve to collapse facts
  // across level boundaries. Try the exact-stack preprocessor for a plain-BV
  // stack, but adopt it only when the complete DAG at least halves.
  const bool provisionalBlockAllowed =
      uf.incremental_reencode_limit == 0 ||
      uf.incremental_reencode_limit >= firstStackMinReencodeLimit;
  if (policy.firstSolveShortcuts() &&
      (firstForcedIncrementalSolve || uf.incremental_scoped_preprocessing) &&
      !assumeLastLevelPerConjunct && provisionalBlockAllowed &&
      assertionsSMT2.size() > 1)
  {
    bool plainBv = true;
    for (const ASTNode& levelConjunction : assertionsSMT2)
    {
      const Fragment& f = fragment(levelConjunction);
      // Array equality and uninterpreted functions have routes of their own
      // above; plain array reads and floating point do not, and were
      // excluded here only because the shortcut was written for the one case
      // that had been measured. See incremental_scoped_preprocessing.
      const bool excluded = uf.incremental_scoped_preprocessing
                                ? (f.arrayEq || f.ufApply)
                                : (f.arrays || f.arrayEq || f.fp || f.ufApply);
      if (excluded)
      {
        plainBv = false;
        break;
      }
    }
    if (plainBv)
    {
      bool accepted = false;
      const SOLVER_RETURN_TYPE trial = exactStackCheckSat(
          assertionsSMT2, firstForcedIncrementalSolve, true, &accepted);
      if (accepted)
      {
        result = trial;
        return true;
      }
    }
  }
  return false;
}

void IncrementalSolver::Impl::synchronizeCbpPrefix(
    const ASTVec& assertionsSMT2, bool firstForcedIncrementalSolve)
{
  UserDefinedFlags& uf = bm->UserFlags;

  // Constant-bit propagation state persists across calls. A pop, changed
  // level, or base growth rolls the engine and caller overlay back to their
  // longest common prefix; the diagnostic reset mode rebuilds that prefix.
  bool cbpBootstrapDeferred = false;
  if (policy.crossLevelPropagation())
  {
    ScopedProfileTimer cbpTimer(profile.enabled, profile.cbpNs);
    ScopedProfileTimer syncTimer(profile.enabled, profile.cbpSyncNs);

    // A forced first solve has no prefix to reuse yet. Leave an oversized
    // engine genuinely empty for this call; a later real solve builds the
    // complete current state through the ordinary prefix feed.
    const int64_t configuredBootstrapLimit =
        uf.incremental_cbp_bootstrap_limit;
    if (firstForcedIncrementalSolve && configuredBootstrapLimit > 0 &&
        uf.optimize_flag && uf.bitConstantProp_flag &&
        assertionsSMT2.size() > 1 && scopes.cbpFedDepth() == 0 &&
        scopes.cbpMemoDepth() == 0)
    {
      const size_t limit =
          clampToSize(static_cast<uint64_t>(configuredBootstrapLimit));
      cbpBootstrapDeferred = cbpStackExceeds(assertionsSMT2, limit);
      if (cbpBootstrapDeferred)
      {
        if (profile.enabled)
          profile.cbpBootstrapDeferred++;
        if (uf.stats_flag)
          std::cerr << "Incremental: deferred large first-solve cbp bootstrap"
                    << std::endl;
      }
    }

    const size_t lcp = scopes.cbpFedCommonPrefix();
    if (profile.enabled)
      profile.stablePrefix = lcp;
    const bool diverged = lcp < scopes.cbpFedDepth();
    if (diverged)
    {
      if (profile.enabled)
        profile.cbpDivergences++;
      // An epoch that adopted nothing lengthens the barren run; one fresh
      // adoption clears it.
      if (cbpEpochAdopted == 0)
      {
        cbpBarrenDivergences++;
        const size_t leash = cbpEverFixed ? cbpRetireBarrenFixed
                                          : cbpRetireBarrenNeverFixed;
        if (!cbpSessionRetired && cbpBarrenDivergences >= leash)
        {
          cbpSessionRetired = true;
          if (uf.stats_flag)
            std::cerr << "Incremental: cbp retired for the session ("
                      << cbpBarrenDivergences
                      << " adoption-free stack divergences)" << std::endl;
        }
      }
      else
      {
        cbpBarrenDivergences = 0;
      }
      cbpEpochAdopted = 0;

      const size_t fedLevelsBefore = scopes.cbpFedDepth();
      const bool aligned =
          callCbp.get() != NULL && callCbp->levelCount() == fedLevelsBefore &&
          cbpCallerCheckpoints.size() == fedLevelsBefore &&
          !cbpCallerLevelOpen && callCbpDeferred.empty();
      const bool useRollback =
          !cbpSessionRetired && !uf.incremental_cbp_reset && aligned;
      if (useRollback)
      {
        ScopedProfileTimer rollbackTimer(profile.enabled,
                                         profile.cbpRollbackNs);
        const IncrementalCBP::RollbackStats stats = callCbp->rollbackTo(lcp);
        const size_t callerEntries = cbpRollbackCallerTo(lcp);
        assert(stats.levels == fedLevelsBefore - lcp);
        assert(callCbp->levelCount() == lcp);
        assert(cbpCallerCheckpoints.size() == lcp);
        assert(scopes.cbpFedDepth() == lcp);
        if (profile.enabled)
        {
          profile.cbpRollbacks++;
          profile.cbpRolledLevels += stats.levels;
          profile.cbpRollbackFixed += stats.fixedStates;
          profile.cbpRollbackCreated += stats.createdFixedStates;
          profile.cbpRollbackDependencies += stats.dependencyNodes;
          profile.cbpRollbackMultiplications += stats.multiplicationStates;
          profile.cbpRollbackCallerEntries += callerEntries;
        }
      }
      else
      {
        ScopedProfileTimer resetTimer(profile.enabled, profile.cbpResetNs);
        if (profile.enabled)
          profile.cbpResets++;
        cbpReset();
      }
    }

    cbpMemoStable = scopes.trimCbpMemoToCurrent();
  }
  else
  {
    cbpMemoStable = 0;
    if (profile.enabled)
      profile.stablePrefix = scopes.lastCommonPrefix();
  }
  callCbpAdopted = 0;
  callCbpReplayed = 0;
  callCbpOff = !policy.crossLevelPropagation() || cbpSessionRetired ||
               cbpBootstrapDeferred || cbpOverFeedCap();
  callCbpConflict = false;
}

void IncrementalSolver::Impl::encodeBaseLevel(
    const ASTVec& assertionsSMT2, bool firstForcedIncrementalSolve)
{
  UserDefinedFlags& uf = bm->UserFlags;

  // A rebuild leaves the re-simplified base waiting until the backend's
  // configuration window is decided. They become permanent units here.
  if (!pendingRebuiltBase.empty())
  {
    for (const ASTNode& c : pendingRebuiltBase)
    {
      const int lit = rootLit(c);
      SATSolver::vec_literals unit;
      unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
      addClause(unit);
      baseLiveMass =
          addMass(baseLiveMass, addMass(clauseMassOf[c], 1));
      recordPermanentRoot(c);
    }
    pendingRebuiltBase.clear();
  }

  ASTVec conjuncts;
  splitConjuncts(assertionsSMT2[0], bm->ASTTrue, conjuncts);

  ASTVec newLevel0;
  for (const ASTNode& c : conjuncts)
  {
    if (!level0Asserted.insert(c).second)
      continue;
    pendingBaseSeed.push_back(c);
    newLevel0.push_back(c);
    // New content invalidates any cached level whose elimination it
    // contradicts before anything is harvested or encoded.
    if (policy.semanticPreprocessing())
    {
      ScopedProfileTimer screenTimer(profile.enabled, profile.screenNs);
      screenNewContent(c);
    }
    if (policy.semanticPreprocessing())
    {
      const ASTNodeSet& syms = symbolsOf(c);
      baseSymbols.insert(syms.begin(), syms.end());
      if (uf.optimize_flag)
        harvestSigma0(c);
    }
  }

  if (policy.firstSolveShortcuts() && firstForcedIncrementalSolve &&
      assertionsSMT2.size() == 1 && !newLevel0.empty())
  {
    ASTVec reducedBase;
    if (preprocessForcedFirstBase(newLevel0, reducedBase))
      newLevel0.swap(reducedBase);
  }

  for (const ASTNode& c : newLevel0)
  {
    const int lit = rootLit(c);
    SATSolver::vec_literals unit;
    unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
    addClause(unit);
    baseLiveMass = addMass(baseLiveMass, addMass(clauseMassOf[c], 1));
    recordPermanentRoot(c);
  }

  // Screening sees the whole stack's new raw content before any level is
  // prepared, so a deeper mention invalidates a shallower cached elimination
  // before that stale entry can be used.
  if (policy.semanticPreprocessing())
  {
    ScopedProfileTimer screenTimer(profile.enabled, profile.screenNs);
    for (size_t level = 1; level < assertionsSMT2.size(); level++)
      screenNewContent(assertionsSMT2[level]);
  }

  // The permanent base seeds CBP only when a pushed level can consume the
  // facts; a base-only session has no adopter and pays nothing for the feed.
  if (policy.crossLevelPropagation() && uf.optimize_flag &&
      uf.bitConstantProp_flag && assertionsSMT2.size() > 1)
  {
    cbpFeedLevel(0, assertionsSMT2[0]);
    cbpFinishLevel();
  }
}

} // namespace stp

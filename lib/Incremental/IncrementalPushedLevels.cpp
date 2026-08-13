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

size_t IncrementalSolver::Impl::prepareAndEncodePushedLevels(
    const ASTVec& assertionsSMT2, bool assumeLastLevelPerConjunct,
    SATSolver::vec_literals& assumptions)
{
  UserDefinedFlags& uf = bm->UserFlags;
  ASTVec conjuncts;
  std::vector<int> levelRoots;

  // The context carries only retractable definitions harvested from the live
  // pushed prefix. sigma0 is deliberately applied inside cached preparation:
  // its permanence makes staleness sound, so base growth need not churn the
  // piece cache. A definition joins the context before its own level is
  // prepared but definitions from deeper levels never rewrite shallower ones.
  ASTNodeMap ctx;
  ASTNodeSet ctxSources;
  bool ctxHasFp = false;

  // CBP pinning facts are scoped conjuncts. Their symbols participate in
  // private-definition decisions just like the raw assertion stack.
  ASTNodeSet activeCbpFactSymbols;

  // Both eliminability questions below use the occurrence index; it is built
  // lazily, so a stack that asks neither pays nothing.
  invalidateLevelOccurrences();
  for (size_t level = 1; level < assertionsSMT2.size(); level++)
  {
    const bool individually =
        assumeLastLevelPerConjunct && level + 1 == assertionsSMT2.size();
    PreprocessingTransaction levelTransaction(PreprocessingMode::PerLevel,
                                              assertionsSMT2[level]);

    ASTVec levelDefiningConjuncts;
    if (policy.semanticPreprocessing() && uf.optimize_flag)
    {
      const size_t contextBefore = ctx.size();
      conjuncts.clear();
      splitConjuncts(assertionsSMT2[level], bm->ASTTrue, conjuncts);
      for (const ASTNode& c : conjuncts)
        harvestPushed(c, ctx, ctxSources, ctxHasFp);
      if (profile.enabled)
        profile.contextDefinitions += ctx.size() - contextBefore;
      // A defining conjunct must not be rewritten under its own entry: doing
      // so turns (= x t) into TRUE without creating model-replay state.
      for (const ASTNode& c : conjuncts)
        if (ctxSources.find(c) != ctxSources.end())
          levelDefiningConjuncts.push_back(c);
    }

    // Feed the raw level before rewriting its conjuncts under fixings from the
    // prefix up to and including this level. The per-assumption path stays raw
    // so its conjunct-to-assumption mapping remains reportable.
    if (policy.crossLevelPropagation() && uf.optimize_flag && !individually &&
        uf.bitConstantProp_flag)
      cbpFeedLevel(level, assertionsSMT2[level]);

    conjuncts.clear();
    if (!policy.semanticPreprocessing() || !uf.optimize_flag || individually)
    {
      splitConjuncts(assertionsSMT2[level], bm->ASTTrue, conjuncts);
    }
    else
    {
      const bool levelHasFp = fragment(assertionsSMT2[level]).fp;

      // Moderate levels are prepared as one formula for cross-conjunct
      // simplification. Huge define-fun families prepare per conjunct so
      // pushed variants can reuse the pieces already seen.
      ASTVec rawConjuncts;
      if (dagSizeUpToBigMemo(assertionsSMT2[level], bigFormulaCap) <=
          bigFormulaCap)
        rawConjuncts.push_back(assertionsSMT2[level]);
      else
        splitConjuncts(assertionsSMT2[level], bm->ASTTrue, rawConjuncts);

      // At per-conjunct granularity, a definition is eliminable only when its
      // variable stays inside one raw conjunct of this level.
      std::map<ASTNode, size_t> conjunctCountOf;
      if (rawConjuncts.size() > 1)
        for (const ASTNode& rc : rawConjuncts)
          for (const ASTNode& s : symbolsOf(rc))
            conjunctCountOf[s]++;

      // Totalising the raw conjunct preserves raw-keyed symfpu sharing. The
      // late order is needed only when the context itself can splice a
      // floating-point body into the conjunct.
      const bool totaliseEarly = levelHasFp && !ctxHasFp;
      const bool cbpHit = level < cbpMemoStable;
      const bool cbpBuild = !cbpHit && scopes.hasCbpMemo(level);
      ASTNodeSet cbpProtectedSymbols = activeCbpFactSymbols;
      const auto protectSymbols = [&](const ASTNode& n)
      {
        const ASTNodeSet& symbols = symbolsOf(n);
        cbpProtectedSymbols.insert(symbols.begin(), symbols.end());
      };
      if (cbpHit)
      {
        for (const ScopedFact& f : scopes.cbpMemo(level).facts)
          protectSymbols(f.assertion);
      }
      else if (cbpBuild)
      {
        // Facts are discovered while pieces are prepared. Protect every
        // eligible fixed domain up front so a later piece's fact cannot make
        // an earlier piece's definition elimination unsound.
        ASTVec eligibleDomains;
        eligibleDomains.reserve(callCbpSubst.size());
        for (ASTNodeMap::const_iterator it = callCbpSubst.begin();
             it != callCbpSubst.end(); ++it)
        {
          if (callCbpFedConjuncts.find(it->first) ==
              callCbpFedConjuncts.end())
            eligibleDomains.push_back(it->first);
        }
        addSymbolsOf(eligibleDomains, cbpProtectedSymbols);
      }
      size_t cbpMemoIdx = 0;
      std::vector<ScopedFact> cbpFacts;
      for (const ASTNode& rc : rawConjuncts)
      {
        ASTNode replaced = rc;
        bool replayed = false;
        if (cbpHit)
        {
          ScopedProfileTimer cbpTimer(profile.enabled, profile.cbpNs);
          ScopedProfileTimer replayTimer(profile.enabled,
                                         profile.cbpReplayNs);
          if (profile.enabled)
            profile.cbpReplayAttempts++;
          const std::vector<std::pair<ASTNode, ASTNode>>& rw =
              scopes.cbpMemo(level).rewrites;
          if (cbpMemoIdx < rw.size() && rw[cbpMemoIdx].first == rc)
          {
            replaced = rw[cbpMemoIdx].second;
            cbpMemoIdx++;
            replayed = true;
            callCbpReplayed++;
            if (profile.enabled)
              profile.cbpReplays++;
          }
        }
        if (!replayed)
        {
          if (totaliseEarly)
            replaced = fpContext()->prepare(replaced);
          const bool isDefiner = ctxSources.find(rc) != ctxSources.end();
          if (!ctx.empty() && !isDefiner)
          {
            ASTNodeMap cache;
            const ASTNode substituted = SubstitutionMap::replace(
                replaced, ctx, cache, bm->defaultNodeFactory);
            // A fold is useful; a novel FP variant duplicates a raw-keyed
            // circuit and is refused while its defining equations stay live.
            if (!introducesNovelFpOperations(replaced, substituted))
              replaced = substituted;
          }
          // Whole-level preparation substituted its definers inside the node;
          // restore their raw forms alongside it.
          if (rc == assertionsSMT2[level] &&
              !levelDefiningConjuncts.empty())
          {
            ASTVec parts;
            for (const ASTNode& d : levelDefiningConjuncts)
              parts.push_back(totaliseEarly ? fpContext()->prepare(d) : d);
            parts.push_back(replaced);
            replaced = bm->defaultNodeFactory->CreateNode(AND, parts);
          }

          if (!cbpHit)
          {
            const size_t factsBefore = cbpFacts.size();
            replaced = cbpAdopt(replaced, cbpFacts);
            for (size_t i = factsBefore; i < cbpFacts.size(); ++i)
              protectSymbols(cbpFacts[i].assertion);
          }
          if (cbpBuild)
            scopes.cbpMemo(level).rewrites.push_back(
                std::make_pair(rc, replaced));
        }

        // Oversize conjuncts skip the trial passes, whose novel rewritten
        // forms would forfeit bit-blast sharing, but keep context substitution.
        if (dagSizeUpToBigMemo(replaced, bigFormulaCap) > bigFormulaCap)
        {
          conjuncts.push_back(replaced);
          continue;
        }

        if (!totaliseEarly &&
            (levelHasFp ||
             (ctxHasFp && containsFloatingPointTheory(replaced, bm))))
          replaced = fpContext()->prepare(replaced);
        const PreparedPiece* pp =
            &preparePiece(replaced, level, assertionsSMT2, conjunctCountOf,
                          cbpProtectedSymbols, ctx);

        // Settle whether each cached elimination can be expanded under this
        // context. If not, re-prepare under the current one and decide again.
        std::vector<std::pair<ASTNode, ASTNode>> ctxInlines;
        bool inlinesHold = true;
        for (const ScopedElimination& d : pp->eliminated)
        {
          ASTNode expanded;
          if (!ctxInlinable(d.symbol, d.value, ctx, expanded))
          {
            inlinesHold = false;
            break;
          }
          ctxInlines.push_back(std::make_pair(d.symbol, expanded));
        }
        if (!inlinesHold)
        {
          dropPreparedLevel(replaced);
          pp = &preparePiece(replaced, level, assertionsSMT2,
                             conjunctCountOf, cbpProtectedSymbols, ctx);
          ctxInlines.clear();
          for (const ScopedElimination& d : pp->eliminated)
          {
            ASTNode expanded;
            const bool held =
                ctxInlinable(d.symbol, d.value, ctx, expanded);
            assert(held && "a re-prepared piece refuses its own inlining");
            (void)held;
            ctxInlines.push_back(std::make_pair(d.symbol, expanded));
          }
        }
        for (const ASTNode& pc : pp->conjuncts)
          conjuncts.push_back(pc);

        // Eliminated definitions are recorded for model replay and joined
        // onto the context so deeper levels' uses collapse under them.
        for (const ScopedElimination& d : pp->eliminated)
          levelTransaction.addElimination(d.symbol, d.value, d.witness);
        for (const std::pair<ASTNode, ASTNode>& ci : ctxInlines)
        {
          // A null expansion means the context already binds the variable.
          if (ci.second.IsNull())
            continue;
          ctx[ci.first] = ci.second;
          if (profile.enabled)
            profile.contextDefinitions++;
          if (!ctxHasFp && bm->has_floating_point_theory &&
              containsFloatingPointTheory(ci.second, bm))
            ctxHasFp = true;
        }
      }

      // Pinning facts are asserted and retracted with their level. A memo hit
      // reasserts the facts recorded when that prefix was first built.
      if (cbpHit)
      {
        for (const ScopedFact& f : scopes.cbpMemo(level).facts)
        {
          if (!f.domain.IsNull() && !cbpSessionRetired)
            cbpInsertFactDomain(f.domain);
          conjuncts.push_back(f.assertion);
          levelTransaction.facts.push_back(f);
        }
      }
      else
      {
        // Append rather than assign: a refuted level's memo already carries
        // its FALSE.
        if (cbpBuild)
          for (const ScopedFact& f : cbpFacts)
            scopes.cbpMemo(level).facts.push_back(f);
        for (const ScopedFact& f : cbpFacts)
        {
          conjuncts.push_back(f.assertion);
          levelTransaction.facts.push_back(f);
        }
      }

      const std::vector<ScopedFact>& activeFacts =
          cbpHit ? scopes.cbpMemo(level).facts : cbpFacts;
      for (const ScopedFact& f : activeFacts)
      {
        const ASTNodeSet& symbols = symbolsOf(f.assertion);
        activeCbpFactSymbols.insert(symbols.begin(), symbols.end());
      }
    }

    // A bit-level contradiction asserts FALSE at the refuting level.
    if (callCbpConflict)
    {
      conjuncts.push_back(bm->ASTFalse);
      levelTransaction.facts.push_back(
          ScopedFact(ASTNode(), bm->ASTFalse));
      callCbpConflict = false;
    }
    // This level is past rewriting; its parked fixings serve deeper levels.
    cbpFinishLevel();

    levelTransaction.conjuncts = conjuncts;
    scopes.commitLevel(level, levelTransaction);

    if (conjuncts.empty())
      continue;

    levelRoots.clear();
    for (const ASTNode& c : conjuncts)
      levelRoots.push_back(rootLit(c));

    // Promoted levels are already units, but only while preparation still
    // produces the form that was pinned. A drift is assumed for this solve and
    // causes maintenance to demote the level next time.
    if (level <= scopes.promotedDepth())
    {
      if (!scopes.promotedConjunctsChanged(level, conjuncts))
        continue;
      scopes.notePromotionDrift();
      if (uf.stats_flag)
        std::cerr << "Incremental: promoted level " << level
                  << " re-prepared differently, assumed for this solve and "
                     "demoted at the next"
                  << std::endl;
    }

    // Promote the next stable prefix level only after trail reuse is retired.
    // Never promote the deepest level or the per-assumption frame.
    if (policy.unitPromotion() && !individually &&
        uf.incremental_promote_units && !trailReuseAllowed &&
        level == scopes.promotedDepth() + 1 &&
        level + 1 < assertionsSMT2.size() && level < scopes.size() &&
        scopes.stableSolves(level) >= promoteAfterSolves)
    {
      for (const int r : levelRoots)
      {
        SATSolver::vec_literals unit;
        unit.push(SATSolver::mkLit(r >> 1, r & 1));
        addClause(unit);
      }
      baseLiveMass = addMass(baseLiveMass, levelRoots.size());
      assert(conjuncts.size() == levelRoots.size());
      for (const ASTNode& c : conjuncts)
        recordPermanentRoot(c);
      scopes.promote(level, conjuncts);
      if (uf.stats_flag)
        std::cerr << "Incremental: promoted level " << level << " ("
                  << levelRoots.size() << " conjuncts) to units after "
                  << scopes.stableSolves(level) << " stable solves"
                  << std::endl;
      continue;
    }

    if (individually || !policy.aggregateLevelAssumptions())
    {
      // Per-assumption mode keeps one source-conjunct root for reporting;
      // core-only mode uses the same direct-root mechanism for every level.
      if (individually)
        lastLevelIndividual = true;
      for (size_t k = 0; k < conjuncts.size(); k++)
      {
        const int r = levelRoots[k];
        if (policy.retractionSearchHints())
          everAssumedLits[r] = engagedSolves;
        assumedLitLevels.push_back(std::make_pair(r, level));
        if (individually)
          lastLevelLitConjuncts.push_back(
              std::make_pair(r, conjuncts[k]));
        assumptions.push(SATSolver::mkLit(r >> 1, r & 1));
      }
      continue;
    }

    const int lit = levelAssumption(levelRoots);
    if (policy.retractionSearchHints())
      everAssumedLits[lit] = engagedSolves;
    assumedLitLevels.push_back(std::make_pair(lit, level));
    assumptions.push(SATSolver::mkLit(lit >> 1, lit & 1));
  }

  return ctx.size();
}

} // namespace stp

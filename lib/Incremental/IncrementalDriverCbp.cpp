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

// The session-persistent constant-bit-propagation overlay: the caller
// side of IncrementalCBP -- feed/adopt/rollback with the undo trail
// that keeps the substitution, fed-conjunct and fact-domain maps in
// step with the scope ledger's processed-prefix cursor. The engine
// itself is IncrementalCBP.{h,cpp}; the ownership story lives at the
// members' declarations (IncrementalSolverImpl.h).

#include "IncrementalSolverImpl.h"

namespace stp
{

void IncrementalSolver::Impl::cbpBeginCallerLevel(size_t fedBefore)
{
  assert(callCbpDeferred.empty());
  assert(!cbpCallerLevelOpen);
  assert(cbpCallerCheckpoints.size() == scopes.cbpFedDepth());
  cbpSubstTrailedThisLevel.clear();
  cbpCallerCheckpoints.push_back(CbpCallerCheckpoint{
      cbpSubstUndo.size(), cbpFedConjunctsAdded.size(), cbpFactsAdded.size(),
      fedBefore, cbpFedArrays, callCbpOff, callCbpConflict});
  cbpCallerLevelOpen = true;
}

void IncrementalSolver::Impl::cbpTrailSubstitution(const ASTNode& key)
{
  assert(cbpCallerLevelOpen);
  if (!cbpSubstTrailedThisLevel.insert(key).second)
    return;
  ASTNodeMap::const_iterator it = callCbpSubst.find(key);
  cbpSubstUndo.push_back(
      CbpSubstUndo(key, it == callCbpSubst.end() ? ASTNode() : it->second,
                   it != callCbpSubst.end()));
}

void IncrementalSolver::Impl::cbpAssignSubstitution(const ASTNode& key, const ASTNode& value)
{
  cbpTrailSubstitution(key);
  callCbpSubst[key] = value;
}

void IncrementalSolver::Impl::cbpEraseSubstitution(const ASTNode& key)
{
  cbpTrailSubstitution(key);
  callCbpSubst.erase(key);
}

void IncrementalSolver::Impl::cbpInsertFedConjunct(const ASTNode& node)
{
  if (callCbpFedConjuncts.find(node) != callCbpFedConjuncts.end())
    return;
  assert(cbpCallerLevelOpen);
  if (!cbpCallerLevelOpen)
    return;
  callCbpFedConjuncts.insert(node);
  cbpFedConjunctsAdded.push_back(node);
}

bool IncrementalSolver::Impl::cbpInsertFactDomain(const ASTNode& node)
{
  if (callCbpFactEmitted.find(node) != callCbpFactEmitted.end())
    return false;
  assert(cbpCallerLevelOpen);
  if (!cbpCallerLevelOpen)
    return false;
  callCbpFactEmitted.insert(node);
  cbpFactsAdded.push_back(node);
  return true;
}

size_t IncrementalSolver::Impl::cbpRollbackCallerTo(size_t levels)
{
  assert(levels <= cbpCallerCheckpoints.size());
  assert(callCbpDeferred.empty());
  assert(!cbpCallerLevelOpen);
  size_t entries = 0;
  while (cbpCallerCheckpoints.size() > levels)
  {
    const CbpCallerCheckpoint checkpoint = cbpCallerCheckpoints.back();
    cbpCallerCheckpoints.pop_back();
    while (cbpSubstUndo.size() > checkpoint.substUndo)
    {
      const CbpSubstUndo& undo = cbpSubstUndo.back();
      if (undo.existed)
        callCbpSubst[undo.key] = undo.oldValue;
      else
        callCbpSubst.erase(undo.key);
      cbpSubstUndo.pop_back();
      entries++;
    }
    while (cbpFedConjunctsAdded.size() > checkpoint.fedConjunctsAdded)
    {
      const size_t erased =
          callCbpFedConjuncts.erase(cbpFedConjunctsAdded.back());
      assert(erased == 1);
      (void)erased;
      cbpFedConjunctsAdded.pop_back();
      entries++;
    }
    while (cbpFactsAdded.size() > checkpoint.factsAdded)
    {
      const size_t erased = callCbpFactEmitted.erase(cbpFactsAdded.back());
      assert(erased == 1);
      (void)erased;
      cbpFactsAdded.pop_back();
      entries++;
    }
    callCbpFed = checkpoint.fedBefore;
    cbpFedArrays = checkpoint.fedArraysBefore;
    callCbpOff = checkpoint.offBefore;
    callCbpConflict = checkpoint.conflictBefore;
  }
  // The refused level is gone, and its would-be charge with it, so the
  // capacity judgement that refused it no longer describes this stack.
  // Rolling back TO the refusal depth leaves the same stack that was
  // refused, so only a strictly shallower one releases it.
  if (cbpOverFeedCap() && levels < cbpOverFeedCapAt)
    cbpOverFeedCapAt = noFeedCapRefusal;
  cbpSubstTrailedThisLevel.clear();
  cbpCallerLevelOpen = false;
  callCbpDeferred.clear();
  scopes.rollbackCbpFedTo(levels);
  return entries;
}

void IncrementalSolver::Impl::cbpReset()
{
  callCbp.reset();
  callCbpSubst.clear();
  callCbpDeferred.clear();
  callCbpFactEmitted.clear();
  callCbpFedConjuncts.clear();
  scopes.resetCbpFed();
  cbpCallerCheckpoints.clear();
  cbpSubstUndo.clear();
  cbpFedConjunctsAdded.clear();
  cbpFactsAdded.clear();
  cbpSubstTrailedThisLevel.clear();
  cbpCallerLevelOpen = false;
  callCbpFed = 0;
  cbpOverFeedCapAt = noFeedCapRefusal;
  cbpFedArrays = false;
}

// Feed one live level's raw conjunction to the engine and collect
// the newly fixed nodes into the substitution. An already-fed level
// (the stable prefix of a persisting session) is a no-op: its
// fixings are in the map and its rewrites replay from the memo. The
// level's own fed conjuncts' fixings are DEFERRED until
// cbpFinishLevel: a conjunct must never rewrite under its own
// assumption-of-truth (substituting a fed conjunct's TRUE into its
// own slot erases the constraint -- the circularity measured as a
// refinement livelock the moment it was admitted), and parking the
// whole level's entries keeps every sibling rewrite safe too.
// Occurrences inside DEEPER levels' conjuncts still fold, justified
// without a pinning fact by the fed conjunct's own asserted slot.
void IncrementalSolver::Impl::cbpFeedLevel(size_t level, const ASTNode& levelConjunction)
{
  if (callCbpOff || cbpSessionRetired)
    return;
  // Levels feed in stack order exactly once; anything else is a
  // prefix this session already carries.
  if (level != scopes.cbpFedDepth())
    return;
  const bool refeed = level < cbpMemoStable;
  ScopedProfileTimer cbpTimer(profile.enabled, profile.cbpNs);
  ScopedProfileTimer feedTimer(profile.enabled, profile.cbpFeedNs);
  ScopedProfileTimer feedClassTimer(
      profile.enabled, refeed ? profile.cbpRefeedNs : profile.cbpFreshFeedNs);
  if (!callCbp)
    callCbp.reset(new IncrementalCBP(bm, bm->defaultNodeFactory));

  // Charge the cap what this level ADDS, not what it spans. Levels share
  // subgraphs by identity -- a pushed level is usually a small delta over
  // the cone its parent already established -- and the engine visits a
  // shared node once, ever: extendParentMap stops at depsVisited, and the
  // parent map, the fixed-bits map and the undo trail all key on the node.
  // Summing per-level DAG sizes therefore charged one shared cone once per
  // level that mentions it, and a stack of twenty such levels read as
  // twenty times the mass the engine was actually holding. It is the same
  // over-count that makes DAG size the wrong measure for adoption's shrink
  // gate: interned structure is not paid for twice.
  const size_t cap = cbpFeedCap();
  const size_t levelNodes = callCbp->freshNodeCount(levelConjunction, cap);
  const size_t fedBefore = callCbpFed;
  assert(callCbpFed <= cap);
  if (levelNodes > cap - callCbpFed)
  {
    if (profile.enabled)
      profile.cbpFeedRejected++;
    feedClassTimer.retarget(profile.enabled, profile.cbpRejectedFeedNs);
    callCbpOff = true;
    cbpOverFeedCapAt = level;
    if (bm->UserFlags.stats_flag)
      std::cerr << "Incremental: cbp off at level " << level
                << " (stack over the feed cap)" << std::endl;
    return;
  }
  callCbpFed += levelNodes;
  cbpBeginCallerLevel(fedBefore);
  if (profile.enabled)
  {
    profile.cbpFedLevels++;
    profile.cbpFedNodes += levelNodes;
    if (refeed)
    {
      profile.cbpRefedLevels++;
      profile.cbpRefedNodes += levelNodes;
    }
    else
    {
      profile.cbpFreshLevels++;
      profile.cbpFreshNodes += levelNodes;
    }
  }

  ASTVec fed;
  splitConjuncts(levelConjunction, bm->ASTTrue, fed);
  fed.push_back(levelConjunction);
  for (const ASTNode& c : fed)
    cbpInsertFedConjunct(c);

  bool consistent;
  const bool wasInConflict = callCbp->inConflict();
  {
    ScopedProfileTimer propagationTimer(profile.enabled,
                                        profile.cbpPropagateNs);
    consistent = callCbp->feedLevel(levelConjunction);
  }
  // The charge IS the retained mass. freshNodeCount and extendParentMap
  // walk the same graph under the same stopping rule, so an accepted feed
  // grows the engine's dependency set by exactly what was charged -- the
  // invariant the old per-level sum could not state, let alone check. A
  // feed onto an already-conflicting engine returns before extending the
  // graph at all, and is the one case that owes nothing.
  assert(wasInConflict || callCbpFed == callCbp->retainedNodes());
  (void)wasInConflict;
  assert(callCbp->levelCount() == cbpCallerCheckpoints.size());
  if (!consistent)
  {
    // The live prefix is contradictory by bit-level reasoning
    // alone; the caller asserts FALSE at this level. The feed
    // still consumed the level -- the engine's map and its latched
    // conflict carry this level's assumed truth -- so it MUST be
    // recorded: an unrecorded feed survives the level's pop (the
    // divergence check never sees it) and refutes whatever level
    // is pushed in its place. The refutation is the level's
    // memoised output, so an identical re-push replays FALSE
    // instead of re-running the feed.
    callCbpConflict = true;
    callCbpOff = true;
    scopes.markCbpFed(level);
    assert(cbpCallerCheckpoints.size() == scopes.cbpFedDepth());
    if (scopes.cbpMemoDepth() == level)
    {
      scopes.startCbpMemo(level).facts.push_back(
          ScopedFact(ASTNode(), bm->ASTFalse));
    }
    return;
  }

  // A fixing this level's own feed derived joins the substitution
  // only for DEEPER levels (via cbpFinishLevel) when it pins a
  // SYMBOL -- or an interior node over one: folding either into its
  // own level would usurp the definition harvest, whose machinery
  // (the pushed-definition context, the pieces' private-variable
  // elimination) owns intra-level substitution with model-replay
  // bookkeeping this pass does not carry -- and an interior fold's
  // pinning fact would drag the symbol into the encoding, spoiling
  // its eliminability for the rest of the session. Cross-level
  // visibility is this pass's whole charter; a node fixed here
  // through EARLIER levels' knowledge (the target family's
  // ite-indexed writes, whose flags other levels pin) carries no
  // symbol from THIS feed and still folds in place.
  // One walk per fed level decides whether the per-delta-node array
  // exclusion below has anything to exclude: an array-free fed
  // prefix cannot put an array-carrying node in the delta, and the
  // per-node walks were the dominant cost of feeding a large
  // array-free formula.
  {
    ScopedProfileTimer harvestTimer(profile.enabled, profile.cbpHarvestNs);
    if (!cbpFedArrays && containsArrayOps(levelConjunction, bm))
      cbpFedArrays = true;

    const std::vector<ASTNode>& feedDelta = callCbp->takeNewlyFixed();
    ASTNodeSet feedSymbols;
    for (const ASTNode& n : feedDelta)
    {
      if (callCbpSubst.size() + callCbpDeferred.size() >= cbpHarvestCap)
        break;
      if (n.GetKind() != SYMBOL)
        continue;
      const ASTNode k = callCbp->constantOf(n);
      if (k.IsNull())
        continue;
      callCbpDeferred.push_back(std::make_pair(n, k));
      feedSymbols.insert(n);
      noteEngineDerivedFixing(n);
    }
    for (const ASTNode& n : feedDelta)
    {
      if (callCbpSubst.size() + callCbpDeferred.size() >= cbpHarvestCap)
        break;
      if (n.GetKind() == SYMBOL || n.GetKind() == BVEXTRACT ||
          n.GetKind() == BVCONCAT)
        continue;
      const ASTNode k = callCbp->constantOf(n);
      if (k.IsNull())
        continue;
      if (cbpFedArrays && containsArrayOps(n, bm))
        continue;
      if (!feedSymbols.empty() && reachesAnyOf(n, feedSymbols))
        callCbpDeferred.push_back(std::make_pair(n, k));
      else
        cbpAssignSubstitution(n, k);
      noteEngineDerivedFixing(n);
    }

    for (const ASTNode& c : fed)
    {
      ASTNodeMap::iterator it = callCbpSubst.find(c);
      if (it != callCbpSubst.end())
      {
        callCbpDeferred.push_back(*it);
        cbpEraseSubstitution(c);
      }
    }
  }

  scopes.markCbpFed(level);
  assert(cbpCallerCheckpoints.size() == scopes.cbpFedDepth());
  // The memo entry parallels the feed; if this level was already memoised
  // under the same conjunction (the reset oracle/fallback re-feeding the
  // stable prefix), the existing entry keeps replaying.
  if (scopes.cbpMemoDepth() == level)
    scopes.startCbpMemo(level);
}

// Restore the fed-conjunct fixings cbpFeedLevel parked, once the
// level's own conjuncts are past rewriting.
void IncrementalSolver::Impl::cbpFinishLevel()
{
  if (!cbpCallerLevelOpen)
  {
    assert(callCbpDeferred.empty());
    return;
  }
  ScopedProfileTimer cbpTimer(profile.enabled, profile.cbpNs);
  ScopedProfileTimer finishTimer(profile.enabled, profile.cbpFinishNs);
  if (profile.enabled)
    profile.cbpDeferredRestored += callCbpDeferred.size();
  for (const std::pair<ASTNode, ASTNode>& e : callCbpDeferred)
    cbpAssignSubstitution(e.first, e.second);
  callCbpDeferred.clear();
  cbpSubstTrailedThisLevel.clear();
  cbpCallerLevelOpen = false;
}

// Rewrite one conjunct under the constants accumulated from levels
// <= its own. Adoption follows the trial policy's spirit: constant
// folds only ever shrink (the substitution replaces a subterm by a
// leaf), so any strict shrink is admitted; a same-size or grown
// result means the factory rewrote the spine into a novel shape on
// the way -- the shuffle class the trial gates exist to refuse --
// and the conjunct keeps its raw-keyed form and all the sharing
// that comes with it. Every replaced node's pinning fact (node ==
// constant; the node itself or its negation for Booleans) is
// collected into factsOut and asserted alongside this level's
// conjuncts, so the substitution loses nothing and the models the
// refinement loop validates stay models of the raw stack. Fed
// conjuncts are exempt: their own levels assert them for at least
// as long as any adopter lives.
//
// The substitution handed to replace() is RESTRICTED to entries
// whose keys occur in this conjunct's own DAG. replace() also maps
// nodes it REBUILDS on the way up -- hash-consing folded children
// can reproduce a fixed node the original conjunct never contained
// (a ctx-substituted form collapsing back onto the raw interior AND
// its level was fed as) -- and the fact walk, which can only see
// the original DAG, would assert no pinning fact for it: the
// fixing's whole constraint silently leaves the encoding, and the
// model (or the verdict) is no longer the raw stack's. Restricting
// the map makes "may fire" and "fact asserted" the same set again:
// a rebuilt node can still hit an entry, but only one whose key
// occurs -- and is therefore pinned -- somewhere in this conjunct.
ASTNode IncrementalSolver::Impl::cbpAdopt(const ASTNode& conjunct,
                 std::vector<ScopedFact>& factsOut)
{
  if (callCbpOff || !cbpCallerLevelOpen || callCbpSubst.empty())
    return conjunct;
  ScopedProfileTimer cbpTimer(profile.enabled, profile.cbpNs);
  ScopedProfileTimer adoptTimer(profile.enabled, profile.cbpAdoptNs);
  if (profile.enabled)
    profile.cbpAdoptAttempts++;

  // One walk collects the entries occurring in the conjunct, in a
  // deterministic order the fact emission below reuses. The
  // conjunct's own entry (a ctx-substituted form can be fixed as an
  // interior node without being a fed conjunct) never rewrites its
  // own slot, so the root is skipped as a domain.
  ASTNodeMap occurring;
  std::vector<std::pair<ASTNode, ASTNode>> occurringOrdered;
  {
    ASTNodeSet visited;
    std::vector<ASTNode> pending(1, conjunct);
    while (!pending.empty())
    {
      const ASTNode cur = pending.back();
      pending.pop_back();
      if (!visited.insert(cur).second)
        continue;
      ASTNodeMap::const_iterator sit = callCbpSubst.find(cur);
      if (sit != callCbpSubst.end() && !(cur == conjunct))
      {
        occurring.insert(*sit);
        occurringOrdered.push_back(*sit);
      }
      for (unsigned j = 0; j < cur.Degree(); j++)
        pending.push_back(cur[j]);
    }
  }
  if (occurring.empty())
    return conjunct;

  ASTNodeMap cache;
  const ASTNode adopted = SubstitutionMap::replace(
      conjunct, occurring, cache, bm->defaultNodeFactory);
  if (adopted == conjunct)
    return conjunct;

  const size_t before = dagSizeUpTo(conjunct, bigFormulaCap);
  if (dagSizeUpTo(adopted, before) >= before)
    return conjunct;

  for (const std::pair<ASTNode, ASTNode>& oe : occurringOrdered)
  {
    const ASTNode& cur = oe.first;
    if (callCbpFedConjuncts.find(cur) != callCbpFedConjuncts.end() ||
        !cbpInsertFactDomain(cur))
      continue;
    ASTNode fact;
    if (cur.GetType() == BOOLEAN_TYPE)
      fact = oe.second == bm->ASTTrue
                 ? cur
                 : bm->defaultNodeFactory->CreateNode(NOT, cur);
    else
      fact = bm->defaultNodeFactory->CreateNode(EQ, cur, oe.second);
    factsOut.push_back(ScopedFact(cur, fact));
  }

  callCbpAdopted++;
  cbpEpochAdopted++;
  if (profile.enabled)
    profile.cbpAdoptions++;
  return adopted;
}


} // namespace stp

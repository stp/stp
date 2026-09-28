/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

#include "stp/Incremental/IncrementalScopeState.h"

#include <algorithm>
#include <cassert>
#include <limits>

namespace stp
{

IncrementalScopeState::IncrementalScopeState()
    : nextLevelId(1), lastCommonPrefixValue(0), promotedDepthValue(0),
      promotionDriftPending(false), wholeStackActive(false)
{
}

void IncrementalScopeState::clearCurrentPreprocessing()
{
  wholeStackActive = false;
  wholeStackPreprocessing = PreprocessingTransaction();
  currentEliminations.clear();
  currentEliminatedVariables.clear();
  currentSemanticKeys.clear();
  for (Level& level : levels)
    level.activePreprocessing =
        PreprocessingTransaction(PreprocessingMode::Raw,
                                 level.rawConjunction);
}

void IncrementalScopeState::aggregate(
    const PreprocessingTransaction& transaction)
{
  currentSemanticKeys.insert(currentSemanticKeys.end(),
                             transaction.conjuncts.begin(),
                             transaction.conjuncts.end());
  for (const ScopedElimination& e : transaction.eliminated)
  {
    currentEliminations.push_back(e);
    if (e.symbol.GetKind() == SYMBOL)
      currentEliminatedVariables.insert(e.symbol);
  }
}

IncrementalScopeState::ReconcileResult
IncrementalScopeState::reconcile(const ASTVec& rawStack)
{
  size_t lcp = 0;
  while (lcp < levels.size() && lcp < rawStack.size() &&
         levels[lcp].rawConjunction == rawStack[lcp])
    ++lcp;

  bool demote = promotionDriftPending;
  promotionDriftPending = false;
  if (!demote && promotedDepthValue >= lcp && promotedDepthValue != 0)
    demote = true;

  for (size_t i = 0; i < lcp; ++i)
  {
    if (levels[i].stableSolves != std::numeric_limits<size_t>::max())
      ++levels[i].stableSolves;
  }
  levels.erase(levels.begin() + lcp, levels.end());
  for (size_t i = lcp; i < rawStack.size(); ++i)
    levels.push_back(Level(nextLevelId++, rawStack[i]));

  if (demote)
    clearPromotions();

  lastCommonPrefixValue = lcp;
  clearCurrentPreprocessing();
  return ReconcileResult{lcp, demote};
}

void IncrementalScopeState::commitLevel(
    size_t level, const PreprocessingTransaction& transaction)
{
  assert(!wholeStackActive);
  assert(level < levels.size());
  assert(transaction.accepted);
  assert(transaction.source.IsNull() ||
         transaction.source == levels[level].rawConjunction);
  levels[level].activePreprocessing = transaction;
  aggregate(transaction);
}

void IncrementalScopeState::commitWholeStack(
    const PreprocessingTransaction& transaction)
{
  assert(transaction.accepted);
  currentEliminations.clear();
  currentEliminatedVariables.clear();
  currentSemanticKeys.clear();
  wholeStackPreprocessing = transaction;
  wholeStackActive = true;
  aggregate(transaction);
}

bool IncrementalScopeState::promotedConjunctsChanged(
    size_t level, const ASTVec& conjuncts) const
{
  if (level >= levels.size() || !levels[level].promoted)
    return true;
  return levels[level].promotedConjuncts != conjuncts;
}

void IncrementalScopeState::promote(size_t level, const ASTVec& conjuncts)
{
  assert(level < levels.size());
  assert(level == promotedDepthValue + 1);
  levels[level].promoted = true;
  levels[level].promotedConjuncts = conjuncts;
  promotedDepthValue = level;
}

void IncrementalScopeState::clearPromotions()
{
  for (Level& level : levels)
  {
    level.promoted = false;
    level.promotedConjuncts.clear();
  }
  promotedDepthValue = 0;
}

size_t IncrementalScopeState::cbpFedCommonPrefix() const
{
  size_t lcp = 0;
  while (lcp < cbpFedLevels.size() && lcp < levels.size() &&
         cbpFedLevels[lcp].scopeId == levels[lcp].id)
  {
    assert(cbpFedLevels[lcp].rawConjunction ==
           levels[lcp].rawConjunction);
    ++lcp;
  }
  return lcp;
}

void IncrementalScopeState::markCbpFed(size_t level)
{
  assert(level == cbpFedLevels.size());
  assert(level < levels.size());
  cbpFedLevels.push_back(
      ConsumerLevel(levels[level].id, levels[level].rawConjunction));
}

void IncrementalScopeState::rollbackCbpFedTo(size_t depth)
{
  assert(depth <= cbpFedLevels.size());
  cbpFedLevels.erase(cbpFedLevels.begin() + depth, cbpFedLevels.end());
}

void IncrementalScopeState::releaseEpochStorage()
{
  assert(!wholeStackActive);
  assert(currentEliminations.empty());
  assert(currentEliminatedVariables.empty());
  assert(currentSemanticKeys.empty());

  // Copying the live levels deliberately drops capacity retained by a much
  // deeper, now-popped stack, including capacity in cleared promotion and
  // preprocessing vectors. Scope identity and stability counters survive.
  std::vector<Level>(levels).swap(levels);

  // clear()/resize(0) retain vector and hash-table high-water storage. A
  // relief epoch is a reclamation boundary, so release both the independent
  // CBP consumer and the already-reconciled transaction aggregates rather
  // than merely making them logically empty.
  std::vector<ConsumerLevel>().swap(cbpFedLevels);
  std::vector<CbpMemo>().swap(cbpMemos);
  std::vector<ScopedElimination>().swap(currentEliminations);
  ASTNodeSet().swap(currentEliminatedVariables);
  ASTVec().swap(currentSemanticKeys);
  wholeStackPreprocessing = PreprocessingTransaction();
}

size_t IncrementalScopeState::trimCbpMemoToCurrent()
{
  size_t lcp = 0;
  while (lcp < cbpMemos.size() && lcp < levels.size() &&
         cbpMemos[lcp].rawConjunction == levels[lcp].rawConjunction)
    ++lcp;
  cbpMemos.resize(lcp);
  return lcp;
}

IncrementalScopeState::CbpMemo&
IncrementalScopeState::startCbpMemo(size_t level)
{
  assert(level == cbpMemos.size());
  assert(level < levels.size());
  cbpMemos.push_back(CbpMemo());
  cbpMemos.back().rawConjunction = levels[level].rawConjunction;
  return cbpMemos.back();
}

} // namespace stp

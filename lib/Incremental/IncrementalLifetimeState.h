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

#ifndef INCREMENTALLIFETIMESTATE_H_
#define INCREMENTALLIFETIMESTATE_H_

#include "stp/Incremental/IncrementalWalks.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/ToSATBase.h"

#include <algorithm>
#include <cstdint>
#include <limits>
#include <vector>

namespace stp
{

// The refinement adapter hands this cache out by reference. Its validity is
// the conjunction of one check-sat's eliminated-variable filter and one CNF
// binding generation, so storage, validity and generation reset together.
//
// Invalidation marks staleness without clearing content immediately:
// getSatVariables may have inserted variables for never-blasted symbols into
// the handed-out map. Refresh happens only when the adapter asks again.
class IncrementalSymbolMapCache
{
  ToSATBase::ASTNodeToSATVar entries;
  bool current = false;
  uint64_t generation = 0;

public:
  bool validFor(uint64_t candidateGeneration) const
  {
    return current && generation == candidateGeneration;
  }

  ToSATBase::ASTNodeToSATVar& storage() { return entries; }

  void markCurrent(uint64_t currentGeneration)
  {
    generation = currentGeneration;
    current = true;
  }

  void invalidate() { current = false; }

  void releaseStorage()
  {
    ToSATBase::ASTNodeToSATVar empty;
    entries.swap(empty);
    current = false;
    generation = 0;
  }
};

// One coalesced exact-live-cone snapshot. Its roots, permanent prefix and
// non-structural mass are meaningful only as a unit; clear and relief release
// cannot leave a stale "active" bit beside partially reset payload.
class IncrementalPendingLiveCone
{
  std::vector<Aig_Obj_t*> currentRoots;
  size_t permanentRootCount = 0;
  uint64_t nonStructuralMass = 0;
  bool staged = false;

public:
  bool active() const { return staged; }
  const std::vector<Aig_Obj_t*>& roots() const { return currentRoots; }
  size_t permanentRoots() const { return permanentRootCount; }
  uint64_t nonStructural() const { return nonStructuralMass; }

  void replace(std::vector<Aig_Obj_t*>& roots, size_t permanentRoots,
               uint64_t nonStructural)
  {
    currentRoots.swap(roots);
    permanentRootCount = permanentRoots;
    nonStructuralMass = nonStructural;
    staged = true;
  }

  void clear()
  {
    currentRoots.clear();
    permanentRootCount = 0;
    nonStructuralMass = 0;
    staged = false;
  }

  void releaseStorage()
  {
    std::vector<Aig_Obj_t*> empty;
    currentRoots.swap(empty);
    permanentRootCount = 0;
    nonStructuralMass = 0;
    staged = false;
  }
};

// Retained semantic roots and the live/retained measurements derived from
// them all belong to one encoding epoch. Keeping the accounting here makes a
// rotation unable to retain an old high-water mark beside a fresh root set.
class IncrementalSemanticEpochAccounting
{
  ASTNodeSet retainedRoots;
  uint64_t nodeCharge = 0;
  ASTVec latestLiveRoots;
  uint64_t maxLiveNodes = 0;
  uint64_t lastRetainedNodes = 0;

public:
  void charge(const ASTNode& root, size_t limit)
  {
    if (limit == 0 || root.IsNull() ||
        !retainedRoots.insert(root).second || nodeCharge >= limit)
      return;

    const size_t remaining = limit - static_cast<size_t>(nodeCharge);
    const size_t amount = IncrementalWalks::dagSizeUpTo(root, remaining);
    nodeCharge = amount > remaining ? limit : nodeCharge + amount;
  }

  void stage(const ASTVec& rawStack, const ASTVec& encodedRoots)
  {
    ASTVec next = rawStack;
    next.insert(next.end(), encodedRoots.begin(), encodedRoots.end());
    latestLiveRoots.swap(next);
  }

  bool reliefReached(size_t limit)
  {
    if (limit == 0 || nodeCharge < limit || latestLiveRoots.empty())
      return false;

    const uint64_t live = IncrementalWalks::astDagUnionSize(latestLiveRoots);
    maxLiveNodes = std::max(maxLiveNodes, live);

    ASTVec roots(retainedRoots.begin(), retainedRoots.end());
    lastRetainedNodes = IncrementalWalks::astDagUnionSize(roots);
    return maxLiveNodes != std::numeric_limits<uint64_t>::max() &&
           maxLiveNodes + 1 <= lastRetainedNodes / 4;
  }

  size_t retainedRootCount() const { return retainedRoots.size(); }
  uint64_t maxLiveNodeCount() const { return maxLiveNodes; }
  uint64_t lastRetainedNodeCount() const { return lastRetainedNodes; }

  void releaseStorage()
  {
    ASTNodeSet emptyRetained;
    retainedRoots.swap(emptyRetained);
    nodeCharge = 0;
    ASTVec emptyLive;
    latestLiveRoots.swap(emptyLive);
    maxLiveNodes = 0;
    lastRetainedNodes = 0;
  }
};

} // namespace stp

#endif

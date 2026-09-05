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

/* Prefix constant-bit propagation for the incremental driver; see the header
 * for its cross-call ownership contract. The worklist scheme follows the batch
 * WorkList (cheap transfer functions drain before expensive ones);
 * the transfer functions themselves ARE the batch ones, reached
 * through ConstantBitPropagation::dispatchToTransferFunctions, so the
 * bit-level reasoning is shared with the batch pipeline verbatim.
 */

#include "stp/Incremental/IncrementalCBP.h"

#include "stp/AST/AST.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"

#include <cassert>

using simplifier::constantBitP::ConstantBitPropagation;
using simplifier::constantBitP::FixedBits;
using simplifier::constantBitP::MultiplicationStatsMap;
using simplifier::constantBitP::NodeToFixedBitsMap;
using simplifier::constantBitP::Result;

namespace stp
{

IncrementalCBP::IncrementalCBP(STPMgr* mgr_, NodeFactory* nf_)
    : mgr(mgr_), nf(nf_), fixedMap(new NodeToFixedBitsMap(1000)),
      msm(new MultiplicationStatsMap()), conflict(false)
{
}

IncrementalCBP::~IncrementalCBP()
{
  delete fixedMap;
  delete msm;
}

void IncrementalCBP::beginLevel()
{
  assert(workEmpty());
  assert(currentFixedTrailed.empty());
  assert(currentFixedCreated.empty());
  assert(currentMultiplicationTrailed.empty());
  checkpoints.push_back(Checkpoint{
      fixedUndo.size(), fixedCreated.size(), dependenciesAdded.size(),
      multiplicationUndo.size(), multiplicationCreated.size(), conflict});
}

void IncrementalCBP::finishLevel()
{
  currentFixedTrailed.clear();
  currentFixedCreated.clear();
  currentMultiplicationTrailed.clear();
}

IncrementalCBP::RollbackStats IncrementalCBP::rollbackTo(size_t levels)
{
  assert(levels <= checkpoints.size());
  RollbackStats stats;

  // Conflict handling already clears both queues. Clear all transient output
  // defensively here too: no queued node or per-feed delta belongs to a
  // committed boundary, and every discarded level must leave clean scratch
  // before propagation may resume.
  cheapWork.clear();
  expensiveWork.clear();
  newlyFixed.clear();
  childBits.clear();
  prevChildCounts.clear();
  finishLevel();

  while (checkpoints.size() > levels)
  {
    const Checkpoint checkpoint = checkpoints.back();
    checkpoints.pop_back();
    stats.levels++;

    while (multiplicationCreated.size() > checkpoint.multiplicationCreated)
    {
      msm->map.erase(multiplicationCreated.back());
      multiplicationCreated.pop_back();
      stats.multiplicationStates++;
    }
    while (multiplicationUndo.size() > checkpoint.multiplicationUndo)
    {
      const MultiplicationUndo& undo = multiplicationUndo.back();
      MultiplicationStatsMap::NodeToStats::iterator it =
          msm->map.find(undo.node);
      if (it == msm->map.end())
        msm->map.insert(std::make_pair(undo.node, undo.oldStats));
      else
        it->second = undo.oldStats;
      multiplicationUndo.pop_back();
      stats.multiplicationStates++;
    }

    // Dependency edges were appended in the same order as
    // dependenciesAdded. Removing newly visited nodes in reverse therefore
    // pops precisely their own edges, including duplicate child positions.
    while (dependenciesAdded.size() > checkpoint.dependenciesAdded)
    {
      const ASTNode n = dependenciesAdded.back();
      dependenciesAdded.pop_back();
      for (unsigned i = n.Degree(); i > 0; i--)
      {
        const ASTNode& child = n[i - 1];
        if (child.isConstant())
          continue;
        std::map<uint64_t, std::vector<ASTNode>>::iterator parents =
            parentMap.find(child.GetNodeNum());
        assert(parents != parentMap.end());
        assert(!parents->second.empty());
        assert(parents->second.back() == n);
        parents->second.pop_back();
        if (parents->second.empty())
          parentMap.erase(parents);
      }
      const size_t erased = depsVisited.erase(n);
      assert(erased == 1);
      (void)erased;
      stats.dependencyNodes++;
    }

    while (fixedCreated.size() > checkpoint.fixedCreated)
    {
      const ASTNode n = fixedCreated.back();
      fixedCreated.pop_back();
      NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it =
          fixedMap->map->find(n);
      assert(it != fixedMap->map->end());
      delete it->second;
      fixedMap->map->erase(it);
      stats.createdFixedStates++;
    }
    while (fixedUndo.size() > checkpoint.fixedUndo)
    {
      const FixedUndo& undo = fixedUndo.back();
      NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it =
          fixedMap->map->find(undo.node);
      assert(it != fixedMap->map->end());
      *it->second = undo.oldBits;
      fixedUndo.pop_back();
      stats.fixedStates++;
    }

    conflict = checkpoint.conflict;
  }
  return stats;
}

void IncrementalCBP::extendParentMap(const ASTNode& root)
{
  std::vector<ASTNode> stack;
  stack.push_back(root);

  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();

    if (n.isConstant())
      continue;
    if (!depsVisited.insert(n).second)
      continue;
    dependenciesAdded.push_back(n);

    for (unsigned i = 0; i < n.Degree(); i++)
    {
      const ASTNode& child = n[i];
      if (child.isConstant())
        continue;
      parentMap[child.GetNodeNum()].push_back(n);
    }

    for (unsigned i = 0; i < n.Degree(); i++)
      stack.push_back(n[i]);
  }
}

size_t IncrementalCBP::freshNodeCount(const ASTNode& root, size_t budget) const
{
  ASTNodeSet fresh;
  std::vector<ASTNode> stack;
  stack.push_back(root);

  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();

    if (n.isConstant())
      continue;
    // Already in the graph. extendParentMap stops here too, and it stopped
    // here on the feed that first visited it, so the whole subgraph beneath
    // is present and none of it is new.
    if (depsVisited.find(n) != depsVisited.end())
      continue;
    if (!fresh.insert(n).second)
      continue;
    if (fresh.size() > budget)
      return fresh.size();

    for (unsigned i = 0; i < n.Degree(); i++)
      stack.push_back(n[i]);
  }
  return fresh.size();
}

// The batch WorkList's queue discipline -- the same seven expensive
// transfer kinds, cheap work draining first -- over std::set rather than
// its insertion-ordered dense set. The container is NOT incidental:
// node-number-ordered pops keep the fixpoint's visit order independent
// of feed history (an insertion-ordered replay after a rollback would
// visit in a different order than the original feed), and the two
// orders produce the same fixpoint but different intermediate work, so
// unifying on WorkList is a measured change (a corpus differential),
// not a refactor.
void IncrementalCBP::pushWork(const ASTNode& n)
{
  if (n.isConstant())
    return;
  switch (n.GetKind())
  {
    case BVMULT:
    case BVPLUS:
    case BVDIV:
    case BVMOD:
    case SBVDIV:
    case SBVREM:
    case SBVMOD:
      expensiveWork.insert(n);
      break;
    default:
      cheapWork.insert(n);
      break;
  }
}

ASTNode IncrementalCBP::popWork()
{
  if (!cheapWork.empty())
  {
    const ASTNode n = *cheapWork.begin();
    cheapWork.erase(cheapWork.begin());
    return n;
  }
  const ASTNode n = *expensiveWork.begin();
  expensiveWork.erase(expensiveWork.begin());
  return n;
}

bool IncrementalCBP::workEmpty() const
{
  return cheapWork.empty() && expensiveWork.empty();
}

// Seed the worklist with the sub-DAG's nodes that have at least one
// KNOWN child: a syntactic constant (the batch WorkList's initial
// population rule), or a node an earlier level's feed already fixed
// bits of. The batch pass sees the whole formula in one feed and
// needs only the syntactic rule; here a deeper level's fresh DAG must
// pick up what the shallower feeds already know, or a cross-level
// fixing would only reach nodes that happen to also carry a constant
// child.
void IncrementalCBP::seedWorklist(const ASTNode& n)
{
  ASTNodeSet visited;
  std::vector<ASTNode> stack;
  stack.push_back(n);

  while (!stack.empty())
  {
    const ASTNode node = stack.back();
    stack.pop_back();

    if (node.isConstant())
      continue;
    if (!visited.insert(node).second)
      continue;

    bool hasKnownChild = false;
    for (unsigned i = 0; i < node.Degree(); i++)
    {
      const ASTNode& child = node[i];
      if (child.isConstant())
        hasKnownChild = true;
      else if (!hasKnownChild)
      {
        NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it =
            fixedMap->map->find(child);
        if (it != fixedMap->map->end() && it->second->countFixed() > 0)
          hasKnownChild = true;
      }
      stack.push_back(child);
    }
    if (hasKnownChild)
      pushWork(node);
  }
}

FixedBits* IncrementalCBP::getOrCreate(const ASTNode& n)
{
  assert(!checkpoints.empty());
  NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it =
      fixedMap->map->find(n);
  if (it != fixedMap->map->end())
    return it->second;

  // The batch seeding, verbatim; only the trail bookkeeping is ours.
  FixedBits* fb = ConstantBitPropagation::makeInitialFixedBits(n);
  fixedMap->map->insert(std::make_pair(n, fb));
  fixedCreated.push_back(n);
  currentFixedCreated.insert(n);
  return fb;
}

void IncrementalCBP::recordBeforeMutation(const ASTNode& n, FixedBits* bits)
{
  assert(!checkpoints.empty());
  if (currentFixedCreated.find(n) != currentFixedCreated.end())
    return;
  if (currentFixedTrailed.insert(n).second)
    fixedUndo.push_back(FixedUndo(n, *bits));
}

void IncrementalCBP::recordMultiplicationBeforeMutation(const ASTNode& n)
{
  assert(!checkpoints.empty());
  if (!currentMultiplicationTrailed.insert(n).second)
    return;
  MultiplicationStatsMap::NodeToStats::const_iterator it = msm->map.find(n);
  if (it == msm->map.end())
    multiplicationCreated.push_back(n);
  else
    multiplicationUndo.push_back(MultiplicationUndo(n, it->second));
}

void IncrementalCBP::scheduleParents(const ASTNode& n, const ASTNode& except)
{
  const std::map<uint64_t, std::vector<ASTNode>>::const_iterator it =
      parentMap.find(n.GetNodeNum());
  if (it == parentMap.end())
    return;
  for (const ASTNode& p : it->second)
    if (!(p == except))
      pushWork(p);
}

void IncrementalCBP::propagate()
{
  if (conflict)
    return;

  while (!workEmpty())
  {
    const ASTNode n = popWork();
    if (n.isConstant())
      continue;

    FixedBits* nBits = getOrCreate(n);
    const unsigned previousTop = nBits->countFixed();
    const bool topWasTotal = nBits->isTotallyFixed();

    const unsigned degree = n.Degree();
    childBits.clear();
    prevChildCounts.clear();
    for (unsigned i = 0; i < degree; i++)
    {
      FixedBits* cb = getOrCreate(n[i]);
      childBits.push_back(cb);
      prevChildCounts.push_back(cb->countFixed());
    }

    Result status = simplifier::constantBitP::NO_CHANGE;
    if (SYMBOL != n.GetKind())
    {
      // The batch transfer functions are intentionally opaque here and may
      // fix the result or any operand. Snapshot each pre-existing object at
      // most once in this level; newly created objects are removed wholesale.
      recordBeforeMutation(n, nBits);
      for (unsigned i = 0; i < degree; i++)
        recordBeforeMutation(n[i], childBits[i]);
      if (BVMULT == n.GetKind())
        recordMultiplicationBeforeMutation(n);
      status = ConstantBitPropagation::dispatchToTransferFunctions(
          mgr, n.GetKind(), childBits, *nBits, n, msm);
    }

    if (simplifier::constantBitP::CONFLICT == status)
    {
      conflict = true;
      cheapWork.clear();
      expensiveWork.clear();
      newlyFixed.clear();
      return;
    }

    if (status == simplifier::constantBitP::NO_CHANGE)
      continue;

    if (nBits->countFixed() != previousTop)
    {
      scheduleParents(n, n);
      if (!topWasTotal && nBits->isTotallyFixed())
        newlyFixed.push_back(n);
    }
    for (unsigned i = 0; i < degree; i++)
    {
      if (childBits[i]->countFixed() != prevChildCounts[i])
      {
        scheduleParents(n[i], n);
        pushWork(n[i]);
        const bool wasTotal = prevChildCounts[i] == childBits[i]->getWidth();
        if (!wasTotal && childBits[i]->isTotallyFixed() && !n[i].isConstant())
          newlyFixed.push_back(n[i]);
      }
    }
  }
}

bool IncrementalCBP::feedLevel(const ASTNode& conjunction)
{
  beginLevel();
  newlyFixed.clear();
  if (conflict)
  {
    finishLevel();
    return false;
  }

  extendParentMap(conjunction);
  seedWorklist(conjunction);

  // The level is asserted for the whole call, so its truth is a sound
  // assumption for every consequence drawn this call. The AND transfer
  // function pushes the truth down to every conjunct from here.
  FixedBits* topBits = getOrCreate(conjunction);
  if (conjunction.GetType() == BOOLEAN_TYPE && topBits->isTotallyFixed() &&
      !topBits->getValue(0))
  {
    conflict = true;
    cheapWork.clear();
    expensiveWork.clear();
    newlyFixed.clear();
    finishLevel();
    return false;
  }
  if (conjunction.GetType() == BOOLEAN_TYPE && !topBits->isTotallyFixed())
  {
    recordBeforeMutation(conjunction, topBits);
    topBits->setFixed(0, true);
    topBits->setValue(0, true);
    // The assumption is a fixing like any other: a single-conjunct
    // level's conjunction IS the conjunct (a bare flag, say), and its
    // deep occurrences fold only if the caller sees it. The caller's
    // slot protection and fed-conjunct fact rules handle the rest.
    newlyFixed.push_back(conjunction);
  }
  pushWork(conjunction);

  propagate();
  assert(workEmpty());
  finishLevel();
  return !conflict;
}

ASTNode IncrementalCBP::constantOf(const ASTNode& n) const
{
  if (n.isConstant())
    return ASTNode();
  if (n.GetType() != BOOLEAN_TYPE && n.GetType() != BITVECTOR_TYPE)
    return ASTNode();
  const NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it =
      fixedMap->map->find(n);
  if (it == fixedMap->map->end() || !it->second->isTotallyFixed())
    return ASTNode();

  // The batch conversion, on this engine's factory.
  return ConstantBitPropagation::bitsToNode(nf, n, *it->second);
}

} // namespace stp

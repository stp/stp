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

#ifndef INCREMENTALWALKS_H_
#define INCREMENTALWALKS_H_

// The incremental driver's DAG-walk utilities and their epoch-scoped
// memos: per-node symbol sets over allocation-free paged visit marks,
// capped DAG-size counts (exact only up to the cap -- every caller is a
// threshold test), multi-root union size, and a budget-bounded
// reachability probe. All walks keep their position on the heap, so
// input-chosen DAG depth cannot exhaust the call stack.

#include "stp/AST/AST.h"

#include <cassert>
#include <cstdint>
#include <memory>
#include <unordered_map>
#include <vector>

namespace stp
{

class IncrementalWalks
{
  // Per-node symbol sets, memoised for this encoding epoch; the keys hold
  // their nodes.
  // Looked up by node and never iterated, so it wants hashing rather than
  // the ordered comparison an std::map would do on every probe -- and it is
  // probed once per candidate per piece per check.
  typedef std::unordered_map<ASTNode, ASTNodeSet, ASTNode::ASTNodeHasher,
                             ASTNode::ASTNodeEqual>
      NodeSymbolsMap;
  NodeSymbolsMap symbolsOfCache;

  // Allocation-free scratch marks for symbol DAG walks. Node ids are
  // process-thread-wide, monotone, and not reset with an encoding epoch. A
  // sparse page map is therefore essential: a vector indexed by page number
  // would immediately recreate a pointer span proportional to all historical
  // node ids after every relief rotation, defeating memory reclamation.
  static const size_t symbolVisitPageBits = 16;
  static const size_t symbolVisitPageSize = size_t(1) << symbolVisitPageBits;
  static const size_t symbolVisitPageMask = symbolVisitPageSize - 1;
  std::unordered_map<uint64_t, std::unique_ptr<uint8_t[]>> symbolVisitPages;
  uint8_t symbolVisitEpoch = 0;

  // The first node number this manager can have minted; page offsets are
  // relative to it.
  const uint64_t baseNodeNum;

  // The granularity measurement recurs for the same nodes on every call
  // of a deep session (every level's granularity is re-judged per
  // check-sat); nodes are immutable, so the clipped count is a permanent
  // fact. The CBP feed does NOT measure sizes -- it asks the engine what a
  // level would add to what it already holds, which no per-node size can
  // answer.
  typedef std::unordered_map<ASTNode, size_t, ASTNode::ASTNodeHasher,
                             ASTNode::ASTNodeEqual>
      NodeSizeMemo;
  NodeSizeMemo dagSizeBigMemo;

  void beginSymbolVisit()
  {
    symbolVisitEpoch++;
    if (symbolVisitEpoch != 0)
      return;
    for (auto& entry : symbolVisitPages)
      std::fill(entry.second.get(), entry.second.get() + symbolVisitPageSize,
                uint8_t(0));
    symbolVisitEpoch = 1;
  }

  bool firstSymbolVisit(const ASTNode& n)
  {
    const uint64_t node = n.GetNodeNum();
    assert(node >= baseNodeNum);
    const uint64_t relative = node - baseNodeNum;
    const uint64_t page64 = relative >> symbolVisitPageBits;
    std::unique_ptr<uint8_t[]>& page = symbolVisitPages[page64];
    if (!page)
      page.reset(new uint8_t[symbolVisitPageSize]());
    uint8_t& mark = page[static_cast<size_t>(relative) & symbolVisitPageMask];
    if (mark == symbolVisitEpoch)
      return false;
    mark = symbolVisitEpoch;
    return true;
  }

public:
  // `falseNode` is the manager's ASTFalse: the first node it minted, so
  // every node number is at or above it.
  explicit IncrementalWalks(const ASTNode& falseNode)
      : baseNodeNum(falseNode.GetNodeNum())
  {
  }

  // Both symbol walkers are the shared collectSymbols() walk (AST.h) over
  // the paged epoch marks in place of the library wrapper's per-call
  // ASTNodeSet.
  const ASTNodeSet& symbolsOf(const ASTNode& n)
  {
    NodeSymbolsMap::iterator hit = symbolsOfCache.find(n);
    if (hit != symbolsOfCache.end())
      return hit->second;

    beginSymbolVisit();
    ASTNodeSet& out = symbolsOfCache[n];
    collectSymbols(ASTVec(1, n),
                   [this](const ASTNode& node)
                   { return firstSymbolVisit(node); },
                   out);
    return out;
  }

  // Add the union of symbols reachable from several roots in ONE DAG walk.
  // Calling symbolsOf() for each root separately is intentionally useful when
  // callers need each individual set, but is catastrophic for a large family
  // of overlapping roots: CBP can expose thousands of eligible fixed domains
  // over the same define-fun spine.  Protection only needs their union.
  void addSymbolsOf(const ASTVec& roots, ASTNodeSet& out)
  {
    if (roots.empty())
      return;
    beginSymbolVisit();
    collectSymbols(roots,
                   [this](const ASTNode& node)
                   { return firstSymbolVisit(node); },
                   out);
  }

  // DAG node count up to `cap`; the returned value is only guaranteed
  // exact while it is <= cap, which is what every threshold caller needs.
  static size_t dagSizeUpTo(const ASTNode& n, size_t cap)
  {
    ASTNodeSet visited;
    std::vector<ASTNode> pending(1, n);
    while (!pending.empty() && visited.size() <= cap)
    {
      const ASTNode cur = pending.back();
      pending.pop_back();
      if (!visited.insert(cur).second)
        continue;
      for (unsigned i = 0; i < cur.Degree(); i++)
        pending.push_back(cur[i]);
    }
    return visited.size();
  }

  // The memoised variant, against the epoch-scoped big-formula memo; only
  // meaningful for one fixed cap per instance, which is how the driver
  // uses it (the granularity cap).
  size_t dagSizeUpToBigMemo(const ASTNode& n, size_t cap)
  {
    NodeSizeMemo::const_iterator it = dagSizeBigMemo.find(n);
    if (it != dagSizeBigMemo.end())
      return it->second;
    const size_t s = dagSizeUpTo(n, cap);
    dagSizeBigMemo[n] = s;
    return s;
  }

  static uint64_t astDagUnionSize(const ASTVec& roots)
  {
    ASTNodeSet visited;
    ASTVec pending = roots;
    while (!pending.empty())
    {
      const ASTNode node = pending.back();
      pending.pop_back();
      if (node.IsNull() || !visited.insert(node).second)
        continue;
      for (unsigned i = 0; i < node.Degree(); ++i)
        pending.push_back(node[i]);
    }
    return static_cast<uint64_t>(visited.size());
  }

  // Early-exit containment: does `n` reach any of `syms`? The
  // harvest's per-delta-node filters must stay walk-bounded with no
  // per-node set materialisation -- a large formula's fixpoint delta
  // is tens of thousands of nodes, and building symbol sets for each
  // measured minutes on a single feed. A walk that exhausts its
  // budget answers "reaches": the caller then defers the fixing,
  // which only forgoes an intra-level fold.
  static bool reachesAnyOf(const ASTNode& n, const ASTNodeSet& syms)
  {
    static const size_t walkBudget = 2000;
    ASTNodeSet visited;
    std::vector<ASTNode> pending(1, n);
    while (!pending.empty())
    {
      const ASTNode cur = pending.back();
      pending.pop_back();
      if (cur.isConstant())
        continue;
      if (!visited.insert(cur).second)
        continue;
      if (visited.size() > walkBudget)
        return true;
      if (syms.find(cur) != syms.end())
        return true;
      for (unsigned i = 0; i < cur.Degree(); i++)
        pending.push_back(cur[i]);
    }
    return false;
  }

  size_t cacheEntryCount() const
  {
    return symbolsOfCache.size() + symbolVisitPages.size() +
           dagSizeBigMemo.size();
  }

  // Symbol sets are a pure function of the node, so clearing is
  // reclamation, not invalidation: entries for still-live nodes are
  // re-derived on the next solve that asks. SAT-only policy restarts may
  // reclaim this cheap memo even though they retain the structural AIG
  // epoch.
  void reclaimSymbolSets() { symbolsOfCache.clear(); }

  // Release everything, storage included, at a relief rotation.
  void releaseEpochStorage()
  {
    NodeSymbolsMap emptySymbols;
    symbolsOfCache.swap(emptySymbols);
    std::unordered_map<uint64_t, std::unique_ptr<uint8_t[]>> emptyPages;
    symbolVisitPages.swap(emptyPages);
    symbolVisitEpoch = 0;
    NodeSizeMemo emptySizes;
    dagSizeBigMemo.swap(emptySizes);
  }
};

} // namespace stp

#endif

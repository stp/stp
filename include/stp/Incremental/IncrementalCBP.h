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

/* Prefix constant-bit propagation over the incremental driver's live stack.
 *
 * A worklist engine around the batch transfer functions
 * (ConstantBitPropagation::dispatchToTransferFunctions), fed one level
 * at a time in stack order:
 *
 *   feedLevel(level_conjunction)
 *     Extends the DAG with the level's conjunction, assumes it TRUE
 *     (each fed level is asserted for the whole call, so its truth is
 *     a sound assumption for every consequence drawn this call), and
 *     propagates to a fixpoint.  Facts discovered while feeding level
 *     L therefore depend only on levels <= L -- the same prefix
 *     discipline as the pushed-definition context, and for the same
 *     reason: it keeps a conjunct's rewritten form stable as the stack
 *     grows underneath it, and a fact can never outlive the shallowest
 *     level it was drawn from (it is attached at the level whose feed
 *     discovered it, and stack discipline pops deeper levels first).
 *
 *   takeNewlyFixed()
 *     The nodes that became fully determined during the last feed --
 *     the per-level fact delta, without rescanning the whole map.
 *
 *   constantOf()
 *     The constant a fully-determined BV/Boolean node is fixed to.
 *
 * Kinds without a transfer function (arrays, floating point before
 * lowering) propagate nothing -- sound by imprecision -- and
 * constantOf refuses their types, so feeding raw word-level content
 * is safe.
 *
 * Each feed is a level transaction. rollbackTo() restores the exact fixed-bit,
 * multiplication-cache and dependency state at an earlier level boundary;
 * worklists are quiescent at successful boundaries, cleared immediately on
 * conflict, and defensively cleared again on rollback. This lets
 * IncrementalSolver preserve a common prefix instead of destroying the engine
 * and re-feeding it.
 */

#ifndef INCREMENTALCBP_H_
#define INCREMENTALCBP_H_

#include "stp/AST/AST.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/MultiplicationStats.h"
#include "stp/Simplifier/constantBitP/NodeToFixedBitsMap.h"

#include <cstddef>
#include <map>
#include <set>
#include <vector>

namespace stp
{
class STPMgr;

class IncrementalCBP
{
public:
  struct RollbackStats
  {
    size_t levels = 0;
    size_t fixedStates = 0;
    size_t createdFixedStates = 0;
    size_t dependencyNodes = 0;
    size_t multiplicationStates = 0;
  };

  IncrementalCBP(STPMgr* mgr, NodeFactory* nf);
  ~IncrementalCBP();

  IncrementalCBP(const IncrementalCBP&) = delete;
  IncrementalCBP& operator=(const IncrementalCBP&) = delete;

  /// Extend the DAG with one level's conjunction, assume it true, and
  /// propagate to a fixpoint. Returns false on conflict -- the live
  /// stack up to this level is unsatisfiable.
  bool feedLevel(const ASTNode& conjunction);

  /// Restore the state after exactly `levels` successful or conflicting
  /// feedLevel transactions. Structural and value state introduced by later
  /// levels is removed. Returns deterministic work counts for profiling.
  RollbackStats rollbackTo(size_t levels);

  size_t levelCount() const { return checkpoints.size(); }

  /// How many DISTINCT nodes `root` would ADD to the dependency graph this
  /// engine already holds. Levels share subgraphs by identity, so the sum of
  /// the live levels' DAG sizes is NOT the size of what is retained: one cone
  /// under twenty levels is charged twenty times by that measure and once by
  /// this one. The walk mirrors extendParentMap -- it stops at constants and
  /// at nodes already visited, because nothing beneath those is new either --
  /// so it costs the delta, not the level. It saturates just past `budget`
  /// rather than finishing a walk whose answer cannot change the decision.
  size_t freshNodeCount(const ASTNode& root, size_t budget) const;

  /// Nodes retained for the live stack. Rolled back with the levels, so this
  /// is the union over levels currently fed, never a session total.
  size_t retainedNodes() const { return depsVisited.size(); }

  /// Nodes that became fully determined during the last feedLevel call
  /// (cleared by the call itself). Constants excluded.
  const std::vector<ASTNode>& takeNewlyFixed() const { return newlyFixed; }

  /// The constant a fully-determined node is fixed to, or the null node.
  ASTNode constantOf(const ASTNode& n) const;

  /// Was a conflict detected?
  bool inConflict() const { return conflict; }

private:
  struct FixedUndo
  {
    ASTNode node;
    simplifier::constantBitP::FixedBits oldBits;

    FixedUndo(const ASTNode& node_,
              const simplifier::constantBitP::FixedBits& oldBits_)
        : node(node_), oldBits(oldBits_)
    {
    }
  };

  struct MultiplicationUndo
  {
    ASTNode node;
    simplifier::constantBitP::MultiplicationStats oldStats;

    MultiplicationUndo(
        const ASTNode& node_,
        const simplifier::constantBitP::MultiplicationStats& oldStats_)
        : node(node_), oldStats(oldStats_)
    {
    }
  };

  struct Checkpoint
  {
    size_t fixedUndo;
    size_t fixedCreated;
    size_t dependenciesAdded;
    size_t multiplicationUndo;
    size_t multiplicationCreated;
    bool conflict;
  };

  void beginLevel();
  void finishLevel();
  void extendParentMap(const ASTNode& root);
  void seedWorklist(const ASTNode& n);
  void pushWork(const ASTNode& n);
  ASTNode popWork();
  bool workEmpty() const;
  simplifier::constantBitP::FixedBits* getOrCreate(const ASTNode& n);
  void recordBeforeMutation(const ASTNode& n,
                            simplifier::constantBitP::FixedBits* bits);
  void recordMultiplicationBeforeMutation(const ASTNode& n);
  void scheduleParents(const ASTNode& n, const ASTNode& except);
  void propagate();

  STPMgr* mgr;
  NodeFactory* nf;

  simplifier::constantBitP::NodeToFixedBitsMap* fixedMap;
  simplifier::constantBitP::MultiplicationStatsMap* msm;
  bool conflict;

  // Growable parent overlay: child -> parents, extended per feed.
  std::map<uint64_t, std::vector<ASTNode>> parentMap;
  ASTNodeSet depsVisited;

  // Per-level undo logs. A FixedBits object is copied at most once in one
  // feed, immediately before an opaque batch transfer function may mutate it;
  // objects first created in the feed need only be deleted on rollback.
  std::vector<Checkpoint> checkpoints;
  std::vector<FixedUndo> fixedUndo;
  std::vector<ASTNode> fixedCreated;
  std::vector<ASTNode> dependenciesAdded;
  std::vector<MultiplicationUndo> multiplicationUndo;
  std::vector<ASTNode> multiplicationCreated;
  ASTNodeSet currentFixedTrailed;
  ASTNodeSet currentFixedCreated;
  ASTNodeSet currentMultiplicationTrailed;

  // Two-tier worklist: cheap transfer functions drain before the
  // expensive arithmetic ones run (the batch WorkList's discipline).
  std::set<ASTNode> cheapWork;
  std::set<ASTNode> expensiveWork;

  // Fully-determined transitions of the current feed.
  std::vector<ASTNode> newlyFixed;

  // Reused per propagate step.
  std::vector<simplifier::constantBitP::FixedBits*> childBits;
  std::vector<unsigned> prevChildCounts;
};

} // namespace stp

#endif

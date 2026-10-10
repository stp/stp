/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: October, 2026
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

/*
 * An editable view of a formula for the size-reducing passes.
 *
 * The formula stays an ordinary hash-consed DAG. A node becomes editable
 * only when a pass writes to it: materialise() copies that one interior
 * node into a MutableInterior, which stands for the original from then on.
 * The copy's children may be edited in place; its parents are known; its
 * structure is kept hash-consed in a table of the graph's own, so a copy
 * that comes to equal another node merges into it. Nothing shared is ever
 * written. The immutable nodes above a copy still point at the original,
 * and exportRoot() follows the forwards and rebuilds just those ancestors.
 *
 * Parent counts are exact for every node in the current formula, mutable
 * or not. The immutable side is indexed once at import (a CSR of parent
 * edges); edits adjust live counts incrementally, and a subtree that falls
 * out of the formula has its counts withdrawn, so a symbol's count is the
 * number of places that read it now.
 *
 * The simplifying rules run on the graph unchanged: factory() is a
 * SimplifyingNodeFactory whose raw delegate hash-conses into this graph
 * when any child is mutable and into the manager otherwise.
 */

#ifndef MUTABLEGRAPH_H_
#define MUTABLEGRAPH_H_

#include "stp/AST/AST.h"
#include "stp/AST/MutableInterior.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include <set>
#include <vector>

namespace stp
{
class MutableGraph;

// The raw factory over a graph. Sorting and NOT handling mirror
// HashingNodeFactory, so a node built here has the same child order as its
// hash-consed counterpart would.
class MutableNodeFactory : public NodeFactory
{
  MutableGraph& graph;

public:
  MutableNodeFactory(STPMgr& bm_, MutableGraph& g) : NodeFactory(bm_), graph(g)
  {
  }
  using NodeFactory::CreateArrayTerm;
  using NodeFactory::CreateNode;
  using NodeFactory::CreateTerm;
  virtual ASTNode CreateNode(Kind kind, ASTChildren children) override;
  virtual ASTNode CreateTerm(Kind kind, unsigned int width,
                             ASTChildren children) override;
  virtual ASTNode CreateArrayTerm(Kind kind, unsigned int index,
                                  unsigned int width,
                                  ASTChildren children) override;
  virtual std::string getName() override { return "mutable"; }
};

// What callers build through: every operand is brought to the graph's
// current view before the simplifying rules see it. The rules read a
// node's children and grandchildren directly, so a stale immutable
// operand would let them rebuild structure the formula no longer has.
class NormalisingNodeFactory : public NodeFactory
{
  MutableGraph& graph;
  NodeFactory& inner;

public:
  NormalisingNodeFactory(STPMgr& bm_, MutableGraph& g, NodeFactory& in)
      : NodeFactory(bm_), graph(g), inner(in)
  {
  }
  using NodeFactory::CreateArrayTerm;
  using NodeFactory::CreateNode;
  using NodeFactory::CreateTerm;
  virtual ASTNode CreateNode(Kind kind, ASTChildren children) override;
  virtual ASTNode CreateTerm(Kind kind, unsigned int width,
                             ASTChildren children) override;
  virtual ASTNode CreateArrayTerm(Kind kind, unsigned int index,
                                  unsigned int width,
                                  ASTChildren children) override;
  virtual std::string getName() override { return "normalising"; }
};

class MutableGraph
{
public:
  explicit MutableGraph(STPMgr& bm);
  ~MutableGraph();
  MutableGraph(const MutableGraph&) = delete;
  MutableGraph& operator=(const MutableGraph&) = delete;

  // Index the formula. Nothing is copied.
  void import(const ASTNode& root);
  const ASTNode& root() const { return root_; }

  // The formula as hash-consed nodes: unchanged subtrees come back as they
  // are, edited regions are rebuilt through the manager's hashing factory.
  ASTNode exportRoot();
  // The same for any node of the current formula.
  ASTNode exportNode(const ASTNode& n) { return rebuild(current(n)); }

  // The simplifying rules over this graph's nodes, every operand brought
  // to the current view first.
  NodeFactory& factory() { return normalising_; }
  NodeFactory& rawFactory() { return raw_; }

  static MutableInterior* asMutable(const ASTNode& n);

  // What stands for n in the current formula: n itself unless it has been
  // replaced.
  ASTNode current(const ASTNode& n) const;

  // An editable copy of the immutable interior node n, standing for it from
  // now on. Returns the existing copy when n already has one, and the
  // existing mutable node when one with n's structure already exists. NULL
  // when n has collapsed to a leaf (a NOT whose child became a NOT).
  MutableInterior* materialise(const ASTNode& n);

  // Point one child slot of an editable node elsewhere. Re-keys the node;
  // a node that comes to equal another merges into it.
  void replaceChild(MutableInterior* parent, size_t slot, const ASTNode& child);
  // `structural` false when the slot merely moves to a copy of the same
  // structure: re-keyed, but the rules do not run.
  void replaceChild(MutableInterior* parent, size_t slot, const ASTNode& child,
                    bool structural);

  // Every holder of `old` now holds `by`; `old` dies. `structural` false
  // when `by` is the same structure under another handle.
  void replaceNode(MutableInterior* old, const ASTNode& by,
                   bool structural = true);

  // The same for any interior node of the formula, mutable or not: an
  // immutable one is forwarded to `by` without being copied first.
  void replace(const ASTNode& node, const ASTNode& by);

  // An immutable node of the formula with a replaced node somewhere below
  // it: it still points at the old structure, and export rebuilds it.
  bool isStale(const ASTNode& n) const;

  // Places that read n in the current formula.
  size_t parentCount(const ASTNode& n) const;
  void parents(const ASTNode& n, std::vector<ASTNode>& out) const;

  // What the edits did, for a pass's worklist. Cleared by the consumer.
  struct Change
  {
    enum What
    {
      Patched,      // a mutable node's child slot changed
      Attached,     // a node entered the formula
      Detached,     // a node left the formula
      CountChanged  // a node's parent count changed
    };
    What what;
    ASTNode node;
  };
  const std::vector<Change>& changes() const { return changes_; }
  void clearChanges() { changes_.clear(); }

  // Recounts every parent from scratch over the current formula and
  // compares with the incremental counts; checks the table and the parent
  // back-pointers. O(formula). For tests and assertion builds.
  bool checkInvariant(std::string* why = NULL) const;

  // The handle the graph works with: what stands for n now, and a copy
  // where n stands above a replacement. Every entry point applies it.
  ASTNode normalise(const ASTNode& n);
  void normalise(ASTChildren children, ASTVec& out);

  // For MutableNodeFactory and MutableInterior only.
  ASTNode lookupOrCreate(Kind kind, unsigned index, unsigned width,
                         ASTChildren children);
  void released(MutableInterior* n);

private:
  STPMgr& bm;
  const bool trace_; // MUTABLEGRAPH_TRACE in the environment
  MutableNodeFactory raw_;
  SimplifyingNodeFactory simplifying_;
  NormalisingNodeFactory normalising_;
  ASTNode root_;
  bool tearingDown_ = false;

  // The immutable side. Dense indices: the imported DAG first, then any
  // immutable node that entered the formula later.
  std::vector<ASTNode> nodes_;
  ankerl::unordered_dense::map<uint64_t, uint32_t> index_;
  uint32_t imported_ = 0;          // nodes_[0, imported_) have CSR entries
  std::vector<uint32_t> offsets_;  // size imported_+1
  std::vector<uint32_t> csrParents_;
  // Parent edges from immutable nodes that entered after import, by child.
  ankerl::unordered_dense::map<uint64_t, std::vector<uint32_t>> extraParents_;
  // Live immutable parents per dense index: CSR and extra edges whose parent
  // is still in the formula and not forwarded. The root carries one more.
  std::vector<uint32_t> liveImm_;
  // Mutable parents of an immutable node, one entry per child slot.
  ankerl::unordered_dense::map<uint64_t, std::vector<MutableInterior*>>
      mutParents_;
  // An immutable node that has been replaced, and what stands for it.
  ankerl::unordered_dense::map<uint64_t, ASTNode> forward_;
  // The forwards made by an edit, as opposed to by a copy: the rules run
  // on a node only where the structure below it changed, so materialising
  // (a copy) leaves the formula's meaning and its export as they were.
  ankerl::unordered_dense::set<uint64_t> editedForward_;
  unsigned distanceVia(const ASTNode& rawChild, Kind parentKind) const;
  // The same for a mutable node that has been replaced: nothing holds it
  // any more, but a handle a pass kept, or a table hit mid-merge, resolves
  // to its successor.
  // By identity: a detached copy and the node that replaces its
  // structure can share a number until the copy is refreshed.
  ankerl::unordered_dense::map<const MutableInterior*, ASTNode> mutForward_;
  // Immutable nodes with a replaced node somewhere below them, by dense
  // index. Transient: the operation that forwards a node converts every
  // node above it before it returns (settle), so that after any public
  // operation the formula holds no stale node, every live interior node
  // above an edit is mutable and keyed in the table, and a parent count
  // is exact with respect to structure rather than to handles.
  std::vector<bool> stale_;
  // Above this many children a node is not keyed, sorted or merged: see
  // MutableInterior::wide_.
  static const size_t WIDE = 64;
  void markStaleAbove(uint32_t idx);
  // Stale nodes held by a mutable parent, converted when the operation that
  // made them stale has finished: a mutable node holds current children.
  std::vector<uint32_t> pendingStale_; // a heap, lowest number on top
  struct StaleAfter
  {
    const MutableGraph* g;
    bool operator()(uint32_t a, uint32_t b) const
    {
      return g->nodes_[a].GetNodeNum() > g->nodes_[b].GetNodeNum();
    }
  } staleAfter_{this};

  // Mutable nodes whose structure changed, for the rules: drained by
  // settle, children before parents, each over a copy of its children.
  // The rules never run inside a patch, so nothing re-enters the node
  // being patched.
  // Ordered by number, which is above the children's: a child's rules run
  // before its parent's, as a bottom-up rebuild would.
  std::set<std::pair<uint64_t, MutableInterior*>> dirty_;
  // `distance` from the structural change that queued it: 0 for the
  // changed node itself.
  void markDirty(MutableInterior* m, unsigned distance = 0);
  // How far up a change can alter what a rule returns: child and
  // grandchild inspection, plus the three-deep idioms. Measured in the
  // design note's "rule horizon" section.
  static const unsigned HORIZON = 3;
  // Kinds whose rules walk a chain below them without bound (reads over
  // write chains, extracts through pass-through operators): the climb
  // continues through them at the same distance.
  static bool looksThrough(Kind k);
  void drainDirty();
  int depth_ = 0;
  void settle();
  friend struct MutableGraphNest;
  // Origins of an immutable node that stands for replaced ones (a leaf or
  // an existing node a mutable node merged into). Mutable nodes carry
  // their own.
  ankerl::unordered_dense::map<uint64_t, std::vector<uint64_t>> immOrigins_;

  // The mutable side.
  struct Probe
  {
    Kind kind;
    ASTChildren children;
  };
  // Keyed by the children's identity, not their numbers: a detached node
  // stays keyed while a node below it is renumbered.
  static uintptr_t identity(const ASTNode& n)
  {
    return reinterpret_cast<uintptr_t>(n._int_node_ptr);
  }
  struct Hasher
  {
    using is_transparent = void;
    size_t operator()(const MutableInterior* n) const;
    size_t operator()(const Probe& p) const;
  };
  struct Equal
  {
    using is_transparent = void;
    bool operator()(const MutableInterior* a, const MutableInterior* b) const;
    bool operator()(const Probe& p, const MutableInterior* n) const;
    bool operator()(const MutableInterior* n, const Probe& p) const
    {
      return operator()(p, n);
    }
  };
  ankerl::unordered_dense::set<MutableInterior*, Hasher, Equal> table_;
  std::vector<ASTNode> owned_; // one handle per mutable node ever made
  // For a wide node: which slots hold each child, by identity. A wide
  // node never re-sorts, so slots are stable; built on the first repoint
  // and kept by replaceChild, so repointing a 100,000-way conjunction
  // once per eliminated conjunct does not scan it each time.
  typedef ankerl::unordered_dense::map<uintptr_t, std::vector<uint32_t>> SlotIndex;
  ankerl::unordered_dense::map<const MutableInterior*, SlotIndex> wideSlots_;
  SlotIndex& slotIndex(MutableInterior* wide);
  std::vector<Change> changes_;

  uint32_t indexOf(const ASTNode& n); // adds n when unknown
  bool indexed(const ASTNode& n, uint32_t& idx) const;
  // Immutable nodes only: a mutable copy carries its original's number.
  bool isForwarded(const ASTNode& n) const
  {
    return !n.isMutableInterior() &&
           forward_.find(n.GetNodeNum()) != forward_.end();
  }
  bool isRoot(const ASTNode& n) const { return n == root_; }
  size_t immutableParentCount(const ASTNode& n) const;
  size_t originParentCount(const std::vector<uint64_t>& origins) const;
  bool liveImmutable(uint32_t idx) const;

  // `number` is the number of the immutable node this copies, or 0 for a
  // fresh one. A NOT is numbered from its child either way.
  MutableInterior* create(Kind kind, unsigned index, unsigned width,
                          ASTChildren children, uint64_t number = 0);
  // A fresh number for a node whose structure changed, above its children;
  // its parents are re-keyed and re-sorted, since their order is by number.
  void renumber(MutableInterior* m);
  static bool numberedAbove(const MutableInterior* m);
  // The number m should carry: a NOT's child plus one; the number of a
  // forwarded immutable node of the same structure when nothing live has
  // it (the export hands that node back, so the order the rules see is
  // the export's); else a fresh one.
  uint64_t numberFor(const MutableInterior* m) const;
  bool numberFree(const ASTNode& forwarded) const;
  void rekey(MutableInterior* n, bool structural = true);

  // Edge bookkeeping. A node's own child edges count exactly while the node
  // is in the formula, so the first parent a node gains walks down
  // registering its edges, and the last parent it loses walks down
  // withdrawing them.
  void registerParentEdge(MutableInterior* parent, const ASTNode& child);
  void unregisterParentEdge(MutableInterior* parent, const ASTNode& child);
  void attach(const ASTNode& n);
  void detach(const ASTNode& n);
  void moveStanding(const std::vector<uint64_t>& origins, const ASTNode& to,
                    bool edited);
  // `target` takes over for the immutable node n: n's parents, standing and
  // place in the formula. n's own child edges are withdrawn. `edited` says
  // whether target differs from n in structure (an edit) or is a copy.
  void standFor(const ASTNode& n, const ASTNode& target, bool edited);
  void repointAll(MutableInterior* p, const ASTNode& from, const ASTNode& to,
                  bool structural = true);
  bool eraseFromTable(MutableInterior* m);
  ASTNode refresh(MutableInterior* m);
  // The simplifying rules over m's kind and current children: m itself
  // when nothing fires (m is in the table, so the factory finds it), or
  // the node m should become.
  ASTNode runRules(MutableInterior* m);
  ASTNode runRules(Kind kind, unsigned index, unsigned width, ASTChildren kids);
  // A stale immutable node that is out of the formula: what it would be
  // now, built through the graph's factory and standing for it from here
  // on. No edges to retire, since none of its own were counted.
  ASTNode rebuildDetached(const ASTNode& n);
  void kill(MutableInterior* n);
  void note(Change::What what, const ASTNode& n)
  {
    changes_.push_back(Change{what, n});
  }

  ASTNode rebuild(const ASTNode& n);
};
}

#endif

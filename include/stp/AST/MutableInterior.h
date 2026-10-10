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

#ifndef MUTABLEINTERIOR_H_
#define MUTABLEINTERIOR_H_

#include "stp/AST/ASTInternal.h"
#include "stp/AST/ASTNode.h"
#include <vector>

namespace stp
{
class MutableGraph;

// An interior node that a MutableGraph may edit in place.
//
// It is an ASTInternal, so an ASTNode handle to it works wherever a handle
// works: the node factories, the simplifying rules and the per-node passes
// read it through the same virtuals as ASTInterior. It differs in three
// ways. Its children are a vector, so a slot can be patched. It is never in
// the manager's unique table; the graph keys it in a table of its own. And
// it knows its parents inside the graph.
//
// Only the graph constructs or edits one. Everything else holds handles.
class MutableInterior : public ASTInternal
{
  friend class MutableGraph;

  std::vector<ASTNode> children_;
  uint32_t value_width_ = 0;
  uint32_t index_width_ = 0;
  uint32_t sig_width_ = 0;
  uint32_t exp_width_ = 0;
  mutable const SourceSort* source_sort_cache_ = NULL;

  // NULL once the graph is gone; CleanUp then only frees the node.
  MutableGraph* graph_;

  // One entry per child slot of a mutable parent holding this node: a
  // multiset, so bvmul(t, t) counts t twice. Parents that are immutable
  // are counted by the graph against this node's origins.
  std::vector<MutableInterior*> parents_;

  // The immutable nodes this one stands for. Their live immutable parents
  // are this node's parents too, and export follows them here.
  std::vector<uint64_t> origins_;

  // Replaced by another node; every holder has been repointed. Kept alive
  // by the graph until it is torn down, so a stale pointer in a pass is a
  // visible dead node rather than freed memory. A node that merely left the
  // formula is not dead: it stays in the table with no parents, as an
  // unreachable hash-consed node does, and can be attached again.
  bool dead_ = false;
  // Whether this node's own child edges are registered: true exactly while
  // it is in the formula.
  bool attached_ = false;
  // Too many children to re-sort and re-hash on every patch: kept out of
  // the graph's table and never merged. Two such nodes with the same
  // children would be merged only at export.
  bool wide_ = false;
  // Queued for the rules: its children changed in structure since the
  // rules last saw it.
  bool dirty_ = false;
  // While queued: how many nodes up from the nearest structural change
  // this one is. The rules look a bounded distance down (the horizon),
  // so the queue stops climbing past it except along kinds whose rules
  // look through chains.
  uint8_t dirtyDistance_ = 0;
  // For a dead node: whether what replaced it differs in structure (an
  // edit or a merge) or is the same structure under another handle (the
  // factory's NOT of a copied child, say).
  bool diedByEdit_ = true;

  // Numbering, as the manager's: a NOT is its child's number plus one,
  // any other node outnumbers its children. A copy of an immutable node
  // keeps that node's number (the original forwards to it and is dead),
  // so the order of commutative children, which the rules read, is the
  // order the export will have. A node whose structure changes takes a
  // fresh number, as the export gives it a fresh node.
  static uint64_t freshNumber()
  {
    return node_uid_cntr.fetch_add(2, std::memory_order_relaxed) + 2;
  }

  MutableInterior(STPMgr* mgr, MutableGraph* graph, Kind kind,
                  ASTChildren children);

public:
  virtual ~MutableInterior();
  MutableInterior(const MutableInterior&) = delete;
  MutableInterior& operator=(const MutableInterior&) = delete;

  virtual ASTChildren GetChildren() const override
  {
    return ASTChildren(children_.data(), children_.size());
  }

  // A handle to this node, as any other holder has it.
  ASTNode handle() { return ASTNode(this); }

  bool isDead() const { return dead_; }
  MutableGraph* graph() const { return graph_; }
  const std::vector<MutableInterior*>& mutableParents() const
  {
    return parents_;
  }
  const std::vector<uint64_t>& origins() const { return origins_; }

protected:
  virtual void setIndexWidth(uint32_t i) override
  {
    if (index_width_ == i)
      return;
    index_width_ = i;
    source_sort_cache_ = NULL;
  }
  virtual uint32_t getIndexWidth() const override { return index_width_; }
  virtual void setValueWidth(uint32_t v) override
  {
    if (value_width_ == v)
      return;
    value_width_ = v;
    source_sort_cache_ = NULL;
  }
  virtual uint32_t getValueWidth() const override { return value_width_; }
  virtual void setSigWidth(uint32_t s) override
  {
    if (sig_width_ == s)
      return;
    sig_width_ = s;
    source_sort_cache_ = NULL;
  }
  virtual uint32_t getSigWidth() const override { return sig_width_; }
  virtual void setExpWidth(uint32_t e) override
  {
    if (exp_width_ == e)
      return;
    exp_width_ = e;
    source_sort_cache_ = NULL;
  }
  virtual uint32_t getExpWidth() const override { return exp_width_; }
  virtual const SourceSort* cachedSourceSort() const override
  {
    return source_sort_cache_;
  }
  virtual void setCachedSourceSort(const SourceSort* s) const override
  {
    source_sort_cache_ = s;
  }

  virtual void CleanUp() override;
  virtual void nodeprint(ostream& os) override;
};
}

#endif

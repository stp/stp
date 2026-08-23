/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2010
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

#ifndef DEPENDENCIES_H_
#define DEPENDENCIES_H_

#include "stp/AST/AST.h"
#include <ankerl/unordered_dense.h>
#include <cstdint>
#include <utility>
#include <vector>

namespace simplifier
{
namespace constantBitP
{

using std::cout;
using std::endl;
using stp::ASTNode;

// From a child, get the parents of that node.
//
// Stored as one flat CSR-style adjacency: every node in the DAG gets a dense
// index, all parent lists live back-to-back in a single array, and an
// offsets array delimits each node's slice. Building is one DFS that emits
// (child, parent) pairs plus a stable counting sort, so there are no
// per-node containers to allocate, and iterating a node's parents walks
// contiguous memory. Parents appear in each slice in the order the DFS
// first saw the edge, which is the same order the previous per-node
// insertion-ordered sets iterated in.
//
// The DFS keeps its frames on the heap. Nesting depth is whatever the input
// formula nests to, and deep inputs exist -- CPAchecker k-induction traces
// nest ~9,300 deep -- so one call frame per level exhausts the stack and
// kills the process. See DeepDag_Test.cpp.
class Dependencies
{
private:
  typedef ankerl::unordered_dense::map<uint64_t, uint32_t> IndexMap;

  IndexMap index;               // node id -> dense index; doubles as "visited"
  std::vector<ASTNode> nodes;   // dense index -> node
  std::vector<uint32_t> offsets; // size N+1; parents of i at [offsets[i], offsets[i+1])
  std::vector<ASTNode> parents;  // parent nodes themselves: iteration stays
                                 // one contiguous walk, no indirection

  // (childIdx, parentIdx) in DFS discovery order; cleared after compaction.
  typedef std::vector<std::pair<uint32_t, uint32_t>> EdgeList;

  typedef ankerl::unordered_dense::set<uint64_t> WideSeen;

  // Where the walk of one node has got to. `wide` is that node's slot in
  // the duplicate-child sets, or NO_WIDE for the usual narrow node, which
  // dedups by scanning instead and so needs no set at all.
  struct Frame
  {
    uint32_t idx;
    uint32_t degree;
    uint32_t next;
    uint32_t wide;
  };

  static constexpr uint32_t NO_WIDE = UINT32_MAX;

  uint32_t discover(const ASTNode& n)
  {
    const auto it = index.try_emplace(n.GetNodeNum(), (uint32_t)nodes.size());
    if (it.second)
      nodes.push_back(n);
    return it.first->second;
  }

  // Wide nodes are rare, so their sets are handed out from a pool that only
  // ever grows to the deepest nesting of wide nodes, rather than sitting in
  // every frame.
  Frame enter(const uint32_t idx, std::vector<WideSeen>& wideSeen,
              uint32_t& wideInUse) const
  {
    Frame f;
    f.idx = idx;
    f.degree = (uint32_t)nodes[idx].Degree();
    f.next = 0;
    f.wide = NO_WIDE;

    if (f.degree > 32) // where the quadratic scan starts to bite.
    {
      if (wideInUse == wideSeen.size())
        wideSeen.emplace_back();
      else
        wideSeen[wideInUse].clear(); // keeps the buckets it already has.
      f.wide = wideInUse++;
    }
    return f;
  }

  // A (parent -> child) edge repeats only when a node lists the same child
  // more than once (e.g. BVPLUS(x,x)); dedup by scanning the earlier
  // children, or through a set once the quadratic scan would bite.
  void build(const uint32_t topIdx, EdgeList& edges)
  {
    std::vector<Frame> stack;
    std::vector<WideSeen> wideSeen;
    uint32_t wideInUse = 0;

    stack.push_back(enter(topIdx, wideSeen, wideInUse));

    while (!stack.empty())
    {
      Frame& f = stack.back();

      if (f.next == f.degree)
      {
        if (f.wide != NO_WIDE)
          wideInUse--;
        stack.pop_back();
        continue;
      }

      const uint32_t currentIdx = f.idx;
      const unsigned i = f.next++;

      // Discovering a child can move `nodes`, so neither of these may be
      // read across one. The child itself is stored in the node that lists
      // it rather than in `nodes`, so that reference does survive.
      const ASTNode& current = nodes[currentIdx];
      const ASTNode& child = current[i];

      if (child.isConstant()) // don't care about what depends on constants.
        continue;

      const uint64_t childId = child.GetNodeNum();

      if (f.wide != NO_WIDE)
      {
        if (!wideSeen[f.wide].insert(childId).second)
          continue;
      }
      else
      {
        bool repeated = false;
        for (unsigned j = 0; j < i; j++)
          if (current[j].GetNodeNum() == childId)
          {
            repeated = true;
            break;
          }
        if (repeated)
          continue;
      }

      // By value: this inserts into `index`, which can move the entry the
      // iterator points at.
      const auto r = index.try_emplace(childId, (uint32_t)nodes.size());
      const uint32_t childIdx = r.first->second;
      const bool firstVisit = r.second;
      if (firstVisit)
        nodes.push_back(child);
      edges.emplace_back(childIdx, currentIdx);

      // On a repeat visit through a new parent, the edges to the children
      // are already recorded. Descending invalidates `f`, so nothing above
      // may be read after this point.
      if (firstVisit)
        stack.push_back(enter(childIdx, wideSeen, wideInUse));
    }
  }

  void compact(const EdgeList& edges)
  {
    offsets.assign(nodes.size() + 1, 0);
    for (const auto& e : edges)
      offsets[e.first + 1]++;
    for (size_t i = 1; i < offsets.size(); i++)
      offsets[i] += offsets[i - 1];

    parents.resize(edges.size()); // null ASTNodes, then counting-sorted in
    std::vector<uint32_t> cursor(offsets.begin(), offsets.end() - 1);
    for (const auto& e : edges) // stable: keeps per-child discovery order
      parents[cursor[e.first]++] = nodes[e.second];
  }

public:
  Dependencies(const Dependencies&) = delete;
  Dependencies& operator=(const Dependencies&) = delete;

  Dependencies(const ASTNode& top)
  {
    if (top.isConstant())
      return;

    EdgeList edges;
    build(discover(top), edges);
    compact(edges);
  }

  // A node's slice of the flat parent array.
  class ParentRange
  {
    const ASTNode* from;
    const ASTNode* to;

  public:
    ParentRange(const ASTNode* from_, const ASTNode* to_)
        : from(from_), to(to_)
    {
    }

    const ASTNode* begin() const { return from; }
    const ASTNode* end() const { return to; }
    size_t size() const { return to - from; }
  };

  ParentRange getDependents(const ASTNode& n) const
  {
    if (!n.isConstant())
    {
      const auto it = index.find(n.GetNodeNum());
      if (it != index.end())
      {
        const uint32_t i = it->second;
        return ParentRange(parents.data() + offsets[i],
                           parents.data() + offsets[i + 1]);
      }
    }
    return ParentRange(nullptr, nullptr);
  }

  // The higher node depends on the lower node.
  // The value produces by the lower node is read by the higher node.
  bool nodeDependsOn(const ASTNode& higher, const ASTNode& lower) const
  {
    for (const ASTNode& p : getDependents(lower))
      if (p == higher)
        return true;
    return false;
  }
};
}
}

#endif /* DEPENDENCIES_H_ */

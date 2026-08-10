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
#include "extlib-unordered-dense/ankerl/unordered_dense.h"
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

  uint32_t discover(const ASTNode& n)
  {
    const auto it = index.try_emplace(n.GetNodeNum(), (uint32_t)nodes.size());
    if (it.second)
      nodes.push_back(n);
    return it.first->second;
  }

  // A (parent -> child) edge repeats only when a node lists the same child
  // more than once (e.g. BVPLUS(x,x)); dedup by scanning the earlier
  // children, or through a set once the quadratic scan would bite.
  void build(const ASTNode& current, const uint32_t currentIdx,
             EdgeList& edges)
  {
    const unsigned degree = current.Degree();

    ankerl::unordered_dense::set<uint64_t> seenWide;
    const bool wide = degree > 32;

    for (unsigned i = 0; i < degree; i++)
    {
      const ASTNode& child = current[i];
      if (child.isConstant()) // don't care about what depends on constants.
        continue;

      const uint64_t childId = child.GetNodeNum();

      if (wide)
      {
        if (!seenWide.insert(childId).second)
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

      // By value: the recursive call inserts into `index`, which can move
      // the entry the iterator points at.
      const auto r = index.try_emplace(childId, (uint32_t)nodes.size());
      const uint32_t childIdx = r.first->second;
      const bool firstVisit = r.second;
      if (firstVisit)
        nodes.push_back(child);
      edges.emplace_back(childIdx, currentIdx);

      // On a repeat visit through a new parent, the edges to the children
      // are already recorded.
      if (firstVisit)
        build(child, childIdx, edges);
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
    build(top, discover(top), edges);
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

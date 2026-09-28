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

#ifndef WORKLIST_H_
#define WORKLIST_H_

#include "stp/AST/AST.h"
#include "stp/AST/ASTNode.h"
#include "stp/Util/BitOps.h"
#include <ankerl/unordered_dense.h>
#include <vector>

namespace simplifier
{
namespace constantBitP
{

// Nodes waiting to be propagated, taken cheapest-visit-first.
//
// Transfer functions differ in cost by orders of magnitude: a bitwise-and is
// linear in the bit-width, an n-ary addition costs the width times the number
// of addends, and the division family is one to three orders of magnitude
// above everything else. Visiting the costly ones last is what makes them pay
// off: by the time one is reached, its children have absorbed every change the
// cheaper nodes could derive, so a single visit does the work that would
// otherwise be split across many. Simplification can produce n-ary nodes with
// tens of thousands of children, where one visit walks every child and any one
// of them fixing a single bit reschedules the lot.
//
// The queue is buckets rather than a heap: the estimated cost of a visit is
// rounded down to a power of two and each bucket is a set, so push and pop
// stay constant-time and a node is still queued at most once. The estimate
// only has to order the kinds correctly, not size them.
class WorkList
{
private:
  typedef ankerl::unordered_dense::set<stp::ASTNode, ASTNode::ASTNodeHasher,
                                       ASTNode::ASTNodeEqual>
      WorkListSetType;

  // Estimated costs run from a single bit operation to (children x width) on
  // the widest n-ary nodes, so one bucket per power of two covers everything
  // a 64-bit count can hold.
  static const unsigned bucketCount = 64;

  WorkListSetType buckets[bucketCount];

  // No bucket below this one holds anything, so popping only rescans a
  // bucket once it has emptied.
  unsigned lowest;

  WorkList(const WorkList&); // Shouldn't needed to copy or assign.
  WorkList& operator=(const WorkList&);

  // Roughly the number of bit operations one visit costs. Only the relative
  // order matters, not the magnitude.
  static uint64_t visitCost(const stp::ASTNode& n)
  {
    const uint64_t width = n.GetValueWidth() > 0 ? n.GetValueWidth() : 1;
    const uint64_t degree = n.Degree() > 0 ? n.Degree() : 1;

    switch (n.GetKind())
    {
      // Shift-and-add over the partial products, run in both directions,
      // once per adjacent operand pair.
      case stp::BVMULT:
        return (degree - 1) * width * width;

      // Repeated multiplication, iterated to a fixed point.
      case stp::BVDIV:
      case stp::BVMOD:
      case stp::SBVDIV:
      case stp::SBVREM:
      case stp::SBVMOD:
        return width * width * width;

      default:
        break;
    }

    // A pass or two over the bits of each child. Addition needs no case of
    // its own: the column algorithm walks every addend once per column, which
    // is what this already charges, and two-operand addition is handled by a
    // carry chain as cheap as the bitwise transfer functions.
    return degree * width;
  }

  static unsigned bucketOf(const stp::ASTNode& n)
  {
    const uint64_t cost = visitCost(n);
    assert(cost > 0);
    return 63 - ::stp::countLeadingZeroes64(cost);
  }

  // Where the walk of one node has got to. `addedParent` is that node's
  // `alreadyAdded`: it is pushed once, at its first constant child.
  struct Frame
  {
    const stp::ASTNode* n;
    unsigned i = 0;
    bool addedParent = false;

    Frame(const stp::ASTNode& node) : n(&node) {}
  };

  // We add to the worklist any node that immediately depends on a constant.
  //
  // Iterative: this seeds constant-bit propagation by descending the whole
  // input DAG, and how deeply that nests is the input's choice. A call per
  // level exhausts the stack on the deeply nested formulas that exist -- a
  // chain under an if-then-else condition reached here once the passes ahead
  // of it stopped crashing. See DeepDag_Test.cpp.
  //
  // The order is the recursion's, which matters: `push` inserts into a set
  // whose iteration order is its insertion order, and `pop` takes the front,
  // so the order nodes are added is the order propagation visits them. A
  // node is therefore still pushed at its first constant child and before
  // the walk descends into that child. The stack holds pointers into each
  // node's own child storage, which the node above keeps alive for the whole
  // walk.
  void addToWorklist(const stp::ASTNode& top, stp::ASTNodeSet& visited)
  {
    std::vector<Frame> stack;

    // The head of the recursive version: what it answered without a call.
    auto enter = [&](const stp::ASTNode& n) {
      if (n.isConstant())
        return;
      if (!visited.insert(n).second)
        return;
      stack.push_back(Frame(n));
    };

    enter(top);

    while (!stack.empty())
    {
      Frame& f = stack.back();

      if (f.i == f.n->Degree())
      {
        stack.pop_back();
        continue;
      }

      // Held through the push below, which can move `f` but not these: the
      // child is stored in the node that lists it.
      const stp::ASTNode& parent = *f.n;
      const stp::ASTNode& child = parent[f.i++];

      if (!f.addedParent && child.isConstant())
      {
        f.addedParent = true;
        push(parent);
      }

      // Nothing above may be read after this.
      enter(child);
    }
  }

public:
  // Add to the worklist any node that immediately depends on a constant.

  WorkList(const ASTNode& top) : lowest(bucketCount) { initWorkList(top); }

  int size()
  {
    int result = 0;
    for (unsigned b = lowest; b < bucketCount; b++)
      result += buckets[b].size();
    return result;
  }

  void initWorkList(const ASTNode& n)
  {
    stp::ASTNodeSet visited;
    addToWorklist(n, visited);
  }

  void push(const stp::ASTNode& n)
  {
    if (n.isConstant()) // don't ever add constants to the worklist.
      return;

    const unsigned b = bucketOf(n);
    buckets[b].insert(n);
    if (b < lowest)
      lowest = b;
  }

  stp::ASTNode pop()
  {
    assert(!isEmpty());
    while (buckets[lowest].empty())
      lowest++;

    ASTNode ret = *buckets[lowest].begin();
    buckets[lowest].erase(buckets[lowest].begin());
    return ret;
  }

  bool isEmpty()
  {
    while (lowest < bucketCount && buckets[lowest].empty())
      lowest++;
    return lowest == bucketCount;
  }
};
}
}

#endif /* WORKLIST_H_ */

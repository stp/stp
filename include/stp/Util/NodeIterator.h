/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Jan, 2012
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

#ifndef NODEITERATOR_H_
#define NODEITERATOR_H_

#include "stp/AST/ASTNode.h"
#include "stp/STPManager/STPManager.h"
#include <vector>

namespace stp
{
// Returns each node once, then returns the sentinel.
// NB if the sentinel is contained in the node that's passed, then it'll be
// wrong.
class NodeIterator // not copyable
{
  // A contiguous LIFO frontier retains the historical traversal order while
  // avoiding std::stack's deque blocks. It stores one AST handle per pending
  // edge; the path-frame representation stored two words per active ancestor
  // and repeatedly re-entered ancestors to discover their next child.
  std::vector<ASTNode> toVisit;

  const ASTNode& sentinel;
  uint8_t iteration;

protected:
  // The generic iterator retains its historical virtual `ok` hook. Known
  // built-in filters call this templated core directly, letting their
  // predicate inline into the walk instead of paying an indirect call for
  // every node.
  template <typename Accept>
  ASTNode nextIf(Accept&& accept)
  {
    while (!toVisit.empty())
    {
      ASTNode result = toVisit.back();
      toVisit.pop_back();
      if (!accept(result) || result.getIteration() == iteration)
        continue;

      if (result == sentinel)
        return result;

      result.setIteration(iteration);
      for (const ASTNode& child : result.GetChildren())
      {
        if (child.getIteration() != iteration)
          toVisit.push_back(child);
      }
      return result;
    }

    return sentinel;
  }

public:
  NodeIterator(const ASTNode& n, const ASTNode& _sentinel, STPMgr& stpMgr)
      : sentinel(_sentinel), iteration(stpMgr.getNextIteration())
  {
    toVisit.push_back(n);
  }

  ASTNode next()
  {
    return nextIf([this](const ASTNode& n) { return ok(n); });
  }

  ASTNode end() { return sentinel; }

  virtual bool ok(const ASTNode& /*n*/) { return true; }
};

// Iterator that omits return atoms.
class NonAtomIterator final : public NodeIterator
{
  bool ok(const ASTNode& n) override { return !n.isAtom(); }

public:
  NonAtomIterator(const ASTNode& n, const ASTNode& uf, STPMgr& stpMgr)
      : NodeIterator(n, uf, stpMgr)
  {
  }

  ASTNode next()
  {
    return nextIf([](const ASTNode& n) { return !n.isAtom(); });
  }
};
}

#endif /* NODEITERATOR_H_ */

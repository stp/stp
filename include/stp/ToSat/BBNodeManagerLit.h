/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: August, 2026
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

#ifndef BBNODEMANAGERLIT_H
#define BBNODEMANAGERLIT_H

#include "stp/AIG/Manager.h"
#include "stp/AST/AST.h"
#include "stp/ToSat/AIGBudget.h"
#include "stp/ToSat/BBNodeLit.h"

#include <algorithm>
#include <iostream>
#include <deque>
#include <map>
#include <vector>

namespace stp
{

// The blaster's second backend: the same gate builders as BBNodeManagerAIG,
// over the in-house AIG instead of ABC's.
//
// Every method here answers a question BitBlaster asks. Where the two
// managers differ is not in the questions but in whether they can be answered
// without the manager: ABC's object carries its own kind and its own fanins,
// so isCI() and friends are static there. A node here is an index into an
// array, so they are ordinary members and the blaster asks through `nf`.
class BBNodeManagerLit
{
public:
  aig::Manager mgr;

  // Hard cap on AND gates; -1 (the default) is no limit, 0 permits none.
  int64_t nodeBudget = -1;

  // Map from symbols to their nodes. std::map rather than a hash map for the
  // same reason BBNodeManagerAIG uses one: fill_node_to_var walks it, and the
  // order it walks in reaches the emitted formula.
  typedef std::map<ASTNode, std::vector<BBNodeLit>> SymbolToBBNode;
  SymbolToBBNode symbolToBBNode;

  int totalNumberOfNodes() { return static_cast<int>(mgr.andCount()); }

  BBNodeManagerLit() = default;
  BBNodeManagerLit(const BBNodeManagerLit&) = delete;
  BBNodeManagerLit& operator=(const BBNodeManagerLit&) = delete;

  void stop()
  {
    mgr.reset();
    symbolToBBNode.clear();
  }

  BBNodeLit getTrue() { return BBNodeLit(aig::LIT_TRUE); }
  BBNodeLit getFalse() { return BBNodeLit(aig::LIT_FALSE); }

  // An input that stands for no symbol. The BV abstraction machinery mints
  // these for proxies and for abstracted results.
  BBNodeLit CreateFreshInput() { return BBNodeLit(mgr.createCi()); }

  // The same symbol always has to come back as the same node.
  BBNodeLit CreateSymbol(const ASTNode& n, unsigned i)
  {
    assert(n.GetKind() == SYMBOL);
    const unsigned width = std::max((unsigned)1, n.GetValueWidth());

    SymbolToBBNode::iterator it = symbolToBBNode.find(n);
    if (symbolToBBNode.end() == it)
    {
      symbolToBBNode[n] = std::vector<BBNodeLit>(width);
      it = symbolToBBNode.find(n);
    }
    assert(it->second.size() == width);
    assert(i < width);

    if (!it->second[i].IsNull())
      return it->second[i];

    it->second[i] = BBNodeLit(mgr.createCi());
    return it->second[i];
  }

  // --- the queries BitBlaster asks about a node ---------------------------

  bool isCI(const BBNodeLit& n) const { return mgr.isCi(aig::nodeOf(n.n)); }
  bool isConstant(const BBNodeLit& n) const { return aig::isConst(n.n); }
  bool isAnd(const BBNodeLit& n) const { return mgr.isAnd(aig::nodeOf(n.n)); }
  unsigned nodeId(const BBNodeLit& n) const { return aig::nodeOf(n.n); }

  // The fanins of an AND, with the sign stripped, as BBNodeManagerAIG does:
  // provenance and traversal are both sign-insensitive, and returning the
  // signed edge would key two memo entries per node.
  BBNodeLit fanin0(const BBNodeLit& n) const
  {
    return BBNodeLit(mgr.fanin0(aig::nodeOf(n.n)) & ~aig::Lit(1));
  }
  BBNodeLit fanin1(const BBNodeLit& n) const
  {
    return BBNodeLit(mgr.fanin1(aig::nodeOf(n.n)) & ~aig::Lit(1));
  }

  // An uncomplemented input this manager minted, and its ordinal.
  //
  // BBNodeAIG answers by carrying the ordinal in the handle. Nothing here
  // renumbers, so the ordinal can be recovered instead: inputs are appended
  // in creation order, so the manager's input list ascends by node id and a
  // binary search over it finds the position. Asked once per abstraction
  // record, never on a blasting path.
  bool isNamedCI(const BBNodeLit& n) const
  {
    return !n.IsNull() && !aig::isNeg(n.n) && isCI(n);
  }
  int ciOrdinal(const BBNodeLit& n) const
  {
    assert(isNamedCI(n));
    const aig::Node want = aig::nodeOf(n.n);
    uint32_t lo = 0, hi = mgr.ciCount();
    while (lo < hi)
    {
      const uint32_t mid = lo + (hi - lo) / 2;
      if (mgr.ciNode(mid) < want)
        lo = mid + 1;
      else
        hi = mid;
    }
    assert(lo < mgr.ciCount() && mgr.ciNode(lo) == want);
    return static_cast<int>(lo);
  }

  // --- the gate builders --------------------------------------------------

  BBNodeLit CreateNode(Kind kind, std::vector<BBNodeLit>& children)
  {
    assert(children.size() != 0);
    for (size_t i = 0, size = children.size(); i < size; ++i)
      assert(!children[i].IsNull());

    aig::Lit r;
    switch (kind)
    {
      case AND:
        r = tower(&aig::Manager::And, children);
        break;

      case NAND:
        r = aig::neg(tower(&aig::Manager::And, children));
        break;

      case OR:
        r = tower(&aig::Manager::Or, children);
        break;

      case NOR:
        r = aig::neg(tower(&aig::Manager::Or, children));
        break;

      case NOT:
        assert(children.size() == 1);
        r = aig::neg(children[0].n);
        break;

      case XOR:
        r = tower(&aig::Manager::Xor, children);
        break;

      case IFF:
        assert(children.size() == 2);
        r = mgr.Iff(children[0].n, children[1].n);
        break;

      case IMPLIES:
        assert(children.size() == 2);
        r = mgr.Or(aig::neg(children[0].n), children[1].n);
        break;

      case ITE:
        assert(children.size() == 3);
        r = mgr.Mux(children[0].n, children[1].n, children[2].n);
        break;

      default:
        std::cerr << "Not handled::!!" << _kind_names[kind];
        FatalError("Never here");
        exit(-1);
    }
    checkBudget();
    return BBNodeLit(r);
  }

  BBNodeLit CreateNode(Kind kind, const BBNodeLit& child0,
                       const std::vector<BBNodeLit>& back_children =
                           std::vector<BBNodeLit>())
  {
    std::vector<BBNodeLit> front;
    front.reserve(1 + back_children.size());
    front.push_back(child0);
    front.insert(front.end(), back_children.begin(), back_children.end());
    return CreateNode(kind, front);
  }

  BBNodeLit CreateNode(Kind kind, const BBNodeLit& child0,
                       const BBNodeLit& child1,
                       const std::vector<BBNodeLit>& back_children =
                           std::vector<BBNodeLit>())
  {
    std::vector<BBNodeLit> front;
    front.reserve(2 + back_children.size());
    front.push_back(child0);
    front.push_back(child1);
    front.insert(front.end(), back_children.begin(), back_children.end());
    return CreateNode(kind, front);
  }

  BBNodeLit CreateNode(Kind kind, const BBNodeLit& child0,
                       const BBNodeLit& child1, const BBNodeLit& child2,
                       const std::vector<BBNodeLit>& back_children =
                           std::vector<BBNodeLit>())
  {
    std::vector<BBNodeLit> front;
    front.reserve(3 + back_children.size());
    front.push_back(child0);
    front.push_back(child1);
    front.push_back(child2);
    front.insert(front.end(), back_children.begin(), back_children.end());
    return CreateNode(kind, front);
  }

  // Called after every CreateNode(). One node can add a whole fan-in tower
  // before this runs, so the count at the throw can overshoot the budget by
  // the width of one operator -- as with the AIG manager, the cap bounds the
  // order of magnitude rather than being an exact ceiling.
  void checkBudget() const
  {
    if (nodeBudget >= 0 && static_cast<int64_t>(mgr.andCount()) > nodeBudget)
      throw AIGBudgetExhausted(static_cast<int>(mgr.andCount()));
  }

private:
  // A two-input gate takes two operands, so a wide one becomes a log-height
  // tower. Same shape as BBNodeManagerAIG::makeTower -- front two off, result
  // to the back -- because the shape decides which operands share subterms
  // and so decides the gate count.
  aig::Lit tower(aig::Lit (aig::Manager::*op)(aig::Lit, aig::Lit),
                 const std::vector<BBNodeLit>& children)
  {
    if (children.size() == 1)
      return children[0].n;

    std::deque<aig::Lit> names;
    for (size_t i = 0, size = children.size(); i < size; ++i)
      names.push_back(children[i].n);

    while (names.size() > 2)
    {
      const aig::Lit a = names.front();
      names.pop_front();
      const aig::Lit b = names.front();
      names.pop_front();
      names.push_back((mgr.*op)(a, b));
    }

    const aig::Lit a = names.front();
    names.pop_front();
    const aig::Lit b = names.front();
    return (mgr.*op)(a, b);
  }
};

} // namespace stp

#endif

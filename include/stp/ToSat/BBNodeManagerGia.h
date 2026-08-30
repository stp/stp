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

#ifndef BBNODEMANAGERGIA_H
#define BBNODEMANAGERGIA_H

#include "stp/AST/AST.h"
#include "stp/ToSat/AIGBudget.h"
#include "stp/ToSat/BBNodeGia.h"

// From ABC
#include "aig/gia/gia.h"

#include <algorithm>
#include <cstdint>
#include <deque>
#include <iostream>
#include <map>
#include <vector>

namespace stp
{

// The blaster's third backend: the same gate builders again, over ABC's Gia
// instead of ABC's Aig or the in-house package.
//
// The reason this one exists is the CNF generator on the other side.
// Mf_ManGenerateCnf -- the LUT-cut generator behind --cnf-generation-effort
// low, high and very-high -- takes a Gia_Man_t, and ToCNFAIG reaches it by
// building an Aig and calling Gia_ManFromAig, so both graphs are live at the
// moment the mapper runs. Blasting into the Gia directly deletes the Aig from
// that path: 12 bytes an object against 48, and no conversion.
//
// Two things are *easier* here than on ABC's Aig, and both are worth knowing
// before anyone tries to keep the three managers in step:
//
//   * No ordered-gate wrappers. orderedAigExor and orderedAigMux exist
//     because Aig_Exor and Aig_Mux2 build two Aig_And nodes inside one
//     Aig_Or argument list, where the evaluation order is unspecified and
//     therefore compiler-dependent -- and the node ids it decides reach the
//     CNF. Gia_ManHashXor and Gia_ManHashMux assign their two intermediates
//     in separate statements, so the question does not arise.
//
//   * ciOrdinal is O(1). Gia_ManAppendCi stores the ordinal in the object
//     (Gia_ObjCioId reads it back), so unlike BBNodeAIG this handle carries
//     no symbol_index, and unlike BBNodeManagerLit there is no binary search
//     over the input list.
//
// One thing is harder, and it is a correctness matter rather than a
// convenience: the CIs of this manager are *not* objects 1..nCi. See
// ToCNFGia for what depends on that and what is done about it.
class BBNodeManagerGia
{
public:
  Gia_Man_t* giaMgr;

  // Hard cap on AND gates; -1 (the default) is no limit, 0 permits none.
  int64_t nodeBudget = -1;

  // Map from symbols to their nodes. std::map rather than a hash map for the
  // same reason the other two managers use one: the lowering walks it, and
  // the order it walks in reaches the emitted formula.
  typedef std::map<ASTNode, std::vector<BBNodeGia>> SymbolToBBNode;
  SymbolToBBNode symbolToBBNode;

  int totalNumberOfNodes() { return Gia_ManAndNum(giaMgr); }

  BBNodeManagerGia() : giaMgr(NULL)
  {
    // The initial object array, which Gia_ManAppendObj doubles as it fills.
    // Gia_ManStart also sizes the CI and CO vectors at a twentieth of this
    // and the hash table at the whole of it, so a large opening bid is not
    // free -- 64k objects is under a megabyte all told and covers a small
    // query without a single resize.
    giaMgr = Gia_ManStart(1 << 16);
    Gia_ManHashAlloc(giaMgr);

    // The two-level rewriting that BBNodeManagerAIG asks Aig_And for.
    giaMgr->fAddStrash = 1;
  }

  BBNodeManagerGia(const BBNodeManagerGia&) = delete;
  BBNodeManagerGia& operator=(const BBNodeManagerGia&) = delete;

  void stop()
  {
    if (giaMgr != NULL)
      Gia_ManStop(giaMgr);
    giaMgr = NULL;
    symbolToBBNode.clear();
  }

  ~BBNodeManagerGia() { stop(); }

  // Gia literal 0 is constant false and 1 is constant true, both being node 0
  // with and without the complement bit.
  BBNodeGia getTrue() { return BBNodeGia(1); }
  BBNodeGia getFalse() { return BBNodeGia(0); }

  // An input that stands for no symbol. The BV abstraction machinery mints
  // these for proxies and for abstracted results, which is why it does not go
  // through CreateSymbol.
  BBNodeGia CreateFreshInput() { return BBNodeGia(Gia_ManAppendCi(giaMgr)); }

  // The same symbol always has to come back as the same node.
  BBNodeGia CreateSymbol(const ASTNode& n, unsigned i)
  {
    assert(n.GetKind() == SYMBOL);

    // booleans have width 0.
    const unsigned width = std::max((unsigned)1, n.GetValueWidth());

    SymbolToBBNode::iterator it = symbolToBBNode.find(n);
    if (symbolToBBNode.end() == it)
    {
      symbolToBBNode[n] = std::vector<BBNodeGia>(width);
      it = symbolToBBNode.find(n);
    }
    assert(it->second.size() == width);
    assert(i < width);

    if (!it->second[i].IsNull())
      return it->second[i];

    it->second[i] = BBNodeGia(Gia_ManAppendCi(giaMgr));
    return it->second[i];
  }

  // --- the queries BitBlaster asks about a node ---------------------------
  //
  // Members rather than statics, as on BBNodeManagerLit: a Gia handle is an
  // index, so answering any of these needs the array it indexes into.

  bool isCI(const BBNodeGia& n) const { return Gia_ObjIsCi(obj(n)); }
  bool isConstant(const BBNodeGia& n) const { return Abc_Lit2Var(n.n) == 0; }
  bool isAnd(const BBNodeGia& n) const { return Gia_ObjIsAnd(obj(n)); }
  unsigned nodeId(const BBNodeGia& n) const
  {
    return (unsigned)Abc_Lit2Var(n.n);
  }

  // The fanins of an AND, with the sign stripped, as the other two managers
  // do: provenance and traversal are both sign-insensitive, and returning the
  // signed edge would key two memo entries per node.
  BBNodeGia fanin0(const BBNodeGia& n) const
  {
    const int id = Abc_Lit2Var(n.n);
    return BBNodeGia(Abc_LitRegular(Gia_ObjFaninLit0(obj(n), id)));
  }
  BBNodeGia fanin1(const BBNodeGia& n) const
  {
    const int id = Abc_Lit2Var(n.n);
    return BBNodeGia(Abc_LitRegular(Gia_ObjFaninLit1(obj(n), id)));
  }

  // An uncomplemented input this manager minted, and its ordinal.
  //
  // Not the same question as isCI(), which ignores the complement bit: a
  // complemented input is still an input, but it is not one the blaster can
  // name, and an abstraction record that stored its ordinal would be
  // recording the wrong polarity.
  bool isNamedCI(const BBNodeGia& n) const
  {
    return !n.IsNull() && !Abc_LitIsCompl(n.n) && isCI(n);
  }
  int ciOrdinal(const BBNodeGia& n) const
  {
    assert(isNamedCI(n));
    return Gia_ObjCioId(obj(n));
  }

  // --- the gate builders --------------------------------------------------

  BBNodeGia CreateNode(Kind kind, std::vector<BBNodeGia>& children)
  {
    assert(children.size() != 0);
    for (size_t i = 0, size = children.size(); i < size; ++i)
      assert(!children[i].IsNull());

    int r;
    switch (kind)
    {
      case AND:
        r = tower(Gia_ManHashAnd, children);
        break;

      case NAND:
        r = Abc_LitNot(tower(Gia_ManHashAnd, children));
        break;

      case OR:
        r = tower(Gia_ManHashOr, children);
        break;

      case NOR:
        r = Abc_LitNot(tower(Gia_ManHashOr, children));
        break;

      case NOT:
        assert(children.size() == 1);
        r = Abc_LitNot(children[0].n);
        break;

      case XOR:
        r = tower(Gia_ManHashXor, children);
        break;

      case IFF:
        assert(children.size() == 2);
        r = Abc_LitNot(Gia_ManHashXor(giaMgr, children[0].n, children[1].n));
        break;

      case IMPLIES:
        assert(children.size() == 2);
        r = Gia_ManHashOr(giaMgr, Abc_LitNot(children[0].n), children[1].n);
        break;

      case ITE:
        assert(children.size() == 3);
        r = Gia_ManHashMux(giaMgr, children[0].n, children[1].n,
                           children[2].n);
        break;

      default:
        std::cerr << "Not handled::!!" << _kind_names[kind];
        FatalError("Never here");
        exit(-1);
    }
    checkBudget();
    return BBNodeGia(r);
  }

  BBNodeGia CreateNode(Kind kind, const BBNodeGia& child0,
                       const std::vector<BBNodeGia>& back_children =
                           std::vector<BBNodeGia>())
  {
    std::vector<BBNodeGia> front;
    front.reserve(1 + back_children.size());
    front.push_back(child0);
    front.insert(front.end(), back_children.begin(), back_children.end());
    return CreateNode(kind, front);
  }

  BBNodeGia CreateNode(Kind kind, const BBNodeGia& child0,
                       const BBNodeGia& child1,
                       const std::vector<BBNodeGia>& back_children =
                           std::vector<BBNodeGia>())
  {
    std::vector<BBNodeGia> front;
    front.reserve(2 + back_children.size());
    front.push_back(child0);
    front.push_back(child1);
    front.insert(front.end(), back_children.begin(), back_children.end());
    return CreateNode(kind, front);
  }

  BBNodeGia CreateNode(Kind kind, const BBNodeGia& child0,
                       const BBNodeGia& child1, const BBNodeGia& child2,
                       const std::vector<BBNodeGia>& back_children =
                           std::vector<BBNodeGia>())
  {
    std::vector<BBNodeGia> front;
    front.reserve(3 + back_children.size());
    front.push_back(child0);
    front.push_back(child1);
    front.push_back(child2);
    front.insert(front.end(), back_children.begin(), back_children.end());
    return CreateNode(kind, front);
  }

  // Called after every CreateNode(). One node can add a whole fan-in tower
  // before this runs, so the count at the throw can overshoot the budget by
  // the width of one operator -- as with the other two managers, the cap
  // bounds the order of magnitude rather than being an exact ceiling.
  //
  // The second clause is not a budget at all. Gia_ManAppendObj prints a line
  // and calls exit(1) when the object count reaches 2^29, which would take
  // the process out with no answer and nothing to catch. Stopping short of it
  // turns that into the same AIGBudgetExhausted every other over-large blast
  // raises, which unwinds and reports.
  void checkBudget() const
  {
    const int64_t ands = Gia_ManAndNum(giaMgr);
    if (nodeBudget >= 0 && ands > nodeBudget)
      throw AIGBudgetExhausted(ands);

    if (Gia_ManObjNum(giaMgr) >= GIA_OBJECT_CEILING)
      throw AIGBudgetExhausted(ands);
  }

private:
  // ABC's hard limit is 1 << 29 objects. Leave room for the fan-in tower that
  // may still be in flight when this fires.
  static const int GIA_OBJECT_CEILING = (1 << 29) - (1 << 16);

  Gia_Obj_t* obj(const BBNodeGia& n) const
  {
    assert(!n.IsNull());
    return Gia_ManObj(giaMgr, Abc_Lit2Var(n.n));
  }

  // A two-input gate takes two operands, so a wide one becomes a log-height
  // tower. Built the same way as the other two managers -- front two off,
  // result to the back -- because which operands end up paired decides which
  // subterms are shared, and so decides the gate count.
  int tower(int (*op)(Gia_Man_t*, int, int),
            const std::vector<BBNodeGia>& children)
  {
    if (children.size() == 1)
      return children[0].n;

    // Two is the overwhelming majority of what a blast emits, and the deque
    // below would allocate twice to pair them. The tower reduces to the same
    // call.
    if (children.size() == 2)
      return op(giaMgr, children[0].n, children[1].n);

    std::deque<int> names;
    for (size_t i = 0, size = children.size(); i < size; ++i)
      names.push_back(children[i].n);

    while (names.size() > 2)
    {
      const int a = names.front();
      names.pop_front();
      const int b = names.front();
      names.pop_front();
      names.push_back(op(giaMgr, a, b));
    }

    const int a = names.front();
    names.pop_front();
    const int b = names.front();
    return op(giaMgr, a, b);
  }
};

} // namespace stp

#endif

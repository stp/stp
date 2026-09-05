/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
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

#ifndef BBNodeManagerAIG_H_
#define BBNodeManagerAIG_H_

#include <cstdint>
#include <stdexcept>

#include "BBNodeAIG.h"
#include "stp/ToSat/AIGBudget.h"
#include "stp/ToSat/ToSATBase.h"

// From ABC
#include "aig/aig/aig.h"
#include "sat/cnf/cnf.h"
#include "opt/dar/dar.h"

namespace stp
{
class ASTNode;
class STPMgr; // we ignore this anyway.

extern vector<BBNodeAIG> _empty_BBNodeAIGVec;

/* ABC's Aig_Exor() and Aig_Mux2() both build their result with two Aig_And()
 * calls sitting in a single Aig_Or() argument list. The order that function
 * arguments are evaluated in is unspecified, so GCC (right to left) and Clang
 * (left to right) create those two AIG nodes in opposite orders. The nodes get
 * different Ids, and because Ids are what everything downstream sorts on, the
 * CNF we emit isn't the same from one compiler to the next.
 *
 * These build the same nodes in a fixed order. Aside from the sequencing they
 * match aigOper.c exactly, so use them in preference to ABC's versions.
 */
inline Aig_Obj_t* orderedAigExor(Aig_Man_t* p, Aig_Obj_t* p0, Aig_Obj_t* p1)
{
  // Aig_Exor()'s fCatchExor branch isn't reproduced here. Nothing in STP turns
  // that on, and Aig_ManStart() leaves it off.
  assert(!p->fCatchExor);

  if (p0 == p1)
    return Aig_ManConst0(p);
  if (p0 == Aig_Not(p1))
    return Aig_ManConst1(p);
  if (Aig_Regular(p0) == Aig_ManConst1(p))
    return Aig_NotCond(p1, p0 == Aig_ManConst1(p));
  if (Aig_Regular(p1) == Aig_ManConst1(p))
    return Aig_NotCond(p0, p1 == Aig_ManConst1(p));

  Aig_Obj_t* const positive = Aig_And(p, p0, Aig_Not(p1));
  Aig_Obj_t* const negative = Aig_And(p, Aig_Not(p0), p1);
  return Aig_Or(p, positive, negative);
}

// Aig_Mux() hard-codes fUseMuxCanon to zero, so it always just hands over to
// Aig_Mux2(). This is Aig_Mux2().
inline Aig_Obj_t* orderedAigMux(Aig_Man_t* p, Aig_Obj_t* pC, Aig_Obj_t* p1,
                                Aig_Obj_t* p0)
{
  Aig_Obj_t* const thn = Aig_And(p, pC, p1);
  Aig_Obj_t* const els = Aig_And(p, Aig_Not(pC), p0);
  return Aig_Or(p, thn, els);
}

// The DAR 4-input subgraph library is a process-global that costs roughly
// 150M instructions to build, and all three of its users -- AIG rewriting
// inside CNF conversion, the exact-encoder's rewrite, and the propositional
// core simplifier -- share the one copy.
//
// It used to have three callers of Dar_LibStart() and a single Dar_LibStop(),
// so the core simplifier tore down the library the other two were still
// relying on and the next rewrite re-paid the build. Dar_LibStop() also
// asserts the library is live, making a second call an abort rather than a
// no-op. One owner, started on demand and kept for the process: Dar_LibStart()
// is already idempotent, so the cost is paid once however many callers there
// are.
inline void ensureDarLibrary()
{
  Dar_LibStart();
}

// Creates AIG nodes with ABC and wraps them in BBNodeAIG's.
class BBNodeManagerAIG
{
public:
  Aig_Man_t* aigMgr;

  // Hard cap on AND gates; -1 (the default) is no limit, 0 permits none.
  // Set it before any blasting starts -- checkBudget() reads it on every
  // CreateNode().
  int64_t nodeBudget = -1;

  // Map from symbols to their AIG nodes.
  typedef std::map<ASTNode, vector<BBNodeAIG>> SymbolToBBNode;
  SymbolToBBNode symbolToBBNode;

  int totalNumberOfNodes()
  {
    return aigMgr->nObjs[AIG_OBJ_AND]; // without having removed non-reachable.
  }

  // --- the interface everything above the manager is allowed to use --------
  //
  // These exist so that no caller reaches through `aigMgr` into ABC. That is
  // not tidiness: BitBlaster cannot be instantiated over a second node
  // representation while it names Aig_Obj_t directly, and every one of these
  // is a method that representation would have to provide anyway.

  // A combinational input that stands for no symbol. The BV abstraction
  // machinery mints these for proxies and for abstracted results, which is
  // why it does not go through CreateSymbol.
  BBNodeAIG CreateFreshInput()
  {
    BBNodeAIG fresh(Aig_ObjCreateCi(aigMgr));
    fresh.symbol_index = aigMgr->vCis->nSize - 1;
    return fresh;
  }

  // How many combinational inputs exist, and the object id of one of them by
  // creation order. The CNF seam left one caller for the id -- the
  // propositional core's map back to the AIG it rewrote -- and everything
  // that wanted a SAT variable now asks CNF::varOfCi() for it by the same
  // ordinal.
  //
  // Positional rather than by node, because dag-aware rewriting replaces the
  // manager wholesale and only the position in vCis survives it.
  int ciCount() const { return aigMgr->vCis->nSize; }

  int ciObjectId(int ordinal) const
  {
    assert(ordinal >= 0 && ordinal < ciCount());
    return Aig_ObjId((Aig_Obj_t*)Vec_PtrEntry(aigMgr->vCis, ordinal));
  }

  BBNodeAIG ciNode(int ordinal) const
  {
    assert(ordinal >= 0 && ordinal < ciCount());
    return BBNodeAIG((Aig_Obj_t*)Vec_PtrEntry(aigMgr->vCis, ordinal));
  }

  // Node-level queries, all on the uncomplemented node: a literal and its
  // negation answer these identically.
  static bool isCI(const BBNodeAIG& n) { return Aig_ObjIsCi(Aig_Regular(n.n)); }

  // Whether this handle is an input of this manager's own making, held
  // uncomplemented so that its ordinal is meaningful -- and that ordinal.
  //
  // Not the same question as isCI(), which strips the complement bit before
  // asking: a complemented input is still an input, but it is not one the
  // blaster can name, and an abstraction record that stored its ordinal would
  // be recording the wrong polarity. The blaster asks these rather than
  // reading BBNodeAIG::symbol_index, so that the shared blasting code does
  // not depend on one backend's handle carrying an ordinal at all.
  static bool isNamedCI(const BBNodeAIG& n)
  {
    return !n.IsNull() && n.symbol_index >= 0;
  }
  static int ciOrdinal(const BBNodeAIG& n)
  {
    assert(isNamedCI(n));
    return n.symbol_index;
  }
  static bool isConstant(const BBNodeAIG& n)
  {
    return Aig_ObjIsConst1(Aig_Regular(n.n));
  }
  static bool isAnd(const BBNodeAIG& n) { return Aig_ObjIsAnd(Aig_Regular(n.n)); }
  static unsigned nodeId(const BBNodeAIG& n)
  {
    return Aig_ObjId(Aig_Regular(n.n));
  }

  // The fanins of an AND, with the sign stripped. Provenance and traversal
  // are both sign-insensitive; returning the signed edge here would key two
  // memo entries per node.
  static BBNodeAIG fanin0(const BBNodeAIG& n)
  {
    return BBNodeAIG(Aig_ObjFanin0(Aig_Regular(n.n)));
  }
  static BBNodeAIG fanin1(const BBNodeAIG& n)
  {
    return BBNodeAIG(Aig_ObjFanin1(Aig_Regular(n.n)));
  }

  // Called after every CreateNode(). A single node can add a whole fan-in
  // tower before this runs, so the count at the throw can overshoot the
  // budget by the width of one operator -- the cap is a bound on the order
  // of magnitude, not an exact ceiling.
  void checkBudget() const
  {
    if (nodeBudget >= 0 &&
        static_cast<int64_t>(aigMgr->nObjs[AIG_OBJ_AND]) > nodeBudget)
      throw AIGBudgetExhausted(aigMgr->nObjs[AIG_OBJ_AND]);
  }

private:
  // AIGs can only take two parameters. This makes a log_2 height
  // tower of varadic inputs.
  Aig_Obj_t* makeTower(Aig_Obj_t* (*t)(Aig_Man_t*, Aig_Obj_t*, Aig_Obj_t*),
                       vector<BBNodeAIG>& children)
  {
    std::deque<Aig_Obj_t*> names;

    for (size_t i = 0, size = children.size(); i < size; ++i)
      names.push_back(children[i].n);

    while (names.size() > 2)
    {
      Aig_Obj_t* a = names.front();
      names.pop_front();

      Aig_Obj_t* b = names.front();
      names.pop_front();

      Aig_Obj_t* n = t(aigMgr, a, b);
      names.push_back(n);
    }

    // last two now.
    assert(names.size() == 2);

    Aig_Obj_t* a = names.front();
    names.pop_front();

    Aig_Obj_t* b = names.front();
    names.pop_front();

    return t(aigMgr, a, b);
  }

  // no copy. no assignment.
  BBNodeManagerAIG& operator=(const BBNodeManagerAIG& other) = delete;
  BBNodeManagerAIG(const BBNodeManagerAIG& other) = delete;

public:
  BBNodeManagerAIG() : aigMgr(NULL)
  {
    aigMgr = Aig_ManStart(0);
    // fancier strashing.
    aigMgr->fAddStrash = 1;
  }

  // Swap in a strash table sized for the whole blast, before anything is
  // built. Only the table: restarting the manager at the hinted size would
  // also make its node-page chunk that large, which costs real memory --
  // measured at +5-9% peak on large blasts -- while the table alone retires
  // Aig_TableResize and runs at load factor <= 1 where the growth policy
  // oscillates between 0.5 and 2. The table holds only AND nodes and none
  // exist yet, so an empty replacement is the same table, larger.
  void hintExpectedAnds(uint64_t n)
  {
    assert(Aig_ManNodeNum(aigMgr) == 0);
    const uint64_t cap = 1ull << 26;
    const uint64_t want = n + (n >> 4) + 1024;
    // The full expected count, not a fraction of it: the chain walk is
    // memory-bound, and a factor sweep put the knee here -- half this table
    // costs 14-18% of blasting for at most 4% of process peak, while twice
    // it buys back under half as much for memory that climbs faster.
    const int slots = Abc_PrimeCudd((unsigned)(want < cap ? want : cap));
    if (slots <= aigMgr->nTableSize)
      return;
    ABC_FREE(aigMgr->pTable);
    aigMgr->nTableSize = slots;
    aigMgr->pTable = ABC_ALLOC(Aig_Obj_t*, slots);
    memset(aigMgr->pTable, 0, sizeof(Aig_Obj_t*) * slots);
  }

  void stop()
  {
    if (aigMgr != NULL)
      Aig_ManStop(aigMgr);
    aigMgr = NULL;
  }

  ~BBNodeManagerAIG() { stop(); }

  BBNodeAIG getTrue() { return BBNodeAIG(Aig_ManConst1(aigMgr)); }

  BBNodeAIG getFalse() { return BBNodeAIG(Aig_ManConst0(aigMgr)); }

  // The same symbol always needs to return the same AIG node,
  // if it doesn't you will get the wrong answer.
  BBNodeAIG CreateSymbol(const ASTNode& n, unsigned i)
  {
    assert(n.GetKind() == SYMBOL);

    // booleans have width 0.
    const unsigned width = std::max((unsigned)1, n.GetValueWidth());

    SymbolToBBNode::iterator it;
    it = symbolToBBNode.find(n);
    if (symbolToBBNode.end() == it)
    {
      symbolToBBNode[n] = vector<BBNodeAIG>(width);
      it = symbolToBBNode.find(n);
    }

    assert(it->second.size() == width);
    assert(i < width);

    if (!it->second[i].IsNull())
      return it->second[i];

    it->second[i] = BBNodeAIG(Aig_ObjCreateCi(aigMgr));
    it->second[i].symbol_index = aigMgr->vCis->nSize - 1;
    return it->second[i];
  }

  BBNodeAIG CreateNode(Kind kind, vector<BBNodeAIG>& children)
  {
    Aig_Obj_t* pNode;
    assert(children.size() != 0);

    for (size_t i = 0, size = children.size(); i < size; ++i)
      assert(!children[i].IsNull());

    switch (kind)
    {
      case AND:
        if (children.size() == 1)
          pNode = children[0].n;
        else if (children.size() == 2)
          pNode = Aig_And(aigMgr, children[0].n, children[1].n);
        else
          pNode = makeTower(Aig_And, children);
        break;

      case OR:
        if (children.size() == 1)
          pNode = children[0].n;
        else if (children.size() == 2)
          pNode = Aig_Or(aigMgr, children[0].n, children[1].n);
        else
          pNode = makeTower(Aig_Or, children);
        break;

      case NAND:
        // The one-child cases mirror AND and OR above. makeTower needs at
        // least two, and a single-bit field is not hypothetical: the
        // significand of a two-bit format has exactly one stored bit, so
        // NOR over it arrives here with one child.
        if (children.size() == 1)
          pNode = children[0].n;
        else if (children.size() == 2)
          pNode = Aig_And(aigMgr, children[0].n, children[1].n);
        else
          pNode = makeTower(Aig_And, children);
        pNode = Aig_Not(pNode);
        break;

      case NOT:
        assert(children.size() == 1);
        pNode = Aig_Not(children[0].n);
        break;

      case NOR:
        if (children.size() == 1)
          pNode = children[0].n;
        else if (children.size() == 2)
          pNode = Aig_Or(aigMgr, children[0].n, children[1].n);
        else
          pNode = makeTower(Aig_Or, children);
        pNode = Aig_Not(pNode);
        break;

      case XOR:
        if (children.size() == 1)
          pNode = children[0].n;
        else if (children.size() == 2)
          pNode = orderedAigExor(aigMgr, children[0].n, children[1].n);
        else
          pNode = makeTower(orderedAigExor, children);
        break;

      case IFF:
        assert(children.size() == 2);
        pNode = orderedAigExor(aigMgr, children[0].n, children[1].n);
        pNode = Aig_Not(pNode);
        break;

      case IMPLIES:
        assert(children.size() == 2);
        pNode = Aig_Or(aigMgr, Aig_Not(children[0].n), children[1].n);
        break;

      case ITE:
        assert(children.size() == 3);
        pNode =
            orderedAigMux(aigMgr, children[0].n, children[1].n, children[2].n);
        break;

      default:
        cerr << "Not handled::!!" << _kind_names[kind];
        FatalError("Never here");
        assert(false);
        exit(-1);
    }
    checkBudget();
    return BBNodeAIG(pNode);
  }

  BBNodeAIG
  CreateNode(Kind kind, const BBNodeAIG& child0,
             const vector<BBNodeAIG>& back_children = _empty_BBNodeAIGVec)
  {
    vector<BBNodeAIG> front_children;
    front_children.reserve(1 + back_children.size());
    front_children.push_back(child0);
    front_children.insert(front_children.end(), back_children.begin(),
                          back_children.end());
    return CreateNode(kind, front_children);
  }

  BBNodeAIG
  CreateNode(Kind kind, const BBNodeAIG& child0, const BBNodeAIG& child1,
             const vector<BBNodeAIG>& back_children = _empty_BBNodeAIGVec)
  {
    vector<BBNodeAIG> front_children;
    front_children.reserve(2 + back_children.size());
    front_children.push_back(child0);
    front_children.push_back(child1);
    front_children.insert(front_children.end(), back_children.begin(),
                          back_children.end());
    return CreateNode(kind, front_children);
  }

  BBNodeAIG
  CreateNode(Kind kind, const BBNodeAIG& child0, const BBNodeAIG& child1,
             const BBNodeAIG& child2,
             const vector<BBNodeAIG>& back_children = _empty_BBNodeAIGVec)
  {
    vector<BBNodeAIG> front_children;
    front_children.reserve(3 + back_children.size());
    front_children.push_back(child0);
    front_children.push_back(child1);
    front_children.push_back(child2);
    front_children.insert(front_children.end(), back_children.begin(),
                          back_children.end());
    return CreateNode(kind, front_children);
  }
};
}

#endif /* BBNodeManagerAIG_H_ */

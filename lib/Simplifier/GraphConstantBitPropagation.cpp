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

#include "stp/Simplifier/GraphConstantBitPropagation.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/Simplifier/Simplifier.h"
#include <algorithm>
#include <iostream>
#include <memory>
#include <vector>

using simplifier::constantBitP::CONFLICT;
using simplifier::constantBitP::ConstantBitPropagation;
using simplifier::constantBitP::FixedBits;
using simplifier::constantBitP::MultiplicationStatsMap;
using simplifier::constantBitP::NO_CHANGE;
using simplifier::constantBitP::WorkList;

namespace stp
{
void GraphConstantBitPropagation::clear()
{
  for (auto& e : fixed)
    delete e.second;
  fixed.clear();
  delete msm;
  msm = NULL;
  delete work;
  work = NULL;
}

FixedBits* GraphConstantBitPropagation::bitsOf(const ASTNode& n)
{
  const auto it = fixed.find(n);
  if (it != fixed.end())
    return it->second;
  FixedBits* b = ConstantBitPropagation::makeInitialFixedBits(n);
  fixed.insert({n, b});
  return b;
}

void GraphConstantBitPropagation::scheduleParents(const ASTNode& n,
                                                  const ASTNode& except)
{
  std::vector<ASTNode> ps;
  g->parents(n, ps);
  for (const ASTNode& p : ps)
    if (p != except)
      work->push(p);
}

// ConstantBitPropagation::propagate over the graph's parents.
void GraphConstantBitPropagation::propagate()
{
  if (status == CONFLICT)
    return;
  while (!work->isEmpty())
  {
    const ASTNode n = work->pop();
    if (n.isConstant())
      continue;
    FixedBits* nBits = bitsOf(n);
    const unsigned previousTop = nBits->countFixed();
    const unsigned degree = n.Degree();
    childrenBits.clear();
    previousChildrenFixedCount.clear();
    for (unsigned i = 0; i < degree; i++)
    {
      FixedBits* cb = bitsOf(n[i]);
      childrenBits.push_back(cb);
      previousChildrenFixedCount.push_back(cb->countFixed());
    }
    if (n.GetKind() != SYMBOL)
    {
      status = ConstantBitPropagation::dispatchToTransferFunctions(
          bm, n.GetKind(), childrenBits, *nBits, n, msm);
      assert(((unsigned)nBits->getWidth()) == n.GetValueWidth() ||
             nBits->getWidth() == 1);
    }
    if (status == CONFLICT)
      return;
    if (status == NO_CHANGE)
      continue;
    if (nBits->countFixed() != previousTop)
      scheduleParents(n, ASTNode());
    for (unsigned i = 0; i < degree; i++)
      if (childrenBits[i]->countFixed() != previousChildrenFixedCount[i])
      {
        scheduleParents(n[i], n);
        work->push(n[i]);
      }
  }
}

ASTNode GraphConstantBitPropagation::constantFor(const ASTNode& node,
                                                 const FixedBits& bits) const
{
  if (!bits.isTotallyFixed() || node.isConstant())
    return ASTNode();
  // Other nodes carry the same information: an extract or concat does not
  // change the fixings.
  if (node.GetKind() == BVEXTRACT || node.GetKind() == BVCONCAT)
    return ASTNode();
  // A floating-point node's FixedBits is a placeholder.
  if (node.GetType() != BOOLEAN_TYPE && node.GetType() != BITVECTOR_TYPE)
    return ASTNode();
  return ConstantBitPropagation::bitsToNode(bm->defaultNodeFactory, node, bits);
}

void GraphConstantBitPropagation::topLevel(MutableGraph& graph, Simplifier* s)
{
  bm->GetRunTimes()->start(RunTimes::ConstantBitPropagation);
  g = &graph;
  simp = s;
  status = NO_CHANGE;
  symbolsFixed = factsConjoined = nodesReplaced = 0;
  clear();
  msm = new MultiplicationStatsMap();
  const ASTNode root = graph.root();
  assert(root.GetType() == BOOLEAN_TYPE);
  work = new WorkList(root);
  NodeFactory& nf = graph.factory();

  // What the structure alone fixes: replaced outright, an equivalence.
  propagate();
  std::vector<std::pair<ASTNode, ASTNode>> unconditional;
  if (status != CONFLICT)
    for (const auto& e : fixed)
    {
      const ASTNode c = constantFor(e.first, *e.second);
      if (!c.IsNull() && e.first.GetKind() != SYMBOL)
        unconditional.push_back({e.first, c});
    }

  // Then with the root asserted.
  if (status != CONFLICT)
  {
    FixedBits& top = *bitsOf(root);
    top.setFixed(0, true);
    top.setValue(0, true);
    work->push(root);
    propagate();
  }
  if (status == CONFLICT)
  {
    graph.setRoot(bm->ASTFalse);
    clear();
    g = NULL;
    bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);
    bm->ASTNodeStats("After Constant Bit Propagation. ", graph.root());
    return;
  }

  // What the assertion fixes: symbols to substitute, interior nodes to pin
  // and replace. In node-number order; the map's order is not defined.
  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  if (ext != NULL && !ext->activeInSolve())
    ext = NULL;
  struct Fact
  {
    ASTNode node;
    ASTNode constant;
    bool replaceHolders; // a witness read stays where it is, pinned only
  };
  std::vector<std::pair<ASTNode, ASTNode>> symbols;
  std::vector<Fact> facts;
  {
    ankerl::unordered_dense::set<uint64_t> unconditionalKeys;
    for (const auto& u : unconditional)
      unconditionalKeys.insert(u.first.GetNodeNum());
    for (const auto& e : fixed)
    {
      const ASTNode& node = e.first;
      if (node == root || unconditionalKeys.count(node.GetNodeNum()) != 0)
        continue;
      const ASTNode c = constantFor(node, *e.second);
      if (c.IsNull())
        continue;
      if (node.GetKind() == SYMBOL)
        symbols.push_back({node, c});
      else
        facts.push_back({node, c, ext == NULL || !ext->isWitnessRead(node)});
    }
  }
  auto byNumber = [](const ASTNode& a, const ASTNode& b) {
    return a.GetNodeNum() < b.GetNodeNum();
  };
  std::sort(unconditional.begin(), unconditional.end(),
            [&](const std::pair<ASTNode, ASTNode>& a, const std::pair<ASTNode, ASTNode>& b) {
              return byNumber(a.first, b.first);
            });
  std::sort(symbols.begin(), symbols.end(),
            [&](const std::pair<ASTNode, ASTNode>& a, const std::pair<ASTNode, ASTNode>& b) {
              return byNumber(a.first, b.first);
            });
  std::sort(facts.begin(), facts.end(),
            [&](const Fact& a, const Fact& b) { return byNumber(a.node, b.node); });
  // The fixed bits are read; from here the formula changes.
  clear();

  auto inFormula = [&](const ASTNode& n) {
    return graph.isRootNode(n) || graph.parentCount(n) > 0;
  };

  // 1. Unconditionally fixed nodes become their constants.
  for (const auto& u : unconditional)
  {
    const ASTNode cur = graph.current(u.first);
    if (cur.Degree() == 0 || !inFormula(cur))
      continue;
    graph.replace(cur, u.second);
    nodesReplaced++;
  }

  // 2. Fixed symbols: defined for the model and substituted; a symbol the
  // map refuses (protected) is pinned by a fact instead.
  ASTVec conjoin;
  for (const auto& sc : symbols)
  {
    if (!inFormula(sc.first))
      continue;
    if (simp->UpdateSubstitutionMap(sc.first, sc.second))
    {
      graph.substitute(sc.first, sc.second);
      symbolsFixed++;
    }
    else if (sc.first.GetType() == BOOLEAN_TYPE)
      conjoin.push_back(sc.second == bm->ASTTrue ? sc.first : nf.CreateNode(NOT, sc.first));
    else
      conjoin.push_back(nf.CreateNode(EQ, sc.first, sc.second));
  }

  // 3. Each fixed interior node is its constant in every holder, then its
  // fact is conjoined at the root, which brings the node back as the
  // fact's operand. The order matters: a fact is built through the
  // simplifying factory, which may turn EQ(n, c) into a node that holds n
  // only through another (NOT(EQ(0, n)) for an xor fixed to one), so
  // "every holder but the fact" cannot be told by handle; repointing first
  // leaves nothing to tell. Inner nodes come first (ascending number), so
  // an outer node's fact is built over their constants, and one that folds
  // to true is implied by the others and dropped.
  for (const Fact& f : facts)
  {
    ASTNode node = graph.current(f.node);
    if (node.Degree() == 0 || !inFormula(node))
      continue;
    if (f.replaceHolders)
    {
      std::vector<ASTNode> holders;
      graph.parents(node, holders);
      std::sort(holders.begin(), holders.end(), byNumber);
      holders.erase(std::unique(holders.begin(), holders.end()), holders.end());
      for (const ASTNode& given : holders)
      {
        // The list is a snapshot: a repoint re-keys holders.
        const ASTNode h = graph.current(given);
        if (h.Degree() == 0 || !inFormula(h))
          continue;
        MutableInterior* m = h.isMutableInterior() ? MutableGraph::asMutable(h)
                                                   : graph.materialise(h);
        if (m == NULL || m->isDead())
          continue;
        // A wide holder (the root conjunction, with a slot per fact) is
        // patched through the graph's slot index, not scanned per fact.
        nodesReplaced += graph.repointAll(m, graph.current(node), f.constant);
      }
      node = graph.current(node);
      if (node.Degree() == 0)
        continue; // folded under the repoints: implied
    }
    ASTNode fact;
    if (node.GetType() == BOOLEAN_TYPE)
      fact = f.constant == bm->ASTTrue ? node : nf.CreateNode(NOT, node);
    else
      fact = nf.CreateNode(EQ, node, f.constant);
    if (fact != bm->ASTTrue)
      conjoin.push_back(fact);
  }
  if (!conjoin.empty())
  {
    const ASTNode r = graph.root();
    ASTVec kids;
    if (r.GetKind() == AND)
      kids.insert(kids.end(), r.begin(), r.end());
    else
      kids.push_back(r);
    kids.insert(kids.end(), conjoin.begin(), conjoin.end());
    graph.setRoot(nf.CreateNode(AND, kids));
    factsConjoined += conjoin.size();
  }

  g = NULL;
  bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);
  if (bm->UserFlags.stats_flag)
    std::cerr << "{CBitP} symbols fixed:" << symbolsFixed << " facts conjoined:"
              << factsConjoined << " nodes replaced:" << nodesReplaced << std::endl;
  bm->ASTNodeStats("After Constant Bit Propagation. ", graph.root());
}

ASTNode GraphConstantBitPropagation::topLevel(const ASTNode& n, Simplifier* s)
{
  MutableGraph graph(*bm);
  graph.import(n);
  topLevel(graph, s);
  return graph.exportRoot();
}
}

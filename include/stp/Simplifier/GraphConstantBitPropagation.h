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
 * Constant bit propagation over a MutableGraph, behind --passes-on-graph.
 *
 * The same transfer functions and fixed-bits domain as ConstantBitPropagation
 * (constantBitP/), over the same worklist, with the graph's parent lists in
 * place of the pass's own Dependencies map. A first propagation without the
 * root asserted finds what the structure alone fixes; the root is then set
 * to true and propagated again. What that fixes is applied as the original
 * applies it: a fixed symbol is substituted and defined for the model; a
 * fixed interior node is pinned by a fact conjoined at the root and replaced
 * by its constant in every other holder, so the constraint on its inputs is
 * kept while the rest of the formula sees the constant. A conflict makes the
 * root false.
 */

#ifndef GRAPHCONSTANTBITPROPAGATION_H_
#define GRAPHCONSTANTBITPROPAGATION_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/MutableGraph.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/WorkList.h"
#include <vector>

namespace stp
{
class Simplifier;

class GraphConstantBitPropagation
{
  STPMgr* bm;
  Simplifier* simp = NULL;
  MutableGraph* g = NULL;

  typedef ankerl::unordered_dense::map<ASTNode, simplifier::constantBitP::FixedBits*,
                                       ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>
      FixedMap;
  FixedMap fixed;
  simplifier::constantBitP::MultiplicationStatsMap* msm = NULL;
  simplifier::constantBitP::WorkList* work = NULL;
  simplifier::constantBitP::Result status = simplifier::constantBitP::NO_CHANGE;
  std::vector<simplifier::constantBitP::FixedBits*> childrenBits;
  std::vector<unsigned> previousChildrenFixedCount;
  unsigned symbolsFixed = 0;
  unsigned factsConjoined = 0;
  unsigned nodesReplaced = 0;

  simplifier::constantBitP::FixedBits* bitsOf(const ASTNode& n);
  void propagate();
  // The parents of n go on the worklist, `except` left off: the transfer
  // function that just ran left it at its fixed point for these values.
  void scheduleParents(const ASTNode& n, const ASTNode& except);
  // The constant a totally fixed node stands for, or null where the node
  // is not one this pass turns into a constant.
  ASTNode constantFor(const ASTNode& node,
                      const simplifier::constantBitP::FixedBits& bits) const;
  void clear();

public:
  GraphConstantBitPropagation(const GraphConstantBitPropagation&) = delete;
  GraphConstantBitPropagation& operator=(const GraphConstantBitPropagation&) = delete;
  explicit GraphConstantBitPropagation(STPMgr* bm_) : bm(bm_) {}
  ~GraphConstantBitPropagation() { clear(); }

  bool isUnsatisfiable() const
  {
    return status == simplifier::constantBitP::CONFLICT;
  }
  void topLevel(MutableGraph& graph, Simplifier* simp);
  // Standalone: import, run, export.
  ASTNode topLevel(const ASTNode& n, Simplifier* simp);
};
}
#endif

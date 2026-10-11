/********************************************************************
 * AUTHORS: Trevor Hansen
 *
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
 * Sharing-aware rewriting on a MutableGraph.
 *
 * Every rule here replaces a node by a smaller one only where the nodes it
 * takes apart die with it, which the parent count decides. The pass used
 * to count parents once over its input and rebuild the formula bottom-up;
 * the counts went stale as rules fired, and a node whose child became
 * single-use after it was visited was never looked at again. On the graph
 * the counts are live: the formula is indexed in place, every node is
 * examined once bottom-up, a rule that fires edits the graph, and the
 * graph's queue runs the rules again over what changed. A count-change
 * event on a node that now has one parent re-examines that parent.
 */

#ifndef REWRITING_H_
#define REWRITING_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/MutableGraph.h"
#include <string>

namespace stp
{

class Rewriting : public NodeRewriter
{
  STPMgr* stpMgr;
  // The factory the rules build through: the graph's while a run is on.
  NodeFactory* nf;
  MutableGraph* g = NULL;
  // STP_REWRITING_CHECK_GRAPH in the environment: recount the graph after
  // every edit. For the fuzzers; O(formula) per edit.
  const bool checkGraph;
  unsigned fired = 0;
  unsigned narrowedBitwise = 0;

  // Exactly one place reads n now: the rule's own node, so n dies with it.
  bool unshared(const ASTNode& n) const { return g->parentCount(n) <= 1; }
  // In the formula as it stands, as opposed to built by a rule and not
  // yet attached.
  bool inFormula(const ASTNode& n) const
  {
    return g->isRootNode(n) || g->parentCount(n) > 0;
  }
  ASTNode rebuild(const ASTNode& n, const ASTVec& kids);

  // Every sharing-aware rule, in order, over one node. Each rule sees what
  // the rules before it produced. Nothing here descends.
  ASTNode applyRules(ASTNode c);
  // The rules over a node a rule just built and over the fresh nodes
  // under it, as the old rebuild fed a rule's result back through its
  // walk. Nodes of the formula stop the descent: the sweep and the queue
  // cover them. `rulesHere` false runs them over the children only.
  ASTNode rewriteFresh(const ASTNode& n, bool rulesHere);
  // The rules over a node of the formula; a result that differs replaces
  // it in the graph.
  void examine(const ASTNode& n);
  // Count-change events since the last drain: a node that now has one
  // parent may let a rule fire on that parent.
  void drainCounts();

public:
  Rewriting(const Rewriting&) = delete;
  Rewriting& operator=(const Rewriting&) = delete;
  // `nf_` is what the pass builds through outside a run; a run builds
  // through its graph.
  Rewriting(STPMgr* stp_, NodeFactory* nf_);

  // NodeRewriter: the rules over a queued node of the graph.
  virtual ASTNode rewrite(const ASTNode& attached) override;

  ASTNode topLevel(ASTNode& n);
};
}
#endif

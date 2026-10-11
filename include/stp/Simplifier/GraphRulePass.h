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
 * A size-reducing pass whose rules are local to a node and guarded by
 * parent counts, run over a MutableGraph.
 *
 * The formula is indexed in place. Every interior node is examined once,
 * in node-number order (children before parents, or the reverse for a
 * pass that asks); a node a rule changes is replaced in the graph,
 * whose queue runs the simplifying rules and this pass's rules again over
 * what changed; a node that comes to have one parent re-examines that
 * parent; the formula is exported once, after the last pass that shares
 * the graph. The counts the rules read are the formula's as it stands, not
 * a snapshot of the input.
 *
 * GraphRewriting, GraphFlatten and GraphCommonFactor (GraphRulePasses.h)
 * are the passes built on this; --passes-on-graph selects them over the
 * rebuilding Rewriting, Flatten and CommonFactor.
 */

#ifndef GRAPHRULEPASS_H_
#define GRAPHRULEPASS_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/MutableGraph.h"
#include <string>

namespace stp
{

class GraphRulePass : public NodeRewriter
{
protected:
  STPMgr* stpMgr;
  // What the rules build through: the graph's factory, set for each run.
  NodeFactory* nf = NULL;
  MutableGraph* g = NULL;
  // STP_CHECK_GRAPH in the environment: recount the graph after every
  // edit, as RemoveUnconstrained does. For the fuzzers; O(formula) per
  // edit.
  const bool checkGraph;
  unsigned fired = 0;

  // Exactly one place reads n now: the rule's own node, so n dies with it.
  bool unshared(const ASTNode& n) const { return g->parentCount(n) <= 1; }
  // In the formula as it stands, as opposed to built by a rule and not
  // yet attached.
  bool inFormula(const ASTNode& n) const
  {
    return g->isRootNode(n) || g->parentCount(n) > 0;
  }
  ASTNode rebuild(const ASTNode& n, const ASTVec& kids);

  // The pass's rules over one node, reading its children, grandchildren
  // and the graph's parent counts, building through nf. Returns the node
  // itself when nothing fires. Nothing here descends.
  virtual ASTNode applyRules(const ASTNode& c) = 0;
  // Whether a change in this node's parent count can let a rule fire on
  // its parent: the kinds the guards are on. Filters the count-change
  // events before any graph query, which is most of a drain's cost.
  virtual bool caresAbout(Kind k)
  {
    (void)k;
    return true;
  }

  // The rules over a node a rule just built and over the fresh nodes
  // under it, as a rebuild would feed a rule's result back through its
  // walk. Nodes of the formula stop the descent: the sweep and the queue
  // cover them. `rulesHere` false runs them over the children only.
  ASTNode rewriteFresh(const ASTNode& n, bool rulesHere);
  // The rules over one node until none fires.
  ASTNode toFixpoint(const ASTNode& c);
  // The rules over a node of the formula; a result that differs replaces
  // it in the graph.
  void examine(const ASTNode& n);
  // Count-change events since the last drain: a node that now has one
  // parent, and had more before the edit, may let a rule fire on that
  // parent. A node that merely moved from the replaced node to its
  // replacement ends at one parent too, and that parent was just built
  // with the rules applied; the snapshot taken before the edit tells the
  // two apart.
  void drainCounts();
  ankerl::unordered_dense::map<uint64_t, size_t> countsBefore_;
  ankerl::unordered_dense::set<uint64_t> drained_; // one query per node per drain
  void snapshotCounts(const ASTNode& c);
  // Whether the sweep goes parents before children. Bottom-up suits rules
  // that read what their operands became (Rewriting, CommonFactor).
  // Flatten goes top-down: the top of a same-kind chain absorbs the whole
  // chain in one application, and the nodes it absorbed are out of the
  // formula by the time the sweep reaches them, where bottom-up would
  // build one intermediate node per level.
  virtual bool topDown() { return false; }
  // Import, sweep, export.
  ASTNode run(const ASTNode& n);
  // The sweep over a graph a previous pass left: no import, no export. The
  // three rule passes run back to back on one graph this way.
  void run(MutableGraph& graph);

  explicit GraphRulePass(STPMgr* stp_);

public:
  virtual ~GraphRulePass() {}
  // NodeRewriter: the rules over a queued node of the graph.
  virtual ASTNode rewrite(const ASTNode& attached) override;
};
}
#endif

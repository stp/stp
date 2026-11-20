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


#include "stp/Simplifier/GraphRulePass.h"
#include "stp/Util/DagWalk.h"
#include <algorithm>
#include <cstdlib>
#include <vector>

namespace stp
{
  GraphRulePass::GraphRulePass(STPMgr* stp_)
      : stpMgr(stp_), checkGraph(std::getenv("STP_CHECK_GRAPH") != NULL)
  {
  }

  ASTNode GraphRulePass::rebuild(const ASTNode& n, const ASTVec& kids)
  {
    if (n.GetIndexWidth() > 0)
      return nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                                 n.GetValueWidth(), kids);
    if (n.GetValueWidth() > 0)
      return nf->CreateTerm(n.GetKind(), n.GetValueWidth(), kids);
    return nf->CreateNode(n.GetKind(), kids);
  }

  ASTNode GraphRulePass::rewriteFresh(const ASTNode& n, bool rulesHere)
  {
    if (n.Degree() == 0 || inFormula(n))
      return n;
    ASTVec kids;
    kids.reserve(n.Degree());
    bool changed = false;
    for (const ASTNode& k : n)
    {
      const ASTNode r = rewriteFresh(k, true);
      changed |= (r != k);
      kids.push_back(r);
    }
    const ASTNode c = changed ? rebuild(n, kids) : n;
    return rulesHere ? toFixpoint(c) : c;
  }

  // The rules over c until none fires, each result's fresh children done
  // first. A rule's result can match a rule earlier in the list (the
  // cancellation of common addends leaves 0 = a + b, which the rule for
  // that shape takes further), so one application is not a fixpoint and
  // a second run of the pass would find work the first left. The rules
  // shrink what they rewrite, so this ends; the bound is a guard against
  // a cycle between two rules, which no rule set should have.
  ASTNode GraphRulePass::toFixpoint(const ASTNode& c)
  {
    ASTNode cur = c;
    for (unsigned round = 0; round < 64; round++)
    {
      const ASTNode r = applyRules(cur);
      if (r == cur)
        return cur;
      fired++;
      cur = rewriteFresh(r, false);
    }
    return cur;
  }

  ASTNode GraphRulePass::rewrite(const ASTNode& c)
  {
    return toFixpoint(c);
  }

  void GraphRulePass::examine(const ASTNode& given)
  {
    const ASTNode c = g->current(given);
    if (c.Degree() == 0 || !inFormula(c))
      return;
    const ASTNode r = rewrite(c);
    if (r == c)
      return;
    snapshotCounts(c);
    g->replace(c, r);
    if (checkGraph)
    {
      std::string why;
      if (!g->checkInvariant(&why))
        FatalError(("graph invariant broken after an edit: " + why).c_str());
    }
  }

  // The counts of the nodes an edit at c hands over to its replacement:
  // its children and grandchildren of the kinds the rules read.
  void GraphRulePass::snapshotCounts(const ASTNode& c)
  {
    auto take = [&](const ASTNode& x) {
      if (x.Degree() > 0 && caresAbout(x.GetKind()))
        countsBefore_.emplace(x.GetNodeNum(), g->parentCount(x));
    };
    for (const ASTNode& k : c)
    {
      take(k);
      for (const ASTNode& gk : k)
        take(gk);
    }
  }

  void GraphRulePass::drainCounts()
  {
    // Called after every node of the sweep, almost always with nothing to
    // do. The maps keep their bucket arrays at their high-water size, so
    // clearing one that is already empty would memset it every time.
    if (g->changes().empty() && countsBefore_.empty())
      return;
    std::vector<ASTNode> candidates;
    while (true)
    {
      if (!drained_.empty())
        drained_.clear();
      for (const MutableGraph::Change& ch : g->changes())
      {
        if (ch.what != MutableGraph::Change::CountChanged)
          continue;
        // The guards are on interior nodes of the kinds the pass reads; a
        // leaf's count decides nothing.
        if (ch.node.Degree() == 0 || !caresAbout(ch.node.GetKind()) ||
            !drained_.insert(ch.node.GetNodeNum()).second)
          continue;
        const ASTNode x = g->current(ch.node);
        if (x.Degree() == 0 || g->parentCount(x) != 1)
          continue;
        const auto before = countsBefore_.find(ch.node.GetNodeNum());
        if (before != countsBefore_.end() && before->second <= 1)
          continue; // held once before the edit as well: nothing new
        g->parents(x, candidates);
      }
      g->clearChanges();
      if (!countsBefore_.empty())
        countsBefore_.clear();
      if (candidates.empty())
        return;
      std::sort(candidates.begin(), candidates.end());
      candidates.erase(std::unique(candidates.begin(), candidates.end()),
                       candidates.end());
      const std::vector<ASTNode> batch(candidates);
      candidates.clear();
      for (const ASTNode& p : batch)
      {
        if (p.Degree() > MutableGraph::WIDE)
          wideLater_.push_back(p);
        else
          examine(p);
      }
    }
  }

  void GraphRulePass::examineWideLater()
  {
    while (!wideLater_.empty())
    {
      std::vector<ASTNode> batch;
      batch.swap(wideLater_);
      std::sort(batch.begin(), batch.end());
      batch.erase(std::unique(batch.begin(), batch.end()), batch.end());
      for (const ASTNode& p : batch)
      {
        examine(p);
        drainCounts();
      }
    }
  }

  void GraphRulePass::run(MutableGraph& graph)
  {
    fired = 0;
    // Every rule replaces a node by an equivalent one: a patched node's
    // domains stay as they are.
    MutableGraph::DomainRecompute recompute(graph, false);
    graph.clearChanges();
    NodeFactory* const before = nf;
    nf = &graph.factory();
    g = &graph;
    graph.installRewriter(this);

    // Every interior node of the current formula once, in node-number
    // order: a node outnumbers its children, so ascending is bottom-up.
    // The list is taken before any edit; what stands for a node now is
    // read as it is reached, and a node an edit took out of the formula
    // is skipped. By handle, since a copy carries its original's number.
    std::vector<ASTNode> order;
    {
      ASTNodeSet seen;
      walkPreOrder(graph.root(), [&](const ASTNode& x) {
        if (x.Degree() == 0 || !seen.insert(x).second)
          return false;
        order.push_back(x);
        return true;
      });
    }
    std::sort(order.begin(), order.end(),
              [](const ASTNode& a, const ASTNode& b) {
                return a.GetNodeNum() < b.GetNodeNum();
              });
    if (topDown())
      std::reverse(order.begin(), order.end());
    for (const ASTNode& x : order)
    {
      examine(x);
      drainCounts();
    }
    examineWideLater();

    graph.installRewriter(NULL);
    g = NULL;
    nf = before;
  }

  ASTNode GraphRulePass::run(const ASTNode& n)
  {
    fired = 0;
    if (n.Degree() == 0)
      return n;
    MutableGraph graph(*stpMgr);
    graph.import(n);
    run(graph);
    return graph.exportRoot();
  }
}

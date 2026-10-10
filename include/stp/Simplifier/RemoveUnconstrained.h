/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: February, 2011
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
 * RemoveUnconstrained.h
 *
 *  Unconstrained variable elination.
 */

#ifndef REMOVEUNCONSTRAINED_H_
#define REMOVEUNCONSTRAINED_H_
#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/AchievableImage.h"
#include "stp/Simplifier/MutableGraph.h"
#include "stp/Simplifier/Simplifier.h"
#include <unordered_map>

namespace stp
{

class RemoveUnconstrained
{
  STPMgr& bm;

  ASTNode freshLike(const ASTNode& like, const std::string& prefix);

  // The formula during topLevel_other(): edits are made on the graph, and
  // the rules read parents, children and counts from it. Handles are the
  // graph's: a node's children are read through kidsOf(), which follows
  // replacements. Terms that go back into the formula are built with gf,
  // the graph's factory; terms recorded as definitions are built with nf
  // over exported (hash-consed) operands.
  MutableGraph* g = NULL;
  NodeFactory* gf = NULL;

  // Symbols that must never be reported unconstrained, however few
  // occurrences they have: the array-equality procedure's anchors, the
  // UF and floating-point abstraction's proxies, symbols the caller knows
  // are constrained elsewhere. Installed for one topLevel() call.
  const std::set<ASTNode>* untouchable = NULL;

  // Symbols to examine. Fed by the graph's change log: a symbol whose
  // parent count changed is a candidate again.
  std::vector<ASTNode> worklist;
  void drain();

  // A collapse deferred because the predicate's other side held an
  // unconstrained symbol, keyed by that symbol: when its count changes
  // (it was eliminated, or gained a use), the deferred symbol is a
  // candidate again. Without this a symbol examined once is never
  // re-examined, and a second run of the pass finds work the first left.
  std::unordered_map<uint64_t, std::vector<ASTNode>> deferredOn;
  // Likewise a ground-path climb that stopped at a shared interior node,
  // keyed by that node: when its count changes (it lost a parent), the
  // symbol below it may climb further.
  std::unordered_map<uint64_t, std::vector<ASTNode>> blockedOn;

  // STP_RU_CHECK_GRAPH in the environment: recount the graph from scratch
  // after every edit. For the fuzzers; O(formula) per edit.
  const bool checkGraph;

  // A symbol with exactly one distinct parent, and not protected.
  bool unconstrained(const ASTNode& n);
  // Any node with exactly one distinct parent, and that parent.
  bool singleParent(const ASTNode& n, ASTNode& parent);
  // n's children as they are now.
  void kidsOf(const ASTNode& n, ASTVec& out);
  // The symbols under n.
  void variablesIn(const ASTNode& n, std::vector<ASTNode>& out);
  // node := a fresh symbol of its sort; returns the symbol.
  ASTNode replaceWithFresh(const ASTNode& node);
  // node := by in the formula.
  void splice(const ASTNode& node, const ASTNode& by);
  ASTNode exported(const ASTNode& n) { return g->exportNode(n); }

  ASTNode topLevel_other(const ASTNode& n, Simplifier* simplifier);

  bool tryGroundPathCollapse(const ASTNode& var);

  bool tryImageConstrainShared(const ASTNode& var, const ASTNode& sharedNode,
                               const GroundStep& step);

  // Membership constraints produced by tryImageConstrainShared during a
  // topLevel_other() run; conjoined onto the result before returning.
  ASTVec imageConstraints;
  // How many a run made, for the fuzzer: a result with one is not a
  // fixed point of the pass, since the next run sees the constraint as
  // formula and the variable it constrains as free (category A in
  // bench-hard/reports/2026-10-10-removeunconstrained-idempotence.md).
  size_t imageConstraintsMade = 0;

  // The untouchable set installed for the current topLevel() call, so
  // that tryImageConstrainShared can add its fresh variables to it: their
  // membership constraint is outside the mutable tree, which would
  // otherwise count them as unconstrained. NULL outside a call, and
  // when the image rewrite is off.
  std::set<ASTNode>* passUntouchable = NULL;

  void replace(const ASTNode& from, const ASTNode to);

  NodeFactory* nf;

  // Set for the duration of a topLevel() call; the substitution map that
  // replace() writes definitions into.
  Simplifier* simplifier;

  // Definitions the substitution map refused to record. Every rule
  // rewrites the graph before replace() is called, so a refusal cannot
  // be undone; topLevel() conjoins these back onto the result instead,
  // which is exactly what the refused substitution would have meant.
  // The untouchable set installed in topLevel() should keep this
  // empty -- it is the repair for anything that slips past it, not the
  // primary mechanism.
  ASTVec refusedDefinitions;

  // Whether the array rules may fire in this pass; set per topLevel()
  // call. They are off once the array-equality procedure owns the
  // formula, because by then every array term worth rewriting sits under
  // a witness read whose shape ExtensionalityContext must be able to
  // recover -- and the frozen-symbol set cannot express that, since it
  // protects the anchors' own symbols rather than the arrays beneath
  // them. Running before the lowering pass is what gives the rules
  // something to do; see TopLevelSTPAux.
  bool arrayRules;

public:
  size_t imageConstraintCount() const { return imageConstraintsMade; }
  RemoveUnconstrained(STPMgr& bm);
	
  RemoveUnconstrained(RemoveUnconstrained const&) = delete;
  RemoveUnconstrained& operator=(RemoveUnconstrained const&) = delete;

  // `alsoUntouchable` extends the protected set for this pass: symbols a
  // caller knows are constrained elsewhere (another assertion-stack
  // level, an already-encoded conjunct) even though this formula alone
  // mentions them once. Merged with the extensionality frozen set when
  // both apply.
  ASTNode topLevel(const ASTNode& n, Simplifier* s,
                   const std::set<ASTNode>* alsoUntouchable = NULL);
};
}

#endif /* REMOVEUNCONSTRAINED_H_ */

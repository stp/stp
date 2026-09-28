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
#include "stp/AST/MutableASTNode.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"

namespace stp
{

class RemoveUnconstrained
{
  STPMgr& bm;

  ASTNode replaceParentWithFresh(MutableASTNode& mute,
                                 vector<MutableASTNode*>& variables);

  ASTNode topLevel_other(const ASTNode& n, Simplifier* simplifier);

  bool tryGroundPathCollapse(MutableASTNode& muteNode,
                             vector<MutableASTNode*>& variables);

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

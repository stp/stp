/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: May, 2011
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

#ifndef ALWAYSTRUE_H_
#define ALWAYSTRUE_H_

// Applies the AlwaysTrueSet to the input node.

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include <map>

namespace stp
{

class AlwaysTrue // not copyable
{
  Simplifier* simplifier;
  STPMgr* stpMgr;
  NodeFactory* nf;

  enum State
  {
    AND_STATE,
    NOT_STATE,
    BOTTOM_STATE
  };

public:
  AlwaysTrue(Simplifier* simplifier_, STPMgr* stp_, NodeFactory* nf_)
  {
    simplifier = simplifier_;
    stpMgr = stp_;
    nf = nf_;
  }

  ASTNode topLevel(ASTNode& n)
  {
    stpMgr->GetRunTimes()->start(RunTimes::AlwaysTrue);
    ASTNodeMap fromTo;
    ASTNode result = visit(n, AND_STATE, fromTo);
    stpMgr->GetRunTimes()->stop(RunTimes::AlwaysTrue);
    return result;
  }

  // Replace nodes that aren't conjoined to the top with TRUE/FALSE,
  // if that node is conjoined..
  // The "state" tracks whether we are still at nodes that are conjoined to the
  // top,
  // only after we get out of the top part can we replace nodes that we know to
  // be
  // true or false.
  ASTNode visit(const ASTNode& n, State state, ASTNodeMap& fromTo)
  {
    if (n.isConstant())
      return n;

    if (fromTo.find(n) != fromTo.end())
    {
      // It has been visited as BOTTOM_STATE once before.
      return fromTo.find(n)->second;
    }

    ASTVec newChildren;
    newChildren.reserve(n.Degree());
    State new_state;

    if (state == BOTTOM_STATE)
    {
      bool result;
      if (simplifier->CheckAlwaysTrueFormSet(n, result))
      {
        cerr << "+";
        if (result)
          return stpMgr->ASTTrue;
        else
          return stpMgr->ASTFalse;
      }
    }

    if (n.GetKind() == SYMBOL)
      return n;

    if (n.GetKind() != AND && state == AND_STATE)
    {
      if (n.GetKind() == NOT)
        new_state = NOT_STATE;
      else
        new_state = BOTTOM_STATE;
    }
    else if (state == NOT_STATE)
      new_state = BOTTOM_STATE;
    else
      new_state = state;

    for (size_t i = 0; i < n.Degree(); i++)
    {
      newChildren.push_back(visit(n[i], new_state, fromTo));
    }

    ASTNode result = n;
    if (newChildren != n.GetChildren())
    {
      if (n.GetType() == BOOLEAN_TYPE)
        result = nf->CreateNode(n.GetKind(), newChildren);
      else
        result = nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                                     n.GetValueWidth(), newChildren);
    }

    if (state == BOTTOM_STATE)
    {
      fromTo.insert(make_pair(n, result));
    }
    return result;
  }
};
}

#endif

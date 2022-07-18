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

/* 

If a node is asserted at the top level, this finds other references (if any) to 
that node, and replaces those reference by true/false.

The "state" tracks whether we are still at nodes that are conjoined to the
top, only after we get out of the top part can we replace nodes that we know to
be true or false.

NB: This flattens ANDs at the top level. Which makes implementation much easier.

*/
#ifndef ALWAYSTRUE_H_
#define ALWAYSTRUE_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include <map>

namespace stp
{
using std::make_pair;

class AlwaysTrue
{
  STPMgr* stpMgr;
  NodeFactory* nf;
  unsigned replaced;
  ASTNodeMap fromTo;

  ASTNode visit(const ASTNode& n, const bool match)
  {
    if (match &&  fromTo.find(n) != fromTo.end())
    {
      if (fromTo[n] == stpMgr->ASTTrue || fromTo[n] == stpMgr->ASTFalse)
          replaced++;
      return fromTo.find(n)->second;
    }

    if (n.GetKind() == SYMBOL || n.isConstant())
      return n;

    ASTVec newChildren;
    newChildren.reserve(n.Degree());
    for (auto& c: n)
    {
      newChildren.push_back(visit(c, true));
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

    fromTo.insert(make_pair(n, result));
    return result;
  }

  void visit(ASTVec& children)
  {
    // if we sort them then we know we'll see an asserted node before any node that it's a descendant of.
    SortByExprNum(children);

    for (auto& c: children)
    {
      // should have been flattened.
      assert(c.GetKind() != AND); 
      fromTo[c] = stpMgr->ASTTrue;

      if (c.GetKind() == NOT)
      {
         fromTo[c[0]] = stpMgr->ASTFalse;
         c = nf->CreateNode(NOT, visit(c[0], false));
      }
      else
        c = visit(c,false);
    }
  }

public:

  AlwaysTrue(STPMgr* stp_, NodeFactory* nf_)
  {
    stpMgr = stp_;
    nf = nf_;
  }

  AlwaysTrue( const AlwaysTrue& ) = delete;
  AlwaysTrue& operator=( const AlwaysTrue& ) = delete;

  ASTNode topLevel(const ASTNode& n)
  {
    stpMgr->GetRunTimes()->start(RunTimes::AlwaysTrue);
    replaced = 0;

    ASTNode result =n;
    if (n.GetKind() == AND)
    {
      ASTVec children = FlattenKind(AND, n.GetChildren());
      visit(children);
      result = nf->CreateNode(AND, children);
    }

    if (stpMgr->UserFlags.stats_flag)
        std::cerr << "{AlwaysTrue} replaced:" << replaced <<std::endl;
    stpMgr->GetRunTimes()->stop(RunTimes::AlwaysTrue);
    fromTo.clear();
    return result;
  }
};
}

#endif

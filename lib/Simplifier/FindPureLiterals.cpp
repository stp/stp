// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: 09/02/2011
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
 * This could very nicely run after unconstrained variable elmination. If we
 *traversed from
 * the root node, we could stop traversing whenever we met a node that wasn't an
 *AND or OR, then
 * we'd just check the number of parents of each boolean symbol that we found.
 *
 * I'm not sure that I've gotten all the polarities sorted.
 */

#include "stp/Simplifier/FindPureLiterals.h"

namespace stp
{

  int FindPureLiterals::swap(polarity_type polarity)
  {
    if (polarity == truePolarity)
      return falsePolarity;

    if (polarity == falsePolarity)
      return truePolarity;

    if (polarity == bothPolarity)
      return bothPolarity;

    throw "SADFSA2332";
  }



  // Build the polarities, then iterate through fixing them.
  bool FindPureLiterals::topLevel(ASTNode& n, Simplifier* simplifier, STPMgr* stpMgr)
  {
    stpMgr->GetRunTimes()->start(RunTimes::PureLiterals);

    build(n, truePolarity);
    bool changed = false;

    map<ASTNode, polarity_type>::const_iterator it = nodeToPolarity.begin();
    while (it != nodeToPolarity.end())
    {
      const ASTNode& n = it->first;
      const polarity_type polarity = it->second;
      if (n.GetType() == BOOLEAN_TYPE && n.GetKind() == SYMBOL &&
          polarity != bothPolarity)
      {
        if (polarity == truePolarity)
          simplifier->UpdateSubstitutionMap(n, n.GetSTPMgr()->ASTTrue);
        else
        {
          assert(polarity == falsePolarity);
          simplifier->UpdateSubstitutionMap(n, n.GetSTPMgr()->ASTFalse);
        }
        changed = true;
      }
      it++;
    }
    stpMgr->GetRunTimes()->stop(RunTimes::PureLiterals);
    return changed;
  }

  void FindPureLiterals::build(const ASTNode& n, polarity_type polarity)
  {
    if (n.isConstant())
      return;

    map<ASTNode, polarity_type>::iterator it = nodeToPolarity.find(n);
    if (it != nodeToPolarity.end())
    {
      int lookupPolarity = it->second;
      if ((polarity | lookupPolarity) == lookupPolarity)
        return; // already traversed.

      it->second |= polarity;
    }
    else
    {
      nodeToPolarity.insert(std::make_pair(n, polarity));
    }
    const Kind k = n.GetKind();
    switch (k)
    {
      case AND:
      case OR:
        for (size_t i = 0; i < n.Degree(); i++)
          build(n[i], polarity);
        break;

      case NOT:
        polarity = swap(polarity);
        build(n[0], polarity);
        break;

      default:
        polarity = bothPolarity; // both
        for (size_t i = 0; i < n.Degree(); i++)
          build(n[i], polarity);
        break;
    }
  }
}


/*
 * FindPureLiterals.h
 *
 *  Created on: 09/02/2011
 *      Author: thansen
 */

/*
 * This could very nicely run after unconstrained variable elmination. If we traversed from
 * the root node, we could stop traversing whenever we met a node that wasn't an AND or OR, then
 * we'd just check the number of parents of each boolean symbol that we found.
 *
 * I'm not sure that I've gotten all the polarities sorted.
 */


#ifndef FINDPURELITERALS_H_
#define FINDPURELITERALS_H_

#include <map>
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../simplifier/simplifier.h"

namespace BEEV
{

class FindPureLiterals
{
  const static int truePolarity = 1;
  const static int falsePolarity = 2;
  const static int bothPolarity = 3;

  map<ASTNode, int> nodeToPolarity;

  int swap(int polarity)
  {
    if (polarity == truePolarity)
      return falsePolarity;

    if (polarity == falsePolarity)
      return truePolarity;

    if (polarity == bothPolarity)
      return bothPolarity;

    throw "SADFSA2332";
  }

public:
  FindPureLiterals()
  {}
  virtual
  ~FindPureLiterals()
  {}

  // Build the polarities, then iterate through fixing them.
  bool topLevel(ASTNode& n, Simplifier *simplifier, STPMgr *stp)
  {
    stp->GetRunTimes()->start(RunTimes::PureLiterals);

    build(n , truePolarity);
    bool changed;

    map<ASTNode, int>::const_iterator it = nodeToPolarity.begin();
    while (it != nodeToPolarity.end())
      {
        const ASTNode& n = it->first;
        const int polarity = it->second;
        if (n.GetType() == BOOLEAN_TYPE && n.GetKind() == SYMBOL && polarity != bothPolarity)
          {
            //cerr << "--> Pure Literal" << n.GetName() << " " << polarity << endl;
            if (polarity == truePolarity)
              simplifier->UpdateSubstitutionMap(n,n.GetSTPMgr()->ASTTrue);
            if (polarity == falsePolarity)
              simplifier->UpdateSubstitutionMap(n,n.GetSTPMgr()->ASTFalse);
            changed = true;
          }
        it++;
      }
    stp->GetRunTimes()->stop(RunTimes::PureLiterals);
    return changed;
  }


  void build(const ASTNode& n , int polarity)
  {
    if (n.isConstant())
      return;

    map<ASTNode, int>::const_iterator it = nodeToPolarity.find(n);
    if (it != nodeToPolarity.end())
      {
        int lookupPolarity = it->second;
        if (polarity & lookupPolarity !=0 )
          return; // already traversed.
        lookupPolarity |= polarity;
        nodeToPolarity.insert(make_pair(n,lookupPolarity));
      }
    else
      {
        nodeToPolarity.insert(make_pair(n,polarity));
      }
    const Kind k = n.GetKind();
    switch (k)
    {
    case AND:
    case OR:
      for (int i =0; i < n.Degree(); i ++)
        build(n[i],polarity);
      break;

    case NOT:
         polarity = swap(polarity);
         build(n[0],polarity);
      break;

    default:
        polarity = bothPolarity; // both
        for (int i =0; i < n.Degree(); i ++)
          build(n[i],polarity);
      break;
    }
  }


};
};
#endif /* FINDPURELITERALS_H_ */

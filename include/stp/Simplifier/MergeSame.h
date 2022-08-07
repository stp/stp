/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2022
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

Factors to merge nodes.

e.g. (or A B ) AND (or A C)

will turn into

(or A (AND B C))

NB: Flattens ANDS conjoined to the top.

*/


#ifndef MERGESAME_H_
#define MERGESAME_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include <map>

namespace stp
{
using std::make_pair;

class MergeSame
{
  STPMgr* stpMgr;
  NodeFactory* nf;
  unsigned replaced = 0;

 void merge(ASTVec& conjuncts, const unsigned firstIndex, const unsigned secondIndex)
 {
    const auto& first = conjuncts[firstIndex];
    const auto& second = conjuncts[secondIndex];
    
    assert (second.GetKind() == OR && second.Degree() == 2);

    if (first.GetKind() == OR && first.Degree() == 2)
    {
      ASTNode newN;

      if (first[0] == second[0])
        newN = nf->CreateNode(OR, first[0], nf->CreateNode(AND, first[1], second[1]));
      else if (first[1] == second[0])
        newN = nf->CreateNode(OR, first[1], nf->CreateNode(AND, first[0], second[1]));
      else if (first[1] == second[1])
        newN = nf->CreateNode(OR, first[1], nf->CreateNode(AND, first[0], second[0]));
      else if (first[0] == second[1])
        newN = nf->CreateNode(OR, first[0], nf->CreateNode(AND, first[1], second[0]));
      else 
        return;

      replaced++;
      conjuncts[firstIndex] = newN;
      conjuncts[secondIndex] = stpMgr->ASTTrue;
    }  
 }

public:

  MergeSame (STPMgr* stp_, NodeFactory* nf_)
  {
    stpMgr = stp_;
    nf = nf_;
  }

  MergeSame( const MergeSame& ) = delete;
  MergeSame& operator=( const MergeSame& ) = delete;

  ASTNode topLevel(const ASTNode& n)
  {
    stpMgr->GetRunTimes()->start(RunTimes::MergeSame);
    replaced = 0;


    // Node number to index in the children vector.
    std::unordered_map<int,int> seen;

    ASTNode result =n;
    if (n.GetKind() == AND)
    {
        ASTVec conjuncts = FlattenKind(AND, n.GetChildren());
        for (unsigned i = 0; i < conjuncts.size(); i++)
        {
          auto& c = conjuncts[i];


          // Convert AND to OR.
          if (
            c.GetKind() == NOT
            && c[0].GetKind() == AND
           )
          {
            ASTVec children;
            for (const auto& child : c[0].GetChildren())
              children.push_back(nf->CreateNode(NOT, child));
            c = nf->CreateNode(OR, children);
            replaced++;
          }


          // (AND (OR a b) .... (OR a c )) => (OR a (AND b c))
          if (c.GetKind() == OR && c.Degree() == 2)
          {
              if (seen.find(c[0].GetNodeNum()) != seen.end())
                  merge(conjuncts, seen[c[0].GetNodeNum()] , i);
              else if (seen.find(c[1].GetNodeNum()) != seen.end())
                  merge(conjuncts, seen[c[1].GetNodeNum()] , i);
              else
              {
                  seen[c[0].GetNodeNum()] = i;
                  seen[c[1].GetNodeNum()] = i;
              }
          }

          // (AND (OR -a -b) .... (OR a b )) => (XOR a b ))
          if (c.GetKind() == OR && c.Degree() == 2)
          {
            const auto not0 = nf->CreateNode(NOT, c[0]);
            const auto not1 = nf->CreateNode(NOT, c[1]);

            if (seen.find(not0.GetNodeNum()) != seen.end() && seen.find(not1.GetNodeNum()) != seen.end())
            {
              const auto i0 = seen[not0.GetNodeNum()];
              const auto i1 = seen[not1.GetNodeNum()];
              if (
                i0 == i1 
                && conjuncts[i0].GetKind() == OR 
                && conjuncts[i0].Degree() == 2 
                && conjuncts[i0][0] == not0
                && conjuncts[i0][1] == not1
                && i0 != i
                && not0 != not1
                )
              {
                conjuncts[i0] = nf->CreateNode(XOR, c[0], c[1]);
                conjuncts[i] = stpMgr->ASTTrue;
                replaced++;
              }
            }
          }
        }

      if (replaced != 0)
        result = nf->CreateNode(AND, conjuncts);
    }

    if (stpMgr->UserFlags.stats_flag)
          std::cerr << "{MergeSame} replaced:" << replaced <<std::endl;
    stpMgr->GetRunTimes()->stop(RunTimes::MergeSame);
    return result;
  }

};
}

#endif

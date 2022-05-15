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
 Sharing aware flattening. 

* For example, given something like ((x + y ) + z) if this is the only occurence of (x+y) anywhere, then transform it into (x + y + z)
* Given ((x+ g) + (x+g)) it shouldn't do anything, even if this is the only reference to (x+g).
* This isn't idempotent. Node creation time simplifications might prune nodes, reducing their count and making extra nodes eligible for flattening.
*/

#ifndef FLATTEN_H_
#define FLATTEN_H_


#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include <map>

namespace stp
{

class Flatten // not copyable
{
  STPMgr* stpMgr;
  NodeFactory* nf;

  std::unordered_map<ASTNode, int, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> counter;
  ASTNodeMap fromTo;

public:
  Flatten(STPMgr* stp_, NodeFactory* nf_)
  {
    stpMgr = stp_;
    nf = nf_;
  }

  ASTNode topLevel(ASTNode& n)
  {
    stpMgr->GetRunTimes()->start(RunTimes::Flatten);
    
    //unsigned initial = stpMgr->NodeSize(n);

    counter.clear();
    fromTo.clear();

    occurences(n);
    ASTNode result = flatten(n);
    

    // I suspect this can't be enabled in general (during debugging) because sometimes the simplifyingNode factor will create more nodes.
    /*
    if (initial < stpMgr->NodeSize(result))
    {
      std::cerr << initial << " "<<  stpMgr->NodeSize(result) << std::endl;
      std::cerr << n;
      std::cerr << result;
      assert(false);
    }
    */

    stpMgr->GetRunTimes()->stop(RunTimes::Flatten);
    return result;
  }

private:

  // counter is 1 if the node has one reference in the tree.
  void occurences(const ASTNode& n)
  {
    if (n.Degree() == 0)
      return;

    if (counter[n]++ > 1)
      return;
  
    std::unordered_set<unsigned> visited;
    
    for (const auto& c: n.GetChildren())
    {
      if (visited.find(c.GetNodeNum()) == visited.end() ) // Don't visit children multiple times.
        {
          visited.insert(c.GetNodeNum());
          occurences(c);
        }
    }
  }

  ASTNode flatten(const ASTNode& n)
  {
    if (n.Degree() == 0)
      return n;

    if (fromTo.find(n) != fromTo.end())
      return fromTo[n];

    const Kind k = n.GetKind();

    bool changed =false;

    ASTVec newChildren;
    newChildren.reserve(n.Degree());

    ASTVec next;

    const bool flattenable = (OR==k || AND==k || XOR==k || BVXOR==k ||  BVOR==k || BVAND==k || BVPLUS==k || BVMULT == k);

    for (const auto& c: n.GetChildren())
    {
      if (flattenable   && (c.GetKind() == k && counter[c] == 1))
      {
         assert(c.Degree() > 1);
         changed=true;
         next.insert(next.end(), c.GetChildren().begin(), c.GetChildren().end());
      }
      else
      {
        const auto& r = flatten(c);
        if (r!=c)
          changed = true;
        newChildren.push_back(r);
      }
    }    

    //std::cerr << "sdef" << n.Degree() << " " << newChildren.size() << " " << next.size() << std::endl;

    for (size_t i = 0; i < next.size(); i++)
    {
      assert(changed);

      if (flattenable && (next[i].GetKind() == k && counter[next[i]] == 1))
      {
         next.insert(next.end(), next[i].GetChildren().begin(), next[i].GetChildren().end());
      }
      else
      {
        const auto& r = flatten(next[i]);
        if (r!=next[i])
          changed = true;
        newChildren.push_back(r);
      }
    }

    if (next.size() > 0)
    {
      assert(newChildren.size() > n.Degree());
    }

    if (changed)
    {
      ASTNode result;
      if (n.GetType() == BOOLEAN_TYPE)
        result = nf->CreateNode(n.GetKind(), newChildren);
      else
        result = nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),n.GetValueWidth(), newChildren);

      fromTo.insert({n,result});
      counter[result]++; // I'm guessing it's unusal, but we might make a node we already have.
      
      return result;
    }

    fromTo.insert({n,n});
    return n;
  }
};
}

#endif

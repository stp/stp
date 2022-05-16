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

#include "stp/Simplifier/Flatten.h"
#include <list>

namespace stp
{

  ASTNode Flatten::topLevel(ASTNode& n)
  {
    stpMgr->GetRunTimes()->start(RunTimes::Flatten);
    
    shareCount.clear();
    fromTo.clear();
    removed=0;

    buildShareCount(n);
    ASTNode result = flatten(n);
    
    if (stpMgr->UserFlags.stats_flag)
    {
      std::cerr << "{Flatten} Nodes Removed:" << removed << std::endl;
    }

    stpMgr->GetRunTimes()->stop(RunTimes::Flatten);
    return result;
  }

  // counter is 1 if the node has one reference in the tree.
  void Flatten::buildShareCount(const ASTNode& n)
  {
    if (n.Degree() == 0)
      return;

    if (shareCount[n.GetNodeNum()]++ > 0) // 0 first time, 1 second time.
      return;
  
    for (const auto& c: n.GetChildren())
        buildShareCount(c);
  }

  ASTNode Flatten::flatten(const ASTNode& n)
  {
    if (n.Degree() == 0)
      return n;

    if (fromTo.find(n.GetNodeNum()) != fromTo.end())
      return fromTo[n.GetNodeNum()];

    const Kind k = n.GetKind();

    ASTNode result =n;

    bool changed =false;
    
    //TODO STP doesn't currerntly handle >2 arity BVMULT.
    const bool flattenable = (OR==k || AND==k || XOR==k || BVXOR==k ||  BVOR==k || BVAND==k || BVPLUS==k);

    ASTVec newChildren;

    const ASTVec& children = n.GetChildren();
    auto it0 = children.begin();

    ASTVec nextChildren;
    auto i = 0;

    // Copy on write.
    auto fill = [&]
    {
      assert(0 ==i);

      newChildren.reserve(children.size());
      newChildren.insert(newChildren.end(), children.begin(), it0-1);
      changed=true;
    };

    while (it0 != children.end() || i < nextChildren.size())
    {
      const ASTNode& c = (it0 != children.end())? *it0++: nextChildren[i++];

      if (flattenable && c.GetKind() == k && shareCount[c.GetNodeNum()] == 1)
      {
         assert(c.Degree() > 1);
         if (!changed)
            fill();

         removed++;

         for (const auto&e: c.GetChildren())
            nextChildren.push_back(e);
      }
      else
      {
        const auto r = flatten(c);
        if (r!=c && !changed)
          fill();
        if (changed)   
          newChildren.push_back(r);
      }
    }    

    if (changed)
    {
      assert(n.Degree() <= newChildren.size());

      if (n.GetType() == BOOLEAN_TYPE)
        result = nf->CreateNode(k, newChildren);
      else
        result = nf->CreateArrayTerm(k, n.GetIndexWidth(),n.GetValueWidth(), newChildren);

      shareCount[result.GetNodeNum()]++; // I'm guessing it's unusal, but we might make a node we already have.
    }

    if (shareCount[n.GetNodeNum()] > 1)
      fromTo.insert({n.GetNodeNum(),result});
    return result;
  }
}

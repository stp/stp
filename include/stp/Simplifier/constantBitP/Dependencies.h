// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2010
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

#ifndef DEPENDENCIES_H_
#define DEPENDENCIES_H_

#include "stp/AST/AST.h"
namespace simplifier
{
namespace constantBitP
{

using std::set;
using std::cout;
using std::endl;

// From a child, get the parents of that node.
class Dependencies
{
private:
  typedef std::unordered_map<stp::ASTNode, set<stp::ASTNode>*,
                   stp::ASTNode::ASTNodeHasher,
                   stp::ASTNode::ASTNodeEqual> NodeToDependentNodeMap;
  NodeToDependentNodeMap dependents;

  const set<ASTNode> empty;

public:
  // All the nodes that depend on the value of a particular node.
  void build(const ASTNode& current, const ASTNode& prior)
  {
    if (current.isConstant()) // don't care about what depends on constants.
      return;

    set<ASTNode>* vec;
    const NodeToDependentNodeMap::iterator it = dependents.find(current);
    if (dependents.end() == it)
    {
      // add it in with a reference to the vector.
      vec = new set<ASTNode>();

      dependents.insert(std::pair<ASTNode, set<ASTNode>*>(current, vec));
    }
    else
    {
      vec = it->second;
    }

    if (prior != current) // initially called with both the same.
    {
      if (vec->count(prior) == 0)
        vec->insert(prior);
      else
        return; // already been added in.
    }

    for (unsigned int i = 0; i < current.GetChildren().size(); i++)
    {
      build(current.GetChildren()[i], current);
    }
  }

  Dependencies(const Dependencies&); // Shouldn't needed to copy or assign.
  Dependencies& operator=(const Dependencies&);

public:
  Dependencies(const ASTNode& top)
  {
    build(top, top);
    checkInvariant();
  }

  ~Dependencies()
  {
    NodeToDependentNodeMap::iterator it = dependents.begin();
    for (/**/; it != dependents.end(); it++)
    {
      // set<stp::ASTNode>*
      delete it->second;
    }
  }

  void replaceFresh(const ASTNode& old, const ASTNode& newN,
                    set<ASTNode>* newNDepends, ASTVec& variables)
  {
    NodeToDependentNodeMap::const_iterator it = dependents.find(old);
    if (it == dependents.end())
      return;

    it->second->erase(old);
    dependents.insert(make_pair(newN, newNDepends));
    variables.push_back(newN);
  }

  // The "toRemove" node is being removed. Used by unconstrained elimination.
  void removeNode(const ASTNode& toRemove, ASTVec& variables)
  {
    for (unsigned i = 0; i < toRemove.GetChildren().size(); i++)
    {
      const ASTNode child = toRemove.GetChildren()[i];

      NodeToDependentNodeMap::const_iterator it = dependents.find(child);
      if (it == dependents.end())
        continue;

      it->second->erase(toRemove);
      if (it->second->size() == 0)
      {
        removeNode(child, variables);
        continue;
      }

      if (child.GetKind() == stp::SYMBOL && it->second->size() == 1)
      {
        variables.push_back(child);
      }
    }
  }

  void print() const
  {
    NodeToDependentNodeMap::const_iterator it = dependents.begin();
    for (/**/; it != dependents.end(); it++)
    {
      cout << (it->first).GetNodeNum();

      const set<ASTNode>* dep = it->second;

      set<ASTNode>::iterator it = dep->begin();
      while (it != dep->end())
      {
        cout << " " << (*it).GetNodeNum();
        it++;
      }
      cout << endl;
    }
  }

  void checkInvariant() const
  {
    // only one node with a single dependent.
  }

  const set<ASTNode>* getDependents(const ASTNode n) const
  {
    if (n.isConstant())
      return &empty;
    const NodeToDependentNodeMap::const_iterator it = dependents.find(n);
    if (it == dependents.end())
      return &empty;

    return it->second;
  }

  // The higher node depends on the lower node.
  // The value produces by the lower node is read by the higher node.
  bool nodeDependsOn(const ASTNode& higher, const ASTNode& lower) const
  {
    const set<ASTNode>* s = getDependents(lower);
    return s->count(higher) > 0;
  }

  bool isUnconstrained(const ASTNode& n)
  {
    if (n.GetKind() != stp::SYMBOL)
      return false;

    NodeToDependentNodeMap::const_iterator it = dependents.find(n);
    assert(it != dependents.end());
    return it->second->size() == 1;
  }

#if 0
      void
      getAllVariables(ASTVec& v)
      {
        for (NodeToDependentNodeMap::const_iterator it = dependents.begin(); it != dependents. end(); it++)
          {
            if (it->first.GetKind() == SYMBOL)
              v.push_back(it->first);
          }
      }
#endif
};
}
}

#endif /* DEPENDENCIES_H_ */

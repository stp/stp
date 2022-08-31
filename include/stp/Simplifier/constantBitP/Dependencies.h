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

using std::cout;
using std::endl;
using stp::ASTNodeSet;

// From a child, get the parents of that node.
class Dependencies
{
private:
  typedef std::unordered_map<uint64_t, ASTNodeSet*>  NodeToDependentNodeMap;
  NodeToDependentNodeMap dependents;

  const ASTNodeSet empty;

  bool checkInvariant() const
  {
    // TODO only one node with a single dependent.
    return true;
  }

  // All the nodes that depend on the value of a particular node.
  void build(const ASTNode& current, const ASTNode& prior)
  {
    if (current.isConstant()) // don't care about what depends on constants.
      return;

    ASTNodeSet* vec;
    const auto it = dependents.find(current.GetNodeNum());
    if (dependents.end() == it)
    {
      // add it in with a reference to the vector.
      vec = new ASTNodeSet();
      dependents.insert({current.GetNodeNum(), vec});
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

    for (const auto child: current)
    {
      build(child, current);
    }
  }

public:

  Dependencies(const Dependencies&) = delete;
  Dependencies& operator=(const Dependencies&) = delete;

  Dependencies(const ASTNode& top)
  {
    build(top, top);
    assert(checkInvariant());
  }

  ~Dependencies()
  {
    for (const auto it : dependents)
      delete it.second;
  }

  const ASTNodeSet* getDependents(const ASTNode& n) const
  {
    if (n.isConstant())
      return &empty;
    const auto it = dependents.find(n.GetNodeNum());
    if (it == dependents.end())
      return &empty;

    return it->second;
  }

  // The higher node depends on the lower node.
  // The value produces by the lower node is read by the higher node.
  bool nodeDependsOn(const ASTNode& higher, const ASTNode& lower) const
  {
    return getDependents(lower)->count(higher) > 0;
  }
};
}
}

#endif /* DEPENDENCIES_H_ */

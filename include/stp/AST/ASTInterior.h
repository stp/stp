/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
 *
 * BEGIN DATE: November, 2005
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

#ifndef ASTINTERIOR_H
#define ASTINTERIOR_H

#include "UsefulDefs.h"
#include "ASTInternalWithChildren.h"
#include "NodeFactory/HashingNodeFactory.h"

namespace stp
{
class ASTNode;
class STPMgr;
typedef vector<ASTNode> ASTVec;

/******************************************************************
 * Internal representation of an interior ASTNode.Generally, these*
 * nodes should have at least one child                           *
 ******************************************************************/
class ASTInterior : public ASTInternalWithChildren
{

  friend class STPMgr;
  friend class ASTNodeHasher;
  friend class ASTNodeEqual;
  friend stp::ASTNode
  HashingNodeFactory::CreateNode(const Kind kind,
                                 const stp::ASTVec& back_children);

private:
  /******************************************************************
   * Hasher for ASTInterior pointer nodes                           *
   ******************************************************************/
  class ASTInteriorHasher
  {
  public:
    size_t operator()(const ASTInterior* int_node_ptr) const;
  };

  /******************************************************************
   * Equality for ASTInterior nodes                                 *
   ******************************************************************/
  class ASTInteriorEqual
  {
  public:
    bool operator()(const ASTInterior* int_node_ptr1,
                    const ASTInterior* int_node_ptr2) const;
  };

  // Used in Equality class for hash tables
  friend bool operator==(const ASTInterior& int_node1,
                         const ASTInterior& int_node2)
  {
    return ((int_node1._kind == int_node2._kind) &&
            (int_node1._children == int_node2._children));
  }

  // Call this when deleting a node that has been stored in the
  // the unique table
  virtual void CleanUp();

  // Returns kinds.  "lispprinter" handles printing of parenthesis
  // and childnodes. (c_friendly is for printing hex. numbers that C
  // compilers will accept)
  virtual void nodeprint(ostream& os, bool c_friendly = false);

public:
  ASTInterior(STPMgr *mgr, Kind kind) : ASTInternalWithChildren(mgr, kind) {}
  ASTInterior(STPMgr *mgr, Kind kind, ASTVec& children)
      : ASTInternalWithChildren(mgr, kind, children)
  {
  }

  // This copies the contents of the child nodes
  // array, along with everything else. Assigning the smart pointer,
  // ASTNode, does NOT invoke this.
  ASTInterior(const ASTInterior& int_node) : ASTInternalWithChildren(int_node)
  {
  }

  virtual ~ASTInterior() {}
};

} // end of namespace stp
#endif

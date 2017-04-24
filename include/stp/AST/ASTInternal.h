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
#ifndef ASTINTERNAL_H
#define ASTINTERNAL_H

#include <iostream>
#include "stp/AST/ASTNode.h"
#include "stp/AST/UsefulDefs.h"

using std::ostream;

namespace stp
{
/******************************************************************
 * struct enumeration:                                            *
 *                                                                *
 * Templated class that allows you to define the number of bytes  *
 * (using class T below) for the enumerated type class E.         *
 ******************************************************************/
template <class E, class T> struct enumeration
{
  typedef T type;
  typedef E enum_type;

  enumeration() : e_(E()) {}

  enumeration(E e) : e_(static_cast<T>(e)) {}

  operator E() const { return static_cast<E>(e_); }

private:
  T e_;
};

/******************************************************************
 * Class ASTInternal:                                             *
 *                                                                *
 * Abstract base class for internal node representation. Requires *
 * Kind and ChildNodes so same traversal works on all nodes.      *
 ******************************************************************/
class ASTInternal
{
  friend class ASTNode;

protected:
  // Pointer back to the node manager that holds this.
  STPMgr * nodeManager;

  // node_uid is a unique positive integer for the node.  The node_uid
  // of a node should always be greater than its descendents (which
  // is easily achieved by incrementing the number each time a new
  // node is created). NOT nodes are odd, and one more than the thing
  // the are NOTs of.
  // 
  uint64_t node_uid;
  static uint64_t node_uid_cntr;

  // reference counting for garbage collection
  uint32_t _ref_count;

  /*******************************************************************
   * ASTNode is of type BV      <==> ((indexwidth=0)&&(valuewidth>0))*
   * ASTNode is of type ARRAY   <==> ((indexwidth>0)&&(valuewidth>0))*
   * ASTNode is of type BOOLEAN <==> ((indexwidth=0)&&(valuewidth=0))*
   *                                                                 *
   * Width of the index of an array. Positive for array, 0 otherwise *
   *******************************************************************/
  virtual void setIndexWidth(uint32_t) = 0;
  virtual uint32_t getIndexWidth() const = 0;
  
  virtual void setValueWidth(uint32_t) = 0;
  virtual uint32_t getValueWidth() const = 0;

  /*******************************************************************
   * ASTNode is of type BV      <==> ((indexwidth=0)&&(valuewidth>0))*
   * ASTNode is of type ARRAY   <==> ((indexwidth>0)&&(valuewidth>0))*
   * ASTNode is of type BOOLEAN <==> ((indexwidth=0)&&(valuewidth=0))*
   *                                                                 *
   * Number of bits of bitvector. +ve for array/bitvector,0 otherwise*
   *******************************************************************/

  // Kind. It's a type tag and the operator.
  enumeration<Kind, unsigned char> _kind;

  //Used just by ASTInterior, but storing it here saves 8-bytes in ASTInterior, sizeof this class is unchanged.
  mutable bool is_simplified;

  //Used just by ASTBVConst, but storing it here saves 8-bytes in ASTBVConst, sizeof this class is unchanged.
  bool cbv_managed_outside;

  mutable uint8_t iteration;

  /****************************************************************
   * Protected Member Functions                                   *
   ****************************************************************/

  // Copying assign operator.  Also copies contents of children.
  ASTInternal& operator=(const ASTInternal& int_node);

  // Cleanup function for removing from hash table
  virtual void CleanUp() = 0;

  virtual ~ASTInternal() {}

  // Abstract virtual print function for internal node. c_friendly
  // is for printing hex. numbers that C compilers will accept
  virtual void nodeprint(ostream& os, bool /*c_friendly*/) { os << "*"; };

  // Treat the result as const pleases
  virtual Kind GetKind() const { return _kind; }

  // Get the child nodes of this node
  virtual ASTVec const& GetChildren() const = 0;

public:
  // Constructor (kind only, empty children, int nodenum)
  ASTInternal(STPMgr* mgr, Kind kind)
      : nodeManager(mgr), node_uid(node_uid_cntr+=2),
         _ref_count(0), _kind(kind), iteration(0)
  {
  }

  // This copies the contents of the child nodes
  // array, along with everything else.  Assigning the smart pointer,
  // ASTNode, does NOT invoke this; This should only be used for
  // temporary hash keys before uniquefication.
  // FIXME:  I don't think children need to be copied.
  ASTInternal(const ASTInternal& int_node)
      : nodeManager(int_node.nodeManager), node_uid(int_node.node_uid),
         _ref_count(0), _kind(int_node._kind), iteration(0)

  {
  }

  // Increment Reference Count
  void IncRef() { ++_ref_count; }

  // Decrement Reference Count
  void DecRef()
  {
    if (--_ref_count == 0)
    {
      // Delete node from unique table and kill it.
      CleanUp();
    }
  }

  unsigned GetNodeNum() const { return node_uid; }

  virtual bool isSimplified() const { return false; }

  virtual void hasBeenSimplified() const
  {
    std::cerr << "astinternal has been";
  }
};
} // end of namespace
#endif

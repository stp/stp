// -*- c++ -*-
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
  /****************************************************************
   * Protected Data                                               *
   ****************************************************************/

  mutable uint8_t iteration;

  // reference counting for garbage collection
  unsigned int _ref_count;

  // Kind. It's a type tag and the operator.
  enumeration<Kind, unsigned char> _kind;

  // Nodenum is a unique positive integer for the node.  The nodenum
  // of a node should always be greater than its descendents (which
  // is easily achieved by incrementing the number each time a new
  // node is created).
  unsigned int _node_num;

  /*******************************************************************
   * ASTNode is of type BV      <==> ((indexwidth=0)&&(valuewidth>0))*
   * ASTNode is of type ARRAY   <==> ((indexwidth>0)&&(valuewidth>0))*
   * ASTNode is of type BOOLEAN <==> ((indexwidth=0)&&(valuewidth=0))*
   *                                                                 *
   * Width of the index of an array. Positive for array, 0 otherwise *
   *******************************************************************/
  unsigned int _index_width;

  /*******************************************************************
   * ASTNode is of type BV      <==> ((indexwidth=0)&&(valuewidth>0))*
   * ASTNode is of type ARRAY   <==> ((indexwidth>0)&&(valuewidth>0))*
   * ASTNode is of type BOOLEAN <==> ((indexwidth=0)&&(valuewidth=0))*
   *                                                                 *
   * Number of bits of bitvector. +ve for array/bitvector,0 otherwise*
   *******************************************************************/
  unsigned int _value_width;

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
  ASTInternal(Kind kind, int nodenum = 0)
      : iteration(0), _ref_count(0), _kind(kind), _node_num(nodenum),
        _index_width(0), _value_width(0)
  {
  }

  // This copies the contents of the child nodes
  // array, along with everything else.  Assigning the smart pointer,
  // ASTNode, does NOT invoke this; This should only be used for
  // temporary hash keys before uniquefication.
  // FIXME:  I don't think children need to be copied.
  ASTInternal(const ASTInternal& int_node)
      : iteration(0), _ref_count(0), _kind(int_node._kind),
        _node_num(int_node._node_num), _index_width(int_node._index_width),
        _value_width(int_node._value_width)
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

  unsigned GetNodeNum() const { return _node_num; }

  virtual bool isSimplified() const { return false; }

  virtual void hasBeenSimplified() const
  {
    std::cerr << "astinternal has been";
  }

  void SetNodeNum(int nn) { _node_num = nn; } 

}; 
} // end of namespace
#endif

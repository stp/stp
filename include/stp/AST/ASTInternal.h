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

// NB: deliberately do NOT include ASTNode.h here. ASTInternal only needs
// ASTVec and a forward declaration of ASTNode (both from UsefulDefs.h);
// including ASTNode.h would create a circular include that forces the hot
// ASTNode accessors (GetKind/GetNodeNum/...) to be defined out-of-line.
#include <atomic>
#include "stp/AST/UsefulDefs.h"
#include "stp/AST/SourceSort.h"
#include <iostream>

using std::ostream;

namespace stp
{
namespace lra {
class Frontend;
}
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
  friend class STPMgr; // the exposed-id table (STPMgr::exposeNode)
  friend class lra::Frontend;

protected:
  // Pointer back to the node manager that holds this.
  STPMgr* nodeManager;

  // node_uid is a unique positive integer for the node.  The node_uid
  // of a node should always be greater than its descendents (which
  // is easily achieved by incrementing the number each time a new
  // node is created). NOT nodes are odd, and one more than the thing
  // the are NOTs of.
  //
  uint64_t node_uid;
  // Process-wide and atomic: a manager may be used from any thread (one at
  // a time), so ids handed out on different threads must never collide.
  static std::atomic<uint64_t> node_uid_cntr;

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

  virtual void setExpWidth(uint32_t) = 0;
  virtual uint32_t getExpWidth() const = 0;

  virtual void setSigWidth(uint32_t) = 0;
  virtual uint32_t getSigWidth() const = 0;

  // Source-language identity carried by leaves. Interior-node sorts are
  // derived by ASTNode::GetSourceSort from their operator and children.
  virtual SourceSort getDeclaredSourceSort() const
  {
    return SourceSort::unknown();
  }

  // Memo for the *derived* source sort, on the nodes that derive one.
  //
  // ASTNode::GetSourceSort walks children for READ, WRITE and ITE -- and for
  // ITE it walks both branches -- so without a memo a shared-branch ITE DAG
  // costs Theta(2^depth) per query and a store chain costs Theta(depth), on a
  // graph of linear size. The front ends ask once per node they build, and
  // containsFloatingPointTheory asks once per node of every query, so the
  // recomputation is not incidental. This is the same treatment cacheFPFormat
  // already gives the floating-point format, for the same reason, and it is
  // sound for the same reason: the derivation reads only the node's kind,
  // children and widths.
  //
  // The pointer is into the manager's intern pool, so a cached answer costs
  // eight bytes and no allocation, and Unknown interns like any other sort --
  // a non-null pointer to an Unknown sort is the negative cache.
  //
  // Only ASTInterior can hold one. Leaves either carry a declared sort or
  // derive theirs from widths that legacy callers still set after
  // construction, and both are already O(1).
  virtual const SourceSort* cachedSourceSort() const { return NULL; }
  virtual void setCachedSourceSort(const SourceSort*) const {}

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
  mutable bool is_simplified : 1;

  //Used just by ASTBVConst, but storing it here saves 8-bytes in ASTBVConst, sizeof this class is unchanged.
  bool cbv_managed_outside : 1;

  // Whether the 3.x API handed out this node's id (STPMgr::exposeNode): its
  // last release then withdraws the id, so that handing one out never keeps
  // the node alive. These flags and the Real-syntax memo share one byte,
  // which keeps the class at 32 bytes.
  bool exposed : 1;

  // Whether this node or a descendant contains Real syntax. Unlike carrier
  // widths, the kinds, children and declared Real sorts are immutable. Both
  // answers can therefore live on the node, without a solver-lifetime map
  // retaining discarded scopes. Used by lra::Frontend::containsRealSyntax.
  mutable bool real_syntax_known : 1;
  mutable bool real_syntax_present : 1;
  // Set only by MutableInterior: the node belongs to a MutableGraph, is
  // keyed in that graph's table rather than the manager's, and may be
  // edited. The manager's table refuses a child with this bit.
  bool mutable_interior : 1;

  mutable uint8_t iteration;

  /****************************************************************
   * Protected Member Functions                                   *
   ****************************************************************/

  // Cleanup function for removing from hash table
  virtual void CleanUp() = 0;

  virtual ~ASTInternal() {}

  // Abstract virtual print function for internal node.
  virtual void nodeprint(ostream& os) { os << "*"; };

  // Treat the result as const pleases.
  // Non-virtual: no subclass overrides it, so this is just a field read.
  Kind GetKind() const { return _kind; }

  // Get the child nodes of this node
  virtual ASTChildren GetChildren() const = 0;

public:
  // Constructor (kind only, empty children, int nodenum)
  ASTInternal(STPMgr* mgr, Kind kind)
      : nodeManager(mgr), node_uid(node_uid_cntr.fetch_add(2, std::memory_order_relaxed) + 2),
        _ref_count(0),
        _kind(kind), exposed(false), real_syntax_known(false),
        real_syntax_present(false), mutable_interior(false), iteration(0)
  {
  }

  // This copies the contents of the child nodes
  // array, along with everything else.  Assigning the smart pointer,
  // ASTNode, does NOT invoke this; This should only be used for
  // temporary hash keys before uniquefication.
  // FIXME:  I don't think children need to be copied.
  ASTInternal(const ASTInternal& int_node)
      : nodeManager(int_node.nodeManager), node_uid(int_node.node_uid),
        _ref_count(0), _kind(int_node._kind), exposed(false),
        real_syntax_known(false), real_syntax_present(false), mutable_interior(false), iteration(0)

  {
  }

  // Increment Reference Count
  void IncRef() { ++_ref_count; }

  // Decrement Reference Count
  void DecRef()
  {
    if (--_ref_count == 0)
    {
      if (exposed)
        WithdrawExposedId();
      // Delete node from unique table and kill it.
      CleanUp();
    }
  }

  // Out of line: STPMgr is incomplete here.
  void WithdrawExposedId();

  uint64_t GetNodeNum() const { return node_uid; }

  virtual bool isSimplified() const { return false; }

  virtual void hasBeenSimplified() const
  {
    std::cerr << "astinternal has been";
  }
};
} // end of namespace
#endif

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

#include "ASTNode.h"
#include "ASTInternal.h"
#include "stp/NodeFactory/HashingNodeFactory.h"
#include "UsefulDefs.h"

namespace stp
{
class ASTNode;
class STPMgr;
typedef vector<ASTNode> ASTVec;

/******************************************************************
 * Internal representation of an interior ASTNode.Generally, these*
 * nodes should have at least one child                           *
 ******************************************************************/
class ASTInterior : public ASTInternal
{

  friend class STPMgr;
  friend class ASTNodeHasher;
  friend class ASTNodeEqual;
  friend stp::ASTNode
  HashingNodeFactory::CreateNode(const Kind kind,
                                 const stp::ASTVec& back_children);

  // The children are stored in a flexible array immediately after this
  // object -- node and children are one allocation, made by create(). This
  // is just the count; childrenPtr() locates the array.
  uint32_t _num_children;

  // Lazily computed by ASTInteriorHasher; 0 means not yet computed.
  // Stays valid because the kind and children never change once set up,
  // so the hash isn't recomputed on insertion or removal from the
  // unique table.
  mutable size_t _cached_hash = 0;

  uint32_t _value_width;
  uint32_t _index_width;

  // The children live immediately after the object in the same allocation.
  ASTNode* childrenPtr() { return reinterpret_cast<ASTNode*>(this + 1); }
  const ASTNode* childrenPtr() const
  {
    return reinterpret_cast<const ASTNode*>(this + 1);
  }

  // Nodes are variable-sized (they carry their children inline), so they are
  // only ever built by create(); ordinary new/delete would size them wrong.
  static void* operator new(std::size_t) = delete;

  // Sets the header fields only; create() placement-constructs the children
  // into the tail afterwards (and fixes up a NOT node's number).
  ASTInterior(STPMgr* mgr, Kind kind, uint32_t num_children)
      : ASTInternal(mgr, kind), _num_children(num_children), _value_width(0),
        _index_width(0)
  {
    is_simplified = false;
  }

public:
  // A non-owning search key for the unique table: lets us probe with a
  // (kind, borrowed children) pair without building a whole node. Enabled by
  // the transparent hasher/equality below.
  struct Probe
  {
    Kind kind;
    ASTChildren children;
  };

  // Build a node whose children are allocated inline with it, in one block.
  static ASTInterior* create(STPMgr* mgr, Kind kind, ASTChildren children);

  // Frees the single (over-sized) allocation. Paired with the raw
  // ::operator new done inside create().
  static void operator delete(void* p) { ::operator delete(p); }

  ASTInterior(const ASTInterior&) = delete;
  ASTInterior& operator=(const ASTInterior&) = delete;

  virtual ~ASTInterior();

  virtual ASTChildren GetChildren() const
  {
    return ASTChildren(childrenPtr(), _num_children);
  }

  bool isSimplified() const { return is_simplified; }

  void hasBeenSimplified() const { is_simplified = true; }

  /******************************************************************
   * Hasher for ASTInterior pointer nodes                           *
   ******************************************************************/
  class ASTInteriorHasher
  {
  public:
    using is_transparent = void; // enable heterogeneous (Probe) lookup
    size_t operator()(const ASTInterior* int_node_ptr) const;
    size_t operator()(const Probe& probe) const;
  };

  /******************************************************************
   * Equality for ASTInterior nodes                                 *
   ******************************************************************/
  class ASTInteriorEqual
  {
  public:
    using is_transparent = void;
    bool operator()(const ASTInterior* n1, const ASTInterior* n2) const
    {
      return *n1 == *n2;
    }
    bool operator()(const Probe& probe, const ASTInterior* n) const
    {
      return probe.kind == n->GetKind() && probe.children == n->GetChildren();
    }
    bool operator()(const ASTInterior* n, const Probe& probe) const
    {
      return operator()(probe, n);
    }
  };

  // Used in Equality class for hash tables
  friend bool operator==(const ASTInterior& int_node1,
                         const ASTInterior& int_node2)
  {
    return int_node1.GetKind() == int_node2.GetKind() &&
           int_node1.GetChildren() == int_node2.GetChildren();
  }

private:
  // Call this when deleting a node that has been stored in the
  // the unique table
  virtual void CleanUp();

  // Returns kinds.  "lispprinter" handles printing of parenthesis
  // and childnodes. (c_friendly is for printing hex. numbers that C
  // compilers will accept)
  virtual void nodeprint(ostream& os, bool c_friendly = false);

  virtual void setIndexWidth(uint32_t i) { _index_width = i; }
  virtual uint32_t getIndexWidth() const { return _index_width; }

  virtual void setValueWidth(uint32_t v) { _value_width = v; }
  virtual uint32_t getValueWidth() const { return _value_width; }
};

static_assert(sizeof(ASTInterior) % alignof(ASTNode) == 0,
              "children are tail-allocated after ASTInterior and must stay "
              "aligned");

} // end of namespace stp
#endif

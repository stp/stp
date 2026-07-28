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

  // The vector of children
  ASTVec _children;

  // Lazily computed by ASTInteriorHasher; 0 means not yet computed.
  // Stays valid because the kind and children never change once set up,
  // so the hash isn't recomputed on insertion or removal from the
  // unique table.
  mutable size_t _cached_hash = 0;

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

  uint32_t _value_width;
  uint32_t _index_width;

  uint32_t _sig_width;
  uint32_t _exp_width;

  virtual void setIndexWidth(uint32_t i) { _index_width = i; }
  virtual uint32_t getIndexWidth() const { return _index_width; }

  virtual void setValueWidth(uint32_t v) { _value_width = v; }
  virtual uint32_t getValueWidth() const { return _value_width; }

  virtual void setSigWidth(uint32_t sw) { _sig_width = sw; }
  virtual uint32_t getSigWidth() const { return _sig_width; }

  virtual void setExpWidth(uint32_t ew) { _exp_width = ew; }
  virtual uint32_t getExpWidth() const { return _exp_width; }

public:
  ASTInterior(STPMgr* mgr, Kind kind, const ASTVec& children)
      : ASTInternal(mgr, kind), _children(children), _value_width(0),
        _index_width(0), _sig_width(0), _exp_width(0)
  {
    is_simplified = false;
    if (kind == NOT)
      node_uid = children[0].GetNodeNum() + 1;
  }

  // As above, but takes ownership of an already-owned children vector,
  // avoiding a copy when the caller has a temporary to give up.
  ASTInterior(STPMgr* mgr, Kind kind, ASTVec&& children)
      : ASTInternal(mgr, kind), _children(std::move(children)), _value_width(0),
        _index_width(0), _sig_width(0), _exp_width(0)
  {
    is_simplified = false;
    if (kind == NOT)
      node_uid = _children[0].GetNodeNum() + 1;
  }

  // This copies the contents of the child nodes
  // array, along with everything else. Assigning the smart pointer,
  // ASTNode, does NOT invoke this.
  ASTInterior(const ASTInterior& int_node)
      : ASTInternal(int_node), _children(int_node._children),
        _value_width(int_node._value_width),
        _index_width(int_node._index_width), _sig_width(int_node._sig_width),
        _exp_width(int_node._exp_width)
  {
    is_simplified = false;
  }

  // Steals the children of a probe node that was built on the stack to
  // search the unique table, keeping its node number and cached hash.
  ASTInterior(ASTInterior&& int_node)
      : ASTInternal(int_node), _children(std::move(int_node._children)),
        _cached_hash(int_node._cached_hash), _value_width(int_node._value_width),
        _index_width(int_node._index_width), _sig_width(int_node._sig_width),
        _exp_width(int_node._exp_width)
  {
    is_simplified = false;
  }

  ASTInterior& operator=(const ASTInterior& other) = delete;

  virtual ~ASTInterior();

  virtual ASTChildren GetChildren() const { return _children; }

  bool isSimplified() const { return is_simplified; }

  void hasBeenSimplified() const { is_simplified = true; }
};

// Defined out of line because they dereference ASTInterior, which is still
// incomplete inside the nested class bodies above.  They must stay in the
// header: they key STPMgr's interior unique table, so they run on every
// hash-cons probe, and being inline keeps that path free of a call.
inline size_t
ASTInterior::ASTInteriorHasher::operator()(const ASTInterior* int_node_ptr) const
{
  if (int_node_ptr->_cached_hash != 0)
    return int_node_ptr->_cached_hash;

  size_t hashval = ((size_t)int_node_ptr->GetKind());
  const ASTChildren ch = int_node_ptr->GetChildren();
  auto iend = ch.end();
  for (auto i = ch.begin(); i != iend; i++)
  {
    hashval += i->Hash();
    hashval += (hashval << 10);
    hashval ^= (hashval >> 6);
  }

  hashval += (hashval << 3);
  hashval ^= (hashval >> 11);
  hashval += (hashval << 15);

  if (hashval == 0)
    hashval = 1; // 0 marks the hash as not yet computed.
  int_node_ptr->_cached_hash = hashval;
  return hashval;
}

inline bool
ASTInterior::ASTInteriorEqual::operator()(const ASTInterior* int_node_ptr1,
                                          const ASTInterior* int_node_ptr2) const
{
  return (*int_node_ptr1 == *int_node_ptr2);
}

} // end of namespace stp
#endif

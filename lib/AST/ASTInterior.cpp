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

#include "stp/AST/ASTInterior.h"
#include "stp/STPManager/STPManager.h"
#include <new>
namespace stp
{
/******************************************************************
 * ASTInterior Member Functions                                   *
 ******************************************************************/

// Allocate the node and its children as a single block, and copy-construct
// the children into the tail (each copy takes a reference on the child).
ASTInterior* ASTInterior::create(STPMgr* mgr, Kind kind, ASTChildren children)
{
  const uint32_t n = static_cast<uint32_t>(children.size());
  void* mem = ::operator new(sizeof(ASTInterior) + n * sizeof(ASTNode));
  // ::new so the global placement-new is used (the class's own operator new
  // is deleted to forbid ordinary, wrongly-sized allocation).
  ASTInterior* node = ::new (mem) ASTInterior(mgr, kind, n);

  ASTNode* kids = node->childrenPtr();
  for (uint32_t i = 0; i < n; i++)
    new (&kids[i]) ASTNode(children[i]);

  // (NOT alpha) is numbered alpha.nodenum + 1; needs the children in place.
  if (kind == NOT)
    node->node_uid = kids[0].GetNodeNum() + 1;

  return node;
}

ASTInterior::~ASTInterior()
{
  // The children were placement-constructed in the tail; destroy them so
  // their references are released. The block itself is freed by operator
  // delete.
  ASTNode* kids = childrenPtr();
  for (uint32_t i = 0; i < _num_children; i++)
    kids[i].~ASTNode();
}

// Call this when deleting a node that has been stored in the
// the unique table
void ASTInterior::CleanUp()
{
  nodeManager->_interior_unique_table.erase(this);
  delete this;
}

// Returns kinds.  "lispprinter" handles printing of parenthesis
// and childnodes. (c_friendly is for printing hex. numbers that C
// compilers will accept)
void ASTInterior::nodeprint(ostream& os, bool /*c_friendly*/)
{
  os << _kind_names[_kind];
}

/******************************************************************
 * ASTInteriorHasher and ASTInteriorEqual Member Functions        *
 ******************************************************************/

// Shared hash of a (kind, children) pair -- the single source of truth so the
// pointer and Probe overloads agree bit-for-bit.
static size_t hashKindChildren(Kind kind, const ASTChildren& ch)
{
  size_t hashval = ((size_t)kind);
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
  return hashval;
}

// ASTInteriorHasher operator()
size_t ASTInterior::ASTInteriorHasher::
operator()(const ASTInterior* int_node_ptr) const
{
  if (int_node_ptr->_cached_hash != 0)
    return int_node_ptr->_cached_hash;

  int_node_ptr->_cached_hash =
      hashKindChildren(int_node_ptr->GetKind(), int_node_ptr->GetChildren());
  return int_node_ptr->_cached_hash;
}

// Transparent overload: hash a borrowed (kind, children) probe the same way.
size_t ASTInterior::ASTInteriorHasher::operator()(const Probe& probe) const
{
  return hashKindChildren(probe.kind, probe.children);
}

} // end of namespace

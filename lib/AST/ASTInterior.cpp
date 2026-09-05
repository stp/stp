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
//
// Deleting an interior node releases its children, and a child that loses
// its last reference is deleted in turn. Left to nest, that is one set of
// destructor frames per level of the DAG, so releasing a deeply nested
// formula runs off the stack -- the depth is the input's, not ours. A short,
// fixed prefix is still cheaper to release directly. Once that bound is
// reached, anything else that dies is queued on the manager; the outermost
// cleanup drains that queue with the same bounded prefix for each entry.
void ASTInterior::CleanUp()
{
  nodeManager->_interior_unique_table.erase(this);

  // Thirty-two nested deletes are small even on the test suite's 1 MiB stack
  // and cover ordinary shallow ASTs without one queue push and pop per node.
  static constexpr uint8_t directDeletionDepth = 32;
  if (nodeManager->_interior_deletion_depth >= directDeletionDepth)
  {
    nodeManager->_pending_deletion.push_back(this);
    return;
  }

  // Held separately: the first delete below is `this`, and nodeManager is
  // one of its members.
  STPMgr* const mgr = nodeManager;

  const bool outermost = mgr->_interior_deletion_depth == 0;

  // Restored by the guard rather than by the line after delete. A destructor
  // that threw would otherwise leave later cleanups starting at the wrong
  // depth and queueing nodes on a drain that may never run again.
  struct DeletionDepth
  {
    STPMgr* mgr;
    DeletionDepth(STPMgr* m) : mgr(m) { ++mgr->_interior_deletion_depth; }
    ~DeletionDepth() { --mgr->_interior_deletion_depth; }
  } deletionDepth(mgr);

  delete this;

  // A nested direct deletion returns to the destructor which released it.
  // The outermost cleanup alone owns the spill queue.
  if (!outermost)
    return;

  while (!mgr->_pending_deletion.empty())
  {
    ASTInterior* const node = mgr->_pending_deletion.back();
    mgr->_pending_deletion.pop_back();
    delete node; // releases up to another bounded prefix of descendants.
  }
}

// Returns kinds.  "lispprinter" handles printing of parenthesis
// and childnodes. (c_friendly is for printing hex. numbers that C
// compilers will accept)
void ASTInterior::nodeprint(ostream& os, bool /*c_friendly*/)
{
  os << _kind_names[_kind];
}

// ASTInteriorHasher::operator() and ASTInteriorEqual::operator() are defined
// inline in ASTInterior.h.

} // end of namespace

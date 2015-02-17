/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: November, 2010
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

#include "stp/AST/NodeFactory/HashingNodeFactory.h"
#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"

using stp::Kind;
using stp::ASTInterior;
using stp::ASTVec;
using stp::ASTNode;

HashingNodeFactory::~HashingNodeFactory()
{
}

// Get structurally hashed version of the node.
stp::ASTNode HashingNodeFactory::CreateNode(const Kind kind,
                                             const stp::ASTVec& back_children)
{
  // We can't create NOT(NOT (..)) nodes because of how the numbering scheme we
  // use works.
  // So you can't trust the hashiing node factory even to return nodes of the
  // same kind that
  // you ask for.
  if (kind == stp::NOT && back_children[0].GetKind() == stp::NOT)
  {
    return back_children[0][0];
  }

  ASTVec children(back_children);
  // The Bitvector solver seems to expect constants on the RHS, variables on the
  // LHS.
  // We leave the order of equals children as we find them.
  if (stp::isCommutative(kind) && kind != stp::AND)
  {
    SortByArith(children);
  }

  ASTInterior* n_ptr = new ASTInterior(kind, children);
  ASTNode n(bm.LookupOrCreateInterior(n_ptr));
  return n;
}

// Create and return an ASTNode for a term
ASTNode HashingNodeFactory::CreateTerm(Kind kind, unsigned int width,
                                       const ASTVec& children)
{

  ASTNode n = CreateNode(kind, children);
  n.SetValueWidth(width);

  // by default we assume that the term is a Bitvector. If
  // necessary the indexwidth can be changed later
  n.SetIndexWidth(0);
  return n;
}

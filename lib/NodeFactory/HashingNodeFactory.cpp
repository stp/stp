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

#include "stp/NodeFactory/HashingNodeFactory.h"
#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"

using namespace stp;

HashingNodeFactory::~HashingNodeFactory()
{
}

// Get structurally hashed version of the node.
ASTNode HashingNodeFactory::CreateNode(const Kind kind,
                                       const ASTVec& back_children)
{
  // We can't create NOT(NOT (..)) nodes because of how the numbering scheme we
  // use works. So you can't trust the hashing node factory even to return
  // nodes of the same kind that you ask for.
  if (kind == NOT && back_children[0].GetKind() == NOT)
  {
    return back_children[0][0];
  }
  
  if (back_children.size()  <= 1 || !isCommutative(kind))
  {
    // Don't create a new vector if it won't be sorted.
    ASTInterior* n_ptr = new ASTInterior(&bm, kind, back_children);
    ASTNode n(bm.LookupOrCreateInterior(n_ptr));
    return n;    
  }
  else if (is_Form_kind(kind)) // formula and commutative.
  {
    const bool isSorted =  std::is_sorted(back_children.begin(),back_children.end(),stp::exprless);
    if (isSorted)
    {
      ASTInterior* n_ptr = new ASTInterior(&bm, kind, back_children);
      ASTNode n(bm.LookupOrCreateInterior(n_ptr));
      return n;
    }

    ASTVec sorted_children = back_children;
    SortByExprNum(sorted_children);  
    ASTInterior* n_ptr = new ASTInterior(&bm, kind, sorted_children);
    ASTNode n(bm.LookupOrCreateInterior(n_ptr));
    return n;
  }
  else
  {
    ASTVec children(back_children);
    // The Bitvector solver seems to expect constants on the RHS, variables on the
    // LHS. 
    SortByArith(children);

    // Todo - we could move the children into the astinterior.
    ASTInterior* n_ptr = new ASTInterior(&bm, kind, children);
    ASTNode n(bm.LookupOrCreateInterior(n_ptr));
    return n;
  }
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

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

#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"
#include <sstream>

namespace stp
{

uint8_t ASTNode::getIteration() const
{
  return _int_node_ptr->iteration;
}

void ASTNode::setIteration(uint8_t v) const
{
  _int_node_ptr->iteration = v;
}

STPMgr* ASTNode::GetSTPMgr() const
{
  return _int_node_ptr->nodeManager;
}

// GetKind, GetChildren and GetNodeNum are now inlined in ASTNode.h (possible
// since ASTInternal.h no longer includes ASTNode.h, breaking the old cycle).
// The ref-counting special members are inlined there too.

void ASTNode::SetIndexWidth(unsigned int _iw) const
{
  _int_node_ptr->setIndexWidth(_iw);
}

void ASTNode::SetValueWidth(unsigned int vw) const
{
  _int_node_ptr->setValueWidth(vw);
}

// return the type of the ASTNode:
//
// 0 iff BOOLEAN; 1 iff BITVECTOR; 2 iff ARRAY; 3 iff UNKNOWN;
// Print the node
void ASTNode::nodeprint(ostream& os, bool c_friendly) const
{
  _int_node_ptr->nodeprint(os, c_friendly);
}

// Get the name from a symbol (char *).  It's an error if kind !=
// SYMBOL
const char* ASTNode::GetName() const
{
  if (GetKind() != SYMBOL)
    FatalError("GetName: Called GetName on a non-symbol: ", *this);

  return ((ASTSymbol*)_int_node_ptr)->GetName();
}

// Get the value of bvconst from a bvconst.  It's an error if kind
// != BVCONST Treat the result as const (the compiler can't enforce
// it).
CBV ASTNode::GetBVConst() const
{
  if (GetKind() != BVCONST)
    FatalError("GetBVConst: non bitvector-constant: ", *this);

  return ((ASTBVConst*)_int_node_ptr)->GetBVConst();
}

unsigned int ASTNode::GetUnsignedConst() const
{
  const ASTNode& n = *this;
  assert(BVCONST == n.GetKind());

  if (sizeof(unsigned int) * 8 < n.GetValueWidth())
  {
    // It may only contain a small value in a bit type,
    // which fits nicely into an unsigned int.  This is
    // common for functions like: bvshl(bv1[128],
    // bv1[128]) where both operands have the same type.
    signed long maxBit = CONSTANTBV::Set_Max(n.GetBVConst());
    if (maxBit >= ((signed long)sizeof(unsigned int)) * 8)
    {
      n.LispPrint(std::cerr); // print the node so they can find it.
      FatalError("GetUnsignedConst: cannot convert bvconst "
                 "of length greater than 32 to unsigned int");
    }
  }
  return (unsigned int)*((unsigned int*)n.GetBVConst());
}

// Hash() is now inlined in ASTNode.h.

void ASTNode::NFASTPrint(int l, int max, int prefix) const
{
  //****************************************
  // stop
  //****************************************
  if (l > max)
  {
    return;
  }

  //****************************************
  // print
  //****************************************
  printf("[%10d]", 0);
  for (int i = 0; i < prefix; i++)
  {
    printf("    ");
  }
  std::cout << GetKind();
  printf("\n");

  //****************************************
  // recurse
  //****************************************

  const ASTChildren children = GetChildren();
  auto it = children.begin();
  for (; it != children.end(); it++)
  {
    it->NFASTPrint(l + 1, max, prefix + 1);
  }
}

bool ASTNode::isSimplfied() const
{
  return _int_node_ptr->isSimplified();
}

void ASTNode::hasBeenSimplfied() const
{
  _int_node_ptr->hasBeenSimplified();
}

} //end of namespace

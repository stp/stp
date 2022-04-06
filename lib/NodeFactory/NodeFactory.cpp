/********************************************************************
 * Vijay Ganesh, Trevor Hansen, Dan Liew, Mate Soos
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
#include "stp/AST/ASTKind.h"
#include "stp/STPManager/STPManager.h"

stp::ASTNode NodeFactory::CreateTerm(stp::Kind kind, unsigned int width,
                                     const stp::ASTVec& children)
{
  return CreateTerm(kind, width, children);
}

ASTNode NodeFactory::CreateTerm(Kind kind, unsigned int width,
                                const ASTNode& child0, const ASTVec& children)
{
  ASTVec child;
  child.reserve(children.size() + 1);
  child.push_back(child0);
  child.insert(child.end(), children.begin(), children.end());
  return CreateTerm(kind, width, child);
}

ASTNode NodeFactory::CreateTerm(Kind kind, unsigned int width,
                                const ASTNode& child0, const ASTNode& child1,
                                const ASTVec& children)
{
  ASTVec child;
  child.reserve(children.size() + 2);
  child.push_back(child0);
  child.push_back(child1);
  child.insert(child.end(), children.begin(), children.end());
  return CreateTerm(kind, width, child);
}

ASTNode NodeFactory::CreateTerm(Kind kind, unsigned int width,
                                const ASTNode& child0, const ASTNode& child1,
                                const ASTNode& child2, const ASTVec& children)
{
  ASTVec child;
  child.reserve(children.size() + 3);
  child.push_back(child0);
  child.push_back(child1);
  child.push_back(child2);
  child.insert(child.end(), children.begin(), children.end());
  return CreateTerm(kind, width, child);
}

ASTNode NodeFactory::CreateNode(Kind kind, const ASTNode& child0,
                                const ASTVec& back_children)
{
  ASTVec front_children;
  front_children.reserve(1 + back_children.size());
  front_children.push_back(child0);
  front_children.insert(front_children.end(), back_children.begin(),
                        back_children.end());
  return CreateNode(kind, front_children);
}

ASTNode NodeFactory::CreateNode(Kind kind, const ASTNode& child0,
                                const ASTNode& child1,
                                const ASTVec& back_children)
{
  ASTVec front_children;
  front_children.reserve(2 + back_children.size());
  front_children.push_back(child0);
  front_children.push_back(child1);
  front_children.insert(front_children.end(), back_children.begin(),
                        back_children.end());
  return CreateNode(kind, front_children);
}

ASTNode NodeFactory::CreateNode(Kind kind, const ASTNode& child0,
                                const ASTNode& child1, const ASTNode& child2,
                                const ASTVec& back_children)
{
  ASTVec front_children;
  front_children.reserve(3 + back_children.size());
  front_children.push_back(child0);
  front_children.push_back(child1);
  front_children.push_back(child2);
  front_children.insert(front_children.end(), back_children.begin(),
                        back_children.end());
  return CreateNode(kind, front_children);
}

ASTNode NodeFactory::CreateArrayTerm(Kind kind, unsigned int index,
                                     unsigned int width, const ASTNode& child0,
                                     const ASTNode& child1,
                                     const ASTNode& child2,
                                     const ASTVec& children)
{
  ASTVec child;
  child.reserve(children.size() + 3);
  child.push_back(child0);
  child.push_back(child1);
  child.push_back(child2);
  child.insert(child.end(), children.begin(), children.end());
  return CreateArrayTerm(kind, index, width, child);
}

stp::ASTNode NodeFactory::CreateArrayTerm(Kind kind, unsigned int index,
                                          unsigned int width,
                                          const stp::ASTVec& children)
{
  ASTNode result = CreateTerm(kind, width, children);
  result.SetIndexWidth(index);
  return result;
}

stp::ASTNode NodeFactory::getTrue()
{
  return bm.ASTTrue;
}
stp::ASTNode NodeFactory::getFalse()
{
  return bm.ASTFalse;
}

ASTNode NodeFactory::CreateSymbol(const char* const name, unsigned indexWidth,
                                  unsigned valueWidth)
{
  ASTNode n = bm.LookupOrCreateSymbol(name);
  n.SetIndexWidth(indexWidth);
  n.SetValueWidth(valueWidth);
  return n;
}

ASTNode NodeFactory::CreateConstant(stp::CBV cbv, unsigned width)
{
  return bm.CreateBVConst(cbv, width);
}

ASTNode NodeFactory::CreateOneConst(unsigned width)
{
  return bm.CreateOneConst(width);
}

ASTNode NodeFactory::CreateZeroConst(unsigned width)
{
  return bm.CreateZeroConst(width);
}

ASTNode NodeFactory::CreateMaxConst(unsigned width)
{
  return bm.CreateMaxConst(width);
}

ASTNode NodeFactory::CreateBVConst(unsigned int width,
                                   unsigned long long int bvconst)
{
  return bm.CreateBVConst(width, bvconst);
}

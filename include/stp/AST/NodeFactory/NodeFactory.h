/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Feb, 2010
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

#ifndef NODEFACTORY_H
#define NODEFACTORY_H

#include "stp/AST/ASTKind.h"
#include "stp/Util/Attributes.h"
#include <vector>

using std::vector;
namespace stp
{
class ASTNode;
typedef vector<ASTNode> ASTVec;
DLL_PUBLIC extern ASTVec _empty_ASTVec;
class STPMgr;
typedef unsigned int* CBV;
}

using stp::ASTNode;
using stp::Kind;
using stp::ASTVec;
using stp::_empty_ASTVec;
using stp::STPMgr;

// Abstract base class for all the node factories.
class DLL_PUBLIC NodeFactory // not copyable
{
protected:
  STPMgr& bm;

public:
  NodeFactory(STPMgr& bm_) : bm(bm_) {}
  virtual ~NodeFactory() {}

  virtual ASTNode CreateTerm(Kind kind, unsigned int width,
                                        const ASTVec& children) = 0;

  virtual ASTNode CreateArrayTerm(Kind kind, unsigned int index,
                                             unsigned int width,
                                             const ASTVec& children);

  virtual ASTNode CreateNode(Kind kind, const ASTVec& children) = 0;

  ASTNode CreateSymbol(const char* const name, unsigned indexWidth,
                       unsigned valueWidth);

  ASTNode CreateTerm(Kind kind, unsigned int width, const ASTNode& child0,
                     const ASTVec& children = _empty_ASTVec);
  ASTNode CreateTerm(Kind kind, unsigned int width, const ASTNode& child0,
                     const ASTNode& child1,
                     const ASTVec& children = _empty_ASTVec);
  ASTNode CreateTerm(Kind kind, unsigned int width, const ASTNode& child0,
                     const ASTNode& child1, const ASTNode& child2,
                     const ASTVec& children = _empty_ASTVec);

  ASTNode CreateNode(Kind kind, const ASTNode& child0,
                                const ASTVec& back_children = _empty_ASTVec);
  ASTNode CreateNode(Kind kind, const ASTNode& child0,
                                const ASTNode& child1,
                                const ASTVec& back_children = _empty_ASTVec);
  ASTNode CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1,
                     const ASTNode& child2,
                     const ASTVec& back_children = _empty_ASTVec);

  ASTNode CreateArrayTerm(Kind kind, unsigned int index, unsigned int width,
                          const ASTNode& child0, const ASTNode& child1,
                          const ASTNode& child2,
                          const ASTVec& children = _empty_ASTVec);

  ASTNode getTrue();
  ASTNode getFalse();

  ASTNode CreateConstant(stp::CBV cbv, unsigned width);

  ASTNode CreateOneConst(unsigned width);
  ASTNode CreateZeroConst(unsigned width);
  ASTNode CreateBVConst(unsigned int width, unsigned long long int bvconst);

  virtual std::string getName() = 0;
};

#endif

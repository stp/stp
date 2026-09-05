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
#include <cstdint>
#include <initializer_list>
#include <vector>

using std::vector;
namespace stp
{
class ASTNode;
typedef vector<ASTNode> ASTVec;
template <class T> class Span;
typedef Span<const ASTNode> ASTChildren;
DLL_PUBLIC extern ASTVec _empty_ASTVec;
class STPMgr;
typedef unsigned int* CBV;
}

using stp::ASTNode;
using stp::Kind;
using stp::ASTVec;
using stp::ASTChildren;
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

  STPMgr& getStpMgr() const { return bm; }

  // A non-owning contiguous child range. ASTVec converts to this view, while
  // callers which already own another contiguous arena avoid materialising
  // a vector merely to cross the factory boundary.
  virtual ASTNode CreateTerm(Kind kind, unsigned int width,
                             ASTChildren children) = 0;

  virtual ASTNode CreateArrayTerm(Kind kind, unsigned int index,
                                  unsigned int width, ASTChildren children);

  virtual ASTNode CreateNode(Kind kind, ASTChildren children) = 0;

  // Preserve the convenient braced-child API without allocating a temporary
  // ASTVec. The initializer-list storage remains alive for the duration of
  // these calls.
  ASTNode CreateTerm(Kind kind, unsigned int width,
                     std::initializer_list<ASTNode> children);
  ASTNode CreateArrayTerm(Kind kind, unsigned int index, unsigned int width,
                          std::initializer_list<ASTNode> children);
  ASTNode CreateNode(Kind kind, std::initializer_list<ASTNode> children);

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
  ASTNode getUndefined();

  // With a nonzero exp_width the constant is made as a floating-point
  // constant of that format. A constant is a leaf, so unlike an interior
  // node it cannot derive a format from its children; a caller replacing a
  // float-valued node with a constant must pass the format through or the
  // float-ness is lost.
  ASTNode CreateConstant(stp::CBV cbv, unsigned width, unsigned exp_width = 0,
                         unsigned sig_width = 0);

  ASTNode CreateOneConst(unsigned width);
  ASTNode CreateZeroConst(unsigned width);
  ASTNode CreateMaxConst(unsigned width);
  ASTNode CreateSignedMinConst(unsigned width);
  
  ASTNode CreateBVConst(unsigned int width, uint64_t bvconst);
  ASTNode CreateFPConst(const stp::ASTNode& bvconst, unsigned exp_width,
                        unsigned sig_width);

  virtual std::string getName() = 0;
};

#endif

/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: October, 2026
 *
 * LICENSE: Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to permit
 * persons to whom the Software is furnished to do so, subject to the
 * following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 ********************************************************************/

#ifndef STRENGTHREDUCINGNODEFACTORY_H_
#define STRENGTHREDUCINGNODEFACTORY_H_

#include "stp/NodeFactory/NodeFactory.h"

namespace stp
{
class NodeDomainAnalysis;
class StrengthReduction;

// A factory layer: the inner factory builds (or folds) the node, then its
// domains are computed from its children's and the strength reductions
// run over it, so every node that comes out is reduced the way
// StrengthReduction::topLevel reduces a whole formula, one node at a time
// as it is made. Sits in a MutableGraph's stack above the simplifying
// rules; the graph recomputes a patched node's domains itself, since a
// patch is not a creation.
class StrengthReducingNodeFactory : public NodeFactory
{
  NodeFactory& inner;
  StrengthReduction& reduction;
  NodeDomainAnalysis& domains;

  ASTNode reduce(const ASTNode& n);

public:
  StrengthReducingNodeFactory(STPMgr& bm_, NodeFactory& in,
                              StrengthReduction& sr, NodeDomainAnalysis& nda)
      : NodeFactory(bm_), inner(in), reduction(sr), domains(nda)
  {
  }
  using NodeFactory::CreateArrayTerm;
  using NodeFactory::CreateNode;
  using NodeFactory::CreateTerm;
  virtual ASTNode CreateNode(Kind kind, ASTChildren children) override;
  virtual ASTNode CreateTerm(Kind kind, unsigned int width,
                             ASTChildren children) override;
  virtual ASTNode CreateArrayTerm(Kind kind, unsigned int index,
                                  unsigned int width,
                                  ASTChildren children) override;
  virtual std::string getName() override { return "strength-reducing"; }
};
}

#endif

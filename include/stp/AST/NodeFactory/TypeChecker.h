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

/*
  A decorator pattern, which calls some base node factory, then type checks each
  of the results.
 */

#ifndef TYPECHECKER_H_
#define TYPECHECKER_H_

#include "stp/AST/NodeFactory/NodeFactory.h"

class TypeChecker : public NodeFactory
{
  NodeFactory& f;

public:
  DLL_PUBLIC TypeChecker(NodeFactory& f_, STPMgr& bm_) : NodeFactory(bm_), f(f_)
  {
  }
  DLL_PUBLIC virtual ~TypeChecker(){};

  stp::ASTNode CreateTerm(stp::Kind kind, unsigned int width,
                          const stp::ASTVec& children);
  stp::ASTNode CreateNode(stp::Kind kind, const stp::ASTVec& children);
  stp::ASTNode CreateArrayTerm(Kind kind, unsigned int index,
                               unsigned int width, const ASTVec& children);

  DLL_PUBLIC virtual std::string getName() { return "type checking"; }
};

#endif /* TYPECHECKER_H_ */

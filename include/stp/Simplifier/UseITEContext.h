/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Feb, 2011
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
  *    Descend through ITEs keeping a stack of what must be true/false.
  *    For instance. In the following:
  *        (ite (or a b) (not (or a b)) c )
  *
  *       In the lhs of the ITE, we know that a or b are true, so, we can
  *rewrite it to:
  *       (ite (or a b) false c)
  *
 */

#ifndef UseITEContext_H_
#define UseITEContext_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include <map>

namespace stp
{
class UseITEContext // not copyable
{
  NodeFactory* nf;
  RunTimes* runtimes;
  ASTNode ASTTrue, ASTFalse;

  void addToContext(const ASTNode& n, ASTNodeSet& context);


  // Unfortunately there can be a lot of paths through a small formula.
  // So we limit how often each node is visited.

  ASTNode visit(const ASTNode& n, std::map<ASTNode, int>& visited,
                ASTNodeSet& visited_empty, ASTNodeSet& context);

public:
  ASTNode topLevel(const ASTNode& n);

  UseITEContext(STPMgr* bm);

};
}

#endif

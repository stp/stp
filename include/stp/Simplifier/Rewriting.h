/********************************************************************
 * AUTHORS: Trevor Hansen
 *
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
 Sharing aware rewriting. 
*/

#ifndef REWRITING_H_
#define REWRITING_H_


#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include <map>

namespace stp
{

class Rewriting
{
  STPMgr* stpMgr;
  NodeFactory* nf;

  // uint8_t wrapped: 257 references read back as 1, i.e. unshared.
  std::unordered_map<uint64_t, uint32_t> shareCount;
  std::unordered_map<uint64_t, ASTNode> fromTo;

  int removed;

  // sharecount is 1 if the node has one reference in the tree.
  void buildShareCount(const ASTNode& n);
  ASTNode applyRules(ASTNode c);

  // rewrite() walks the DAG with its frames on the heap: the input decides
  // how deep the walk goes, so a call per level exhausts the stack on the
  // deeply nested formulas that exist. See DeepDag_Test.cpp.
  struct Frame;
  bool alreadyKnown(const ASTNode& n, ASTNode& answer);
  ASTNode rewrite(const ASTNode& n);

public:
  Rewriting(const Rewriting&) = delete;
  Rewriting & operator=(const Rewriting&) = delete;
  
  Rewriting(STPMgr* stp_, NodeFactory* nf_)
  {
    stpMgr = stp_;
    nf = nf_;
  }

  ASTNode topLevel(ASTNode& n);
};
}

#endif

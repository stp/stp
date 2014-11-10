// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: February, 2011
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
 * RemoveUnconstrained.h
 *
 *  Unconstrained variable elination.
 */

#ifndef REMOVEUNCONSTRAINED_H_
#define REMOVEUNCONSTRAINED_H_
#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/constantBitP/Dependencies.h"
#include "stp/Simplifier/simplifier.h"
#include "stp/Simplifier/MutableASTNode.h"

namespace BEEV
{
using simplifier::constantBitP::Dependencies;

class RemoveUnconstrained // not copyable
{
  STPMgr& bm;

  ASTNode replaceParentWithFresh(MutableASTNode& mute,
                                 vector<MutableASTNode*>& variables);

  ASTNode topLevel_other(const ASTNode& n, Simplifier* simplifier);

  void splitExtractOnly(vector<MutableASTNode*> extracts);

  void replace(MutableASTNode* from, const ASTNode to);

  void replace(const ASTNode& from, const ASTNode to);

  NodeFactory* nf;

public:
  RemoveUnconstrained(STPMgr& bm);

  ASTNode topLevel(const ASTNode& n, Simplifier* s);
};
}

#endif /* REMOVEUNCONSTRAINED_H_ */

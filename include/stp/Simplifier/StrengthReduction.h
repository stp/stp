/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Februrary, 2011
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
 *  Takes the result of an analysis and uses it to simplify, for example,
 *  if both operands of a signed division have the same MSB, it can be converted
 *  to an unsigned division, instead.
 */

#ifndef STRENGTHREDUCTION_H_
#define STRENGTHREDUCTION_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
//#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
//#include <iostream>
#include <map>
#include <string>

namespace stp
{
using std::string;
using simplifier::constantBitP::FixedBits;

class StrengthReduction 
{
  unsigned replaceWithConstant;
  unsigned replaceWithSimpler;
  unsigned unimplementedReduction;

  STPMgr& bm;
  CBV littleOne;
  CBV littleZero;
  NodeFactory* nf;

  // A special version that handles the lhs appearing in the rhs of the fromTo
  // map.
  ASTNode replace(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& cache);

public:

  StrengthReduction(STPMgr& _bm);
  StrengthReduction(const StrengthReduction&) = delete;
  StrengthReduction& operator=(const StrengthReduction&) = delete;
  ~StrengthReduction();

  //TODO merge these two toplevel funtions, they do the same thing..
  ASTNode topLevel(const ASTNode& top, const std::map<ASTNode, FixedBits*>& visited);

  // Replace some of the things that unsigned intervals can figure out for us.
  // Reduce from signed to unsigned if possible.
  ASTNode topLevel(const ASTNode& top, const std::map<const ASTNode, UnsignedInterval*>& visited);
  
  void stats(string name = "StrengthReduction");
};
}

#endif

// -*- c++ -*-
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
 * A lighter-weight, bottom up constant bit propagation.
 */

#ifndef UPWARDSCBITP_H_
#define UPWARDSCBITP_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include <map>
//#include "stp/Simplifier/StrengthReduction.h"

#ifdef _MSC_VER
#include <compdep.h>
#endif

#include <iostream>


namespace stp
{
using simplifier::constantBitP::FixedBits;


class UpwardsCBitP // not copyable
{

public:

  ASTNode topLevel(const ASTNode& top)
  {
    simplifier::constantBitP::ConstantBitPropagation cb(&bm,
        simp, bm.defaultNodeFactory, top);

    return cb.topLevelBothWays(top, false, false);


    //map<const ASTNode, FixedBits*> visited;
    // visit(top, visited, clockwise);

    // StrengthReduction sr(bm);
    // return sr.topLevel(top,visited);
  }
#if 0
  FixedBits* visit(const ASTNode& n, std::map<ASTNode, FixedBits *> &visited)
  {

    std::map<const ASTNode, FixedBits*>::iterator it;
    if ((it = visited.find(n)) != visited.end())
      return it->second;

    const int number_children = n.Degree();
    vector<FixedBits*> children;
    children.reserve(number_children);
    for (int i = 0; i < number_children; i++)
    {
      children.push_back(visit(n[i], visited, clockwise));
    }

    FixedBits* result = NULL;
    const unsigned int width = n.GetValueWidth();
    const bool knownC0 = number_children < 1 ? false : (children[0] != NULL);
    const bool knownC1 = number_children < 2 ? false : (children[1] != NULL);

  // call the transfer functions.

    if (result != NULL && result->isComplete())
      result = NULL;

    if (result != NULL)
      result->checkUnsignedInvariant();

    // result will often be null (which we take to mean the maximum range).
    visited.insert(make_pair(n, result));
    return result;
  }
#endif

  STPMgr& bm;
  Simplifier * simp;

public:

  UpwardsCBitP(STPMgr* _bm, Simplifier* simp_) : bm(*_bm)
  {
  simp = simp_;
  }

  ~UpwardsCBitP()
  {
  }
};
}

#endif

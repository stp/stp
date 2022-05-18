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
#include "stp/Simplifier/StrengthReduction.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include <iostream>
#include <unordered_map>

namespace stp
{
using simplifier::constantBitP::FixedBits;

using NodeToFixedBitsMap = std::unordered_map<const ASTNode, FixedBits*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;

class UpwardsCBitP // not copyable
{
  STPMgr& bm;
  FixedBits* emptyBoolean;
  std::unordered_map<unsigned, FixedBits*> emptyBitVector;

  FixedBits* fresh(const ASTNode& n)
  {
    return new FixedBits(n.GetValueWidth() > 0 ? n.GetValueWidth() : 1,
                         (BOOLEAN_TYPE == n.GetType()));
  }

  FixedBits* visit(const ASTNode& n, NodeToFixedBitsMap& visited)
  {
    {
      auto it = visited.find(n);
      if (it != visited.end())
        return it->second;
    }

    const int number_children = n.Degree();

    vector<FixedBits*> children;
    children.reserve(number_children);

    bool nothingKnown = true;

    for (int i = 0; i < number_children; i++)
    {
      FixedBits* op = visit(n[i], visited);
      if (op != NULL)
        nothingKnown = false;
      children.push_back(op);
    }

    // We need to know something about the children if we want to know something about the parent.
    if ((n.GetKind() == READ) || (n.GetKind() == WRITE) ||
        (children.size() > 0 && nothingKnown) ||
        (n.GetKind() == BVEXTRACT && children[0] == NULL) ||
        (n.GetKind() == BVSX && children[0] == NULL) ||
        (n.GetKind() == BVZX && children[0] == NULL) || (n.GetKind() == SYMBOL))
    {
      visited.insert(std::make_pair(n, (FixedBits*)NULL));
      return NULL;
    }

    FixedBits* result = fresh(n);

    if (n.GetKind() == BVCONST)
    {
      // the CBV doesn't leak. it is a copy of the cbv inside the node.
      CBV cbv = n.GetBVConst();

      for (unsigned int j = 0; j < n.GetValueWidth(); j++)
      {
        result->setFixed(j, true);
        result->setValue(j, CONSTANTBV::BitVector_bit_test(cbv, j));
      }
    }
    else if (TRUE == n.GetKind())
    {
      result->setFixed(0, true);
      result->setValue(0, true);
    }
    else if (FALSE == n.GetKind())
    {
      result->setFixed(0, true);
      result->setValue(0, false);
    }
    else
    {
      for (unsigned i = 0; i < children.size(); i++)
        if (children[i] == NULL)
          children[i] = getEmpty(n[i]);

      if (n.GetKind() == BVMULT)
      {
        simplifier::constantBitP::MultiplicationStatsMap msm;
        simplifier::constantBitP::ConstantBitPropagation::
            dispatchToTransferFunctions(&bm, n.GetKind(), children, *result, n,
                                        &msm);
      }
      else
      {
        simplifier::constantBitP::ConstantBitPropagation::
            dispatchToTransferFunctions(&bm, n.GetKind(), children, *result, n,
                                        NULL);
      }

      if (false)
      {
        std::cerr << n.GetKind();
        for (unsigned i = 0; i < children.size(); i++)
          std::cerr << *children[i];
        std::cerr << " = " << *result << std::endl;
      }
    }

    if (result->isTotallyUnfixed())
    {
      delete result;
      result = NULL;
    }

    visited.insert(std::make_pair(n, result));
    return result;
  }

  // When we call the transfer functions, we can't send nulls, send unfixed instead.
  FixedBits* getEmpty(const ASTNode& n)
  {
    if (n.GetType() == BOOLEAN_TYPE)
    {
      assert(emptyBoolean->isTotallyUnfixed());
      return emptyBoolean;
    }
    if (emptyBitVector.find(n.GetValueWidth()) == emptyBitVector.end())
      emptyBitVector[n.GetValueWidth()] = fresh(n);

    FixedBits* r = emptyBitVector[n.GetValueWidth()];
    assert(r->isTotallyUnfixed());
    return r;
  }

public:

  UpwardsCBitP(STPMgr* _bm) : bm(*_bm)
  {
    emptyBoolean = new FixedBits(1, true);
  }

  UpwardsCBitP(UpwardsCBitP const&) = delete;
  UpwardsCBitP& operator=(UpwardsCBitP const&) = delete;

  ~UpwardsCBitP()
  {
    for (auto it : emptyBitVector)
    {
      assert(it.second->isTotallyUnfixed());
      delete it.second;
    }
    delete emptyBoolean;
  }

  ASTNode topLevel(const ASTNode& top)
  {
    NodeToFixedBitsMap visited;

    bm.GetRunTimes()->start(RunTimes::ConstantBitPropagation);

    visit(top, visited);
    StrengthReduction sr(bm.defaultNodeFactory, &bm.UserFlags);
    ASTNode result = sr.topLevel(top, visited);

    bm.GetRunTimes()->stop(RunTimes::ConstantBitPropagation);

    for (auto it : visited)
      if (it.second != NULL)
        delete it.second;

    return result;
  }

};
}

#endif

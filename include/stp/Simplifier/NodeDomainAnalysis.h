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
 * Builds a map to fixed bits and unsigned intervals.
 */

#ifndef NODEDOMAINANALYSIS_H_
#define NODEDOMAINANALYSIS_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include <iostream>
#include <unordered_map>

namespace stp
{
using simplifier::constantBitP::FixedBits;

using NodeToUnsignedIntervalMap = std::unordered_map<const ASTNode, UnsignedInterval*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;
using NodeToFixedBitsMap = std::unordered_map<const ASTNode, FixedBits*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;

class NodeDomainAnalysis
{
  STPMgr& bm;

  // Cache read-only empty objects of different sizes.
  FixedBits* emptyBoolean;
  std::unordered_map<unsigned, FixedBits*> emptyBitVector;
 
  FixedBits* fresh(const ASTNode& n)
  {
    return new FixedBits(n.GetValueWidth() > 0 ? n.GetValueWidth() : 1,
                         (BOOLEAN_TYPE == n.GetType()));
  }

  // When we call the transfer functions, we can't send nulls, send unfixed instead.
  FixedBits* getEmptyFixedBits(const ASTNode& n);
  
  using AnalysisPair = std::pair<FixedBits*, UnsignedInterval*>;
  NodeToFixedBitsMap toFixedBits;
  NodeToUnsignedIntervalMap toIntervals;

  UnsignedIntervalAnalysis intervalAnalysis;

  unsigned todo = 0;
  unsigned tighten = 0;

  void stats();
public:

  NodeDomainAnalysis(STPMgr* _bm) : bm(*_bm), intervalAnalysis(*_bm)
  {
    emptyBoolean = new FixedBits(1, true);
  }

  NodeDomainAnalysis(NodeDomainAnalysis const&) = delete;
  NodeDomainAnalysis& operator=(NodeDomainAnalysis const&) = delete;

  ~NodeDomainAnalysis()
  {
    for (auto it : emptyBitVector)
    {
      assert(it.second->isTotallyUnfixed());
      delete it.second;
    }
    delete emptyBoolean;

    for (auto it : toFixedBits)
      if (it.second != NULL)
        delete it.second;

    for (auto it : toIntervals)
      if (it.second != NULL)
        delete it.second;

    stats();
  }

   NodeToUnsignedIntervalMap* getIntervalMap()
   {
      return &toIntervals;
   }

   NodeToFixedBitsMap* getCbitMap()
   {
      return &toFixedBits;
   }

  AnalysisPair buildMap(const ASTNode& n);

  void topLevel(const ASTNode& top)
  {
    bm.GetRunTimes()->start(RunTimes::NodeDomainAnalysis);
    buildMap(top);
    bm.GetRunTimes()->stop(RunTimes::NodeDomainAnalysis);
    assert(toIntervals.size() == toFixedBits.size());
  }

  void harmonise(FixedBits * &bits, UnsignedInterval * &interval);

};
}

#endif

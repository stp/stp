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
#include "stp/Simplifier/UnsignedIntervalSet.h"
#include "stp/Simplifier/UnsignedIntervalSetAnalysis.h"
#include "stp/Simplifier/ValueSetAnalysis.h"
#include <iostream>
#include <unordered_map>

namespace stp
{
using simplifier::constantBitP::FixedBits;

using NodeToUnsignedIntervalMap = std::unordered_map<const ASTNode, UnsignedInterval*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;
using NodeToFixedBitsMap = std::unordered_map<const ASTNode, FixedBits*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;
using NodeToUnsignedIntervalSetMap = std::unordered_map<const ASTNode, UnsignedIntervalSet*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;
using NodeToValueSetMap = std::unordered_map<const ASTNode, ValueSet*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;

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
  
  NodeToFixedBitsMap toFixedBits;
  NodeToUnsignedIntervalMap toIntervals;
  NodeToUnsignedIntervalSetMap toIntervalSets;
  NodeToValueSetMap toValueSets;

  UnsignedIntervalAnalysis intervalAnalysis;
  UnsignedIntervalSetAnalysis setAnalysis;
  ValueSetAnalysis valueSetAnalysis;

  unsigned tighten = 0;
  unsigned setTightened = 0;
  unsigned setEnumerated = 0;

  void stats();
public:

  struct DomainInfo
  {
    FixedBits* bits;
    UnsignedInterval* interval;
    UnsignedIntervalSet* intervalSet;
    ValueSet* set;
  };

  NodeDomainAnalysis(STPMgr* _bm)
      : bm(*_bm), intervalAnalysis(*_bm), setAnalysis(*_bm),
        valueSetAnalysis(*_bm)
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

    for (auto it : toIntervalSets)
      if (it.second != NULL)
        delete it.second;

    for (auto it : toValueSets)
      if (it.second != NULL)
        delete it.second;

    stats();
  }

   NodeToUnsignedIntervalMap* getIntervalMap()
   {
      return &toIntervals;
   }

   NodeToUnsignedIntervalSetMap* getIntervalSetMap()
   {
      return &toIntervalSets;
   }

   NodeToFixedBitsMap* getCbitMap()
   {
      return &toFixedBits;
   }

   NodeToValueSetMap* getValueSetMap()
   {
      return &toValueSets;
   }

  DomainInfo buildMap(const ASTNode& n);

  void topLevel(const ASTNode& top)
  {
    bm.GetRunTimes()->start(RunTimes::NodeDomainAnalysis);
    buildMap(top);
    bm.GetRunTimes()->stop(RunTimes::NodeDomainAnalysis);
    assert(toIntervals.size() == toFixedBits.size());
    assert(toIntervalSets.size() == toFixedBits.size());
    assert(toValueSets.size() == toFixedBits.size());
  }

  void harmonise(FixedBits * &bits, UnsignedInterval * &interval);
  void harmonise(FixedBits * &bits, UnsignedInterval * &interval,
                 ValueSet * &set, unsigned width, bool isBoolean);

};
}

#endif

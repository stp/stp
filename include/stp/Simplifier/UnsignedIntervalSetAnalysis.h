/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2026
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
 * A bounded-disjoint-interval-set analysis built on top of the existing
 * single-interval transfer functions.
 *
 * For each node it drives UnsignedIntervalAnalysis::dispatchToTransferFunctions
 * over the cross-product of the children's member intervals and unions the
 * results into a UnsignedIntervalSet. For sign-sensitive kinds the child
 * intervals are first split at the sign poles (reusing UnsignedInterval::split)
 * so the per-piece transfer stays tight; ITE is handled natively as the union
 * of its branches. The single-interval domain is recovered exactly at cap==1.
 */

#ifndef UNSIGNEDINTERVALSETANALYSIS_H_
#define UNSIGNEDINTERVALSETANALYSIS_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include "stp/Simplifier/UnsignedIntervalSet.h"
#include <vector>

namespace stp
{

class UnsignedIntervalSetAnalysis
{
  STPMgr& bm;
  UnsignedIntervalAnalysis ia; // supplies the per-interval transfer functions
  unsigned cap;

  // Whether child 'i' should be split at the sign boundary before the
  // cross-product (only the operands interpreted as signed).
  static bool splitChild(Kind k, unsigned i);

public:
  UnsignedIntervalSetAnalysis(STPMgr& _bm,
                              unsigned cap_ = UnsignedIntervalSet::DEFAULT_CAP)
      : bm(_bm), ia(_bm), cap(cap_)
  {
  }

  UnsignedIntervalSetAnalysis(const UnsignedIntervalSetAnalysis&) = delete;
  UnsignedIntervalSetAnalysis&
  operator=(const UnsignedIntervalSetAnalysis&) = delete;

  unsigned getCap() const { return cap; }

  // Computes the result set for node n from its children's sets. A null
  // child pointer (or a complete child) means "no information". The caller
  // owns the returned set, allocated at width max(1, n.GetValueWidth()).
  UnsignedIntervalSet*
  transfer(const ASTNode& n,
           const std::vector<const UnsignedIntervalSet*>& children);
};
}

#endif

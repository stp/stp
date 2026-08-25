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
 * Performs a basic unsigned interval analysis.
 * The analysis is only bottom up (without assuming that the root node is true).
 * Some of the transfer functions are approximations (they're marked with comments).
 */

#ifndef UNSIGNEDINTERVALANALYSIS_H_
#define UNSIGNEDINTERVALANALYSIS_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include <map>

namespace stp
{
using std::make_pair;

// Shared with NodeDomainAnalysis and StrengthReduction (this header is the
// lowest in the include order, so the type lives here). Flat map: probed per
// node visit, iterated only for order-independent cleanup.
using NodeToUnsignedIntervalMap =
    ankerl::unordered_dense::map<ASTNode, UnsignedInterval*,
                                 ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;

class UnsignedIntervalAnalysis
{
  STPMgr& bm;
  CBV littleOne;
  CBV littleZero;

  unsigned propagatorNotImplemented = 0;
  unsigned iterations = 0;

  UnsignedInterval* freshUnsignedInterval(unsigned width);
  UnsignedInterval* getEmptyInterval(const ASTNode& n);

  // The caller owns the returned interval.
  UnsignedInterval* createInterval(CBV min, CBV max);

  CBV getEmptyCBV(unsigned width);

  std::unordered_map<unsigned, UnsignedInterval*> emptyIntervals;
  std::unordered_map<unsigned, CBV> emptyCBV;

public:

  UnsignedIntervalAnalysis(STPMgr& _bm);
  
  UnsignedIntervalAnalysis(const UnsignedIntervalAnalysis&) = delete;
  UnsignedIntervalAnalysis & operator=(const UnsignedIntervalAnalysis&) = delete;
  
  ~UnsignedIntervalAnalysis();

  // Replace some of the things that unsigned intervals can figure out for us.

  UnsignedInterval* dispatchToTransferFunctions(const ASTNode&n, const vector<const UnsignedInterval*>& children);


  void stats();
};
}

#endif

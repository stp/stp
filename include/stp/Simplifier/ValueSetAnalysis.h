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
 * Computes the set of values a node can take, when that set is small.
 * The analysis is only bottom up (without assuming the root is true).
 * Most operations are handled by evaluating over the cartesian product
 * of the children's sets.
 */

#ifndef VALUESETANALYSIS_H_
#define VALUESETANALYSIS_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/ValueSet.h"

namespace stp
{

class ValueSetAnalysis
{
  STPMgr& bm;

  unsigned propagated = 0;
  unsigned widened = 0;

  // The most combinations of children's values that we'll evaluate.
  static const size_t PRODUCT_CAP =
      ValueSet::MAX_ELEMENTS * ValueSet::MAX_ELEMENTS;

  ValueSet* fresh(const ASTNode& n) const;
  ASTNode toNode(const ASTNode& child, const CBV member);
  static CBV toCBV(const ASTNode& evaluated);

public:
  ValueSetAnalysis(STPMgr& _bm) : bm(_bm) {}

  ValueSetAnalysis(const ValueSetAnalysis&) = delete;
  ValueSetAnalysis& operator=(const ValueSetAnalysis&) = delete;

  // The caller owns the result, which is nullptr when nothing is known.
  ValueSet* dispatchToTransferFunctions(const ASTNode& n,
                                        const vector<const ValueSet*>& children);

  // Whether the constant evaluator handles the kind.
  static bool constEvaluable(Kind k);

  void stats();
};
}

#endif

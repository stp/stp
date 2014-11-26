/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: November, 2010
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

#ifndef CONSTANTBITPROPAGATION_TRANSFERFUNCTIONS_H_
#define CONSTANTBITPROPAGATION_TRANSFERFUNCTIONS_H_

#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
namespace simplifier
{
namespace constantBitP
{
struct MultiplicationStats;

// Multiply is not yet  maximally precise.
//!!!!!!!
Result bvMultiplyBothWays(vector<FixedBits*>& children, FixedBits& output,
                          BEEV::STPMgr* bm, MultiplicationStats* ms = NULL);
Result bvUnsignedDivisionBothWays(vector<FixedBits*>& children,
                                  FixedBits& output, BEEV::STPMgr* bm);
Result bvUnsignedModulusBothWays(vector<FixedBits*>& children,
                                 FixedBits& output, BEEV::STPMgr* bm);
Result bvSignedDivisionBothWays(vector<FixedBits*>& children, FixedBits& output,
                                BEEV::STPMgr* bm);
Result bvSignedRemainderBothWays(vector<FixedBits*>& children,
                                 FixedBits& output, BEEV::STPMgr* bm);
Result bvSignedModulusBothWays(vector<FixedBits*>& children, FixedBits& output,
                               BEEV::STPMgr* bm);
//!!!!!!!

// BOTH WAY FUNCTIONS..-------MAXIMALLY PRECISE..........
Result bvEqualsBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvAndBothWays(vector<FixedBits*>& operands, FixedBits& output);

Result bvOrBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvXorBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvImpliesBothWays(vector<FixedBits*>& children, FixedBits& result);

Result bvAddBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvSubtractBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvNotBothWays(FixedBits& a, FixedBits& output);
Result bvNotBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvITEBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvExtractBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvConcatBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvSignExtendBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvZeroExtendBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvUnaryMinusBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvLeftShiftBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvRightShiftBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvArithmeticRightShiftBothWays(vector<FixedBits*>& children,
                                      FixedBits& output);

// FOUR signed operations.
Result bvSignedGreaterThanBothWays(vector<FixedBits*>& children,
                                   FixedBits& output);

Result bvSignedLessThanBothWays(vector<FixedBits*>& children,
                                FixedBits& output);

Result bvSignedLessThanEqualsBothWays(vector<FixedBits*>& children,
                                      FixedBits& output);

Result bvSignedGreaterThanEqualsBothWays(vector<FixedBits*>& children,
                                         FixedBits& output);

// FOUR unsigned operations.

Result bvLessThanBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvLessThanBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output);

Result bvLessThanEqualsBothWays(vector<FixedBits*>& children,
                                FixedBits& output);

Result bvGreaterThanBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvGreaterThanEqualsBothWays(vector<FixedBits*>& children,
                                   FixedBits& output);
}
}

#endif /* CONSTANTBITPROPAGATION_TRANSFERFUNCTIONS_H_ */

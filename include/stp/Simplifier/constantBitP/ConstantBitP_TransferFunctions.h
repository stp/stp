/********************************************************************
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
using std::vector;

// Multiply is not yet  maximally precise.
//!!!!!!!
DLL_PUBLIC Result bvMultiplyBothWays(vector<FixedBits*>& children, FixedBits& output,
                          stp::STPMgr* bm, MultiplicationStats* ms = NULL);
DLL_PUBLIC Result bvUnsignedDivisionBothWays(vector<FixedBits*>& children,
                                  FixedBits& output, stp::STPMgr* bm);
DLL_PUBLIC Result bvUnsignedModulusBothWays(vector<FixedBits*>& children,
                                 FixedBits& output, stp::STPMgr* bm);
DLL_PUBLIC Result bvSignedDivisionBothWays(vector<FixedBits*>& children, FixedBits& output,
                                stp::STPMgr* bm);
DLL_PUBLIC Result bvSignedRemainderBothWays(vector<FixedBits*>& children,
                                 FixedBits& output, stp::STPMgr* bm);
DLL_PUBLIC Result bvSignedModulusBothWays(vector<FixedBits*>& children, FixedBits& output,
                               stp::STPMgr* bm);
//!!!!!!!

// BOTH WAY FUNCTIONS..-------MAXIMALLY PRECISE..........
DLL_PUBLIC Result bvEqualsBothWays(vector<FixedBits*>& children, FixedBits& output);

DLL_PUBLIC Result bvAndBothWays(vector<FixedBits*>& operands, FixedBits& output);

DLL_PUBLIC Result bvOrBothWays(vector<FixedBits*>& children, FixedBits& output);
DLL_PUBLIC Result bvXorBothWays(vector<FixedBits*>& children, FixedBits& output);

DLL_PUBLIC Result bvImpliesBothWays(vector<FixedBits*>& children, FixedBits& Result);

DLL_PUBLIC Result bvAddBothWays(vector<FixedBits*>& children, FixedBits& output);
DLL_PUBLIC Result bvSubtractBothWays(vector<FixedBits*>& children, FixedBits& output);

DLL_PUBLIC Result bvNotBothWays(FixedBits& a, FixedBits& output);
DLL_PUBLIC Result bvNotBothWays(vector<FixedBits*>& children, FixedBits& output);

DLL_PUBLIC Result bvITEBothWays(vector<FixedBits*>& children, FixedBits& output);

DLL_PUBLIC Result bvExtractBothWays(vector<FixedBits*>& children, FixedBits& output);

DLL_PUBLIC Result bvConcatBothWays(vector<FixedBits*>& children, FixedBits& output);

DLL_PUBLIC Result bvSignExtendBothWays(vector<FixedBits*>& children, FixedBits& output);
DLL_PUBLIC Result bvZeroExtendBothWays(vector<FixedBits*>& children, FixedBits& output);

DLL_PUBLIC Result bvUnaryMinusBothWays(vector<FixedBits*>& children, FixedBits& output);

DLL_PUBLIC Result bvLeftShiftBothWays(vector<FixedBits*>& children, FixedBits& output);
DLL_PUBLIC Result bvRightShiftBothWays(vector<FixedBits*>& children, FixedBits& output);
DLL_PUBLIC Result bvArithmeticRightShiftBothWays(vector<FixedBits*>& children,
                                      FixedBits& output);

// FOUR signed operations.
DLL_PUBLIC Result bvSignedGreaterThanBothWays(vector<FixedBits*>& children,
                                   FixedBits& output);

DLL_PUBLIC Result bvSignedLessThanBothWays(vector<FixedBits*>& children,
                                FixedBits& output);

DLL_PUBLIC Result bvSignedLessThanEqualsBothWays(vector<FixedBits*>& children,
                                      FixedBits& output);

DLL_PUBLIC Result bvSignedGreaterThanEqualsBothWays(vector<FixedBits*>& children,
                                         FixedBits& output);

// FOUR unsigned operations.

DLL_PUBLIC Result bvLessThanBothWays(vector<FixedBits*>& children, FixedBits& output);
DLL_PUBLIC Result bvLessThanBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output);

DLL_PUBLIC Result bvLessThanEqualsBothWays(vector<FixedBits*>& children,
                                FixedBits& output);

DLL_PUBLIC Result bvGreaterThanBothWays(vector<FixedBits*>& children, FixedBits& output);

DLL_PUBLIC Result bvGreaterThanEqualsBothWays(vector<FixedBits*>& children,
                                   FixedBits& output);
}
}

#endif /* CONSTANTBITPROPAGATION_TRANSFERFUNCTIONS_H_ */

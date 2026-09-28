/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Jul 5, 2010
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

#ifndef CONSTANTBITP_UTILITY_H_
#define CONSTANTBITP_UTILITY_H_

#include "ConstantBitPropagation.h"

// Utility functions for use by the transfer functions.
// This should only be included by files defining transfer functions.

namespace simplifier
{
namespace constantBitP
{

Result makeEqual(FixedBits& a, FixedBits& b, unsigned from, unsigned to);
void setUnsignedMinMax(const FixedBits& v, stp::CBV min, stp::CBV max);

struct stats
{
  unsigned fixedToZero;
  unsigned fixedToOne;
  unsigned unfixed;
};

Result merge(Result r1, Result r2);

stats getStats(const vector<FixedBits*>& operands, const unsigned position);

// True when one FixedBits feeds more than one operand slot. The propagator
// holds one FixedBits per node, so a node that repeats a child hands the
// transfer function the same pointer twice: ((_ repeat 2) x) is
// BVCONCAT(x, x), and the hashing node factory builds BVPLUS(x, x) and
// friends. A write through one slot is then already visible through the
// others, which a single left-to-right pass does not expect.
bool operandsAlias(const vector<FixedBits*>& operands);

// Fixed bits over the operands and the output. Aliased operands are counted
// once per slot; that is fine, because this only ever detects that something
// became fixed, and fixing is monotone.
unsigned totalFixedBits(const vector<FixedBits*>& operands,
                        const FixedBits& output);
}
}

#endif

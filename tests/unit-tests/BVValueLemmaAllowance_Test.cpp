/***********
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
**********************/

// How many blocking lemmas one abstracted multiplication, division or
// remainder gets before the refinement gives up on it.
//
// It can be one number for every width, and it can be a rate. The argument
// for the rate is that a blocking lemma rules out one pair of operand values
// out of 2^(2W), so thirty-two of them is a third of an eight-bit operand's
// pairs and one part in 2^101 of a fifty-three-bit one's: the same allowance
// means "enumerate a good deal of it" at one end and "enumerate none of it"
// at the other.
//
// It is off by default all the same, because the argument did not survive
// measurement -- see bv_term_abstraction_value_divisor for the numbers.
// What is pinned here is the arithmetic of both, since the flag exists for
// whoever can show the rate paying on a workload this one does not cover.
//
// Every spelling the ceiling had still means what it meant, which is the
// point of adding the divisor beside it rather than redefining the one
// number: zero still never escalates, an explicit count still caps, and the
// default divisor leaves the flat allowance exactly as it was.
#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/ToSat/BVAbstractionRefiner.h"

#include <gtest/gtest.h>

using namespace stp;

namespace
{

unsigned allowance(unsigned ceiling, unsigned divisor, unsigned width)
{
  UserDefinedFlags uf;
  uf.bv_term_abstraction_rounds = ceiling;
  uf.bv_term_abstraction_value_divisor = divisor;
  return valueLemmaAllowance(uf, width);
}

} // namespace

// The default is the flat allowance, at every width, and the rate is what a
// caller opts into.
TEST(bv_value_lemma_allowance, TheDefaultIsFlat)
{
  UserDefinedFlags defaults;
  EXPECT_EQ(32u, defaults.bv_term_abstraction_rounds);
  EXPECT_EQ(0u, defaults.bv_term_abstraction_value_divisor);

  for (unsigned width : {8u, 16u, 24u, 33u, 53u, 64u})
    EXPECT_EQ(32u, valueLemmaAllowance(defaults, width)) << "width=" << width;
}

// What the rate gives when it is asked for, across the widths that actually
// turn up: 32-bit and 64-bit machine words, and the 53-bit significand
// product of a binary64 fp.mul.
TEST(bv_value_lemma_allowance, TheRateScalesWithTheWidthWhenAskedFor)
{
  EXPECT_EQ(2u, allowance(32, 8, 16));
  EXPECT_EQ(4u, allowance(32, 8, 32));
  EXPECT_EQ(6u, allowance(32, 8, 53));
  EXPECT_EQ(8u, allowance(32, 8, 64));
}

// The ceiling still caps, which is what keeps an explicit --rounds meaning
// what it says at every width. Without it a 4096-bit operand would be given
// 512 attempts, and the measurement that put the crossover near thirty says
// it collapses well before then.
TEST(bv_value_lemma_allowance, TheCeilingStillCaps)
{
  EXPECT_EQ(32u, allowance(32, 8, 256));
  EXPECT_EQ(32u, allowance(32, 8, 4096));
  EXPECT_EQ(3u, allowance(3, 8, 4096));
  EXPECT_EQ(1u, allowance(1, 8, 64));
}

// Never escalating is a statement about the mechanism, not about how many,
// so it survives the scaling untouched at every width.
TEST(bv_value_lemma_allowance, ZeroStillNeverEscalates)
{
  for (unsigned width : {1u, 8u, 53u, 64u, 4096u})
  {
    EXPECT_EQ(0u, allowance(0, 8, width));
    EXPECT_EQ(0u, allowance(0, 0, width));
    EXPECT_EQ(0u, allowance(0, 1, width));
  }
}

// A divisor of zero is exactly the flat allowance, which is what makes the
// two configurations comparable: measuring whether the rate helps means
// being able to ask for the thing it would replace, in the same binary and
// on the same query.
TEST(bv_value_lemma_allowance, ADivisorOfZeroIsTheFlatAllowance)
{
  for (unsigned width : {1u, 8u, 53u, 64u, 4096u})
  {
    EXPECT_EQ(32u, allowance(32, 0, width));
    EXPECT_EQ(7u, allowance(7, 0, width));
  }
}

// A rate that rounds to nothing still buys one attempt. Escalating before
// the abstraction has had a single chance to pay is not what "scale it with
// the width" means at narrow widths -- and it would make the abstraction
// strictly worse than not abstracting there, since the query would carry
// the proxy inputs and the round trip for no lemma at all.
TEST(bv_value_lemma_allowance, ANarrowOperandStillGetsOneAttempt)
{
  EXPECT_EQ(1u, allowance(32, 8, 1));
  EXPECT_EQ(1u, allowance(32, 8, 7));
  EXPECT_EQ(1u, allowance(32, 64, 63));
  EXPECT_EQ(1u, allowance(32, 4096, 64));
}

// It is monotone in every argument, which is the property a knob has to
// have to be usable: widening the operands or lowering the divisor never
// buys fewer attempts, and raising the ceiling never buys fewer either.
TEST(bv_value_lemma_allowance, ItIsMonotoneInEveryArgument)
{
  for (unsigned width = 1; width <= 128; ++width)
  {
    EXPECT_LE(allowance(32, 8, width), allowance(32, 8, width + 1));
    EXPECT_LE(allowance(32, 8, width), allowance(32, 4, width));
    EXPECT_LE(allowance(8, 8, width), allowance(16, 8, width));
  }
}

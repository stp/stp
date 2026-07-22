/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Dan Liew
 *
 * BEGIN DATE: November, 2005
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

#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_Utility.h"
// FIXME: External library
#include "extlib-constbv/constantbv.h"

// The signed and unsigned versions of the four comparison operations: > < >= <=

// Establishes consistency over the intervals of the operations. Then
// increase the minimum value by turning on the highest unfixed bit.
// If that takes us past the other value's maximum. Then that bit
// must be zero.

// Trevor Hansen. BSD License.

namespace simplifier
{
namespace constantBitP
{

Result bvSignedLessThanBothWays(FixedBits& c0, FixedBits& c1,
                                FixedBits& output);
Result bvSignedLessThanEqualsBothWays(FixedBits& c0, FixedBits& c1,
                                      FixedBits& output);

Result bvSignedLessThanBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 2);
  return bvSignedLessThanBothWays(*children[0], *children[1], output);
}

Result bvSignedGreaterThanBothWays(FixedBits& c0, FixedBits& c1,
                                   FixedBits& output)
{
  return bvSignedLessThanBothWays(c1, c0, output);
}

Result bvSignedGreaterThanBothWays(vector<FixedBits*>& children,
                                   FixedBits& output)
{
  assert(children.size() == 2);
  return bvSignedLessThanBothWays(*children[1], *children[0], output);
}

Result bvSignedLessThanEqualsBothWays(vector<FixedBits*>& children,
                                      FixedBits& output)
{
  assert(children.size() == 2);
  return bvSignedLessThanEqualsBothWays(*children[0], *children[1], output);
}

Result bvSignedGreaterThanEqualsBothWays(FixedBits& c0, FixedBits& c1,
                                         FixedBits& output)
{
  return bvSignedLessThanEqualsBothWays(c1, c0, output);
}

Result bvSignedGreaterThanEqualsBothWays(vector<FixedBits*>& children,
                                         FixedBits& output)
{
  assert(children.size() == 2);
  return bvSignedLessThanEqualsBothWays(*children[1], *children[0], output);
}

///////// UNSIGNED.

Result bvLessThanBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output);
Result bvLessThanEqualsBothWays(FixedBits& c0, FixedBits& c1,
                                FixedBits& output);

Result bvLessThanBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 2);
  return bvLessThanBothWays(*children[0], *children[1], output);
}

Result bvGreaterThanBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 2);
  return bvLessThanBothWays(*children[1], *children[0], output);
}

Result bvGreaterThanBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output)
{
  return bvLessThanBothWays(c1, c0, output);
}

Result bvGreaterThanEqualsBothWays(vector<FixedBits*>& children,
                                   FixedBits& result)
{
  assert(children.size() == 2);
  return bvLessThanEqualsBothWays(*children[1], *children[0], result);
}

Result bvGreaterThanEqualsBothWays(FixedBits& c0, FixedBits& c1,
                                   FixedBits& output)
{
  return bvLessThanEqualsBothWays(c1, c0, output);
}

Result bvLessThanEqualsBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 2);
  return bvLessThanEqualsBothWays(*children[0], *children[1], output);
}

typedef unsigned int* CBV;

// Scalar fast path for widths that fit in a machine word. Signed
// comparisons are mapped onto unsigned ones by XORing the sign bit
// ("biasing"): x <=s y iff (x ^ msb) <=u (y ^ msb). In the biased domain
// the MSB behaves like every other bit, so the special sign-bit handling
// of the general-width code disappears.
namespace
{

// Fix bit i of `bits` to the biased value `biasedValue`.
void fixBit(FixedBits& bits, unsigned i, bool biasedValue, uint64_t bias)
{
  const bool real = ((bias >> i) & 1) ? !biasedValue : biasedValue;
  bits.setFixed(i, true);
  bits.setValue(i, real);
}

// Given that lhs <= rhs (or lhs < rhs when strict) holds, fix child bits.
// lhsMin is the biased minimum of lhs, rhsMax the biased maximum of rhs;
// neither changes as bits are fixed (fixing a lhs bit to zero keeps its
// minimum, fixing a rhs bit to one keeps its maximum).
bool fixTrueCase(FixedBits& lhs, uint64_t lhsFixed, uint64_t lhsMin,
                 FixedBits& rhs, uint64_t rhsFixed, uint64_t rhsMax,
                 bool strict, uint64_t bias, uint64_t mask)
{
  bool changed = false;

  // Highest unfixed bit first: if turning it on in the minimum overshoots
  // the other side's maximum, it must be zero. Once one bit can stay on,
  // no lower bit can overshoot either.
  uint64_t unfixed = ~lhsFixed & mask;
  while (unfixed != 0)
  {
    const unsigned i = 63 - __builtin_clzll(unfixed);
    const uint64_t bit = 1ULL << i;
    const uint64_t trial = lhsMin | bit;
    if (strict ? trial >= rhsMax : trial > rhsMax)
    {
      fixBit(lhs, i, false, bias);
      changed = true;
      unfixed &= ~bit;
    }
    else
      break;
  }

  // Mirrored for rhs: if turning the bit off in the maximum undershoots
  // the other side's minimum, it must be one.
  unfixed = ~rhsFixed & mask;
  while (unfixed != 0)
  {
    const unsigned i = 63 - __builtin_clzll(unfixed);
    const uint64_t bit = 1ULL << i;
    const uint64_t trial = rhsMax & ~bit;
    if (strict ? trial <= lhsMin : trial < lhsMin)
    {
      fixBit(rhs, i, true, bias);
      changed = true;
      unfixed &= ~bit;
    }
    else
      break;
  }

  return changed;
}

// c0 < c1 (strict) or c0 <= c1; signed comparisons set a sign-flipping bias.
Result scalarCompare(FixedBits& c0, FixedBits& c1, FixedBits& output,
                     bool strict, bool isSigned)
{
  const unsigned width = c0.getWidth();
  assert(width <= 64 && c1.getWidth() == width);

  const uint64_t mask = (width == 64) ? ~0ULL : ((1ULL << width) - 1);
  const uint64_t bias = isSigned ? (1ULL << (width - 1)) : 0;

  uint64_t f0, v0, f1, v1;
  c0.fillPackedWords(&f0, &v0);
  c1.fillPackedWords(&f1, &v1);
  v0 ^= f0 & bias;
  v1 ^= f1 & bias;

  const uint64_t min0 = v0, max0 = v0 | (~f0 & mask);
  const uint64_t min1 = v1, max1 = v1 | (~f1 & mask);

  bool changed = false;

  // Entailed true: every value of c0 is below every value of c1.
  if (strict ? max0 < min1 : max0 <= min1)
  {
    if (output.isFixed(0) && !output.getValue(0))
      return CONFLICT;
    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, true);
      changed = true;
    }
  }

  // Entailed false: no value of c0 is below any value of c1.
  if (strict ? min0 >= max1 : min0 > max1)
  {
    if (output.isFixed(0) && output.getValue(0))
      return CONFLICT;
    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, false);
      changed = true;
    }
  }

  if (output.isFixed(0))
  {
    if (output.getValue(0))
      changed |= fixTrueCase(c0, f0, min0, c1, f1, max1, strict, bias, mask);
    else
      // !(c0 < c1) is c1 <= c0, and !(c0 <= c1) is c1 < c0.
      changed |= fixTrueCase(c1, f1, min1, c0, f0, max0, !strict, bias, mask);
  }

  return changed ? CHANGED : NO_CHANGE;
}
}

void destroy(CBV a, CBV b, CBV c, CBV d)
{
  CONSTANTBV::BitVector_Destroy(a);
  CONSTANTBV::BitVector_Destroy(b);
  CONSTANTBV::BitVector_Destroy(c);
  CONSTANTBV::BitVector_Destroy(d);
}

// Fast exit. Without creating min/max.
bool fast_exit(FixedBits& c0, FixedBits& c1)
{
  assert(c0.getWidth() == c1.getWidth());
  for (int i = (int)c0.getWidth() - 1; i >= 0; i--)
  {
    const char c_0 = c0[i];
    const char c_1 = c1[i];

    if (c_0 == '0')
    {
      if (c_1 == '0')
      {
        continue;
      }
      return false;
    }

    if (c_0 == '1')
    {
      if (c_1 == '1')
      {
        continue;
      }
      return false;
    }

    if (c_0 == '*' && c_1 == '*')
    {
      return true;
    }

    return false;
  }
  return false;
}

// Convert the before/after count of fixed bits into a Result. Transfer
// functions only ever fix extra bits, so an unchanged count means nothing
// was altered. The propagation loop trusts NO_CHANGE and skips rescheduling,
// so it must only be returned when that is really so.
Result fixedCountToResult(const unsigned before, const FixedBits& c0,
                          const FixedBits& c1, const FixedBits& output)
{
  const unsigned now = c0.countFixed() + c1.countFixed() + output.countFixed();
  assert(now >= before);
  return (now == before) ? NO_CHANGE : CHANGED;
}

///////// Signed operations.

Result bvSignedLessThanBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output)
{
  assert(c0.getWidth() == c1.getWidth());

  if (!output.isFixed(0) && fast_exit(c0, c1))
    return NO_CHANGE;

  if (c0.getWidth() <= 64)
    return scalarCompare(c0, c1, output, true, true);

  const unsigned initialFixedCount =
      c0.countFixed() + c1.countFixed() + output.countFixed();

  CBV c0_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c0_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c1_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c1_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);

  setSignedMinMax(c0, c0_min, c0_max);
  setSignedMinMax(c1, c1_min, c1_max);

  // EG. [0,5] < [6,8]. i.e. max of first is less than min of second.
  if (signedCompare(c0_max, c1_min) < 0)
  {
    if (output.isFixed(0) && !output.getValue(0)) // output is fixed to false.
    {
      destroy(c0_min, c0_max, c1_min, c1_max);
      return CONFLICT;
    }

    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, true);
    }
  }

  // EG. [3,5] < [0,1].
  if (signedCompare(c0_min, c1_max) >= 0)
  {
    // min is greater than max.
    if (output.isFixed(0) && output.getValue(0))
    {
      destroy(c0_min, c0_max, c1_min, c1_max);
      return CONFLICT;
    }

    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, false);
    }
  }

  if (output.isFixed(0) && !output.getValue(0))
  {
    FixedBits t(1, true);
    t.setFixed(0, true);
    t.setValue(0, true);
    destroy(c0_min, c0_max, c1_min, c1_max);
    return merge(bvSignedGreaterThanEqualsBothWays(c0, c1, t),
                 fixedCountToResult(initialFixedCount, c0, c1, output));
  }

  const int msb = c0.getWidth() - 1;

  // The signed case.
  if (output.isFixed(0) && output.getValue(0))
  {
    //////////// MSB
    // turn off the sign bit of c0's minimum.
    // If that value is greater or equal to c1's max. SEt it.
    if (!c0.isFixed(msb))
    {
      // turn it on in the minimum.
      CONSTANTBV::BitVector_Bit_Off(c0_min, msb);
      if (signedCompare(c0_min, c1_max) >= 0)
      {
        c0.setFixed(msb, true);
        c0.setValue(msb, true);
        setSignedMinMax(c0, c0_min, c0_max);
      }
      else
      {
        CONSTANTBV::BitVector_Bit_On(c0_min, msb);
      }
    }

    if (!c1.isFixed(msb))
    {
      CONSTANTBV::BitVector_Bit_On(c1_max, msb);
      if (signedCompare(c1_max, c0_min) <= 0)
      {
        c1.setFixed(msb, true);
        c1.setValue(msb, false);
        setSignedMinMax(c1, c1_min, c1_max);
      }
      else
      {
        CONSTANTBV::BitVector_Bit_Off(c1_max, msb);
      }
    }

    ///////////// Bits other than the MSB

    if (output.isFixed(0) && output.getValue(0))
    {
      for (int i = (int)c0.getWidth() - 1 - 1; i >= 0; i--)
      {
        if (!c0.isFixed(i))
        {
          // turn it on in the minimum.
          CONSTANTBV::BitVector_Bit_On(c0_min, i);
          if (signedCompare(c0_min, c1_max) >= 0)
          {
            c0.setFixed(i, true);
            c0.setValue(i, false);
            setSignedMinMax(c0, c0_min, c0_max);
          }
          else
          {
            CONSTANTBV::BitVector_Bit_Off(c0_min, i);
            break;
          }
        }
      }

      for (int i = (int)c1.getWidth() - 1 - 1; i >= 0; i--)
      {
        if (!c1.isFixed(i))
        {
          CONSTANTBV::BitVector_Bit_Off(c1_max, i);
          if (signedCompare(c1_max, c0_min) <= 0)
          {
            c1.setFixed(i, true);
            c1.setValue(i, true);
            setSignedMinMax(c1, c1_min, c1_max);
          }
          else
          {
            CONSTANTBV::BitVector_Bit_On(c1_max, i);
            break;
          }
        }
      }
    }
  }
  destroy(c0_min, c0_max, c1_min, c1_max);
  return fixedCountToResult(initialFixedCount, c0, c1, output);
}

Result bvSignedLessThanEqualsBothWays(FixedBits& c0, FixedBits& c1,
                                      FixedBits& output)
{
  assert(c0.getWidth() == c1.getWidth());

  if (!output.isFixed(0) && fast_exit(c0, c1))
    return NO_CHANGE;

  if (c0.getWidth() <= 64)
    return scalarCompare(c0, c1, output, false, true);

  const unsigned initialFixedCount =
      c0.countFixed() + c1.countFixed() + output.countFixed();

  CBV c0_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c0_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c1_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c1_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);

  setSignedMinMax(c0, c0_min, c0_max);
  setSignedMinMax(c1, c1_min, c1_max);

  if (signedCompare(c0_max, c1_min) <= 0)
  {
    if (output.isFixed(0) && !output.getValue(0))
    {
      destroy(c0_min, c0_max, c1_min, c1_max);
      return CONFLICT;
    }

    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, true);
    }
  }

  if (signedCompare(c0_min, c1_max) > 0)
  {
    if (output.isFixed(0) && output.getValue(0))
    {
      destroy(c0_min, c0_max, c1_min, c1_max);
      return CONFLICT;
    }

    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, false);
    }
  }

  // If true. Reverse and send to the other..
  if (output.isFixed(0) && !output.getValue(0))
  {
    FixedBits t(1, true);
    t.setFixed(0, true);
    t.setValue(0, true);
    destroy(c0_min, c0_max, c1_min, c1_max);
    return merge(bvSignedGreaterThanBothWays(c0, c1, t),
                 fixedCountToResult(initialFixedCount, c0, c1, output));
  }

  const int msb = c0.getWidth() - 1;

  if (output.isFixed(0) && output.getValue(0))
  {
    //////////// MSB
    // turn off the sign bit of c0's minimum.
    // If that value is greater or equal to c1's max. SEt it.
    if (!c0.isFixed(msb))
    {
      // turn it on in the minimum.
      CONSTANTBV::BitVector_Bit_Off(c0_min, msb);
      if (signedCompare(c0_min, c1_max) > 0)
      {
        c0.setFixed(msb, true);
        c0.setValue(msb, true);
        setSignedMinMax(c0, c0_min, c0_max);
      }
      else
      {
        CONSTANTBV::BitVector_Bit_On(c0_min, msb);
      }
    }

    if (!c1.isFixed(msb))
    {
      CONSTANTBV::BitVector_Bit_On(c1_max, msb);
      if (signedCompare(c1_max, c0_min) < 0)
      {
        c1.setFixed(msb, true);
        c1.setValue(msb, false);
        setSignedMinMax(c1, c1_min, c1_max);
      }
      else
      {
        CONSTANTBV::BitVector_Bit_Off(c1_max, msb);
      }
    }
    //////////// Others.

    // Starting from the high order. Turn on each bit in turn. If it being
    // turned on pushes it past the max of the other side
    // then we know it must be turned off.
    for (int i = (int)c0.getWidth() - 1 - 1; i >= 0; i--)
    {
      if (!c0.isFixed(i)) // bit is variable.
      {
        // turn it on in the minimum.
        CONSTANTBV::BitVector_Bit_On(c0_min, i);
        if (signedCompare(c0_min, c1_max) > 0)
        {
          c0.setFixed(i, true);
          c0.setValue(i, false);
          setSignedMinMax(c0, c0_min, c0_max);
        }
        else
        {
          CONSTANTBV::BitVector_Bit_Off(c0_min, i);
          break;
        }
      }
    }

    // Starting from the high order. Turn on each bit in turn. If it being
    // turned on pushes it past the max of the other side
    // then we know it must be turned off.
    for (int i = (int)c0.getWidth() - 1 - 1; i >= 0; i--)
    {
      if (!c1.isFixed(i)) // bit is variable.
      {
        // turn it on in the minimum.
        CONSTANTBV::BitVector_Bit_Off(c1_max, i);
        if (signedCompare(c1_max, c0_min) < 0)
        {
          c1.setFixed(i, true);
          c1.setValue(i, true);
          setSignedMinMax(c1, c1_min, c1_max);
        }
        else
        {
          CONSTANTBV::BitVector_Bit_On(c1_max, i);
          break;
        }
      }
    }
  }

  destroy(c0_min, c0_max, c1_min, c1_max);
  return fixedCountToResult(initialFixedCount, c0, c1, output);
}

///////////////////////// UNSIGNED.

// UNSIGNED!!
Result bvLessThanBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output)
{
  assert(c0.getWidth() == c1.getWidth());

  if (!output.isFixed(0) && fast_exit(c0, c1))
    return NO_CHANGE;

  if (c0.getWidth() <= 64)
    return scalarCompare(c0, c1, output, true, false);

  const unsigned initialFixedCount =
      c0.countFixed() + c1.countFixed() + output.countFixed();

  CBV c0_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c0_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c1_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c1_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);

  setUnsignedMinMax(c0, c0_min, c0_max);
  setUnsignedMinMax(c1, c1_min, c1_max);

  // EG. [0,5] < [6,8]. i.e. max of first is less than min of second.
  if (unsignedCompare(c0_max, c1_min) < 0)
  {
    if (output.isFixed(0) && !output.getValue(0)) // output is fixed to false.
    {
      destroy(c0_min, c0_max, c1_min, c1_max);
      return CONFLICT;
    }

    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, true);
    }
  }

  // EG. [3,5] < [0,1].
  if (unsignedCompare(c0_min, c1_max) >= 0)
  {
    // min is greater than max.
    if (output.isFixed(0) && output.getValue(0))
    {
      destroy(c0_min, c0_max, c1_min, c1_max);
      return CONFLICT;
    }

    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, false);
    }
  }

  // If true. Reverse and send to the other.
  if (output.isFixed(0) && !output.getValue(0))
  {
    FixedBits t(1, true);
    t.setFixed(0, true);
    t.setValue(0, true);
    destroy(c0_min, c0_max, c1_min, c1_max);
    return merge(bvGreaterThanEqualsBothWays(c0, c1, t),
                 fixedCountToResult(initialFixedCount, c0, c1, output));
  }

  if (output.isFixed(0) && output.getValue(0))
  {
    // Starting from the high order. Turn on each bit in turn. If it being
    // turned on pushes it past the max of the other side
    // then we know it must be turned off.
    for (int i = (int)c0.getWidth() - 1; i >= 0; i--)
    {
      if (!c0.isFixed(i)) // bit is variable.
      {
        // turn it on in the minimum.
        CONSTANTBV::BitVector_Bit_On(c0_min, i);
        if (unsignedCompare(c0_min, c1_max) >= 0)
        {
          c0.setFixed(i, true);
          c0.setValue(i, false);
          setUnsignedMinMax(c0, c0_min, c0_max);
        }
        else
        {
          CONSTANTBV::BitVector_Bit_Off(c0_min, i);
          break;
        }
      }
    }

    for (int i = (int)c1.getWidth() - 1; i >= 0; i--)
    {
      if (!c1.isFixed(i)) // bit is variable.
      {
        CONSTANTBV::BitVector_Bit_Off(c1_max, i);
        if (unsignedCompare(c1_max, c0_min) <= 0)
        {
          c1.setFixed(i, true);
          c1.setValue(i, true);
          setUnsignedMinMax(c1, c1_min, c1_max);
        }
        else
        {
          CONSTANTBV::BitVector_Bit_On(c1_max, i);
          break;
        }
      }
    }
  }

  destroy(c0_min, c0_max, c1_min, c1_max);
  return fixedCountToResult(initialFixedCount, c0, c1, output);
}

Result bvLessThanEqualsBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output)
{
  assert(c0.getWidth() == c1.getWidth());

  if (!output.isFixed(0) && fast_exit(c0, c1))
    return NO_CHANGE;

  if (c0.getWidth() <= 64)
    return scalarCompare(c0, c1, output, false, false);

  const unsigned initialFixedCount =
      c0.countFixed() + c1.countFixed() + output.countFixed();

  CBV c0_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c0_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c1_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
  CBV c1_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);

  setUnsignedMinMax(c0, c0_min, c0_max);
  setUnsignedMinMax(c1, c1_min, c1_max);

  // EG. [0,5] <= [6,8]. i.e. max of first is less than min of second.
  if (unsignedCompare(c0_max, c1_min) <= 0)
  {
    if (output.isFixed(0) && !output.getValue(0)) // output is fixed to false.
    {
      destroy(c0_min, c0_max, c1_min, c1_max);
      return CONFLICT;
    }

    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, true);
    }
  }

  // EG. [3,5] <= [0,1].
  if (unsignedCompare(c0_min, c1_max) > 0)
  {
    if (output.isFixed(0) && output.getValue(0))
    {
      destroy(c0_min, c0_max, c1_min, c1_max);
      return CONFLICT;
    }

    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, false);
    }
  }

  // If true. Reverse and send to the other..
  if (output.isFixed(0) && !output.getValue(0))
  {
    FixedBits t(1, true);
    t.setFixed(0, true);
    t.setValue(0, true);
    destroy(c0_min, c0_max, c1_min, c1_max);
    return merge(bvGreaterThanBothWays(c0, c1, t),
                 fixedCountToResult(initialFixedCount, c0, c1, output));
  }

  // We only deal with the true case in this function.

  if (output.isFixed(0) && output.getValue(0))
  {
    // Starting from the high order. Turn on each bit in turn. If it being
    // turned on pushes it past the max of the other side
    // then we know it must be turned off.
    for (int i = (int)c0.getWidth() - 1; i >= 0; i--)
    {
      if (!c0.isFixed(i)) // bit is variable.
      {
        // turn it on in the minimum.
        CONSTANTBV::BitVector_Bit_On(c0_min, i);
        if (unsignedCompare(c0_min, c1_max) > 0)
        {
          c0.setFixed(i, true);
          c0.setValue(i, false);
          setUnsignedMinMax(c0, c0_min, c0_max);
        }
        else
        {
          CONSTANTBV::BitVector_Bit_Off(c0_min, i);
          break;
        }
      }
    }

    // Starting from the high order. Turn on each bit in turn. If it being
    // turned on pushes it past the max of the other side
    // then we know it must be turned off.
    for (int i = c0.getWidth() - 1; i >= 0; i--)
    {
      if (!c1.isFixed(i)) // bit is variable.
      {
        // turn it on in the minimum.
        CONSTANTBV::BitVector_Bit_Off(c1_max, i);
        if (unsignedCompare(c1_max, c0_min) < 0)
        {
          c1.setFixed(i, true);
          c1.setValue(i, true);
          setUnsignedMinMax(c1, c1_min, c1_max);
        }
        else
        {
          CONSTANTBV::BitVector_Bit_On(c1_max, i);
          break;
        }
      }
    }
  }
  destroy(c0_min, c0_max, c1_min, c1_max);
  return fixedCountToResult(initialFixedCount, c0, c1, output);
}
}
}

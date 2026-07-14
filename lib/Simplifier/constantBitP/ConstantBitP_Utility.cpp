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

#include "stp/Simplifier/constantBitP/ConstantBitP_Utility.h"
#include "extlib-constbv/constantbv.h"
#include "stp/Util/Attributes.h"
#include <vector>

// Utility functions used by the transfer functions.

using std::vector;

namespace stp
{
typedef unsigned int* CBV;
DLL_PUBLIC ATTR_NORETURN void FatalError(const char* str);
}

namespace simplifier
{
namespace constantBitP
{

using stp::CBV;

// Find ALL the unfixed values in the column and fix it to the specified value.
void fixUnfixedTo(vector<FixedBits*>& operands, const unsigned position,
                  bool toFix)
{
  for (unsigned i = 0; i < operands.size(); i++)
  {
    if (!operands[i]->isFixed(position))
    {
      operands[i]->setFixed(position, true);
      operands[i]->setValue(position, toFix);
    }
  }
}

// counts of how many of each in the column.
stats getStats(const vector<FixedBits*>& operands, const unsigned position)
{
  stats result = {0, 0, 0};

  for (unsigned i = 0, size = operands.size(); i < size; i++)
  {
    if (operands[i]->isFixed(position))
    {
      if (operands[i]->getValue(position)) // fixed to one.
        result.fixedToOne++;
      else
        result.fixedToZero++; // fixed to zero.
    }
    else
      result.unfixed++;
  }

  assert(result.fixedToOne + result.fixedToZero + result.unfixed ==
         operands.size());
  return result;
}

Result makeEqual(FixedBits& a, FixedBits& b, unsigned from, unsigned to)
{
  assert(to >= from);
  assert(from <= a.getWidth());
  assert(from <= b.getWidth());

  Result result = NO_CHANGE;
  for (unsigned i = from; i < to; i++)
  {
    if (a.isFixed(i) && !b.isFixed(i))
    {
      b.setFixed(i, true);
      b.setValue(i, a.getValue(i));
      result = CHANGED;
    }
    else if (b.isFixed(i) && !a.isFixed(i))
    {
      a.setFixed(i, true);
      a.setValue(i, b.getValue(i));
      result = CHANGED;
    }
    else if (b.isFixed(i) && a.isFixed(i))
    {
      if (a.getValue(i) != b.getValue(i))
        return CONFLICT;
    }
  }
  return result;
}

void setSignedMinMax(FixedBits& v, CBV min, CBV max)
{
  const unsigned int msb = v.getWidth() - 1;

  for (unsigned i = 0; i < (unsigned)v.getWidth(); i++)
  {
    if (v.isFixed(i))
    {
      if (v.getValue(i)) // if it's on. It's on.

      {
        CONSTANTBV::BitVector_Bit_On(max, i);
        CONSTANTBV::BitVector_Bit_On(min, i);
      }
      else
      {
        CONSTANTBV::BitVector_Bit_Off(max, i);
        CONSTANTBV::BitVector_Bit_Off(min, i);
      }
    }
    else
    {
      if (i != msb)
      { // not fixed. Make the maximum Maximum.
        CONSTANTBV::BitVector_Bit_On(max, i);
        CONSTANTBV::BitVector_Bit_Off(min, i);
      }
      else
      { // except for the msb. Where we reduce the min.
        CONSTANTBV::BitVector_Bit_On(min, i);
        CONSTANTBV::BitVector_Bit_Off(max, i);
      }
    }
  }
  assert(CONSTANTBV::BitVector_Compare(min, max) <= 0);
}

#ifndef NDEBUG
// The original per-bit implementation, kept as the reference that the
// block-store version is checked against in debug builds.
static void setUnsignedMinMax_reference(const FixedBits& v, CBV min, CBV max)
{
  CONSTANTBV::BitVector_Fill(max);
  CONSTANTBV::BitVector_Empty(min);

  for (unsigned i = 0; i < v.getWidth(); i++)
  {
    if (v.isFixed(i))
    {
      if (v.getValue(i))
        CONSTANTBV::BitVector_Bit_On(min, i);
      else
        CONSTANTBV::BitVector_Bit_Off(max, i);
    }
  }
}
#endif

void setUnsignedMinMax(const FixedBits& v, CBV min, CBV max)
{
  // The minimum admitted value has just the fixed ones; the maximum also
  // has every unfixed bit. Build byte buffers and block-store them: one
  // CONSTANTBV call per bitvector instead of one per bit. This runs in
  // the inner loops of the division and comparison propagators.
  const unsigned width = v.getWidth();
  const unsigned bytes = (width + 7) / 8;

  const unsigned STACK_BYTES = 128; // up to 1024 bits on the stack.
  unsigned char stackBuf[2 * STACK_BYTES];
  std::vector<unsigned char> heapBuf;
  unsigned char* minBuf = stackBuf;
  unsigned char* maxBuf = stackBuf + STACK_BYTES;
  if (bytes > STACK_BYTES)
  {
    heapBuf.resize(2 * bytes);
    minBuf = heapBuf.data();
    maxBuf = heapBuf.data() + bytes;
  }

  unsigned i = 0;
  for (unsigned byte = 0; byte < bytes; byte++)
  {
    unsigned char mn = 0, mx = 0;
    for (unsigned b = 0; b < 8 && i < width; b++, i++)
    {
      if (v.isFixed(i))
      {
        if (v.getValue(i))
        {
          mn |= 1 << b;
          mx |= 1 << b;
        }
      }
      else
        mx |= 1 << b;
    }
    minBuf[byte] = mn;
    maxBuf[byte] = mx;
  }

  CONSTANTBV::BitVector_Block_Store(min, minBuf, bytes);
  CONSTANTBV::BitVector_Block_Store(max, maxBuf, bytes);

#ifndef NDEBUG
  CBV refMin = CONSTANTBV::BitVector_Create(width, true);
  CBV refMax = CONSTANTBV::BitVector_Create(width, true);
  setUnsignedMinMax_reference(v, refMin, refMax);
  assert(CONSTANTBV::BitVector_equal(min, refMin));
  assert(CONSTANTBV::BitVector_equal(max, refMax));
  CONSTANTBV::BitVector_Destroy(refMin);
  CONSTANTBV::BitVector_Destroy(refMax);
#endif
  assert(CONSTANTBV::BitVector_Lexicompare(min, max) <= 0);
}

int unsignedCompare(const stp::CBV& lhs, const stp::CBV& rhs)
{
  /// NB: Uses the memory layout of the constant bit library to extract the
  /// bitwidth.
  // assert(*((unsigned *)&lhs-3) == *((unsigned *)&rhs-3));
  return CONSTANTBV::BitVector_Lexicompare(lhs, rhs);
}

int signedCompare(const stp::CBV& lhs, const stp::CBV& rhs)
{
  /// NB: Uses the memory layout of the constant bit library to extract the
  /// bitwidth.
  // assert(*((unsigned *)&lhs-3) == *((unsigned *)&rhs-3));
  return CONSTANTBV::BitVector_Compare(lhs, rhs);
}

Result merge(Result r1, Result r2)
{
  if (r1 == CONFLICT || r2 == CONFLICT)
    return CONFLICT;

  if (r1 == CHANGED || r2 == CHANGED)
    return CHANGED;

  if (r1 == NO_CHANGE && r2 == NO_CHANGE)
    return NO_CHANGE;

  return NOT_IMPLEMENTED;
}

int toInt(const stp::CBV value)
{
  return *((unsigned int*)value);
}
}
}

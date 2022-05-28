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
 * holds an unsigned interval.
 */

#ifndef UNSIGNEDINTERVAL_H_
#define UNSIGNEDINTERVAL_H_

#include "stp/AST/AST.h"
#include <iostream>

namespace stp
{

struct UnsignedInterval
{

  CBV minV;
  CBV maxV;
  
  // Takes ownership of the CBVs.
  UnsignedInterval(CBV _min, CBV _max)
  {
    minV = _min;
    maxV = _max;
    checkUnsignedInvariant();
  }

  UnsignedInterval(unsigned width)
  {
    minV = CONSTANTBV::BitVector_Create(width, true);
    maxV = CONSTANTBV::BitVector_Create(width, true);
    CONSTANTBV::BitVector_Fill(maxV);
  }

  ~UnsignedInterval()
  {
   CONSTANTBV::BitVector_Destroy(minV);
   CONSTANTBV::BitVector_Destroy(maxV); 
  }

  UnsignedInterval(UnsignedInterval const&) = delete;
  UnsignedInterval& operator=(UnsignedInterval const&) = delete;

  void print() const
  {
    unsigned char* a = CONSTANTBV::BitVector_to_Bin(minV);
    unsigned char* b = CONSTANTBV::BitVector_to_Bin(maxV);
    std::cerr << a << " " << b << std::endl;
    free(a);
    free(b);
  }

  bool isConstant() const
  { 
    return !CONSTANTBV::BitVector_Lexicompare(minV, maxV); 
  }

  bool isComplete() const
  {
    return (CONSTANTBV::BitVector_is_empty(minV) &&
            CONSTANTBV::BitVector_is_full(maxV));
  }

  unsigned getWidth() const
  {
    return bits_(minV);
  }

  void resetToComplete()
  {
    CONSTANTBV::BitVector_Empty(minV);
    CONSTANTBV::BitVector_Fill(maxV);
    checkUnsignedInvariant();
  }

  bool replaceMinIfTightens(CBV min)
  {
    if (CONSTANTBV::BitVector_Lexicompare(min, minV) > 0)
      {
        assert(bits_(min) == getWidth());
        CONSTANTBV::BitVector_Copy(minV,min);
        checkUnsignedInvariant();
        return true;
      }
      return false;
  }

  bool replaceMaxIfTightens(CBV max)
  {
      if (CONSTANTBV::BitVector_Lexicompare(max, maxV) < 0)
      {
        assert(bits_(max) == getWidth());
        CONSTANTBV::BitVector_Copy(maxV,max);
        checkUnsignedInvariant();
        return true;
      }
      return false;
  }

  void checkUnsignedInvariant() const
  {
    assert(minV != NULL);
    assert(maxV != NULL);
    assert(size_(minV) == size_(maxV));
    assert(CONSTANTBV::BitVector_Lexicompare(minV, maxV) <= 0);
  }

  // If the interval is interpreted as a clockwise interval.
  bool crossesSignedUnsigned(int width) const
  {
    bool minMSB = CONSTANTBV::BitVector_bit_test(minV, width - 1);
    bool maxMSB = CONSTANTBV::BitVector_bit_test(maxV, width - 1);

    // If the min is zero, and the max is one, then it must cross.
    if (!minMSB && maxMSB)
      return true;
    if (!(minMSB ^ maxMSB)) // bits are the same.
      return CONSTANTBV::BitVector_Compare(minV, maxV) > 0;
    return false;
  }
};
}
#endif

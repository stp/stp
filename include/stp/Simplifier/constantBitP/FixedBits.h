/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Dan Liew, Mate Soos
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

#ifndef FIXEDBITS_H_
#define FIXEDBITS_H_

#include <cstdint>
#include <cstring>
#include "stp/Util/Attributes.h"
#include <stp/Util/Attributes.h>

#include <algorithm>
#include <cassert>
#include <iostream>
#include <vector>

class MTRand;

namespace stp
{
class ASTNode;
typedef unsigned int* CBV;
DLL_PUBLIC ATTR_NORETURN void FatalError(const char* str);
}

namespace simplifier
{
namespace constantBitP
{

// Gives the file and line number as a string.
#define CONSTANTBITP_UTILITY_STR(s) #s
#define CONSTANTBITP_UTILITY_XSTR(s) CONSTANTBITP_UTILITY_STR(s)
#define LOCATION __FILE__ ":" CONSTANTBITP_UTILITY_XSTR(__LINE__) ": "

static THREAD_LOCAL int staticUniqueId = 1;

// Bits can be fixed, or unfixed. Fixed bits are fixed to either zero or one.
// Unfixed bits are marked as '*' when using operator[]
class FixedBits
{
private:
  bool* fixed;
  bool* values;
  unsigned width;
  bool representsBoolean;

  DLL_PUBLIC void init(const FixedBits& copy);
  int uniqueId;

  bool unsignedHolds_new(unsigned val);
  bool unsignedHolds_old(unsigned val);

public:
  DLL_PUBLIC FixedBits(unsigned n, bool isBoolean);

  FixedBits(const FixedBits& copy)
  {
    assert(this != &copy);
    init(copy);
    uniqueId = staticUniqueId++;
  }

  bool isBoolean() const { return representsBoolean; }

  ~FixedBits()
  {
    delete[] fixed;
    delete[] values;
  }

  bool operator<=(const FixedBits& copy) const
  {
    return uniqueId <= copy.uniqueId;
  }

  char operator[](const unsigned n) const
  {
    assert(n < width);
    if (!isFixed(n))
      return '*';
    else if (getValue(n))
      return '1';
    else
      return '0';
  }

  // Equality when I was a java programmer sorry!~.
  bool operator==(const FixedBits& other) const { return this == &(other); }

  FixedBits& operator=(const FixedBits& copy)
  {
    if (this == &copy)
      return *this;

    delete[] fixed;
    delete[] values;
    init(copy);
    return *this;
  }

  // All values are fixed to false.
  void fixToZero();

  unsigned getWidth() const { return width; }

  // the value contained in the fixed thingy.
  unsigned getUnsignedValue() const
  {
    assert(isTotallyFixed());
    assert(getWidth() <= 32);
    unsigned result = 0;

    for (unsigned i = 0; i < width; i++)
    {
      if (getValue(i))
        result += (1u << i);
    }

    return result;
  }

  // True if all bits are fixed (irrespective of what value they are fixed to).
  DLL_PUBLIC bool isTotallyFixed() const;
  bool isTotallyUnfixed() const;

  // set value of bit "n" to the value.
  void setValue(unsigned n, bool value)
  {
    assert(((char)value) == 0 || (char)value == 1);
    assert(n < width && fixed[n]);
    values[n] = value;
  }

  bool getValue(unsigned n) const
  {
    assert(n < width && fixed[n]);
    return values[n];
  }

  // returns -1 if it's zero.
  int topmostPossibleLeadingOne()
  {
    int i;
    for (i = (int)getWidth() - 1; i >= 0; i--)
    {
      if (!isFixed(i) || getValue(i))
        break;
    }
    return i;
  }

  unsigned minimum_trailingOne()
  {
    unsigned i = 0;
    for (; i < getWidth(); i++)
    {
      if (!isFixed(i) || getValue(i))
        break;
    }
    return i;
  }

  unsigned maximum_trailingOne()
  {
    unsigned i = 0;
    for (; i < getWidth(); i++)
    {
      if (isFixed(i) && getValue(i))
        break;
    }
    return i;
  }

  unsigned minimum_numberOfTrailingZeroes()
  {
    unsigned i = 0;
    for (; i < getWidth(); i++)
    {
      if (!isFixed(i) || getValue(i))
        break;
    }
    return i;
  }

  unsigned maximum_numberOfTrailingZeroes()
  {
    unsigned i = 0;
    for (; i < getWidth(); i++)
    {
      if (isFixed(i) && getValue(i))
        break;
    }
    return i;
  }

  // Returns the position of the first non-fixed value.
  unsigned leastUnfixed() const
  {
    unsigned i = 0;
    for (; i < getWidth(); i++)
    {
      if (!isFixed(i))
        break;
    }
    return i;
  }

  int mostUnfixed() const
  {
    int i = (int)getWidth() - 1;
    for (; i >= 0; i--)
    {
      if (!isFixed(i))
        break;
    }
    return i;
  }

  // is this bit fixed to zero?
  bool isFixedToZero(int n) const { return isFixed(n) && !getValue(n); }

  // is this bit fixed to one?
  bool isFixedToOne(int n) const { return isFixed(n) && getValue(n); }

  // is this bit fixed to either zero or one?
  bool isFixed(unsigned n) const
  {
    assert(n < width);
    return fixed[n];
  }

  // set bit n to either fixed or unfixed.
  void setFixed(unsigned n, bool value)
  {
    assert(n < width);
    fixed[n] = value;
  }

  // Whether the set of values contains this one.
  bool unsignedHolds(unsigned val);

  void replaceWithContents(const FixedBits& a)
  {
    assert(getWidth() >= a.getWidth());

    for (unsigned i = 0; i < a.getWidth(); i++)
    {
      if (a.isFixed(i))
      {
        setFixed(i, true);
        setValue(i, a.getValue(i));
      }
      else
      {
        setFixed(i, false);
      }
    }
  }

  void copyIn(const FixedBits& a)
  {
    unsigned to = std::min(getWidth(), a.getWidth());
    for (unsigned i = 0; i < to; i++)
    {
      assert(!isFixed(i));
      if (a.isFixed(i))
      {
        setFixed(i, true);
        setValue(i, a.getValue(i));
      }
    }
  }

  // todo merger with unsignedHolds()
  bool containsZero() const
  {
    for (unsigned i = 0; i < getWidth(); i++)
    {
      if (isFixed(i) && getValue(i))
        return false;
    }

    return true;
  }

  unsigned countFixed() const
  {
    unsigned result = 0;
    for (unsigned i = 0; i < width; i++)
    {
      if (isFixed(i))
        result++;
    }

    return result;
  }

  // Result needs to be explicitly deleted.
  DLL_PUBLIC stp::CBV GetBVConst() const;
  DLL_PUBLIC stp::CBV GetMaxBVConst() const;
  DLL_PUBLIC stp::CBV GetMinBVConst() const;

  // Result needs to be explicitly deleted.
  stp::CBV GetBVConst(unsigned to, unsigned from) const;

  void getUnsignedMinMax(unsigned& minShift, unsigned& maxShift) const;

  // Writes ceil(width/8) bytes into each buffer: bit i of minBuf is set
  // for a fixed one, and maxBuf additionally has every unfixed bit. Bits
  // beyond the width (in the final byte) may be set in maxBuf; the
  // caller's BitVector_Block_Store masks them off.
  void fillUnsignedMinMaxBuffers(unsigned char* minBuf,
                                 unsigned char* maxBuf) const
  {
    static_assert(sizeof(bool) == 1, "bools are loaded eight at a time");
    const unsigned bytes = (width + 7) / 8;
    for (unsigned byte = 0; byte < bytes; byte++)
    {
      const unsigned base = byte * 8;
      const unsigned n = width - base >= 8 ? 8 : width - base;
      uint64_t f = 0, v = 0;
      memcpy(&f, fixed + base, n);
      memcpy(&v, values + base, n);
      // The bools are 0x00/0x01 bytes; gather each byte's low bit.
      const uint64_t ones = 0x0101010101010101ULL;
      const uint64_t gather = 0x0102040810204080ULL;
      const uint64_t mn = f & v;
      const uint64_t mx = (f ^ ones) | mn; // unfixed or fixed one.
      minBuf[byte] = (unsigned char)((mn * gather) >> 56);
      maxBuf[byte] = (unsigned char)((mx * gather) >> 56);
    }
  }

  // True if some bit is fixed in both, but to different values. Reads the
  // bool arrays as 64-bit lanes; no packing, so an early hit is nearly
  // free. Branching once per 64 bools rather than per lane lets the
  // compiler vectorise the block.
  bool disagrees(const FixedBits& other) const
  {
    static_assert(sizeof(bool) == 1, "bools are loaded eight at a time");
    assert(other.width == width);
    unsigned i = 0;
    for (; i + 64 <= width; i += 64)
    {
      uint64_t acc = 0;
      for (unsigned b = 0; b < 64; b += 8)
      {
        uint64_t f0, v0, f1, v1;
        memcpy(&f0, fixed + i + b, 8);
        memcpy(&v0, values + i + b, 8);
        memcpy(&f1, other.fixed + i + b, 8);
        memcpy(&v1, other.values + i + b, 8);
        // The bools are 0x00/0x01 bytes.
        acc |= f0 & f1 & (v0 ^ v1);
      }
      if (acc != 0)
        return true;
    }
    for (; i + 8 <= width; i += 8)
    {
      uint64_t f0, v0, f1, v1;
      memcpy(&f0, fixed + i, 8);
      memcpy(&v0, values + i, 8);
      memcpy(&f1, other.fixed + i, 8);
      memcpy(&v1, other.values + i, 8);
      if ((f0 & f1 & (v0 ^ v1)) != 0)
        return true;
    }
    for (; i < width; i++)
      if (fixed[i] && other.fixed[i] && values[i] != other.values[i])
        return true;
    return false;
  }

  // Packs one 64-bit chunk — bits [w*64, min(width, (w+1)*64)) — of the
  // fixedness flags and the fixed-one values, LSB-first: bit i of fixedW
  // is isFixed(w*64+i), bit i of valueW is a fixed one there.
  void fillPackedWord(unsigned w, uint64_t& fixedW, uint64_t& valueW) const
  {
    static_assert(sizeof(bool) == 1, "bools are loaded eight at a time");
    const uint64_t gather = 0x0102040810204080ULL;
    uint64_t fw = 0, vw = 0;
    const unsigned base = w * 64;
    const unsigned limit = width - base >= 64 ? 64 : width - base;
    for (unsigned b = 0; b < limit; b += 8)
    {
      const unsigned n = limit - b >= 8 ? 8 : limit - b;
      uint64_t f = 0, v = 0;
      memcpy(&f, fixed + base + b, n);
      memcpy(&v, values + base + b, n);
      // The bools are 0x00/0x01 bytes; gather each byte's low bit.
      fw |= ((f * gather) >> 56) << b;
      vw |= (((f & v) * gather) >> 56) << b;
    }
    fixedW = fw;
    valueW = vw;
  }

  // As above over the whole width. Each array needs ceil(width/64) words.
  void fillPackedWords(uint64_t* fixedW,
                       uint64_t* valueW) const
  {
    const unsigned words = (width + 63) / 64;
    for (unsigned w = 0; w < words; w++)
      fillPackedWord(w, fixedW[w], valueW[w]);
  }

  void mergeIn(const FixedBits& a)
  {
    assert(a.getWidth() == getWidth());
    for (unsigned i = 0; i < width; i++)
    {
      if (a.isFixed(i) && !isFixed(i))
      {
        setFixed(i, true);
        setValue(i, a.getValue(i));
      }
    }
  }

  static FixedBits meet(const FixedBits& a, const FixedBits& b);

  DLL_PUBLIC void join(const FixedBits& a);

  DLL_PUBLIC void join(unsigned int a);

  DLL_PUBLIC static FixedBits createRandom(const unsigned length,
                                const unsigned probabilityOfSetting,
                                MTRand& rand);

  DLL_PUBLIC void fromUnsigned(unsigned val);

  static FixedBits fromUnsignedInt(unsigned width, unsigned val);

  DLL_PUBLIC static FixedBits concreteToAbstract(const stp::ASTNode& n);

  DLL_PUBLIC static bool equals(const FixedBits& a, const FixedBits& b);

  static bool updateOK(const FixedBits& o, const FixedBits& n);

  static bool updateOK(const FixedBits& o, const FixedBits& n, const int upTo);

  static bool in(const FixedBits& a, const FixedBits& b);

  bool in(stp::CBV a);
  
};

DLL_PUBLIC std::ostream& operator<<(std::ostream& output, const FixedBits& h);
}
}
#endif /*FIXED_H_*/

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
#include "stp/Util/BitOps.h"
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
  // Packed LSB-first: bit i of fixedW_[i/64] says whether bit i is fixed;
  // the same bit of valueW_ is its value. Value bits are only meaningful
  // where the fixed bit is set (they go stale when a bit is unfixed), so
  // every multi-bit reader masks the value words with the fixedness words.
  // Bits at or above the width in the fixedness words are always zero.
  // Widths of 64 or less live inside the object; wider ones in one heap
  // block holding the fixedness words followed by the value words.
  uint64_t* fixedW_;
  uint64_t* valueW_;
  uint64_t inlineStorage[2];
  unsigned width;
  bool representsBoolean;

  unsigned numWords() const { return (width + 63) / 64; }

  bool onHeap() const { return width > 64; }

  // Set in the final fixedness word: the bits below the width.
  uint64_t topMask() const
  {
    return (width % 64 == 0) ? ~0ULL : ((1ULL << (width % 64)) - 1);
  }

  // Points fixedW_/valueW_ at storage for the current width. The contents
  // are uninitialised.
  void allocate()
  {
    if (width <= 64)
    {
      fixedW_ = &inlineStorage[0];
      valueW_ = &inlineStorage[1];
    }
    else
    {
      fixedW_ = new uint64_t[2 * numWords()];
      valueW_ = fixedW_ + numWords();
    }
  }

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
    if (onHeap())
      delete[] fixedW_;
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

    if (onHeap())
      delete[] fixedW_;
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
    return (unsigned)(valueW_[0] & topMask());
  }

  // True if all bits are fixed (irrespective of what value they are fixed to).
  DLL_PUBLIC bool isTotallyFixed() const;
  bool isTotallyUnfixed() const;

  // set value of bit "n" to the value.
  void setValue(unsigned n, bool value)
  {
    assert(((char)value) == 0 || (char)value == 1);
    assert(n < width && isFixed(n));
    const uint64_t bit = 1ULL << (n & 63);
    if (value)
      valueW_[n >> 6] |= bit;
    else
      valueW_[n >> 6] &= ~bit;
  }

  bool getValue(unsigned n) const
  {
    assert(n < width && isFixed(n));
    return (valueW_[n >> 6] >> (n & 63)) & 1;
  }

private:
  // Bits of word w that could possibly be one: unfixed, or fixed to one.
  uint64_t possibleOnes(unsigned w) const
  {
    const uint64_t mask = (w == numWords() - 1) ? topMask() : ~0ULL;
    return (~fixedW_[w] & mask) | (fixedW_[w] & valueW_[w]);
  }

  // Position of the lowest set bit at or above the width if none is set.
  unsigned lowestSet(uint64_t (FixedBits::*wordFn)(unsigned) const) const
  {
    for (unsigned w = 0; w < numWords(); w++)
    {
      const uint64_t t = (this->*wordFn)(w);
      if (t != 0)
        return w * 64 + ::stp::countTrailingZeroes64(t);
    }
    return width;
  }

  uint64_t fixedOnes(unsigned w) const { return fixedW_[w] & valueW_[w]; }

  uint64_t unfixedBits(unsigned w) const
  {
    const uint64_t mask = (w == numWords() - 1) ? topMask() : ~0ULL;
    return ~fixedW_[w] & mask;
  }

public:
  // returns -1 if it's zero.
  int topmostPossibleLeadingOne()
  {
    for (int w = (int)numWords() - 1; w >= 0; w--)
    {
      const uint64_t t = possibleOnes(w);
      if (t != 0)
        return w * 64 + 63 - ::stp::countLeadingZeroes64(t);
    }
    return -1;
  }

  unsigned minimum_trailingOne()
  {
    return lowestSet(&FixedBits::possibleOnes);
  }

  unsigned maximum_trailingOne() { return lowestSet(&FixedBits::fixedOnes); }

  unsigned minimum_numberOfTrailingZeroes()
  {
    return lowestSet(&FixedBits::possibleOnes);
  }

  unsigned maximum_numberOfTrailingZeroes()
  {
    return lowestSet(&FixedBits::fixedOnes);
  }

  // Returns the position of the first non-fixed value.
  unsigned leastUnfixed() const
  {
    return lowestSet(&FixedBits::unfixedBits);
  }

  int mostUnfixed() const
  {
    for (int w = (int)numWords() - 1; w >= 0; w--)
    {
      const uint64_t t = unfixedBits(w);
      if (t != 0)
        return w * 64 + 63 - ::stp::countLeadingZeroes64(t);
    }
    return -1;
  }

  // is this bit fixed to zero?
  bool isFixedToZero(int n) const { return isFixed(n) && !getValue(n); }

  // is this bit fixed to one?
  bool isFixedToOne(int n) const { return isFixed(n) && getValue(n); }

  // is this bit fixed to either zero or one?
  bool isFixed(unsigned n) const
  {
    assert(n < width);
    return (fixedW_[n >> 6] >> (n & 63)) & 1;
  }

  // set bit n to either fixed or unfixed.
  void setFixed(unsigned n, bool value)
  {
    assert(n < width);
    const uint64_t bit = 1ULL << (n & 63);
    if (value)
      fixedW_[n >> 6] |= bit;
    else
      fixedW_[n >> 6] &= ~bit;
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
    const unsigned to = std::min(getWidth(), a.getWidth());
    for (unsigned w = 0; w * 64 < to; w++)
    {
      const uint64_t mask =
          (to - w * 64 >= 64) ? ~0ULL : ((1ULL << (to - w * 64)) - 1);
      uint64_t af, av;
      a.fillPackedWord(w, af, av);
      assert((fixedW_[w] & mask) == 0);
      const uint64_t add = af & mask;
      if (add != 0)
        fixWordBits(w, add, av);
    }
  }

  // todo merger with unsignedHolds()
  bool containsZero() const
  {
    for (unsigned w = 0; w < numWords(); w++)
      if (fixedOnes(w) != 0)
        return false;
    return true;
  }

  unsigned countFixed() const
  {
    unsigned result = 0;
    for (unsigned w = 0; w < numWords(); w++)
      result += ::stp::popCount64(fixedW_[w]);
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
    const unsigned bytes = (width + 7) / 8;
    for (unsigned byte = 0; byte < bytes; byte++)
    {
      const unsigned w = byte / 8;
      const unsigned shift = (byte % 8) * 8;
      const uint64_t mn = fixedW_[w] & valueW_[w];
      const uint64_t mx = mn | ~fixedW_[w]; // unfixed or fixed one.
      minBuf[byte] = (unsigned char)(mn >> shift);
      maxBuf[byte] = (unsigned char)(mx >> shift);
    }
  }

  // True if some bit is fixed in both, but to different values.
  bool disagrees(const FixedBits& other) const
  {
    assert(other.width == width);
    for (unsigned w = 0; w < numWords(); w++)
      if ((fixedW_[w] & other.fixedW_[w] & (valueW_[w] ^ other.valueW_[w])) !=
          0)
        return true;
    return false;
  }

  // Fix the bits of `add` in word w, each to the corresponding bit of
  // `vals`. Other bits are untouched.
  void fixWordBits(unsigned w, uint64_t add, uint64_t vals)
  {
    assert(w < numWords());
    assert((add & ~((w == numWords() - 1) ? topMask() : ~0ULL)) == 0);
    fixedW_[w] |= add;
    valueW_[w] = (valueW_[w] & ~add) | (vals & add);
  }

  // Packs one 64-bit chunk — bits [w*64, min(width, (w+1)*64)) — of the
  // fixedness flags and the fixed-one values, LSB-first: bit i of fixedW
  // is isFixed(w*64+i), bit i of valueW is a fixed one there.
  void fillPackedWord(unsigned w, uint64_t& fixedW, uint64_t& valueW) const
  {
    fixedW = fixedW_[w];
    valueW = fixedW_[w] & valueW_[w];
  }

  // As above over the whole width. Each array needs ceil(width/64) words.
  void fillPackedWords(uint64_t* fixedW,
                       uint64_t* valueW) const
  {
    for (unsigned w = 0; w < numWords(); w++)
      fillPackedWord(w, fixedW[w], valueW[w]);
  }

  void mergeIn(const FixedBits& a)
  {
    assert(a.getWidth() == getWidth());
    for (unsigned w = 0; w < numWords(); w++)
    {
      const uint64_t add = a.fixedW_[w] & ~fixedW_[w];
      fixedW_[w] |= add;
      valueW_[w] = (valueW_[w] & ~add) | (a.valueW_[w] & add);
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

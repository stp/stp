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

#include "stp/AST/AST.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_Utility.h"
#include "stp/Simplifier/constantBitP/MultiplicationStats.h"
#include "stp/Simplifier/constantBitP/multiplication/ColumnCounts.h"
#include "stp/Simplifier/constantBitP/multiplication/ColumnStats.h"
#include "stp/Util/BitOps.h"
#include <cstdint>
#include <cstring>
// Multiply.

using namespace stp;

namespace simplifier
{
namespace constantBitP
{
using std::endl;


static inline uint64_t rightShiftedWord(const uint64_t* m, unsigned words,
                                        unsigned s, unsigned j);
static inline int convolutionAt(const uint64_t* a, const uint64_t* revB,
                                unsigned words, unsigned width, unsigned j);
static inline void reverseBitArray(uint64_t* m, unsigned words,
                                   unsigned width);

// The fixed-to-one and unfixed masks of both operands, packed into words so
// a column's pair-category counts are shifted-window popcounts rather than
// a per-column scan. Rebuild after either operand changes.
struct PairMasks
{
  static const unsigned INLINE_WORDS = 8; // up to 512 bits on the stack.
  uint64_t stackBuf[4 * INLINE_WORDS];
  std::vector<uint64_t> heapBuf;
  uint64_t* xOne;
  uint64_t* xUnfixed;
  uint64_t* revYOne; // y, bit-reversed.
  uint64_t* revYUnfixed;
  unsigned words;

  void build(const FixedBits& x, const FixedBits& y)
  {
    const unsigned width = x.getWidth();
    words = (width + 63) / 64;
    uint64_t* buf = stackBuf;
    if (words > INLINE_WORDS)
    {
      heapBuf.resize(4 * words);
      buf = heapBuf.data();
    }
    xOne = buf;
    xUnfixed = buf + words;
    revYOne = buf + 2 * words;
    revYUnfixed = buf + 3 * words;

    widthCached = width;
    for (unsigned t = 0; t < words; t++)
    {
      const uint64_t liveMask = (t == words - 1 && (width & 63) != 0)
                                    ? (((uint64_t)1 << (width & 63)) - 1)
                                    : ~(uint64_t)0;
      uint64_t f, one;
      x.fillPackedWord(t, f, one);
      xOne[t] = one;
      xUnfixed[t] = ~f & liveMask;
      y.fillPackedWord(t, f, one);
      revYOne[t] = one;
      revYUnfixed[t] = ~f & liveMask;
    }
    reverseBitArray(revYOne, words, width);
    reverseBitArray(revYUnfixed, words, width);
  }

  // Bit i of x was just fixed: leave the unfixed set, join the ones if set.
  void xFixed(unsigned i, bool value)
  {
    xUnfixed[i >> 6] &= ~((uint64_t)1 << (i & 63));
    if (value)
      xOne[i >> 6] |= (uint64_t)1 << (i & 63);
  }

  void yFixed(unsigned i, bool value)
  {
    const unsigned r = widthCached - 1 - i;
    revYUnfixed[r >> 6] &= ~((uint64_t)1 << (r & 63));
    if (value)
      revYOne[r >> 6] |= (uint64_t)1 << (r & 63);
  }

  unsigned widthCached;
};

Result fixIfCanForMultiplication(vector<FixedBits*>& children,
                                 const unsigned index,
                                 const int aspirationalSum, PairMasks* pm)
{
  assert(index < children[0]->getWidth());

  FixedBits& x = *children[0];
  FixedBits& y = *children[1];

  // The counts ColumnStats(x, y, index) walks the column for, but from the
  // packed masks: a pair contributes "ones" when both operands are fixed
  // to one, "one fixed" when one is fixed to one and the other unfixed,
  // and "unfixed" when both are unfixed. (Pairs with a fixed zero are the
  // remainder, and aren't needed here.)
  const unsigned width = x.getWidth();
  int columnOnes, columnUnfixed, columnOneFixed;
  if (pm == NULL)
  {
    ColumnStats cs(x, y, index);
    columnOnes = cs.columnOnes;
    columnUnfixed = cs.columnUnfixed;
    columnOneFixed = cs.columnOneFixed;
  }
  else
  {
    columnOnes = convolutionAt(pm->xOne, pm->revYOne, pm->words, width, index);
    columnUnfixed =
        convolutionAt(pm->xUnfixed, pm->revYUnfixed, pm->words, width, index);
    columnOneFixed =
        convolutionAt(pm->xOne, pm->revYUnfixed, pm->words, width, index) +
        convolutionAt(pm->xUnfixed, pm->revYOne, pm->words, width, index);
  }

  Result result = NO_CHANGE;

  // only one of the conditionals can run.
  [[maybe_unused]] bool run = false;

  // We need every value that is unfixed to be set to one.
  if (aspirationalSum == columnOnes + columnOneFixed + columnUnfixed &&
      ((columnOneFixed + columnUnfixed) > 0))
  {
    for (unsigned i = 0; i <= index; i++)
    {
      // If y is unfixed, and it's not anded with zero.
      if (!y.isFixed(i) && !(x.isFixed(index - i) && !x.getValue(index - i)))
      {
        y.setFixed(i, true);
        y.setValue(i, true);
        if (pm)
          pm->yFixed(i, true);
        result = CHANGED;
      }

      if (!x.isFixed(index - i) && !(y.isFixed(i) && !y.getValue(i)))
      {
        x.setFixed(index - i, true);
        x.setValue(index - i, true);
        if (pm)
          pm->xFixed(index - i, true);
        result = CHANGED;
      }
    }
    assert(result == CHANGED);
    run = true;
  }

  // We have all the ones that we need already. (thanks). Set everything we can
  // to zero.
  if (aspirationalSum == columnOnes &&
      (columnUnfixed > 0 || columnOneFixed > 0))
  {
    assert(!run);
    for (unsigned i = 0; i <= index; i++)
    {
      if (!y.isFixed(i) && x.isFixed(index - i) &&
          x.getValue(index - i)) // one fixed.

      {
        y.setFixed(i, true);
        y.setValue(i, false);
        if (pm)
          pm->yFixed(i, false);
        result = CHANGED;
      }

      if (!x.isFixed(index - i) && y.isFixed(i) &&
          y.getValue(i)) // one fixed other way.
      {
        x.setFixed(index - i, true);
        x.setValue(index - i, false);
        if (pm)
          pm->xFixed(index - i, false);
        result = CHANGED;
      }
    }
  }
  return result;
}

static inline uint64_t reverseBits64(uint64_t v)
{
  v = ((v >> 1) & 0x5555555555555555ULL) | ((v & 0x5555555555555555ULL) << 1);
  v = ((v >> 2) & 0x3333333333333333ULL) | ((v & 0x3333333333333333ULL) << 2);
  v = ((v >> 4) & 0x0F0F0F0F0F0F0F0FULL) | ((v & 0x0F0F0F0F0F0F0F0FULL) << 4);
  v = ((v >> 8) & 0x00FF00FF00FF00FFULL) | ((v & 0x00FF00FF00FF00FFULL) << 8);
  v = ((v >> 16) & 0x0000FFFF0000FFFFULL) |
      ((v & 0x0000FFFF0000FFFFULL) << 16);
  return (v >> 32) | (v << 32);
}

// Reverse the low `width` bits of m in place; bits at or above the width
// must be zero on entry and are zero on exit.
static inline void reverseBitArray(uint64_t* m, unsigned words, unsigned width)
{
  for (unsigned i = 0, j = words - 1; i < j; i++, j--)
  {
    const uint64_t t = reverseBits64(m[i]);
    m[i] = reverseBits64(m[j]);
    m[j] = t;
  }
  if (words & 1)
    m[words / 2] = reverseBits64(m[words / 2]);
  const unsigned s = words * 64 - width;
  if (s != 0)
    for (unsigned t = 0; t < words; t++)
    {
      m[t] >>= s;
      if (t + 1 < words)
        m[t] |= m[t + 1] << (64 - s);
    }
}

// Word `j` of (m >> s), for a `words`-long array.
static inline uint64_t rightShiftedWord(const uint64_t* m, unsigned words,
                                        unsigned s, unsigned j)
{
  const unsigned word = j + (s >> 6);
  const unsigned bit = s & 63;
  if (word >= words)
    return 0;
  uint64_t r = m[word] >> bit;
  if (bit != 0 && word + 1 < words)
    r |= m[word + 1] << (64 - bit);
  return r;
}

// The number of pairs i + k == j with a[i] and revB[width-1-k] both set,
// i.e. the boolean convolution of a and (un-reversed) b at column j.
static inline int convolutionAt(const uint64_t* a, const uint64_t* revB,
                                unsigned words, unsigned width, unsigned j)
{
  int count = 0;
  const unsigned s = width - 1 - j;
  // Only pairs with i <= j exist, so a's words above bit j can't contribute
  // (the matching window of revB is all zero there).
  const unsigned tEnd = (words > j / 64 + 1) ? j / 64 + 1 : words;
  for (unsigned t = 0; t < tEnd; t++)
  {
    const uint64_t aw = a[t];
    if (aw != 0)
      count += ::stp::popCount64(aw & rightShiftedWord(revB, words, s, t));
  }
  return count;
}

// Uses the zeroes / ones present adjust the column counts:
//   columnH[j] -= #{i <= j : y[i] fixed to zero}
//              +  #{i <= j : x[i] fixed to zero and y[j-i] not fixed to zero}
//   columnL[j] += #{i + k == j : x[i] and y[k] both fixed to one}
// The counts come from running prefix sums and two boolean convolutions
// evaluated as shifted-window popcounts over packed words.
Result adjustColumns(const FixedBits& x, const FixedBits& y, int* columnL,
                     int* columnH)
{
  const unsigned bitWidth = x.getWidth();
  const unsigned words = (bitWidth + 63) / 64;

  const unsigned INLINE_WORDS = 8; // up to 512 bits on the stack.
  uint64_t stackBuf[4 * INLINE_WORDS];
  std::vector<uint64_t> heapBuf;
  uint64_t* buf = stackBuf;
  if (words > INLINE_WORDS)
  {
    heapBuf.resize(4 * words);
    buf = heapBuf.data();
  }
  uint64_t* xFF = buf;                // x fixed to zero.
  uint64_t* xOne = buf + words;       // x fixed to one.
  uint64_t* revYFF = buf + 2 * words; // y fixed to zero, bit-reversed.
  uint64_t* revYOne = buf + 3 * words;

  for (unsigned t = 0; t < words; t++)
  {
    uint64_t f, one;
    x.fillPackedWord(t, f, one);
    xOne[t] = one;
    xFF[t] = f ^ one; // fixed and not one.
    y.fillPackedWord(t, f, one);
    revYOne[t] = one;
    revYFF[t] = f ^ one;
  }
  reverseBitArray(revYOne, words, bitWidth);
  reverseBitArray(revYFF, words, bitWidth);

  bool anyXFF = false, anyYFF = false, anyXOne = false, anyYOne = false;
  for (unsigned t = 0; t < words; t++)
  {
    anyXFF |= xFF[t] != 0;
    anyXOne |= xOne[t] != 0;
    anyYFF |= revYFF[t] != 0;
    anyYOne |= revYOne[t] != 0;
  }
  const bool ffPairsPossible = anyXFF && anyYFF;
  const bool onePairsPossible = anyXOne && anyYOne;
  if (!anyXFF && !anyYFF && !onePairsPossible)
    return NO_CHANGE; // nothing fixed that could adjust any count.

  int xZeroes = 0, yZeroes = 0;
  for (unsigned j = 0; j < bitWidth; j++)
  {
    // Running prefix counts of the fixed-to-zero bits at or below j.
    const unsigned r = bitWidth - 1 - j;
    if ((revYFF[r >> 6] >> (r & 63)) & 1)
      yZeroes++;
    if ((xFF[j >> 6] >> (j & 63)) & 1)
      xZeroes++;

    // The two convolutions at column j, with the shifted-window address
    // arithmetic computed once for both.
    int ffPairs = 0, onePairs = 0;
    const unsigned s = bitWidth - 1 - j;
    const unsigned tEnd = (words > j / 64 + 1) ? j / 64 + 1 : words;
    for (unsigned t = 0; t < tEnd; t++)
    {
      const unsigned word = t + (s >> 6);
      if (word >= words)
        break;
      const unsigned bit = s & 63;
      if (ffPairsPossible && xFF[t] != 0)
      {
        uint64_t win = revYFF[word] >> bit;
        if (bit != 0 && word + 1 < words)
          win |= revYFF[word + 1] << (64 - bit);
        ffPairs += ::stp::popCount64(xFF[t] & win);
      }
      if (onePairsPossible && xOne[t] != 0)
      {
        uint64_t win = revYOne[word] >> bit;
        if (bit != 0 && word + 1 < words)
          win |= revYOne[word + 1] << (64 - bit);
        onePairs += ::stp::popCount64(xOne[t] & win);
      }
    }

    const int decrement = yZeroes + xZeroes - ffPairs;
    if (decrement != 0)
      columnH[j] -= decrement;
    if (onePairs != 0)
      columnL[j] += onePairs;
  }
  return NO_CHANGE;
}

Result setToZero(FixedBits& y, unsigned from, unsigned to)
{
  Result r = NO_CHANGE;
  assert(from <= to);
  assert(to <= y.getWidth());

  /***NB < to ***/
  for (unsigned i = from; i < to; i++)
  {
    if (y[i] == '*')
    {
      y.setFixed(i, true);
      y.setValue(i, false);
      r = CHANGED;
    }
    else if (y[i] == '1')
      return CONFLICT;
  }
  return r;
}

// Zero the output bits that cannot be reached by any product of a value
// admitted by x and one admitted by y: multiply the two largest admitted
// values and take the position of that product's leading one as the bound.
//
// This subsumes an earlier version that bounded the product by the sum of
// the operands' leading-one positions plus one. That version, and the
// exhaustive check that this one fixes at least as much, now live in
// tests/unit-tests/ConstantBitP_TransferFunctions_Test.cpp.
Result useLeadingZeroesToFix(FixedBits& x, FixedBits& y, FixedBits& output)
{
  const int bitWidth = x.getWidth();
  CBV x_c = CONSTANTBV::BitVector_Create(2 * bitWidth, true);
  CBV y_c = CONSTANTBV::BitVector_Create(2 * bitWidth, true);

  for (int i = 0; i < bitWidth; i++)
  {
    if (x[i] == '1' || x[i] == '*')
      CONSTANTBV::BitVector_Bit_On(x_c, i);

    if (y[i] == '1' || y[i] == '*')
      CONSTANTBV::BitVector_Bit_On(y_c, i);
  }

  stp::CBV result = CONSTANTBV::BitVector_Create(2 * bitWidth + 1, true);
  [[maybe_unused]] CONSTANTBV::ErrCode ec =
      CONSTANTBV::BitVector_Multiply(result, x_c, y_c);
  assert(ec == CONSTANTBV::ErrCode_Ok);

  for (int j = (2 * bitWidth) - 1; j >= 0; j--)
  {
    if (CONSTANTBV::BitVector_bit_test(result, j))
      break;
    if (j < bitWidth)
    {
      if (!output.isFixed(j))
      {
        output.setFixed(j, true);
        output.setValue(j, false);
      }
      else
      {
        if (output.getValue(j))
        {
          CONSTANTBV::BitVector_Destroy(x_c);
          CONSTANTBV::BitVector_Destroy(y_c);
          CONSTANTBV::BitVector_Destroy(result);
          return CONFLICT;
        }
      }
    }
  }

  CONSTANTBV::BitVector_Destroy(x_c);
  CONSTANTBV::BitVector_Destroy(y_c);
  CONSTANTBV::BitVector_Destroy(result);

  return NOT_IMPLEMENTED;
}

// Remove from x any trailing "boths", that don't have support in y and output.
//
// This subsumes an earlier version that started the scan at x's minimum
// trailing-one position rather than at bit zero. That version, and the
// exhaustive check that this one leaves it nothing to find, now live in
// tests/unit-tests/ConstantBitP_TransferFunctions_Test.cpp.
Result trailingOneReasoning(FixedBits& x, FixedBits& y, FixedBits& output)
{
  Result r = NO_CHANGE;

  const int bitwidth = output.getWidth();

  const int y_min = y.minimum_trailingOne();
  const int y_max = y.maximum_trailingOne();

  const int output_max = output.maximum_trailingOne();

  for (int i = 0; i < bitwidth; i++)
  {
    if (x[i] == '0')
      continue;

    if (x[i] == '1')
      break;

    for (int j = y_min; j <= std::min(y_max, output_max); j++)
    {
      if (j + i >= bitwidth || (y[j] != '0' && output[i + j] != '0'))
        return r;
    }

    x.setFixed(i, true);
    x.setValue(i, false);
    r = CHANGED;
  }

  return r;
}

// if x has n trailing zeroes, and y has m trailing zeroes, then the output has
// n+m trailing zeroes.
// if the output has n trailing zeroes and x has p trailing zeroes, then y has
// n-p trailing zeroes.
Result useTrailingZeroesToFix(FixedBits& x, FixedBits& y, FixedBits& output)
{
  const int bitwidth = output.getWidth();

  Result r0 = trailingOneReasoning(x, y, output);
  Result r1 = trailingOneReasoning(y, x, output);

  // Calculate the minimum number of trailing zeroes in the operands,
  // the result has a >= number.
  int min =
      x.minimum_numberOfTrailingZeroes() + y.minimum_numberOfTrailingZeroes();
  min = std::min(min, bitwidth);

  Result r2 = setToZero(output, 0, min);
  if (r2 == CONFLICT)
    return CONFLICT;

  if (r0 == CHANGED || r1 == CHANGED || r2 == CHANGED)
    return CHANGED;

  return NO_CHANGE;
}

// 64x64 -> 128 multiply via 32-bit halves; the library builds for 32-bit
// targets, so no compiler 128-bit support is assumed.
static inline void mul64(uint64_t a, uint64_t b, uint64_t& hi, uint64_t& lo)
{
  const uint64_t aL = (uint32_t)a, aH = a >> 32;
  const uint64_t bL = (uint32_t)b, bH = b >> 32;
  const uint64_t t0 = aL * bL;
  const uint64_t t1 = aH * bL + (t0 >> 32);
  const uint64_t t2 = aL * bH + (uint32_t)t1;
  lo = (t2 << 32) | (uint32_t)t0;
  hi = aH * bH + (t1 >> 32) + (t2 >> 32);
}

// dst = (a * b) mod 2^(64*words). dst must not alias a or b.
static void mulLowWords(uint64_t* dst, const uint64_t* a, const uint64_t* b,
                        unsigned words)
{
  for (unsigned i = 0; i < words; i++)
    dst[i] = 0;
  for (unsigned i = 0; i < words; i++)
  {
    if (a[i] == 0)
      continue;
    uint64_t carry = 0;
    for (unsigned j = 0; i + j < words; j++)
    {
      uint64_t hi, lo;
      mul64(a[i], b[j], hi, lo);
      // hi:lo + carry + dst[i+j] <= (2^64-1)^2 + 2*(2^64-1) = 2^128 - 1,
      // so folding both carry-outs into hi cannot overflow.
      const uint64_t s = lo + carry;
      hi += (s < lo) ? 1 : 0;
      const uint64_t s2 = dst[i + j] + s;
      hi += (s2 < s) ? 1 : 0;
      dst[i + j] = s2;
      carry = hi;
    }
  }
}

// a = (2 - a) mod 2^(64*words).
static void twoMinus(uint64_t* a, unsigned words)
{
  uint64_t borrow = 0;
  for (unsigned i = 0; i < words; i++)
  {
    const uint64_t lhs = (i == 0) ? (uint64_t)2 : 0;
    const uint64_t sub = a[i] + borrow;
    const uint64_t nextBorrow = ((sub < a[i]) || (lhs < sub)) ? 1 : 0;
    a[i] = lhs - sub;
    borrow = nextBorrow;
  }
}

// Length of the fixed low prefix when it is odd (bit zero fixed to one),
// otherwise zero.
static unsigned oddPrefixLength(const FixedBits& c)
{
  const unsigned k = c.leastUnfixed();
  if (k == 0 || !c.getValue(0))
    return 0;
  return k;
}

// The multiplicative inverse mod 2^k of c's low k bits, as a fully fixed
// width-k FixedBits. Those bits must be fixed, with bit zero one. Newton /
// Hensel lifting: an odd number is its own inverse mod 8, and each
// inv' = inv * (2 - c*inv) step doubles the number of correct low bits.
FixedBits makeLowInverse(const FixedBits& c, unsigned k)
{
  assert(k >= 1 && k <= c.leastUnfixed());
  assert(c.getValue(0));

  const unsigned words = (k + 63) / 64;
  const unsigned INLINE_WORDS = 8; // up to 512 bits on the stack.
  uint64_t stackBuf[4 * INLINE_WORDS];
  std::vector<uint64_t> heapBuf;
  uint64_t* buf = stackBuf;
  if (words > INLINE_WORDS)
  {
    heapBuf.resize(4 * words);
    buf = heapBuf.data();
  }
  uint64_t* cw = buf;
  uint64_t* inv = buf + words;
  uint64_t* t1 = buf + 2 * words;
  uint64_t* t2 = buf + 3 * words;

  const uint64_t topMask =
      ((k & 63) != 0) ? (((uint64_t)1 << (k & 63)) - 1) : ~(uint64_t)0;

  for (unsigned w = 0; w < words; w++)
  {
    uint64_t f, one;
    c.fillPackedWord(w, f, one);
    cw[w] = one;
  }
  cw[words - 1] &= topMask; // fixed bits above the hole at k don't belong.

  memcpy(inv, cw, words * sizeof(uint64_t));
  for (unsigned correct = 3; correct < k; correct *= 2)
  {
    mulLowWords(t1, cw, inv, words); // t1 = c * inv
    twoMinus(t1, words);             // t1 = 2 - c * inv
    mulLowWords(t2, inv, t1, words); // t2 = inv * (2 - c * inv)
    std::swap(inv, t2);
  }
  inv[words - 1] &= topMask;

#ifndef NDEBUG
  { // c * inv == 1 (mod 2^k).
    mulLowWords(t1, cw, inv, words);
    t1[words - 1] &= topMask;
    assert(t1[0] == 1);
    for (unsigned w = 1; w < words; w++)
      assert(t1[w] == 0);
  }
#endif

  FixedBits d(k, false);
  for (unsigned w = 0; w < words; w++)
    d.fixWordBits(w, (w == words - 1) ? topMask : ~(uint64_t)0, inv[w]);
  return d;
}

// A copy of the low k bits of `a`, as a width-k FixedBits.
static FixedBits lowSlice(const FixedBits& a, unsigned k)
{
  assert(k >= 1 && k <= a.getWidth());
  FixedBits r(k, false);
  for (unsigned w = 0; w * 64 < k; w++)
  {
    uint64_t f, v;
    a.fillPackedWord(w, f, v);
    const unsigned rem = k - w * 64;
    const uint64_t mask = (rem >= 64) ? ~(uint64_t)0 : (((uint64_t)1 << rem) - 1);
    if ((f & mask) != 0)
      r.fixWordBits(w, f & mask, v);
  }
  return r;
}

// Fix into `dst` any bits that `slice` (a low slice of dst that has since
// gained bits) has fixed but dst hasn't. Returns whether any bit was newly
// fixed. Disagreement is impossible: the slice started as a copy and a
// sound propagator never unfixes or flips.
static bool mergeLowSlice(FixedBits& dst, const FixedBits& slice)
{
  assert(slice.getWidth() <= dst.getWidth());
  bool changed = false;
  const unsigned k = slice.getWidth();
  for (unsigned w = 0; w * 64 < k; w++)
  {
    uint64_t sf, sv, df, dv;
    slice.fillPackedWord(w, sf, sv);
    dst.fillPackedWord(w, df, dv);
    assert((sf & df & (sv ^ dv)) == 0);
    const uint64_t add = sf & ~df;
    if (add != 0)
    {
      dst.fixWordBits(w, add, sv);
      changed = true;
    }
  }
  return changed;
}

// Use trailing fixed to fix.
// Create two constants and multiply them out fixing the result.
Result useTrailingFixedToFix(FixedBits& x, FixedBits& y, FixedBits& output)
{
  int xBottom = x.leastUnfixed();
  int yBottom = y.leastUnfixed();

  int minV = std::min(xBottom, yBottom);

  if (minV == 0)
    return NO_CHANGE; // nothing determined.

  // It gives the position of the first non-fixed. We want the last fixed.
  minV--;

  // The multiply doesn't like to overflow. So we widen the output.
  stp::CBV xCBV = x.GetBVConst(minV, 0);
  stp::CBV yCBV = y.GetBVConst(minV, 0);
  stp::CBV result = CONSTANTBV::BitVector_Create(2 * (minV + 1), true);

  CONSTANTBV::ErrCode ec = CONSTANTBV::BitVector_Multiply(result, xCBV, yCBV);
  if (ec != CONSTANTBV::ErrCode_Ok)
  {
    assert(false);
    throw 2314231;
  }

  Result status = NOT_IMPLEMENTED;
  for (int i = 0; i <= minV; i++)
  {
    bool expected = CONSTANTBV::BitVector_bit_test(result, i);

    if (output.isFixed(i) && (output.getValue(i) ^ expected))
      status = CONFLICT;
    else if (!output.isFixed(i))
    {
      output.setFixed(i, true);
      output.setValue(i, expected);
    }
  }

  CONSTANTBV::BitVector_Destroy(xCBV);
  CONSTANTBV::BitVector_Destroy(yCBV);
  CONSTANTBV::BitVector_Destroy(result);

  return status;
}

// One run of the column-based reasoning over x * y == output, to its own
// fixed point. The public bvMultiplyBothWays alternates this with
// inverseRelationPass until neither derives anything further.
Result multiplyCore(vector<FixedBits*>& children, FixedBits& output,
                    MultiplicationStats* ms)
{
  assert(children.size() == 2);

  FixedBits& x = *children[0];
  FixedBits& y = *children[1];

  assert(x.getWidth() == y.getWidth());
  assert(x.getWidth() == output.getWidth());

  const unsigned bitWidth = x.getWidth();

  // For a square (bvmul t t) both operands are the *same* FixedBits object, so
  // fixing a bit through one view silently changes the other. The packed pm
  // masks below cache each operand separately and update only the side they
  // were told about, so they desync under aliasing. The always-live
  // ColumnStats path (pm == NULL) re-reads x and y each call and is immune, so
  // fall back to it here.
  const bool aliased = (children[0] == children[1]);



  Result r = useTrailingZeroesToFix(x, y, output);
  if (CONFLICT == r)
    return r;

  // bitWidth is unbounded, so wide instances go to the heap (this used to
  // alloca inside the loop, which only returns the stack space when the
  // function exits). Uninitialised: the loop below writes columnL/columnH
  // and rebuildSums writes sumL/sumH each iteration.
  const unsigned INLINE_COLUMNS = 256; // 6KB of stack.
  signed stackCols[6 * INLINE_COLUMNS];
  std::vector<signed> heapCols;
  signed* cols = stackCols;
  if (bitWidth > INLINE_COLUMNS)
  {
    heapCols.resize(6 * bitWidth);
    cols = heapCols.data();
  }
  signed* columnH = cols;
  signed* columnL = cols + bitWidth;
  signed* sumH = cols + 2 * bitWidth;
  signed* sumL = cols + 3 * bitWidth;
  signed* baseH = cols + 4 * bitWidth; // adjustColumns' result, cached
  signed* baseL = cols + 5 * bitWidth; // while x and y are unchanged.

  // Packed column stats for fixIfCanForMultiplication. Built lazily: many
  // calls trigger no column. Once built the masks persist across passes
  // and stay in sync: fixIfCanForMultiplication updates them as it fixes
  // bits; anything else that touches x or y invalidates them.
  PairMasks pm;
  bool masksValid = false;

  bool columnsDirty = true;
  bool changed = true;
  while (changed)
  {
    changed = false;
    ColumnCounts cc(columnH, columnL, sumH, sumL, bitWidth, output);

    if (columnsDirty)
    {
      for (unsigned i = 0; i < bitWidth; i++)
      {
        columnL[i] = 0;
        columnH[i] = i + 1;
      }
      // Use the number of zeroes and ones in a column to update the possible
      // counts.
      adjustColumns(x, y, columnL, columnH);
      memcpy(baseH, columnH, bitWidth * sizeof(signed));
      memcpy(baseL, columnL, bitWidth * sizeof(signed));
      columnsDirty = false;
    }
    else
    {
      // Neither operand changed in the last pass (only the output did), so
      // adjustColumns would recompute exactly the cached columns.
      memcpy(columnH, baseH, bitWidth * sizeof(signed));
      memcpy(columnL, baseL, bitWidth * sizeof(signed));
    }

    if (cc.rebuildSums() == CONFLICT)
      return CONFLICT;
    Result r = cc.fixedPoint();

    if (r == CONFLICT)
      return CONFLICT;

    r = NO_CHANGE;
    Result rOperands = NO_CHANGE;

    // If any of the sums have a cardinality of 1. Set the result.
    for (unsigned column = 0; column < bitWidth; column++)
    {
      if (cc.sumL[column] == cc.sumH[column])
      {
        //(1) If the output has a known value. Set the output.
        bool newValue = !(sumH[column] % 2 == 0);
        if (!output.isFixed(column))
        {
          output.setFixed(column, true);
          output.setValue(column, newValue);
          r = CHANGED;
        }
        else if (output.getValue(column) != newValue)
          return CONFLICT;
      }
    }

    for (unsigned column = 0; column < bitWidth; column++)
    {
      if (cc.columnL[column] == cc.columnH[column])
      {
        if (!aliased && !masksValid)
        {
          pm.build(x, y);
          masksValid = true;
        }

        //(2) Knowledge of the sum may fix the operands.
        Result tempResult = fixIfCanForMultiplication(
            children, column, cc.columnH[column], aliased ? NULL : &pm);

        if (CONFLICT == tempResult)
          return CONFLICT;

        if (CHANGED == tempResult)
        {
          r = CHANGED; // the masks were updated incrementally.
          rOperands = CHANGED;
          columnsDirty = true;
        }
      }
    }


    assert(CONFLICT != r);

    if (ms != NULL)
    {
      *ms = MultiplicationStats(bitWidth, cc.columnL, cc.columnH, cc.sumL,
                                cc.sumH);
      ms->x = *children[0];
      ms->y = *children[1];
      ms->r = output;
    }

    if (CHANGED == r)
    {
      if (CHANGED == useTrailingZeroesToFix(x, y, output))
      {
        // May have fixed operand bits behind the caches' backs.
        columnsDirty = true;
        masksValid = false;
        rOperands = CHANGED;
      }
    }

    // Another pass can only discover something if an operand changed:
    // output bits fixed above take exactly the parity the sums already
    // carry, so with x and y untouched the next pass would rebuild an
    // identical state and fix nothing further.
    if (CHANGED == rOperands)
      changed = true;
  }

  if (children[0]->isTotallyFixed() && children[1]->isTotallyFixed())
  {
    assert(output.isTotallyFixed());
  }

// The below assertions are for performance only. It's not maximally precise
// anyway!!!

#ifndef NDEBUG
  if (r != CONFLICT)
  {
    FixedBits x_c(x), y_c(y), o_c(output);

    // These are subsumed by the consistency over the columns..
    useTrailingFixedToFix(x_c, y_c, o_c);
    useLeadingZeroesToFix(x_c, y_c, o_c);

    // This one should have been called to fixed point!
    useTrailingZeroesToFix(x_c, y_c, o_c);

    if (!FixedBits::equals(x_c, x) || !FixedBits::equals(y_c, y) ||
        !FixedBits::equals(o_c, output))
    {
      std::cerr << x << y << output << endl;
      std::cerr << x_c << y_c << o_c << endl;
      assert(false);
    }
  }
#endif

  return NOT_IMPLEMENTED;
}

// For c * other == output where the low k bits of c are fixed and odd, c is
// invertible mod 2^k, so the same constraint can also be read as
//    inv(c) * (output mod 2^k)  ==  (other mod 2^k).
// The column/interval reasoning isn't closed under multiplying through by
// the inverse, so running the core propagator over this second view can fix
// bits the original view can't express. One pass tries both orientations;
// `progress` is set when a bit of x, y or the output was newly fixed.
Result inverseRelationPass(FixedBits& x, FixedBits& y, FixedBits& output,
                           bool& progress)
{
  const int sides = (&x == &y) ? 1 : 2; // for a square both views coincide.
  for (int side = 0; side < sides; side++)
  {
    FixedBits& c = (side == 0) ? x : y;
    FixedBits& other = (side == 0) ? y : x;

    const unsigned k = oddPrefixLength(c);
    if (k < 2) // the mod-2 relation is column zero, the core has it.
      continue;

    FixedBits outS = lowSlice(output, k);
    FixedBits othS = lowSlice(other, k);

    // With no fixed bit on either side of the derived relation there is
    // nothing to feed through the bijection.
    if (outS.isTotallyUnfixed() && othS.isTotallyUnfixed())
      continue;

    FixedBits d = makeLowInverse(c, k);
    vector<FixedBits*> ch = {&d, &outS};
    if (CONFLICT == multiplyCore(ch, othS, NULL))
      return CONFLICT;

    progress |= mergeLowSlice(other, othS);
    progress |= mergeLowSlice(output, outS);
  }
  return NO_CHANGE;
}

Result bvMultiplyBothWays(vector<FixedBits*>& children, FixedBits& output,
                          stp::STPMgr* /*bm*/, MultiplicationStats* ms)
{
  // BVTypeCheck allows BVMULT nodes with more than two children, and the
  // hashing node factory builds them (the simplifying factory binarises).
  // The reasoning below is about exactly two operands; running it on the
  // first two children of a wider multiply fixes bits unsoundly.
  if (children.size() != 2)
    return NO_CHANGE;

  assert(children[0]->getWidth() == children[1]->getWidth());
  assert(children[0]->getWidth() == output.getWidth());

  // Alternate the two views of the constraint until a joint fixed point.
  // Each productive inverse pass fixes at least one previously unfixed
  // bit, so this terminates; and the loop always ends with a core pass
  // that found nothing further, keeping the `ms` snapshot current.
  while (true)
  {
    if (CONFLICT == multiplyCore(children, output, ms))
      return CONFLICT;

    bool progress = false;
    if (CONFLICT ==
        inverseRelationPass(*children[0], *children[1], output, progress))
      return CONFLICT;
    if (!progress)
      break;
  }

  return NOT_IMPLEMENTED;
}
}
}

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

// ------------------- exact reasoning over the low bits -------------------
//
// The low w = min(width, 8) bits of x, y and the output are related by
// out_low == x_low * y_low (mod 2^w) — higher operand bits can't reach
// down. Over at most 256 candidate values per side that relation can be
// solved exactly: enumerate the surviving (a, b) pairs and fix every bit
// that all survivors agree on. This is maximally precise for the width-w
// sub-relation (and for the whole node when width <= 8), catching
// correlations both the column counts and the inverse view lose — e.g.
// <0*1> * <0*1> is 1 or 3 mod 8 either way, so output bit 2 is zero.
//
// The tables are facts about multiplication, not about propagator states:
// bit b of M[a][i] is bit i of a*b mod 256, so "which b keep output bit i
// consistent" is a 256-bit AND.

struct ExactMulTables
{
  uint64_t M[256][8][4]; // M[a][i]: the set of b with bit i of a*b set.
  uint64_t P[8][2][4];   // P[i][v]: the set of values whose bit i is v.

  ExactMulTables()
  {
    memset(M, 0, sizeof(M));
    memset(P, 0, sizeof(P));
    for (unsigned a = 0; a < 256; a++)
      for (unsigned b = 0; b < 256; b++)
      {
        const unsigned p = (a * b) & 255;
        for (unsigned i = 0; i < 8; i++)
          if ((p >> i) & 1)
            M[a][i][b >> 6] |= (uint64_t)1 << (b & 63);
      }
    for (unsigned v = 0; v < 256; v++)
      for (unsigned i = 0; i < 8; i++)
        P[i][(v >> i) & 1][v >> 6] |= (uint64_t)1 << (v & 63);
  }
};

static const ExactMulTables& exactTables()
{
  static const ExactMulTables t; // 66KB, built on the first multiply.
  return t;
}

// The set of values 0..2^w-1 consistent with the fixed low bits of v.
static void possibleLowValues(const FixedBits& v, unsigned w, uint64_t S[4])
{
  const ExactMulTables& t = exactTables();
  if (w >= 8)
    S[0] = S[1] = S[2] = S[3] = ~(uint64_t)0;
  else
  {
    // Universe: the 2^w (<= 128) values representable in w bits. Beware
    // 64-bit shifts: at w == 7 the second word is exactly full.
    const unsigned count = 1u << w;
    S[0] = (count >= 64) ? ~(uint64_t)0 : (((uint64_t)1 << count) - 1);
    S[1] = (count >= 128) ? ~(uint64_t)0
                          : ((count > 64) ? (((uint64_t)1 << (count - 64)) - 1)
                                          : 0);
    S[2] = S[3] = 0;
  }
  for (unsigned i = 0; i < w; i++)
    if (v.isFixed(i))
    {
      const uint64_t* p = t.P[i][v.getValue(i) ? 1 : 0];
      S[0] &= p[0];
      S[1] &= p[1];
      S[2] &= p[2];
      S[3] &= p[3];
    }
}

static inline bool emptySet(const uint64_t S[4])
{
  return (S[0] | S[1] | S[2] | S[3]) == 0;
}

static inline bool intersects(const uint64_t A[4], const uint64_t B[4])
{
  return ((A[0] & B[0]) | (A[1] & B[1]) | (A[2] & B[2]) | (A[3] & B[3])) != 0;
}

// Fix the unfixed low-w bits of v that every value in S agrees on. S is the
// non-empty projection of the surviving solutions and was filtered by v's
// fixed bits, so it can't disagree with one.
static bool fixAgreedBits(FixedBits& v, unsigned w, const uint64_t S[4])
{
  const ExactMulTables& t = exactTables();
  bool changed = false;
  for (unsigned i = 0; i < w; i++)
  {
    if (v.isFixed(i))
      continue;
    const bool canBeOne = intersects(S, t.P[i][1]);
    const bool canBeZero = intersects(S, t.P[i][0]);
    if (canBeOne == canBeZero)
      continue;
    v.setFixed(i, true);
    v.setValue(i, canBeOne);
    changed = true;
  }
  return changed;
}

// One exact pass over the low min(width, 8) bits. Sets `progress` when a
// bit was newly fixed; CONFLICT when the sub-relation has no solution.
Result exactLowBitsPass(FixedBits& x, FixedBits& y, FixedBits& output,
                        bool& progress)
{
  const unsigned w = std::min(x.getWidth(), 8u);
  const ExactMulTables& t = exactTables();

  // With nothing fixed below w every pair survives and no bit can fix.
  bool anyFixed = false;
  for (unsigned i = 0; i < w && !anyFixed; i++)
    anyFixed = x.isFixed(i) || y.isFixed(i) || output.isFixed(i);
  if (!anyFixed)
    return NO_CHANGE;

  const bool aliased = (&x == &y);

  uint64_t Sx[4], Sy[4];
  possibleLowValues(x, w, Sx);
  possibleLowValues(y, w, Sy);

  // The output's fixed bits below w, used to filter partners.
  unsigned char outIdx[8];
  bool outVal[8];
  unsigned nOut = 0;
  for (unsigned i = 0; i < w; i++)
    if (output.isFixed(i))
    {
      outIdx[nOut] = (unsigned char)i;
      outVal[nOut++] = output.getValue(i);
    }

  bool xFree = true, yFree = true;
  for (unsigned i = 0; i < w && (xFree || yFree); i++)
  {
    xFree = xFree && !x.isFixed(i);
    yFree = yFree && !y.isFixed(i);
  }

  // With no output constraint below w, no (a, b) can die, so the operands
  // can't be pruned; and if an operand is completely free as well, the
  // output join degenerates to "bits below the minimum trailing-zero count
  // are zero" — exactly what useTrailingZeroesToFix already derives.
  if (nOut == 0 && (xFree || yFree))
    return NO_CHANGE;

  uint64_t xSurv[4] = {0, 0, 0, 0}, ySurv[4] = {0, 0, 0, 0};
  unsigned outSeen0 = 0, outSeen1 = 0; // output bit values witnessed.
  const unsigned outAll = (w >= 8) ? 255u : ((1u << w) - 1);

  if (nOut == 0 && !aliased)
  {
    // Every pair survives: only the output join is in question. Stop as
    // soon as every output bit has been witnessed both ways.
    for (unsigned wd = 0; wd < 4; wd++)
    {
      uint64_t bits = Sx[wd];
      while (bits != 0 && (outSeen0 != outAll || outSeen1 != outAll))
      {
        const unsigned a = wd * 64 + ::stp::countTrailingZeroes64(bits);
        bits &= bits - 1;
        for (unsigned i = 0; i < w; i++)
        {
          const uint64_t* m = t.M[a][i];
          if ((outSeen1 & (1u << i)) == 0 && intersects(Sy, m))
            outSeen1 |= 1u << i;
          if ((outSeen0 & (1u << i)) == 0 &&
              ((Sy[0] & ~m[0]) | (Sy[1] & ~m[1]) | (Sy[2] & ~m[2]) |
               (Sy[3] & ~m[3])) != 0)
            outSeen0 |= 1u << i;
        }
      }
    }
    for (unsigned i = 0; i < w; i++)
    {
      const bool canBeOne = (outSeen1 >> i) & 1;
      const bool canBeZero = (outSeen0 >> i) & 1;
      assert(canBeOne || canBeZero);
      if (canBeOne == canBeZero)
        continue;
      output.setFixed(i, true);
      output.setValue(i, canBeOne);
      progress = true;
    }
    return NO_CHANGE;
  }

  for (unsigned wd = 0; wd < 4; wd++)
  {
    uint64_t bits = Sx[wd];
    while (bits != 0)
    {
      const unsigned a = wd * 64 + ::stp::countTrailingZeroes64(bits);
      bits &= bits - 1;

      if (aliased)
      {
        // A square: the partner is a itself.
        bool ok = true;
        for (unsigned f = 0; f < nOut && ok; f++)
        {
          const bool bit = (t.M[a][outIdx[f]][a >> 6] >> (a & 63)) & 1;
          ok = (bit == outVal[f]);
        }
        if (!ok)
          continue;
        xSurv[a >> 6] |= (uint64_t)1 << (a & 63);
        for (unsigned i = 0; i < w; i++)
        {
          if ((t.M[a][i][a >> 6] >> (a & 63)) & 1)
            outSeen1 |= 1u << i;
          else
            outSeen0 |= 1u << i;
        }
        continue;
      }

      // B: the y values compatible with a and the fixed output bits.
      uint64_t B[4] = {Sy[0], Sy[1], Sy[2], Sy[3]};
      for (unsigned f = 0; f < nOut; f++)
      {
        const uint64_t* m = t.M[a][outIdx[f]];
        if (outVal[f])
        {
          B[0] &= m[0];
          B[1] &= m[1];
          B[2] &= m[2];
          B[3] &= m[3];
        }
        else
        {
          B[0] &= ~m[0];
          B[1] &= ~m[1];
          B[2] &= ~m[2];
          B[3] &= ~m[3];
        }
      }
      if (emptySet(B))
        continue;

      xSurv[a >> 6] |= (uint64_t)1 << (a & 63);
      ySurv[0] |= B[0];
      ySurv[1] |= B[1];
      ySurv[2] |= B[2];
      ySurv[3] |= B[3];

      for (unsigned i = 0; i < w; i++)
      {
        const uint64_t* m = t.M[a][i];
        if ((outSeen1 & (1u << i)) == 0 && intersects(B, m))
          outSeen1 |= 1u << i;
        if ((outSeen0 & (1u << i)) == 0 &&
            ((B[0] & ~m[0]) | (B[1] & ~m[1]) | (B[2] & ~m[2]) |
             (B[3] & ~m[3])) != 0)
          outSeen0 |= 1u << i;
      }
    }
  }

  if (emptySet(xSurv))
    return CONFLICT;

  if (fixAgreedBits(x, w, xSurv))
    progress = true;
  if (!aliased && fixAgreedBits(y, w, ySurv))
    progress = true;
  for (unsigned i = 0; i < w; i++)
  {
    if (output.isFixed(i))
      continue;
    const bool canBeOne = (outSeen1 >> i) & 1;
    const bool canBeZero = (outSeen0 >> i) & 1;
    assert(canBeOne || canBeZero); // some pair survived.
    if (canBeOne == canBeZero)
      continue;
    output.setFixed(i, true);
    output.setValue(i, canBeOne);
    progress = true;
  }
  return NO_CHANGE;
}

// ------------------- exact reasoning over small domains -------------------
//
// When few operand bits are unfixed the joint candidate space is tiny
// (2^unfixed pairs), and the relation can be solved exactly over the FULL
// width: enumerate every assignment of the unfixed bits, drop those whose
// product contradicts a fixed output bit, and fix every bit all survivors
// agree on. Unlike the low-8 solve this catches high-bit correlations; it
// fires exactly where the residual imprecision was measured to live
// (states with nearly-determined operands).

static const unsigned LOG_MAX_WIDTH = 14; // logGroupExactPass's domain.

// Fix the unfixed bits of v where the survivors' AND and OR agree. The
// survivor set satisfies v's fixed bits by construction.
static bool fixFromJoin(FixedBits& v, const uint64_t* andAcc,
                        const uint64_t* orAcc, unsigned words)
{
  const unsigned width = v.getWidth();
  bool changed = false;
  for (unsigned w = 0; w < words; w++)
  {
    const uint64_t liveMask = (w == words - 1 && (width & 63) != 0)
                                  ? (((uint64_t)1 << (width & 63)) - 1)
                                  : ~(uint64_t)0;
    uint64_t f, one;
    v.fillPackedWord(w, f, one);
    const uint64_t add = ~(andAcc[w] ^ orAcc[w]) & ~f & liveMask;
    if (add != 0)
    {
      v.fixWordBits(w, add, andAcc[w]);
      changed = true;
    }
  }
  return changed;
}

// One pass of the bounded enumeration. Sets `progress` when a bit was
// newly fixed; CONFLICT when no assignment is consistent.
Result smallDomainPass(FixedBits& x, FixedBits& y, FixedBits& output,
                       bool& progress)
{
  const unsigned width = x.getWidth();
  const unsigned words = (width + 63) / 64;
  const bool aliased = (&x == &y);

  // At width <= 8 the low-bits solve is already exactly the full relation;
  // re-deriving its result by enumeration is pure waste.
  if (width <= 8)
    return NO_CHANGE;

  // Never strengthen the all-unfixed state. A square's structure fixes
  // bits "from nothing" (bit 1 of t*t is always zero), but propagate()'s
  // scheduler only visits a node once something near it has fixed bits,
  // so deriving from bottom leaves never-visited nodes short of their own
  // transfer's fixpoint (checkAtFixedPoint). The same facts are derived
  // the moment any bit arrives — which is when the node gets scheduled.
  bool anyFixed = false;
  for (unsigned i = 0; i < width && !anyFixed; i++)
    anyFixed = x.isFixed(i) || y.isFixed(i) || output.isFixed(i);
  if (!anyFixed)
    return NO_CHANGE;

  // The assignments are walked in Gray-code order: consecutive ones differ
  // in a single unfixed bit, so the product updates with one shifted
  // add/subtract — O(words) per assignment, and the budget scales as
  // assignments * words. Inside the log pass's domain the full budget
  // upholds the maximal-precision contract; above it the tail of the
  // 2^u distribution costs far more than the few bits it yields, so the
  // walk is capped lower.
  const unsigned MAX_BITS_LIMIT = 16; // compile-time cap, sizes pos[].
  const unsigned MAX_BITS = (width <= LOG_MAX_WIDTH) ? MAX_BITS_LIMIT : 13;
  const unsigned long MAX_WORK = 1ul << 17;

  const unsigned unfixed = (width - x.countFixed()) +
                           (aliased ? 0 : (width - y.countFixed()));
  if (unfixed > MAX_BITS || ((unsigned long)1 << unfixed) * words > MAX_WORK)
    return NO_CHANGE;

  // With a fully unconstrained output the walk cannot prune the operands
  // and only yields the output join, so the 2^u cost is tail-heavy for
  // little return. At widths the log-group pass covers it computes that
  // join in group space instead; above them the few derivable bits are
  // not worth the walk.
  if (output.countFixed() == 0 && unfixed > 13)
    return NO_CHANGE;

  // Positions of the unfixed bits, x's first.
  unsigned char pos[MAX_BITS_LIMIT];
  unsigned nx = 0, k = 0;
  for (unsigned i = 0; i < width; i++)
    if (!x.isFixed(i))
      pos[k++] = (unsigned char)i;
  nx = k;
  if (!aliased)
    for (unsigned i = 0; i < width; i++)
      if (!y.isFixed(i))
        pos[k++] = (unsigned char)i;
  assert(k == unfixed);

  const unsigned INLINE_WORDS = 8;
  uint64_t stackBuf[11 * INLINE_WORDS];
  std::vector<uint64_t> heapBuf;
  uint64_t* buf = stackBuf;
  if (words > INLINE_WORDS)
  {
    heapBuf.resize(11 * words);
    buf = heapBuf.data();
  }
  uint64_t* a = buf;
  uint64_t* b = buf + words;
  uint64_t* p = buf + 2 * words;
  uint64_t* xAnd = buf + 3 * words;
  uint64_t* xOr = buf + 4 * words;
  uint64_t* yAnd = buf + 5 * words;
  uint64_t* yOr = buf + 6 * words;
  uint64_t* oAnd = buf + 7 * words;
  uint64_t* oOr = buf + 8 * words;
  uint64_t* aBase = buf + 9 * words;
  uint64_t* bBase = buf + 10 * words;

  for (unsigned w = 0; w < words; w++)
  {
    uint64_t f, one;
    x.fillPackedWord(w, f, one);
    aBase[w] = one;
    if (aliased)
      bBase[w] = one;
    else
    {
      y.fillPackedWord(w, f, one);
      bBase[w] = one;
    }
  }

  // The output's fixed bits, hoisted out of the walk.
  std::vector<uint64_t> oBuf(2 * words);
  uint64_t* oF = oBuf.data();
  uint64_t* oV = oBuf.data() + words;
  uint64_t oAnyFixed = 0;
  for (unsigned w = 0; w < words; w++)
  {
    output.fillPackedWord(w, oF[w], oV[w]);
    oAnyFixed |= oF[w];
  }
  // With no output constraint every assignment survives: the operand
  // joins cannot prune, and the walk's only yield is the output join —
  // which saturates long before the walk ends. Track only the output
  // accumulators and stop once every live bit has been seen both ways.
  const bool outFree = (oAnyFixed == 0);

  // dst +=/-= (src << shift), mod 2^(64*words).
  const auto addSubShifted = [words](uint64_t* dst, const uint64_t* src,
                                     unsigned shift, bool subtract) {
    if (shift >= words * 64)
      return;
    const unsigned wo = shift >> 6, sh = shift & 63;
    uint64_t carry = 0;
    for (unsigned w = wo; w < words; w++)
    {
      uint64_t s = src[w - wo] << sh;
      if (sh != 0 && w - wo > 0)
        s |= src[w - wo - 1] >> (64 - sh);
      if (!subtract)
      {
        const uint64_t r = dst[w] + s;
        uint64_t c = (r < s) ? 1 : 0;
        const uint64_t r2 = r + carry;
        c += (r2 < carry) ? 1 : 0;
        dst[w] = r2;
        carry = c;
      }
      else
      {
        const uint64_t sub = s + carry;
        const uint64_t nb = ((sub < s) || (dst[w] < sub)) ? 1 : 0;
        dst[w] -= sub;
        carry = nb;
      }
    }
  };
  // dst +=/-= (1 << shift), mod 2^(64*words).
  const auto addSubBit = [words](uint64_t* dst, unsigned shift,
                                 bool subtract) {
    if (shift >= words * 64)
      return;
    unsigned w = shift >> 6;
    uint64_t c = (uint64_t)1 << (shift & 63);
    if (!subtract)
      for (; w < words && c != 0; w++)
      {
        const uint64_t r = dst[w] + c;
        c = (r < c) ? 1 : 0;
        dst[w] = r;
      }
    else
      for (; w < words && c != 0; w++)
      {
        const uint64_t nb = (dst[w] < c) ? 1 : 0;
        dst[w] -= c;
        c = nb;
      }
  };

  memcpy(a, aBase, words * sizeof(uint64_t));
  memcpy(b, bBase, words * sizeof(uint64_t));
  mulLowWords(p, a, b, words);

  bool anySurvivor = false;
  for (unsigned long m = 0;; m++)
  {
    // Evaluate the current assignment.
    if (outFree)
    {
      if (!anySurvivor)
      {
        anySurvivor = true;
        for (unsigned w = 0; w < words; w++)
          oAnd[w] = oOr[w] = p[w];
      }
      else
        for (unsigned w = 0; w < words; w++)
        {
          oAnd[w] &= p[w];
          oOr[w] |= p[w];
        }
      if ((m & 15) == 15)
      {
        // Saturated once every live bit has been seen as 0 and as 1.
        bool saturated = true;
        for (unsigned w = 0; w < words && saturated; w++)
        {
          const uint64_t liveMask = (w == words - 1 && (width & 63) != 0)
                                        ? (((uint64_t)1 << (width & 63)) - 1)
                                        : ~(uint64_t)0;
          saturated = ((oOr[w] & ~oAnd[w]) & liveMask) == liveMask;
        }
        if (saturated)
          break;
      }
    }
    else
    {
      bool ok = true;
      for (unsigned w = 0; w < words && ok; w++)
        ok = ((p[w] & oF[w]) == oV[w]);
      if (ok)
      {
        if (!anySurvivor)
        {
          anySurvivor = true;
          for (unsigned w = 0; w < words; w++)
          {
            xAnd[w] = xOr[w] = a[w];
            yAnd[w] = yOr[w] = b[w];
            oAnd[w] = oOr[w] = p[w];
          }
        }
        else
          for (unsigned w = 0; w < words; w++)
          {
            xAnd[w] &= a[w];
            xOr[w] |= a[w];
            yAnd[w] &= b[w];
            yOr[w] |= b[w];
            oAnd[w] &= p[w];
            oOr[w] |= p[w];
          }
      }
    }

    if (m + 1 >= ((unsigned long)1 << k))
      break;

    // Gray step: flip the unfixed bit indexed by ctz(m+1).
    const unsigned t = ::stp::countTrailingZeroes64(m + 1);
    const unsigned i = pos[t];
    const uint64_t bit = (uint64_t)1 << (i & 63);
    if (aliased || t < nx) // an x bit (and for a square, both operands).
    {
      if (aliased)
      {
        // p tracks a^2: use the value of a *without* bit i either side.
        if ((a[i >> 6] & bit) == 0)
        {
          addSubShifted(p, a, i + 1, false);
          addSubBit(p, 2 * i, false);
          a[i >> 6] |= bit;
          b[i >> 6] |= bit;
        }
        else
        {
          a[i >> 6] &= ~bit;
          b[i >> 6] &= ~bit;
          addSubShifted(p, a, i + 1, true);
          addSubBit(p, 2 * i, true);
        }
      }
      else if ((a[i >> 6] & bit) == 0)
      {
        addSubShifted(p, b, i, false);
        a[i >> 6] |= bit;
      }
      else
      {
        addSubShifted(p, b, i, true);
        a[i >> 6] &= ~bit;
      }
    }
    else // a y bit.
    {
      if ((b[i >> 6] & bit) == 0)
      {
        addSubShifted(p, a, i, false);
        b[i >> 6] |= bit;
      }
      else
      {
        addSubShifted(p, a, i, true);
        b[i >> 6] &= ~bit;
      }
    }
  }

  if (!anySurvivor)
    return CONFLICT;

  if (!outFree)
  {
    // With an unconstrained output every pair survived, so the operand
    // joins are full and can fix nothing.
    if (fixFromJoin(x, xAnd, xOr, words))
      progress = true;
    if (!aliased && fixFromJoin(y, yAnd, yOr, words))
      progress = true;
  }
  if (fixFromJoin(output, oAnd, oOr, words))
    progress = true;
  return NO_CHANGE;
}

// --------------- exact reasoning via the odd group's structure ---------------
//
// Writing v = 2^s * u with u odd, x*y = 2^(s+t) * (u*w mod 2^(k-s-t)), and
// the odd residues mod 2^m form {±1} x <3> (cyclic of order 2^(m-2) for
// m >= 3). In log space multiplication is exponent addition, so "which u
// in this stratum have a partner w making the product land in the allowed
// set" is a difference set over Z/2 x Z/2^(m-2), computable by OR-ing
// rotated bitset rows — no pairwise enumeration. Together with the
// stratification by trailing zeros this yields the exact full join for
// any state at width k, in time polynomial in 2^(k)/64 words rather than
// pairs. Gated to 9 <= k <= LOG_MAX_WIDTH and to states the bounded
// enumeration doesn't already solve exactly.

struct OddLogTables
{
  // Per modulus 2^m: value -> (sign<<15 | exp), and (sign, exp) -> value.
  std::vector<uint16_t> v2l[LOG_MAX_WIDTH + 1];
  std::vector<uint16_t> l2v[LOG_MAX_WIDTH + 1];

  OddLogTables()
  {
    for (unsigned m = 3; m <= LOG_MAX_WIDTH; m++)
    {
      const unsigned mod = 1u << m, half = 1u << (m - 2);
      v2l[m].assign(mod, 0);
      l2v[m].assign(2 * half, 0);
      unsigned v = 1;
      for (unsigned e = 0; e < half; e++)
      {
        v2l[m][v] = (uint16_t)e;
        l2v[m][e] = (uint16_t)v;
        const unsigned neg = (mod - v) & (mod - 1);
        v2l[m][neg] = (uint16_t)(0x8000u | e);
        l2v[m][half + e] = (uint16_t)neg;
        v = (v * 3) & (mod - 1);
      }
    }
  }
};

static const OddLogTables& oddLogTables()
{
  static const OddLogTables t; // ~100KB, built on first use.
  return t;
}

// Odd residues mod 2^m as two sign rows of 2^(m-2) bits (m <= 14 -> at
// most 64 words per row).
struct OddSet
{
  static const unsigned MAXW = (1u << (LOG_MAX_WIDTH - 2)) / 64;
  uint64_t row[2][MAXW];
  unsigned m, half, words;

  void clear(unsigned m_)
  {
    m = m_;
    half = (m >= 2) ? (1u << (m - 2)) : 1;
    words = (half + 63) / 64;
    memset(row[0], 0, words * sizeof(uint64_t));
    memset(row[1], 0, words * sizeof(uint64_t));
  }
  void addValue(unsigned v)
  {
    if (m < 3)
    {
      row[(m == 2 && v == 3) ? 1 : 0][0] |= 1;
      return;
    }
    const uint16_t l = oddLogTables().v2l[m][v];
    row[l >> 15][(l & 0x7fffu) >> 6] |= (uint64_t)1 << (l & 63);
  }
  bool contains(unsigned v) const
  {
    if (m < 3)
      return (row[(m == 2 && v == 3) ? 1 : 0][0] & 1) != 0;
    const uint16_t l = oddLogTables().v2l[m][v];
    return (row[l >> 15][(l & 0x7fffu) >> 6] >> (l & 63)) & 1;
  }
  bool empty() const
  {
    uint64_t o = 0;
    for (unsigned s = 0; s < 2; s++)
      for (unsigned w = 0; w < words; w++)
        o |= row[s][w];
    return o == 0;
  }
  unsigned count() const
  {
    unsigned c = 0;
    for (unsigned s = 0; s < 2; s++)
      for (unsigned w = 0; w < words; w++)
        c += ::stp::popCount64(row[s][w]);
    return c;
  }
  bool full() const
  {
    const uint64_t top =
        (half & 63) ? (((uint64_t)1 << (half & 63)) - 1) : ~(uint64_t)0;
    for (unsigned s = 0; s < 2; s++)
      for (unsigned w = 0; w < words; w++)
        if ((row[s][w] | ((w == words - 1) ? ~top : 0)) != ~(uint64_t)0)
          return false;
    return true;
  }
  // Reduce mod 2^mNew (mNew <= m): exponent rows fold cyclically (ord(3)
  // divides), signs are preserved.
  void projectTo(OddSet& out, unsigned mNew) const
  {
    out.clear(mNew);
    if (m < 3 || mNew < 3)
    {
      // Tiny targets: fall back to elementwise via values.
      for (unsigned sgn = 0; sgn < 2; sgn++)
        for (unsigned w = 0; w < words; w++)
        {
          uint64_t bits = row[sgn][w];
          while (bits)
          {
            const unsigned e = w * 64 + ::stp::countTrailingZeroes64(bits);
            bits &= bits - 1;
            const unsigned v = (m < 3)
                                   ? ((m == 2 && sgn) ? 3u : 1u)
                                   : oddLogTables().l2v[m][sgn * half + e];
            out.addValue(v & ((1u << mNew) - 1));
          }
        }
      return;
    }
    const unsigned newHalf = out.half;
    for (unsigned sgn = 0; sgn < 2; sgn++)
    {
      if (newHalf >= 64)
      {
        const unsigned nwm = out.words - 1; // power of two
        for (unsigned w = 0; w < words; w++)
          out.row[sgn][w & nwm] |= row[sgn][w];
      }
      else
      {
        const uint64_t chunkMask = ((uint64_t)1 << newHalf) - 1;
        uint64_t acc = 0;
        for (unsigned w = 0; w < words; w++)
        {
          uint64_t v = row[sgn][w];
          for (unsigned off = 0; off < 64 && (w * 64 + off) < half;
               off += newHalf)
            acc |= (v >> off) & chunkMask;
        }
        out.row[sgn][0] |= acc;
      }
    }
  }
};

// dst.row[.] |= rotate(src.row[.], r) with the sign twist sb.
static void orRotatedRow(uint64_t* dst, const uint64_t* src, unsigned r,
                         unsigned half, unsigned words)
{
  r &= (half - 1);
  if (half <= 64)
  {
    const uint64_t mask =
        (half == 64) ? ~(uint64_t)0 : (((uint64_t)1 << half) - 1);
    uint64_t v = src[0] & mask;
    if (r)
      v = ((v << r) | (v >> (half - r))) & mask;
    dst[0] |= v;
    return;
  }
  // words is a power of two (half = 2^(m-2)), so modular indexing is a
  // mask — the previous % here cost more than the ORs themselves.
  const unsigned wo = r >> 6, sh = r & 63, wm = words - 1;
  if (sh == 0)
  {
    for (unsigned w = 0; w < words; w++)
      dst[w] |= src[(w - wo) & wm];
  }
  else
  {
    for (unsigned w = 0; w < words; w++)
    {
      const unsigned s1 = (w - wo) & wm;
      const unsigned s0 = (s1 - 1) & wm;
      dst[w] |= (src[s1] << sh) | (src[s0] >> (64 - sh));
    }
  }
}

// out |= { a + b : a in A, b in B } (negate B's exponents for the
// difference set). Iterates the smaller operand, translating the larger;
// stops early once out saturates.
// Fill `out` completely (both sign rows over its modulus).
static void setFull(OddSet& out)
{
  const uint64_t top = (out.half >= 64 || out.half == 0)
                           ? ~(uint64_t)0
                           : (((uint64_t)1 << out.half) - 1);
  for (unsigned s = 0; s < 2; s++)
    for (unsigned w = 0; w < out.words; w++)
      out.row[s][w] = (w == out.words - 1) ? top : ~(uint64_t)0;
}

static void accumulateSum(OddSet& out, const OddSet& A, const OddSet& B,
                          bool negateB)
{
  // Pigeonhole shortcuts on the group of size 2*half: a difference set
  // A (-) B is full once |B| exceeds A's hole count (some translate of B
  // must hit A for every offset), and a sumset is full once
  // |A| + |B| exceeds the group size.
  {
    const unsigned groupSize = 2 * out.half;
    const unsigned cA = A.count(), cB = B.count();
    if (cA + cB > groupSize)
    {
      setFull(out);
      return;
    }
    if (negateB && cB > groupSize - cA)
    {
      setFull(out);
      return;
    }
  }
  const OddSet* iter = &B;
  const OddSet* base = &A;
  bool negateIter = negateB;
  OddSet Brefl;
  if (A.count() < B.count())
  {
    if (!negateB)
    {
      // a + b is symmetric: iterate the smaller side.
      iter = &A;
      base = &B;
    }
    else
    {
      // A (-) B = union over a in A of translate(reflect(B), a): reflect
      // once, then iterate the (smaller) A with plain offsets.
      Brefl.clear(B.m);
      const unsigned half_ = B.half;
      for (unsigned s = 0; s < 2; s++)
        for (unsigned w = 0; w < B.words; w++)
        {
          uint64_t bits = B.row[s][w];
          while (bits)
          {
            const unsigned e = w * 64 + ::stp::countTrailingZeroes64(bits);
            bits &= bits - 1;
            const unsigned er = (half_ - e) & (half_ - 1);
            Brefl.row[s][er >> 6] |= (uint64_t)1 << (er & 63);
          }
        }
      iter = &A;
      base = &Brefl;
      negateIter = false;
    }
  }
  const unsigned half = out.half, words = out.words;

  unsigned sinceCheck = 0;
  for (unsigned sb = 0; sb < 2; sb++)
    for (unsigned w = 0; w < words; w++)
    {
      uint64_t bits = iter->row[sb][w];
      while (bits)
      {
        const unsigned eb = w * 64 + ::stp::countTrailingZeroes64(bits);
        bits &= bits - 1;
        const unsigned r = negateIter ? ((half - eb) & (half - 1)) : eb;
        for (unsigned sa = 0; sa < 2; sa++)
          orRotatedRow(out.row[sa ^ sb], base->row[sa], r, half, words);
        if (++sinceCheck >= 8)
        {
          sinceCheck = 0;
          if (out.full())
            return;
        }
      }
    }
}

// dst |= src lifted from modulus 2^src.m to dst's larger modulus: the
// exponent row of the coarser set tiles cyclically (3^e mod 2^m depends
// only on e mod 2^(m-2)), signs map straight across.
static void liftOrInto(OddSet& dst, const OddSet& src)
{
  assert(dst.m >= src.m);
  if (src.m < 3)
  {
    // Coarse sign-only information: expand elementwise.
    for (unsigned sgn = 0; sgn < 2; sgn++)
      if (src.row[sgn][0] & 1)
      {
        // Every odd value with that residue mod 2^src.m.
        const unsigned mod = 1u << src.m;
        const unsigned res = (src.m == 2 && sgn) ? 3u : 1u;
        for (unsigned u = 1; u < (2u * dst.half); u += 2)
          if (src.m < 2 || (u & (mod - 1)) == res)
            dst.addValue(u);
      }
    return;
  }
  const unsigned sh = src.half, dw = dst.words;
  for (unsigned sgn = 0; sgn < 2; sgn++)
  {
    if (sh >= 64)
    {
      for (unsigned w = 0; w < dw; w++)
        dst.row[sgn][w] |= src.row[sgn][w % src.words];
    }
    else
    {
      uint64_t pat = src.row[sgn][0];
      for (unsigned width = sh; width < 64; width <<= 1)
        pat |= pat << width;
      for (unsigned w = 0; w < dw; w++)
        dst.row[sgn][w] |= pat;
    }
  }
}

// Emit every element of `set` (odd part u, value u << shift) into the
// value join accumulators.
static void emitAll(const OddSet& set, unsigned shift, unsigned k,
                    uint64_t& vAnd, uint64_t& vOr, bool& any)
{
  const unsigned bigHalf = set.half;
  for (unsigned sgn = 0; sgn < 2; sgn++)
    for (unsigned w = 0; w < set.words; w++)
    {
      uint64_t bits = set.row[sgn][w];
      while (bits)
      {
        const unsigned e = w * 64 + ::stp::countTrailingZeroes64(bits);
        bits &= bits - 1;
        const unsigned u = (set.m < 3)
                               ? ((set.m == 2 && sgn) ? 3u : 1u)
                               : oddLogTables().l2v[set.m][sgn * bigHalf + e];
        const uint64_t v = ((uint64_t)u << shift) & ((1u << k) - 1);
        vAnd &= v;
        vOr |= v;
        any = true;
      }
    }
}

// The exact full-width join for k <= LOG_MAX_WIDTH via the group
// decomposition. Values fit one word (k <= 14).
Result logGroupExactPass(FixedBits& x, FixedBits& y, FixedBits& output,
                         bool& progress, bool& fired)
{
  const unsigned k = x.getWidth();
  if (k < 9 || k > LOG_MAX_WIDTH)
    return NO_CHANGE;

  // The bounded enumeration already produced the exact join for small
  // unfixed counts; only larger states need this pass. When the output is
  // completely unconstrained the enumeration bows out earlier (its walk
  // can only feed the output join), so this pass takes over from there.
  const bool aliased = (&x == &y);
  const unsigned unfixed =
      (k - x.countFixed()) + (aliased ? 0 : (k - y.countFixed()));
  const unsigned enumCovers = (output.countFixed() == 0) ? 13 : 16;
  if (unfixed <= enumCovers)
    return NO_CHANGE;

  // Nothing fixed anywhere -> the join fixes nothing.
  bool anyFixed = false, anyOut = false, xAll = true, yAll = true;
  for (unsigned i = 0; i < k; i++)
  {
    anyOut = anyOut || output.isFixed(i);
    xAll = xAll && !x.isFixed(i);
    yAll = yAll && !y.isFixed(i);
    anyFixed = anyFixed || x.isFixed(i) || y.isFixed(i);
  }
  anyFixed = anyFixed || anyOut;
  if (!anyFixed)
    return NO_CHANGE;
  // With an unconstrained output and one fully free operand, the join
  // fixes only the trailing zeros the core already derives.
  if (!anyOut && (xAll || yAll))
    return NO_CHANGE;

  fired = true; // the result below is the exact join: never rerun.

  uint64_t xF, xV, yF, yV, oF, oV;
  x.fillPackedWord(0, xF, xV);
  y.fillPackedWord(0, yF, yV);
  output.fillPackedWord(0, oF, oV);

  static OddSet Xs[LOG_MAX_WIDTH], Ys[LOG_MAX_WIDTH], Os[LOG_MAX_WIDTH];
  for (unsigned s = 0; s < k; s++)
  {
    Xs[s].clear(k - s);
    Ys[s].clear(k - s);
    Os[s].clear(k - s);
  }
  const unsigned mask = (1u << k) - 1;
  const bool xHas0 = ((0 ^ xV) & xF) == 0, yHas0 = ((0 ^ yV) & yF) == 0,
             oHas0 = ((0 ^ oV) & oF) == 0;
  for (unsigned v = 1; v <= mask; v++)
  {
    const unsigned s = ::stp::countTrailingZeroes64(v), u = v >> s;
    if (((v ^ xV) & xF) == 0)
      Xs[s].addValue(u);
    if (!aliased && ((v ^ yV) & yF) == 0)
      Ys[s].addValue(u);
    if (((v ^ oV) & oF) == 0)
      Os[s].addValue(u);
  }

  uint64_t xAnd = mask, xOr = 0, yAnd = mask, yOr = 0, oAnd = mask, oOr = 0;
  bool anyX = false, anyY = false, anyO = false;

  if (aliased)
  {
    // Squares: single free variable, test each element directly.
    if (xHas0 && oHas0)
    {
      xAnd = 0; // value 0 survives.
      anyX = true;
      oAnd &= 0;
      oOr |= 0;
      anyO = true;
    }
    for (unsigned s = 0; s < k; s++)
    {
      const unsigned m = k - s;
      const unsigned bigHalf = Xs[s].half;
      for (unsigned sgn = 0; sgn < 2; sgn++)
        for (unsigned w = 0; w < Xs[s].words; w++)
        {
          uint64_t bits = Xs[s].row[sgn][w];
          while (bits)
          {
            const unsigned e = w * 64 + ::stp::countTrailingZeroes64(bits);
            bits &= bits - 1;
            const unsigned u =
                (m < 3) ? ((m == 2 && sgn) ? 3u : 1u)
                        : oddLogTables().l2v[m][sgn * bigHalf + e];
            const uint64_t sq =
                (2 * s >= k) ? 0 : (((uint64_t)u * u) << (2 * s)) & mask;
            const bool okOut = ((sq ^ oV) & oF) == 0;
            if (!okOut)
              continue;
            const uint64_t v = ((uint64_t)u << s) & mask;
            xAnd &= v;
            xOr |= v;
            anyX = true;
            oAnd &= sq;
            oOr |= sq;
            anyO = true;
          }
        }
    }
    if (!anyX)
      return CONFLICT;
    // x and y are the same object; the output join comes from squares.
    bool ch = false;
    for (unsigned i = 0; i < k; i++)
    {
      if (!x.isFixed(i) && (((xAnd >> i) & 1) == ((xOr >> i) & 1)))
      {
        x.setFixed(i, true);
        x.setValue(i, (xAnd >> i) & 1);
        ch = true;
      }
      if (anyO && !output.isFixed(i) && (((oAnd >> i) & 1) == ((oOr >> i) & 1)))
      {
        output.setFixed(i, true);
        output.setValue(i, (oAnd >> i) & 1);
        ch = true;
      }
    }
    if (ch)
      progress = true;
    return NO_CHANGE;
  }

  // Per-stratum survivor filters, unioned across partner strata; the
  // final emission intersects each stratum with its filter once. The
  // fullness flags let saturated pairs skip their correlations entirely.
  static OddSet xFilt[LOG_MAX_WIDTH], yFilt[LOG_MAX_WIDTH],
      oFilt[LOG_MAX_WIDTH];
  bool xFull[LOG_MAX_WIDTH], yFull[LOG_MAX_WIDTH], oFull[LOG_MAX_WIDTH];
  for (unsigned s = 0; s < k; s++)
  {
    xFilt[s].clear(k - s);
    yFilt[s].clear(k - s);
    oFilt[s].clear(k - s);
    xFull[s] = yFull[s] = oFull[s] = false;
  }

  // x == 0 pairs: every admitted y survives (product 0), and vice versa.
  if (xHas0 && oHas0)
  {
    bool anyPartner = yHas0;
    for (unsigned t = 0; t < k && !anyPartner; t++)
      anyPartner = !Ys[t].empty();
    if (anyPartner)
    {
      xAnd = 0;
      anyX = true;
      oAnd = 0;
      anyO = true;
      if (yHas0)
      {
        yAnd = 0;
        anyY = true;
      }
      for (unsigned t = 0; t < k; t++)
      {
        liftOrInto(yFilt[t], Ys[t]);
        yFull[t] = yFull[t] || yFilt[t].full();
      }
    }
  }
  if (yHas0 && oHas0)
  {
    bool anyPartner = xHas0;
    for (unsigned s = 0; s < k && !anyPartner; s++)
      anyPartner = !Xs[s].empty();
    if (anyPartner)
    {
      yAnd = 0;
      anyY = true;
      oAnd = 0;
      anyO = true;
      if (xHas0)
      {
        xAnd = 0;
        anyX = true;
      }
      for (unsigned s = 0; s < k; s++)
      {
        liftOrInto(xFilt[s], Xs[s]);
        xFull[s] = xFull[s] || xFilt[s].full();
      }
    }
  }

  for (unsigned s = 0; s < k; s++)
  {
    if (Xs[s].empty())
      continue;
    for (unsigned t = 0; t < k; t++)
    {
      if (Ys[t].empty())
        continue;
      if (s + t >= k)
      {
        // Product is zero regardless of the odd parts.
        if (!oHas0)
          continue;
        oAnd = 0;
        anyO = true;
        if (!xFull[s])
        {
          liftOrInto(xFilt[s], Xs[s]);
          xFull[s] = xFilt[s].full();
        }
        if (!yFull[t])
        {
          liftOrInto(yFilt[t], Ys[t]);
          yFull[t] = yFilt[t].full();
        }
        continue;
      }
      if (xFull[s] && yFull[t] && oFull[s + t])
        continue; // nothing left for this pair to contribute.
      const unsigned m = k - s - t;
      const OddSet& Om = Os[s + t];
      if (Om.empty())
        continue;

      OddSet Xm, Ym;
      Xs[s].projectTo(Xm, m);
      Ys[t].projectTo(Ym, m);

      // Existence check once: if no product of these strata can land in
      // Om, the pair contributes nothing to any side.
      OddSet D;
      D.clear(m);
      accumulateSum(D, Om, Ym, /*negate*/ true);
      if (D.empty())
        continue;

      if (!xFull[s])
      {
        liftOrInto(xFilt[s], D);
        xFull[s] = xFilt[s].full();
      }
      if (!yFull[t])
      {
        OddSet E;
        E.clear(m);
        accumulateSum(E, Om, Xm, true);
        liftOrInto(yFilt[t], E);
        yFull[t] = yFilt[t].full();
      }
      if (!oFull[s + t])
      {
        OddSet P;
        P.clear(m);
        accumulateSum(P, Xm, Ym, false);
        for (unsigned sgn = 0; sgn < 2; sgn++)
          for (unsigned w = 0; w < P.words; w++)
            oFilt[s + t].row[sgn][w] |= Om.row[sgn][w] & P.row[sgn][w];
        oFull[s + t] = oFilt[s + t].full();
      }
    }
  }

  // Emit: survivors of each stratum = stratum set AND its filter.
  for (unsigned s = 0; s < k; s++)
  {
    OddSet t1;
    t1.clear(k - s);
    for (unsigned sgn = 0; sgn < 2; sgn++)
      for (unsigned w = 0; w < t1.words; w++)
        t1.row[sgn][w] = Xs[s].row[sgn][w] & xFilt[s].row[sgn][w];
    emitAll(t1, s, k, xAnd, xOr, anyX);
    for (unsigned sgn = 0; sgn < 2; sgn++)
      for (unsigned w = 0; w < t1.words; w++)
        t1.row[sgn][w] = Ys[s].row[sgn][w] & yFilt[s].row[sgn][w];
    emitAll(t1, s, k, yAnd, yOr, anyY);
    for (unsigned sgn = 0; sgn < 2; sgn++)
      for (unsigned w = 0; w < t1.words; w++)
        t1.row[sgn][w] = Os[s].row[sgn][w] & oFilt[s].row[sgn][w];
    emitAll(t1, s, k, oAnd, oOr, anyO);
  }

  if (!anyX || !anyY || !anyO)
    return CONFLICT;

  bool ch = false;
  for (unsigned i = 0; i < k; i++)
  {
    if (!x.isFixed(i) && (((xAnd >> i) & 1) == ((xOr >> i) & 1)))
    {
      x.setFixed(i, true);
      x.setValue(i, (xAnd >> i) & 1);
      ch = true;
    }
    if (!y.isFixed(i) && (((yAnd >> i) & 1) == ((yOr >> i) & 1)))
    {
      y.setFixed(i, true);
      y.setValue(i, (yAnd >> i) & 1);
      ch = true;
    }
    if (!output.isFixed(i) && (((oAnd >> i) & 1) == ((oOr >> i) & 1)))
    {
      output.setFixed(i, true);
      output.setValue(i, (oAnd >> i) & 1);
      ch = true;
    }
  }
  if (ch)
    progress = true;
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

  bool logDone = false;

  // Alternate the views of the constraint — the column fixpoint, the
  // inverse relation, and the exact low-bits solve — until a joint fixed
  // point. Each productive pass fixes at least one previously unfixed
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
    if (CONFLICT ==
        exactLowBitsPass(*children[0], *children[1], output, progress))
      return CONFLICT;
    if (CONFLICT ==
        smallDomainPass(*children[0], *children[1], output, progress))
      return CONFLICT;
    if (!logDone)
    {
      // One firing computes the exact join, after which no pass can add
      // anything; the flag stops the expensive recomputation on the
      // wrap-up iterations of this loop.
      bool fired = false;
      if (CONFLICT == logGroupExactPass(*children[0], *children[1], output,
                                        progress, fired))
        return CONFLICT;
      logDone = fired;
    }
    if (!progress)
      break;
  }

  return NOT_IMPLEMENTED;
}
}
}

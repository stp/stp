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

#include <cstdint>
#include <vector>

// The signed and unsigned versions of the four comparison operations: > < >= <=

// Establishes consistency over the intervals of the operations, then fixes
// child bits against the other side's extremum.
//
// Signed comparisons are mapped onto unsigned ones by XORing the sign bit
// ("biasing"): x <=s y iff (x ^ msb) <=u (y ^ msb). In the biased domain
// the MSB behaves like every other bit.
//
// When the comparison is known to hold, the minimum of the smaller side
// and the maximum of the larger side never change while bits are fixed
// (fixing a bit of the smaller side to zero keeps its minimum, fixing a
// bit of the larger side to one keeps its maximum), so whether a bit can
// be fixed reduces to comparing 2^i against delta = max - min. All the
// derivable bits are therefore those at or above a single threshold
// position, found with one multi-word subtraction.

// Trevor Hansen. BSD License.

namespace simplifier
{
namespace constantBitP
{

namespace
{

// The biased minimum and maximum words of one side. biasTop is nonzero
// only for the final word of a signed comparison.
inline void minMaxWord(const FixedBits& x, unsigned w, unsigned words,
                       uint64_t topMask, uint64_t biasTop, uint64_t& mn,
                       uint64_t& mx)
{
  uint64_t f, v;
  x.fillPackedWord(w, f, v);
  const bool top = (w == words - 1);
  if (top)
    v ^= f & biasTop;
  mn = v;
  mx = v | (~f & (top ? topMask : ~0ULL));
}

// Lexicographic three-way compare of (max of a) against (min of b).
int cmpMaxMin(const FixedBits& a, const FixedBits& b, unsigned words,
              uint64_t topMask, uint64_t biasTop)
{
  for (int w = (int)words - 1; w >= 0; w--)
  {
    uint64_t mnA, mxA, mnB, mxB;
    minMaxWord(a, w, words, topMask, biasTop, mnA, mxA);
    minMaxWord(b, w, words, topMask, biasTop, mnB, mxB);
    if (mxA != mnB)
      return mxA < mnB ? -1 : 1;
  }
  return 0;
}

// Lexicographic three-way compare of (min of a) against (max of b).
int cmpMinMax(const FixedBits& a, const FixedBits& b, unsigned words,
              uint64_t topMask, uint64_t biasTop)
{
  for (int w = (int)words - 1; w >= 0; w--)
  {
    uint64_t mnA, mxA, mnB, mxB;
    minMaxWord(a, w, words, topMask, biasTop, mnA, mxA);
    minMaxWord(b, w, words, topMask, biasTop, mnB, mxB);
    if (mnA != mxB)
      return mnA < mxB ? -1 : 1;
  }
  return 0;
}

// Given that lhs <= rhs (or lhs < rhs when strict) holds, fix child bits:
// an unfixed lhs bit i must be zero when min(lhs) + 2^i exceeds max(rhs),
// and an unfixed rhs bit i must be one when max(rhs) - 2^i undershoots
// min(lhs). Both conditions are exactly 2^i > delta (non-strict) or
// 2^i >= delta (strict) for delta = max(rhs) - min(lhs), so every
// derivable bit sits at or above one threshold position.
bool fixTrueCase(FixedBits& lhs, FixedBits& rhs, bool strict, unsigned words,
                 uint64_t topMask, uint64_t biasTop)
{
  const unsigned width = lhs.getWidth();

  const unsigned STACK_WORDS = 16; // up to 1024 bits on the stack.
  uint64_t stackBuf[STACK_WORDS];
  std::vector<uint64_t> heapBuf;
  uint64_t* delta = stackBuf;
  if (words > STACK_WORDS)
  {
    heapBuf.resize(words);
    delta = heapBuf.data();
  }

  // delta = max(rhs) - min(lhs), low to high with a borrow.
  uint64_t borrow = 0;
  for (unsigned w = 0; w < words; w++)
  {
    uint64_t mnL, mxL, mnR, mxR;
    minMaxWord(lhs, w, words, topMask, biasTop, mnL, mxL);
    minMaxWord(rhs, w, words, topMask, biasTop, mnR, mxR);
    const uint64_t d1 = mxR - mnL;
    delta[w] = d1 - borrow;
    borrow = (mxR < mnL) || (d1 < borrow);
  }
  // The intervals were consistent, so max(rhs) >= min(lhs).
  assert(borrow == 0);

  // Top set bit of delta, and whether delta is a power of two.
  int topBit = -1;
  bool single = false;
  for (int w = (int)words - 1; w >= 0; w--)
  {
    if (delta[w] != 0)
    {
      topBit = w * 64 + 63 - __builtin_clzll(delta[w]);
      single = (delta[w] & (delta[w] - 1)) == 0;
      for (int lower = w - 1; single && lower >= 0; lower--)
        single = delta[lower] == 0;
      break;
    }
  }

  // Bits at or above eligibleFrom can be fixed.
  const unsigned eligibleFrom =
      (unsigned)((strict && single) ? topBit : topBit + 1);
  if (eligibleFrom >= width)
    return false;

  bool changed = false;
  for (unsigned w = eligibleFrom / 64; w < words; w++)
  {
    const uint64_t wordMask = (w == words - 1) ? topMask : ~0ULL;
    uint64_t elig = wordMask;
    if (w == eligibleFrom / 64 && (eligibleFrom % 64) != 0)
      elig &= ~((1ULL << (eligibleFrom % 64)) - 1);
    const uint64_t biasW = (w == words - 1) ? biasTop : 0;

    uint64_t f, v;

    // lhs bits become biased zero.
    lhs.fillPackedWord(w, f, v);
    const uint64_t lhsFix = ~f & elig;
    if (lhsFix != 0)
    {
      lhs.fixWordBits(w, lhsFix, biasW & lhsFix);
      changed = true;
    }

    // rhs bits become biased one.
    rhs.fillPackedWord(w, f, v);
    const uint64_t rhsFix = ~f & elig;
    if (rhsFix != 0)
    {
      rhs.fixWordBits(w, rhsFix, rhsFix ^ (biasW & rhsFix));
      changed = true;
    }
  }
  return changed;
}

// c0 < c1 (strict) or c0 <= c1; signed comparisons set a sign-flipping bias.
Result wordCompare(FixedBits& c0, FixedBits& c1, FixedBits& output,
                   bool strict, bool isSigned)
{
  const unsigned width = c0.getWidth();
  assert(c1.getWidth() == width);

  const unsigned words = (width + 63) / 64;
  const uint64_t topMask =
      (width % 64 == 0) ? ~0ULL : ((1ULL << (width % 64)) - 1);
  const uint64_t biasTop = isSigned ? (1ULL << ((width - 1) % 64)) : 0;

  bool changed = false;

  // Entailed true: every value of c0 is below every value of c1.
  const int maxMin = cmpMaxMin(c0, c1, words, topMask, biasTop);
  if (strict ? maxMin < 0 : maxMin <= 0)
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
  const int minMax = cmpMinMax(c0, c1, words, topMask, biasTop);
  if (strict ? minMax >= 0 : minMax > 0)
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
      changed |= fixTrueCase(c0, c1, strict, words, topMask, biasTop);
    else
      // !(c0 < c1) is c1 <= c0, and !(c0 <= c1) is c1 < c0.
      changed |= fixTrueCase(c1, c0, !strict, words, topMask, biasTop);
  }

  return changed ? CHANGED : NO_CHANGE;
}
}

///////// Signed operations.

Result bvSignedLessThanBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output)
{
  return wordCompare(c0, c1, output, true, true);
}

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

Result bvSignedLessThanEqualsBothWays(FixedBits& c0, FixedBits& c1,
                                      FixedBits& output)
{
  return wordCompare(c0, c1, output, false, true);
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

///////// Unsigned operations.

Result bvLessThanBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output)
{
  return wordCompare(c0, c1, output, true, false);
}

Result bvLessThanBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 2);
  return bvLessThanBothWays(*children[0], *children[1], output);
}

Result bvGreaterThanBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output)
{
  return bvLessThanBothWays(c1, c0, output);
}

Result bvGreaterThanBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 2);
  return bvLessThanBothWays(*children[1], *children[0], output);
}

Result bvLessThanEqualsBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output)
{
  return wordCompare(c0, c1, output, false, false);
}

Result bvLessThanEqualsBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 2);
  return bvLessThanEqualsBothWays(*children[0], *children[1], output);
}

Result bvGreaterThanEqualsBothWays(FixedBits& c0, FixedBits& c1,
                                   FixedBits& output)
{
  return bvLessThanEqualsBothWays(c1, c0, output);
}

Result bvGreaterThanEqualsBothWays(vector<FixedBits*>& children,
                                   FixedBits& result)
{
  assert(children.size() == 2);
  return bvLessThanEqualsBothWays(*children[1], *children[0], result);
}
}
}

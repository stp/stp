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
#include "stp/Util/BitOps.h"
// FIXME: External library
#include "extlib-constbv/constantbv.h"

#include <cstdint>
#include <vector>

// Left shift, right shift.
// Trevor Hansen. BSD License.

// smtlib & x86 semantics differ for what happens when a value is shifted by
// greater
// than the bitWidth. On x86, in 64-bit mode, only the bottom 6 bits of the
// shift are
// used. In SMTLIB the total value is used.

namespace simplifier
{
namespace constantBitP
{

const bool debug_shift = false;

namespace
{
// The fixed/value bits packed into words, so the possible-shift set can be
// computed with word operations rather than bit-at-a-time probing. Widths
// up to 256 bits (the overwhelmingly common case) live on the stack.
struct PackedBits
{
  static const unsigned INLINE_WORDS = 4;
  uint64_t inlineStore[2 * INLINE_WORDS];
  uint64_t* fixed;
  uint64_t* value; // only meaningful where fixed.
  unsigned words;
  std::vector<uint64_t> heapStore;

  explicit PackedBits(const FixedBits& b) : words((b.getWidth() + 63) / 64)
  {
    allocate();
    b.fillPackedWords(fixed, value);
  }

  PackedBits(const PackedBits& o) : words(o.words)
  {
    allocate();
    copyFrom(o);
  }

  void copyFrom(const PackedBits& o)
  {
    assert(words == o.words);
    for (unsigned j = 0; j < words; j++)
    {
      fixed[j] = o.fixed[j];
      value[j] = o.value[j];
    }
  }

  bool isFixedBit(unsigned i) const
  {
    return (fixed[i >> 6] >> (i & 63)) & 1;
  }

  bool valueBit(unsigned i) const
  {
    return (value[i >> 6] >> (i & 63)) & 1;
  }

  // Word j of (m >> s). Bits above the width are zero because only bits
  // below the width are ever set.
  uint64_t shiftedWord(const uint64_t* m, unsigned s, unsigned j) const
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

  // Word j of (m << s). May carry set bits above the width; callers mask.
  uint64_t leftShiftedWord(const uint64_t* m, unsigned s, unsigned j) const
  {
    const int word = (int)j - (int)(s >> 6);
    const unsigned bit = s & 63;
    if (word < 0)
      return 0;
    uint64_t r = m[word] << bit;
    if (bit != 0 && word >= 1)
      r |= m[word - 1] >> (64 - bit);
    return r;
  }

  void fixBits(unsigned j, uint64_t mask, uint64_t values)
  {
    fixed[j] |= mask;
    value[j] = (value[j] & ~mask) | (values & mask);
  }

  // Bits of word j that lie below the width.
  static uint64_t widthMask(unsigned j, unsigned width)
  {
    const uint64_t base = (uint64_t)j * 64;
    if (base + 64 <= width)
      return ~(uint64_t)0;
    if (base >= width)
      return 0;
    return (((uint64_t)1 << (width - base)) - 1);
  }

private:
  void allocate()
  {
    if (words <= INLINE_WORDS)
    {
      fixed = inlineStore;
      value = inlineStore + words;
    }
    else
    {
      heapStore.resize(2 * words);
      fixed = heapStore.data();
      value = heapStore.data() + words;
    }
  }

  PackedBits& operator=(const PackedBits&); // use copyFrom.
};

// Meet (the union of what the two states admit), written into a.
void meetInto(PackedBits& a, const PackedBits& b)
{
  for (unsigned j = 0; j < a.words; j++)
  {
    a.fixed[j] &= b.fixed[j] & ~(a.value[j] ^ b.value[j]);
    a.value[j] &= a.fixed[j];
  }
}

// The shift operand must lie in the union of the possible shift amounts:
// the bit patterns of the possible finite shifts, unioned with whatever
// "shift >= bitWidth" allows when shifting everything out is possible.
// Fixes shift bits the union agrees on; CONFLICT if one contradicts a
// fixed bit.
Result applyShiftUnion(const unsigned bitWidth, PackedBits& packedShift,
                       const unsigned* possibleList, const unsigned nPossible,
                       const bool shiftOutPossible)
{
  const unsigned words = packedShift.words;

  // The union of the finite patterns: bits where they all agree are
  // fixed. (Patterns are < bitWidth, so any bits above word zero of the
  // union are fixed to zero.)
  uint64_t* vFixed = (uint64_t*)alloca(sizeof(uint64_t) * words);
  uint64_t* vValue = (uint64_t*)alloca(sizeof(uint64_t) * words);
  if (nPossible > 0)
  {
    const uint64_t ref = possibleList[0];
    uint64_t diff = 0;
    for (unsigned k = 1; k < nPossible; k++)
      diff |= ref ^ (uint64_t)possibleList[k];
    vFixed[0] = ~diff & PackedBits::widthMask(0, bitWidth);
    vValue[0] = ref & vFixed[0];
    for (unsigned j = 1; j < words; j++)
    {
      vFixed[j] = PackedBits::widthMask(j, bitWidth);
      vValue[j] = 0;
    }
  }
  else
    for (unsigned j = 0; j < words; j++)
      vFixed[j] = vValue[j] = 0;

  if (shiftOutPossible)
  {
    // What "shift >= bitWidth" forces, exactly as the maximally precise
    // comparison propagator would: possibleShift[bitWidth] was only set
    // when the maximum admitted shift value is >= bitWidth, so for every
    // unfixed bit an admitted value >= bitWidth with that bit one exists
    // (the maximum itself). An unfixed bit is therefore only ever forced
    // to one, precisely when clearing it drops the maximum admitted
    // value below bitWidth.
    uint64_t* wFixed = (uint64_t*)alloca(sizeof(uint64_t) * words);
    uint64_t* wValue = (uint64_t*)alloca(sizeof(uint64_t) * words);
    uint64_t* maxAdm = (uint64_t*)alloca(sizeof(uint64_t) * words);
    unsigned nonZeroHighWords = 0;
    for (unsigned j = 0; j < words; j++)
    {
      wFixed[j] = packedShift.fixed[j];
      wValue[j] = packedShift.value[j];
      maxAdm[j] = (packedShift.value[j] | ~packedShift.fixed[j]) &
                  PackedBits::widthMask(j, bitWidth);
      if (j > 0 && maxAdm[j] != 0)
        nonZeroHighWords++;
    }

    for (unsigned j = 0; j < words; j++)
    {
      uint64_t pending = ~packedShift.fixed[j] &
                         PackedBits::widthMask(j, bitWidth);
      while (pending)
      {
        const unsigned b = ::stp::countTrailingZeroes64(pending);
        pending &= pending - 1;
        const uint64_t bit = (uint64_t)1 << b;

        // Is (maxAdm with this bit cleared) < bitWidth?
        bool less;
        if (j == 0)
          less = (nonZeroHighWords == 0) &&
                 ((maxAdm[0] & ~bit) < (uint64_t)bitWidth);
        else
          less = (nonZeroHighWords == (maxAdm[j] == bit ? 1u : 0u)) &&
                 (maxAdm[0] < (uint64_t)bitWidth) &&
                 ((maxAdm[j] & ~bit) == 0);
        if (less)
        {
          wFixed[j] |= bit;
          wValue[j] |= bit;
        }
      }
    }

    if (nPossible > 0)
    {
      // Union: drop bits the >= case leaves open or disagrees on.
      for (unsigned j = 0; j < words; j++)
      {
        vFixed[j] &= wFixed[j] & ~(vValue[j] ^ wValue[j]);
        vValue[j] &= vFixed[j];
      }
    }
    else
    {
      // Only shifts >= bitWidth are possible.
      for (unsigned j = 0; j < words; j++)
      {
        vFixed[j] = wFixed[j];
        vValue[j] = wValue[j];
      }
    }
  }

  // Write the union into the shift.
  for (unsigned j = 0; j < words; j++)
  {
    if (vFixed[j] & packedShift.fixed[j] & (packedShift.value[j] ^ vValue[j]))
      return CONFLICT;
    packedShift.fixBits(j, vFixed[j], vValue[j]);
  }
  return NOT_IMPLEMENTED;
}

// Whether the concrete shift amount i is admitted by the fixed bits of the
// shift operand. Equivalent to FixedBits::unsignedHolds(i) for i < 2^64,
// given anyHighFixedOne = "some bit above word zero is fixed to one".
inline bool shiftHolds(const PackedBits& shift, bool anyHighFixedOne,
                       uint64_t i)
{
  if (anyHighFixedOne)
    return false;
  return (i & shift.fixed[0]) == (shift.value[0] & shift.fixed[0]);
}

bool anyFixedOneAboveWordZero(const PackedBits& shift)
{
  for (unsigned j = 1; j < shift.words; j++)
    if (shift.fixed[j] & shift.value[j])
      return true;
  return false;
}

// Bits of word j whose global index is >= threshold.
inline uint64_t bitsAtOrAbove(unsigned j, unsigned threshold)
{
  const uint64_t base = (uint64_t)j * 64;
  if (base >= threshold)
    return ~(uint64_t)0;
  if (base + 64 <= threshold)
    return 0;
  return ~(((uint64_t)1 << (threshold - base)) - 1);
}

// Whether shifting the operand right by s contradicts the fixed output
// bits: some column c <= width-1-s has both output[c] and op[c+s] fixed,
// to different values.
inline bool rightShiftDisagrees(const PackedBits& op, const PackedBits& out,
                                unsigned s)
{
  for (unsigned j = 0; j < out.words; j++)
  {
    const uint64_t opF = op.shiftedWord(op.fixed, s, j);
    if (opF == 0)
      continue;
    const uint64_t opV = op.shiftedWord(op.value, s, j);
    if (opF & out.fixed[j] & (opV ^ out.value[j]))
      return true;
  }
  return false;
}
}

namespace
{
inline uint64_t bitReverse64(uint64_t x)
{
  x = __builtin_bswap64(x);
  x = ((x & 0x0F0F0F0F0F0F0F0FULL) << 4) | ((x >> 4) & 0x0F0F0F0F0F0F0F0FULL);
  x = ((x & 0x3333333333333333ULL) << 2) | ((x >> 2) & 0x3333333333333333ULL);
  x = ((x & 0x5555555555555555ULL) << 1) | ((x >> 1) & 0x5555555555555555ULL);
  return x;
}

// The packed words of `src` with the bit order reversed over its width:
// reverse the word order and each word, giving the reverse of the padded
// words*64-bit value, then shift out the padding. Each output array needs
// `words` words.
void packReversed(const FixedBits& src, uint64_t* rf, uint64_t* rv)
{
  const unsigned width = src.getWidth();
  const unsigned words = (width + 63) / 64;
  const unsigned pad = words * 64 - width;

  uint64_t* f = (uint64_t*)alloca(sizeof(uint64_t) * words);
  uint64_t* v = (uint64_t*)alloca(sizeof(uint64_t) * words);
  src.fillPackedWords(f, v);

  for (unsigned j = 0; j < words; j++)
  {
    uint64_t lowF = bitReverse64(f[words - 1 - j]);
    uint64_t lowV = bitReverse64(v[words - 1 - j]);
    if (pad != 0)
    {
      const uint64_t highF = (j + 1 < words) ? bitReverse64(f[words - 2 - j]) : 0;
      const uint64_t highV = (j + 1 < words) ? bitReverse64(v[words - 2 - j]) : 0;
      lowF = (lowF >> pad) | (highF << (64 - pad));
      lowV = (lowV >> pad) | (highV << (64 - pad));
    }
    rf[j] = lowF;
    rv[j] = lowV;
  }
}

// Fix in `dst` the reversed bits of `revSrc` that `dst` does not have yet.
void mergeReversed(const FixedBits& revSrc, FixedBits& dst)
{
  const unsigned words = (dst.getWidth() + 63) / 64;
  uint64_t* rf = (uint64_t*)alloca(sizeof(uint64_t) * words);
  uint64_t* rv = (uint64_t*)alloca(sizeof(uint64_t) * words);
  packReversed(revSrc, rf, rv);

  for (unsigned j = 0; j < words; j++)
  {
    uint64_t df, dv;
    dst.fillPackedWord(j, df, dv);
    const uint64_t add = rf[j] & ~df;
    if (add != 0)
      dst.fixWordBits(j, add, rv[j]);
  }
}
}

Result bvRightShiftBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  const unsigned bitWidth = output.getWidth();

  assert(2 == children.size());

  FixedBits& op = *children[0];
  FixedBits& shift = *children[1];

  // Reversing the operand and the output turns the right shift into a
  // left shift.
  const unsigned words = (bitWidth + 63) / 64;
  uint64_t* rf = (uint64_t*)alloca(sizeof(uint64_t) * words);
  uint64_t* rv = (uint64_t*)alloca(sizeof(uint64_t) * words);

  FixedBits opReverse(bitWidth, false);
  packReversed(op, rf, rv);
  for (unsigned j = 0; j < words; j++)
    if (rf[j] != 0)
      opReverse.fixWordBits(j, rf[j], rv[j]);

  FixedBits outputReverse(bitWidth, false);
  packReversed(output, rf, rv);
  for (unsigned j = 0; j < words; j++)
    if (rf[j] != 0)
      outputReverse.fixWordBits(j, rf[j], rv[j]);

  vector<FixedBits*> args;
  args.push_back(&opReverse);
  args.push_back(&shift); // shift is unmodified.
  const Result result = bvLeftShiftBothWays(args, outputReverse);

  if (CONFLICT == result)
    return CONFLICT;

  // Write the reversed deductions back.
  mergeReversed(opReverse, op);
  mergeReversed(outputReverse, output);

  return result;
}

// The shift must be less than the position of the first alternation in the
// (fixed bits of the) output.
static unsigned getMaxShiftFromValueViaAlternation(const unsigned bitWidth,
                                                   const PackedBits& output)
{
  unsigned maxShiftFromValue = UINT_MAX;

  bool foundTrue = false;
  bool foundFalse = false;
  for (int i = bitWidth - 1; i >= 0; i--)
  {
    if (output.isFixedBit(i))
    {
      const bool v = output.valueBit(i);
      if (v && foundFalse)
      {
        maxShiftFromValue = i;
        break;
      }
      if (!v && foundTrue)
      {
        maxShiftFromValue = i;
        break;
      }
      if (v)
        foundTrue = true;
      else
        foundFalse = true;
    }
  }

  if (maxShiftFromValue != UINT_MAX)
    maxShiftFromValue = bitWidth - 2 - maxShiftFromValue;

  return maxShiftFromValue;
}

// The range of the values the fixed bits admit, clamped as the original
// FixedBits::getUnsignedMinMax: anything reaching past the low 32 bits
// saturates to UINT_MAX.
static void packedUnsignedMinMax(const PackedBits& b, unsigned bitWidth,
                                 unsigned& min, unsigned& max)
{
  bool bigMin = false, bigMax = false;
  for (unsigned j = 0; j < b.words; j++)
  {
    const uint64_t high = bitsAtOrAbove(j, 32) & PackedBits::widthMask(j, bitWidth);
    if (b.fixed[j] & b.value[j] & high)
      bigMin = true;
    if ((b.value[j] | ~b.fixed[j]) & high)
      bigMax = true;
  }
  const uint64_t low = ~bitsAtOrAbove(0, 32) & PackedBits::widthMask(0, bitWidth);
  min = bigMin ? UINT_MAX : (unsigned)(b.fixed[0] & b.value[0] & low);
  max = bigMax ? UINT_MAX : (unsigned)((b.value[0] | ~b.fixed[0]) & low);
}

// The core of the arithmetic right-shift transfer, on packed state. The
// operand's MSB must be fixed on entry. Deductions are written into the
// packed arguments; the wrapper transfers them back to the FixedBits.
static Result ashrCore(const unsigned bitWidth, PackedBits& packedOp,
                       PackedBits& packedShift, PackedBits& packedOut)
{
  const unsigned MSBIndex = bitWidth - 1;
  const unsigned msbWord = MSBIndex >> 6;
  const uint64_t msbBit = (uint64_t)1 << (MSBIndex & 63);

  assert(packedOp.fixed[msbWord] & msbBit);

  // The topmost number of possible shifts corresponds to all
  // the values of shift that shift out everything.
  // i.e. possibleShift[bitWidth+1] is the SET of all operations that shift past
  // the end.
  const unsigned numberOfPossibleShifts = bitWidth + 1;
  bool* possibleShift = (bool*)alloca(sizeof(bool) * numberOfPossibleShifts);
  for (unsigned i = 0; i < numberOfPossibleShifts; i++)
    possibleShift[i] = false;

  // The output's MSB always equals the operand's.
  if (!(packedOut.fixed[msbWord] & msbBit))
    packedOut.fixBits(msbWord, msbBit, packedOp.value[msbWord]);

  unsigned minShiftFromShift,
      maxShiftFromShift; // The range of the "shift" value.
  packedUnsignedMinMax(packedShift, bitWidth, minShiftFromShift,
                       maxShiftFromShift);

  // The shift can't be any bigger than the topmost alternation in the output.
  // For example if the output is 0.01000, then the shift can not be bigger than
  // 3.
  unsigned maxShiftFromOutput =
      getMaxShiftFromValueViaAlternation(bitWidth, packedOut);

  maxShiftFromShift = std::min(maxShiftFromShift, (unsigned)maxShiftFromOutput);

  {
    const bool highFixedOne = anyFixedOneAboveWordZero(packedShift);

    for (unsigned i = minShiftFromShift;
         i <= std::min(bitWidth, maxShiftFromShift); i++)
    {
      // if the bit-pattern of 'i' is in the set represented by the 'shift'.
      if (shiftHolds(packedShift, highFixedOne, i))
        possibleShift[i] = true;
    }

    // Complication. Given a shift like [.1] possibleShift[2] is now false.
    // A shift of 2 isn't possible. But one of three is.
    // possibleShift[2] means any shift >=2 is possible. So it needs to be set
    // to true.
    if (maxShiftFromShift >= bitWidth)
      possibleShift[bitWidth] = true;

    // Now check one-by-one each shifting.
    // If we are shifting a zero to where a one is (say), then that shifting
    // isn't possible. (A shift of bitWidth has no overlapping columns, so
    // it is never filtered here, as before.)
    for (unsigned shiftIt = minShiftFromShift; shiftIt < numberOfPossibleShifts;
         shiftIt++)
    {
      if (possibleShift[shiftIt] && shiftIt < bitWidth &&
          rightShiftDisagrees(packedOp, packedOut, shiftIt))
        possibleShift[shiftIt] = false;
    }
  }

  int nOfPossibleShifts = 0;
  for (unsigned i = 0; i < numberOfPossibleShifts; i++)
  {
    if (possibleShift[i])
    {
      nOfPossibleShifts++;
      maxShiftFromShift = i;
      if (debug_shift)
      {
        std::cerr << "Possible Shift:" << i << std::endl;
      }
    }
  }

  if (debug_shift)
  {
    std::cerr << "Number of possible shifts:" << nOfPossibleShifts << endl;
  }

  // If it's empty. It's a conflict.
  if (0 == nOfPossibleShifts)
  {
    return CONFLICT;
  }

  // Collect the possible finite shift amounts once.
  const unsigned words = packedOut.words;
  unsigned* possibleList = (unsigned*)alloca(sizeof(unsigned) * bitWidth);
  possibleList[0] = 0; // quieten -Wmaybe-uninitialized; only read when nPossible > 0.
  unsigned nPossible = 0;
  for (unsigned s = 0; s < bitWidth; s++)
    if (possibleShift[s])
      possibleList[nPossible++] = s;
  const bool shiftOutPossible = possibleShift[bitWidth];

  if (CONFLICT == applyShiftUnion(bitWidth, packedShift, possibleList,
                                  nPossible, shiftOutPossible))
    return CONFLICT;

  // If a particular input bit appears in every possible shifting,
  // and if that bit is unfixed,
  // and if the result is fixed to the same value in every position,
  // then that bit must be fixed. E.g.  [--] << [0-] == [00]
  //
  // A bit below the largest possible shift amount is shifted out in some
  // scenario (and everything is if a shift of >= bitWidth is possible), so
  // the candidates are the unfixed operand bits at or above every possible
  // shift amount. For those, every possible shift contributes the output
  // bit that is `shift` positions lower, i.e. word-wise, (output << s).
  if (!shiftOutPossible && nPossible > 0)
  {
    const unsigned maxS = possibleList[nPossible - 1];
    const unsigned s0 = possibleList[0];
    uint64_t* agree = (uint64_t*)alloca(sizeof(uint64_t) * words);
    uint64_t* ref = (uint64_t*)alloca(sizeof(uint64_t) * words);

    for (unsigned j = 0; j < words; j++)
    {
      agree[j] = packedOut.leftShiftedWord(packedOut.fixed, s0, j);
      ref[j] = packedOut.leftShiftedWord(packedOut.value, s0, j);
    }
    for (unsigned k = 1; k < nPossible; k++)
    {
      const unsigned s = possibleList[k];
      for (unsigned j = 0; j < words; j++)
      {
        const uint64_t f = packedOut.leftShiftedWord(packedOut.fixed, s, j);
        const uint64_t v = packedOut.leftShiftedWord(packedOut.value, s, j);
        agree[j] &= f & ~(v ^ ref[j]);
      }
    }

    for (unsigned j = 0; j < words; j++)
    {
      const uint64_t fixable = agree[j] & ~packedOp.fixed[j] &
                               bitsAtOrAbove(j, maxS) &
                               PackedBits::widthMask(j, bitWidth);
      if (fixable != 0)
        packedOp.fixBits(j, fixable, ref[j]);
    }
  }

  // Go through each of the possible shifts. If the same value is fixed
  // at every location, then it's fixed too in the result. The contribution
  // of shift s at column c is op[c+s] for c <= bitWidth-1-s, and the
  // (fixed) MSB for higher columns; a shift of >= bitWidth contributes the
  // MSB everywhere.
  const bool MSBValue = (packedOp.value[msbWord] & msbBit) != 0;
  if (nPossible > 0 || shiftOutPossible)
  {
    uint64_t* agree = (uint64_t*)alloca(sizeof(uint64_t) * words);
    uint64_t* ref = (uint64_t*)alloca(sizeof(uint64_t) * words);
    bool first = true;

    for (unsigned k = 0; k <= nPossible; k++)
    {
      unsigned boundary; // columns at or above read the MSB.
      unsigned s = 0;
      if (k < nPossible)
      {
        s = possibleList[k];
        boundary = bitWidth - s;
      }
      else if (shiftOutPossible)
        boundary = 0;
      else
        break;

      for (unsigned j = 0; j < words; j++)
      {
        const uint64_t hi = bitsAtOrAbove(j, boundary);
        const uint64_t f = packedOp.shiftedWord(packedOp.fixed, s, j) | hi;
        const uint64_t v =
            (packedOp.shiftedWord(packedOp.value, s, j) & ~hi) |
            (MSBValue ? hi : 0);
        if (first)
        {
          agree[j] = f;
          ref[j] = v;
        }
        else
          agree[j] &= f & ~(v ^ ref[j]);
      }
      first = false;
    }

    for (unsigned j = 0; j < words; j++)
    {
      const uint64_t agreed = agree[j] & PackedBits::widthMask(j, bitWidth);
      if (agreed & packedOut.fixed[j] & (packedOut.value[j] ^ ref[j]))
        return CONFLICT;
      const uint64_t newFix = agreed & ~packedOut.fixed[j];
      if (newFix != 0)
        packedOut.fixBits(j, newFix, ref[j]);
    }
  }
  return NOT_IMPLEMENTED;
}

// Transfer newly fixed bits from the packed state back into the FixedBits.
static void writeBack(FixedBits& to, const PackedBits& from,
                      const uint64_t* originalFixed)
{
  for (unsigned j = 0; j < from.words; j++)
  {
    const uint64_t add = from.fixed[j] & ~originalFixed[j];
    if (add != 0)
      to.fixWordBits(j, add, from.value[j]);
  }
}

Result bvArithmeticRightShiftBothWays(vector<FixedBits*>& children,
                                      FixedBits& output)
{
  const unsigned bitWidth = output.getWidth();
  assert(2 == children.size());
  assert(bitWidth > 0);
  assert(children[0]->getWidth() == children[1]->getWidth());
  const unsigned MSBIndex = bitWidth - 1;
  const unsigned msbWord = MSBIndex >> 6;
  const uint64_t msbBit = (uint64_t)1 << (MSBIndex & 63);

  FixedBits& op = *children[0];
  FixedBits& shift = *children[1];

  PackedBits packedOp(op);
  PackedBits packedShift(shift);
  PackedBits packedOut(output);
  const unsigned words = packedOp.words;

  // Snapshot what was fixed on entry, for the write-back.
  uint64_t* origOp = (uint64_t*)alloca(sizeof(uint64_t) * words);
  uint64_t* origShift = (uint64_t*)alloca(sizeof(uint64_t) * words);
  uint64_t* origOut = (uint64_t*)alloca(sizeof(uint64_t) * words);
  for (unsigned j = 0; j < words; j++)
  {
    origOp[j] = packedOp.fixed[j];
    origShift[j] = packedShift.fixed[j];
    origOut[j] = packedOut.fixed[j];
  }

  // The output's MSB always equals the operand's (whatever the shift is),
  // so copy it over before considering the case split below: the branch
  // with the opposite MSB would only conflict.
  if (!(packedOp.fixed[msbWord] & msbBit) && (packedOut.fixed[msbWord] & msbBit))
    packedOp.fixBits(msbWord, msbBit, packedOut.value[msbWord]);

  Result result;
  if (!(packedOp.fixed[msbWord] & msbBit))
  {
    // The MSB isn't fixed: run the core with it set each way and take the
    // union (meet in the fixed-bits lattice) of the survivors.
    PackedBits op1(packedOp), shift1(packedShift), out1(packedOut);
    PackedBits op2(packedOp), shift2(packedShift), out2(packedOut);
    op1.fixBits(msbWord, msbBit, msbBit);
    op2.fixBits(msbWord, msbBit, 0);

    const Result r1 = ashrCore(bitWidth, op1, shift1, out1);
    const Result r2 = ashrCore(bitWidth, op2, shift2, out2);

    if (r1 == CONFLICT && r2 == CONFLICT)
      return CONFLICT;

    if (r1 == CONFLICT)
    {
      packedOp.copyFrom(op2);
      packedShift.copyFrom(shift2);
      packedOut.copyFrom(out2);
      result = r2;
    }
    else if (r2 == CONFLICT)
    {
      packedOp.copyFrom(op1);
      packedShift.copyFrom(shift1);
      packedOut.copyFrom(out1);
      result = r1;
    }
    else
    {
      meetInto(op1, op2);
      meetInto(shift1, shift2);
      meetInto(out1, out2);
      packedOp.copyFrom(op1);
      packedShift.copyFrom(shift1);
      packedOut.copyFrom(out1);
      result = r1;
    }
  }
  else
  {
    result = ashrCore(bitWidth, packedOp, packedShift, packedOut);
    if (result == CONFLICT)
      return CONFLICT;
  }

  writeBack(op, packedOp, origOp);
  writeBack(shift, packedShift, origShift);
  writeBack(output, packedOut, origOut);
  return result;
}


// The core of the left-shift transfer, on packed state. Deductions are
// written into the packed arguments; the wrapper transfers them back to
// the FixedBits.
static Result shlCore(const unsigned bitWidth, PackedBits& packedOp,
                      PackedBits& packedShift, PackedBits& packedOut)
{
  const unsigned words = packedOp.words;

  // The topmost entry of possibleShift is the set of all the values of
  // shift that shift out everything (>= bitWidth), making the output zero.
  const unsigned numberOfPossibleShifts = bitWidth + 1;
  bool* possibleShift = (bool*)alloca(sizeof(bool) * numberOfPossibleShifts);
  for (unsigned i = 0; i < numberOfPossibleShifts; i++)
    possibleShift[i] = false;

  unsigned minShift, maxShift;
  packedUnsignedMinMax(packedShift, bitWidth, minShift, maxShift);

  // The shift must be at most the position of the lowest one in the
  // output: zeroes are shifted in below it.
  int positionOfFirstOne = -1;
  for (unsigned j = 0; j < words && positionOfFirstOne < 0; j++)
  {
    const uint64_t ones = packedOut.fixed[j] & packedOut.value[j];
    if (ones != 0)
      positionOfFirstOne = j * 64 + ::stp::countTrailingZeroes64(ones);
  }

  if (positionOfFirstOne >= 0)
  {
    if ((unsigned)positionOfFirstOne < minShift)
      return CONFLICT;
    maxShift = std::min(maxShift, (unsigned)positionOfFirstOne);
  }

  {
    const bool highFixedOne = anyFixedOneAboveWordZero(packedShift);
    for (unsigned i = minShift; i <= std::min(bitWidth, maxShift); i++)
    {
      // if the bit-pattern of 'i' is in the set represented by the 'shift'.
      if (shiftHolds(packedShift, highFixedOne, i))
        possibleShift[i] = true;
    }
  }

  // Given a shift like [-1], possibleShift[2] is false, but a shift of
  // three is possible: possibleShift[bitWidth] stands for every shift
  // >= bitWidth.
  if (maxShift >= bitWidth)
    possibleShift[bitWidth] = true;

  // Filter the shifts that contradict the fixed bits: a one in the output
  // below the shift amount, or a disagreement between output[c] and
  // op[c - shift].
  for (unsigned s = 0; s < bitWidth; s++)
  {
    if (!possibleShift[s])
      continue;
    bool disagrees = false;
    for (unsigned j = 0; j < words && !disagrees; j++)
    {
      if (packedOut.fixed[j] & packedOut.value[j] & ~bitsAtOrAbove(j, s))
        disagrees = true; // a one below the shift amount.
      else
      {
        const uint64_t opF = packedOp.leftShiftedWord(packedOp.fixed, s, j);
        const uint64_t opV = packedOp.leftShiftedWord(packedOp.value, s, j);
        if (opF & packedOut.fixed[j] & (opV ^ packedOut.value[j]))
          disagrees = true;
      }
    }
    if (disagrees)
      possibleShift[s] = false;
  }
  // A shift of >= bitWidth makes the output entirely zero.
  if (possibleShift[bitWidth])
    for (unsigned j = 0; j < words; j++)
      if (packedOut.fixed[j] & packedOut.value[j])
      {
        possibleShift[bitWidth] = false;
        break;
      }

  int nOfPossibleShifts = 0;
  for (unsigned i = 0; i < numberOfPossibleShifts; i++)
    if (possibleShift[i])
      nOfPossibleShifts++;

  // If it's empty. It's a conflict.
  if (0 == nOfPossibleShifts)
    return CONFLICT;

  // Collect the possible finite shift amounts once.
  unsigned* possibleList = (unsigned*)alloca(sizeof(unsigned) * bitWidth);
  possibleList[0] = 0; // quieten -Wmaybe-uninitialized; only read when nPossible > 0.
  unsigned nPossible = 0;
  for (unsigned s = 0; s < bitWidth; s++)
    if (possibleShift[s])
      possibleList[nPossible++] = s;
  const bool shiftOutPossible = possibleShift[bitWidth];

  if (CONFLICT == applyShiftUnion(bitWidth, packedShift, possibleList,
                                  nPossible, shiftOutPossible))
    return CONFLICT;

  // If a particular input bit appears in every possible shifting,
  // and if that bit is unfixed,
  // and if the result is fixed to the same value in every position,
  // then that bit must be fixed. E.g.  [--] << [0-] == [00]
  //
  // The top bits are shifted out by the largest possible shift (all of
  // them, if shifting everything out is possible), so the candidates are
  // the unfixed operand bits below bitWidth - maxShift. For those, every
  // possible shift contributes the output bit `shift` positions higher,
  // i.e. word-wise, (output >> s).
  if (!shiftOutPossible && nPossible > 0)
  {
    const unsigned maxS = possibleList[nPossible - 1];
    const unsigned s0 = possibleList[0];
    uint64_t* agree = (uint64_t*)alloca(sizeof(uint64_t) * words);
    uint64_t* ref = (uint64_t*)alloca(sizeof(uint64_t) * words);

    for (unsigned j = 0; j < words; j++)
    {
      agree[j] = packedOut.shiftedWord(packedOut.fixed, s0, j);
      ref[j] = packedOut.shiftedWord(packedOut.value, s0, j);
    }
    for (unsigned k = 1; k < nPossible; k++)
    {
      const unsigned s = possibleList[k];
      for (unsigned j = 0; j < words; j++)
      {
        const uint64_t f = packedOut.shiftedWord(packedOut.fixed, s, j);
        const uint64_t v = packedOut.shiftedWord(packedOut.value, s, j);
        agree[j] &= f & ~(v ^ ref[j]);
      }
    }

    for (unsigned j = 0; j < words; j++)
    {
      const uint64_t fixable = agree[j] & ~packedOp.fixed[j] &
                               ~bitsAtOrAbove(j, bitWidth - maxS) &
                               PackedBits::widthMask(j, bitWidth);
      if (fixable != 0)
        packedOp.fixBits(j, fixable, ref[j]);
    }
  }

  // Go through each of the possible shifts. If the same value is fixed
  // at every location, then it's fixed too in the result. The contribution
  // of shift s at column c is op[c-s] for c >= s and a shifted-in zero
  // below; a shift of >= bitWidth contributes zero everywhere.
  if (nPossible > 0 || shiftOutPossible)
  {
    uint64_t* agree = (uint64_t*)alloca(sizeof(uint64_t) * words);
    uint64_t* ref = (uint64_t*)alloca(sizeof(uint64_t) * words);
    bool first = true;

    for (unsigned k = 0; k <= nPossible; k++)
    {
      unsigned s = 0;
      bool everythingOut = false;
      if (k < nPossible)
        s = possibleList[k];
      else if (shiftOutPossible)
        everythingOut = true;
      else
        break;

      for (unsigned j = 0; j < words; j++)
      {
        uint64_t f, v;
        if (everythingOut)
        {
          f = ~(uint64_t)0;
          v = 0;
        }
        else
        {
          // Bits below the shift amount are (fixed) shifted-in zeroes;
          // leftShiftedWord already leaves the value zero there.
          f = packedOp.leftShiftedWord(packedOp.fixed, s, j) |
              ~bitsAtOrAbove(j, s);
          v = packedOp.leftShiftedWord(packedOp.value, s, j);
        }
        if (first)
        {
          agree[j] = f;
          ref[j] = v;
        }
        else
          agree[j] &= f & ~(v ^ ref[j]);
      }
      first = false;
    }

    for (unsigned j = 0; j < words; j++)
    {
      const uint64_t agreed = agree[j] & PackedBits::widthMask(j, bitWidth);
      if (agreed & packedOut.fixed[j] & (packedOut.value[j] ^ ref[j]))
        return CONFLICT;
      const uint64_t newFix = agreed & ~packedOut.fixed[j];
      if (newFix != 0)
        packedOut.fixBits(j, newFix, ref[j]);
    }
  }
  return NOT_IMPLEMENTED;
}

Result bvLeftShiftBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  const unsigned bitWidth = output.getWidth();
  assert(2 == children.size());
  assert(bitWidth > 0);

  FixedBits& op = *children[0];
  FixedBits& shift = *children[1];

  PackedBits packedOp(op);
  PackedBits packedShift(shift);
  PackedBits packedOut(output);
  const unsigned words = packedOp.words;

  // Snapshot what was fixed on entry, for the write-back.
  uint64_t* origOp = (uint64_t*)alloca(sizeof(uint64_t) * words);
  uint64_t* origShift = (uint64_t*)alloca(sizeof(uint64_t) * words);
  uint64_t* origOut = (uint64_t*)alloca(sizeof(uint64_t) * words);
  for (unsigned j = 0; j < words; j++)
  {
    origOp[j] = packedOp.fixed[j];
    origShift[j] = packedShift.fixed[j];
    origOut[j] = packedOut.fixed[j];
  }

  const Result result = shlCore(bitWidth, packedOp, packedShift, packedOut);
  if (result == CONFLICT)
    return CONFLICT;

  writeBack(op, packedOp, origOp);
  writeBack(shift, packedShift, origShift);
  writeBack(output, packedOut, origOut);
  return result;
}
}
}

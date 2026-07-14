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
    for (unsigned j = 0; j < 2 * words; j++)
      fixed[j] = 0; // zeroes both halves; value follows fixed.

    const unsigned width = b.getWidth();
    for (unsigned i = 0; i < width; i++)
      if (b.isFixed(i))
      {
        fixed[i >> 6] |= (uint64_t)1 << (i & 63);
        if (b.getValue(i))
          value[i >> 6] |= (uint64_t)1 << (i & 63);
      }
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

Result bvRightShiftBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  Result result = NO_CHANGE;
  const unsigned bitWidth = output.getWidth();

  assert(2 == children.size());

  FixedBits& op = *children[0];
  FixedBits& shift = *children[1];

  FixedBits outputReverse(bitWidth, false);
  FixedBits opReverse(bitWidth, false);

  // Reverse the output and the input.
  for (unsigned i = 0; i < bitWidth; i++)
  {
    if (op.isFixed(i))
    {
      opReverse.setFixed(bitWidth - 1 - i, true);
      opReverse.setValue(bitWidth - 1 - i, op.getValue(i));
    }

    if (output.isFixed(i))
    {
      outputReverse.setFixed(bitWidth - 1 - i, true);
      outputReverse.setValue(bitWidth - 1 - i, output.getValue(i));
    }
  }

  vector<FixedBits*> args;
  args.push_back(&opReverse);
  args.push_back(&shift); // shift is unmodified.
  result = bvLeftShiftBothWays(args, outputReverse);

  if (CONFLICT == result)
    return CONFLICT;

  // Now write the reversed values back.
  // Reverse the output and the input.
  for (unsigned i = 0; i < bitWidth; i++)
  {
    if (opReverse.isFixed(i) && !op.isFixed(bitWidth - 1 - i))
    {
      op.setFixed(bitWidth - 1 - i, true);
      op.setValue(bitWidth - 1 - i, opReverse.getValue(i));
    }

    if (outputReverse.isFixed(i) && !output.isFixed(bitWidth - 1 - i))
    {
      output.setFixed(bitWidth - 1 - i, true);
      output.setValue(bitWidth - 1 - i, outputReverse.getValue(i));
    }
  }

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
  unsigned nPossible = 0;
  for (unsigned s = 0; s < bitWidth; s++)
    if (possibleShift[s])
      possibleList[nPossible++] = s;
  const bool shiftOutPossible = possibleShift[bitWidth];

  // The shift operand must lie in the union of the possible shift amounts:
  // the bit patterns of the possible finite shifts, unioned with whatever
  // "shift >= bitWidth" allows when shifting everything out is possible.
  {
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
      // Refine a copy of the shift with (shift >= bitWidth), and union it in.
      FixedBits bitWidthFB = FixedBits::fromUnsignedInt(bitWidth, bitWidth);
      FixedBits truth(1, true);
      truth.setFixed(0, true);
      truth.setValue(0, true);
      FixedBits working(bitWidth, false);
      for (unsigned i = 0; i < bitWidth; i++)
        if (packedShift.isFixedBit(i))
        {
          working.setFixed(i, true);
          working.setValue(i, packedShift.valueBit(i));
        }

      vector<FixedBits*> args;
      args.push_back(&working);
      args.push_back(&bitWidthFB);
      Result r = bvGreaterThanEqualsBothWays(args, truth);
      assert(CONFLICT != r);
      (void)r;

      for (unsigned i = 0; i < bitWidth; i++)
      {
        const unsigned j = i >> 6;
        const uint64_t bit = (uint64_t)1 << (i & 63);
        if (nPossible > 0)
        {
          // Union: drop bits "working" leaves open or disagrees on.
          if (!working.isFixed(i) ||
              ((vFixed[j] & bit) && working.getValue(i) != ((vValue[j] & bit) != 0)))
            vFixed[j] &= ~bit;
        }
        else if (working.isFixed(i))
        {
          // Only shifts >= bitWidth are possible.
          vFixed[j] |= bit;
          if (working.getValue(i))
            vValue[j] |= bit;
          else
            vValue[j] &= ~bit;
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
  }

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
    uint64_t pending = from.fixed[j] & ~originalFixed[j];
    while (pending)
    {
      const unsigned b = __builtin_ctzll(pending);
      pending &= pending - 1;
      to.setFixed(j * 64 + b, true);
      to.setValue(j * 64 + b, (from.value[j] >> b) & 1);
    }
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

Result bvLeftShiftBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  const unsigned bitWidth = output.getWidth();
  assert(2 == children.size());
  assert(bitWidth > 0);

  FixedBits& op = *children[0];
  FixedBits& shift = *children[1];

  if (debug_shift)
  {
    cerr << "op:" << op << endl;
    cerr << "shift:" << shift << endl;
    cerr << "output:" << output << endl;
  }

  // The topmost number of possible shifts corresponds to all
  // the values of shift that shift out everything.
  // i.e. possibleShift[bitWidth+1] is the SET of all operations that shift past
  // the end.
  const unsigned numberOfPossibleShifts = bitWidth + 1;
  bool* possibleShift = (bool*)alloca(sizeof(bool) * numberOfPossibleShifts);
  for (unsigned i = 0; i < numberOfPossibleShifts; i++)
    possibleShift[i] = false;

  unsigned minShift, maxShift;
  shift.getUnsignedMinMax(minShift, maxShift);

  // The shift must be less than the position of the first one in the output
  int positionOfFirstOne = -1;
  for (unsigned i = 0; i < bitWidth; i++)
  {
    if (output.isFixed(i) && output.getValue(i))
    {
      positionOfFirstOne = i;
      break;
    }
  }

  if (positionOfFirstOne >= 0)
  {
    if ((unsigned)positionOfFirstOne < minShift)
      return CONFLICT;

    maxShift = std::min(maxShift, (unsigned)positionOfFirstOne);
  }

  for (unsigned i = minShift; i <= std::min(bitWidth, maxShift); i++)
  {
    // if the bit-pattern of 'i' is in the set represented by the 'shift'.
    if (shift.unsignedHolds(i))
      possibleShift[i] = true;
  }

  // Complication. Given a shift like [-1]. possibleShift[2] is now false.
  // A shift of 2 isn't possible. But one of three is.
  // possibleShift[2] means any shift >=2 is possible. So it needs to be set
  // to true.
  {
    if (maxShift >= bitWidth)
      possibleShift[bitWidth] = true;
  }

  // Now check one-by-one each shifting.
  // If we are shifting a zero to where a one is (say), then that shifting isn't
  // possible.
  for (unsigned shiftIt = 0; shiftIt < numberOfPossibleShifts; shiftIt++)
  {
    if (possibleShift[shiftIt])
    {
      for (unsigned column = 0; column < bitWidth; column++)
      {
        if (column < shiftIt)
        {
          if (output.isFixed(column) &&
              output.getValue(
                  column)) // output is one in the column. That's wrong.
          {
            possibleShift[shiftIt] = false;
            break;
          }
        }
        else
        {
          // if they are fixed to different values. That's wrong.
          if (output.isFixed(column) && op.isFixed(column - shiftIt) &&
              (output.getValue(column) != op.getValue(column - shiftIt)))
          {
            possibleShift[shiftIt] = false;
            break;
          }
        }
      }
    }
  }

  int nOfPossibleShifts = 0;
  for (unsigned i = 0; i < numberOfPossibleShifts; i++)
  {
    if (possibleShift[i])
    {
      nOfPossibleShifts++;
      if (debug_shift)
      {
        std::cerr << "Possible:" << i << std::endl;
      }
    }
  }

  if (debug_shift)
  {
    std::cerr << "Number of possible shifts:" << nOfPossibleShifts << endl;
  }

  // If it's empty. It's a conflict.
  if (0 == nOfPossibleShifts)
    return CONFLICT;

  // We have a list of all the possible shift amounts.
  // We take the union of all the bits that are possible.

  FixedBits v(bitWidth, false);
  bool first = true;
  for (unsigned i = 0; i < numberOfPossibleShifts - 1; i++)
  {
    if (possibleShift[i])
    {
      if (first)
      {
        first = false;
        for (unsigned j = 0; j < (unsigned)v.getWidth(); j++)
        {
          v.setFixed(j, true);
          if (j < sizeof(unsigned) * 8)
            v.setValue(j, 0 != (i & (1u << j)));
          else
            v.setValue(j, false);
        }
      }
      else
      {
        // join.
        for (unsigned j = 0;
             j < (unsigned)v.getWidth() && j < sizeof(unsigned) * 8; j++)
        {
          if (v.isFixed(j))
          {
            // union.
            if (v.getValue(j) != (0 != (i & (1u << j))))
              v.setFixed(j, false);
          }
        }
      }
    }
  }

  // The top most entry of the shift table is special. It means all values of
  // shift
  // that fill it completely with zeroes. We take the union of all of the values
  // >bitWidth
  // in this function.
  if (possibleShift[numberOfPossibleShifts - 1])
  {
    FixedBits bitWidthFB = FixedBits::fromUnsignedInt(bitWidth, bitWidth);
    FixedBits output(1, true);
    output.setFixed(0, true);
    output.setValue(0, true);
    FixedBits working(shift);

    vector<FixedBits*> args;
    args.push_back(&working);
    args.push_back(&bitWidthFB);

    // Write into working anything that can be determined given it's >=bitWidth.
    Result r = bvGreaterThanEqualsBothWays(args, output);
    assert(CONFLICT != r);

    // Get the union of "working" with the prior union.
    for (unsigned i = 0; i < bitWidth; i++)
    {
      if (!working.isFixed(i) && v.isFixed(i))
        v.setFixed(i, false);
      if (working.isFixed(i) && v.isFixed(i) &&
          (working.getValue(i) != v.getValue(i)))
        v.setFixed(i, false);
      if (first) // no less shifts possible.
      {
        if (working.isFixed(i))
        {
          v.setFixed(i, true);
          v.setValue(i, working.getValue(i));
        }
      }
    }
  }

  if (debug_shift)
  {
    std::cerr << "Shift Amount:" << v << std::endl;
  }

  for (unsigned i = 0; i < bitWidth; i++)
  {
    if (v.isFixed(i))
    {
      if (!shift.isFixed(i))
      {
        shift.setFixed(i, true);
        shift.setValue(i, v.getValue(i));
      }
      else if (shift.isFixed(i) && shift.getValue(i) != v.getValue(i))
        return CONFLICT;
    }
  }

  // If a particular input bit appears in every possible shifting,
  // and if that bit is unfixed,
  // and if the result it is fixed to the same value in every position.
  // Then, that bit must be fixed.
  // E.g.  [--] << [0-] == [00]

  bool* candidates = (bool*)alloca(sizeof(bool) * bitWidth);
  for (unsigned i = 0; i < bitWidth; i++)
  {
    candidates[i] = !op.isFixed(i);
  }

  // candidates: So far: the bits that are unfixed.

  for (unsigned i = 0; i < numberOfPossibleShifts; i++)
  {
    if (possibleShift[i])
    {
      // If this shift is possible, then some bits will be shifted out.
      for (unsigned j = 0; j < i; j++)
        candidates[bitWidth - 1 - j] = false;
    }
  }

  // candidates: So far: + the input bits that are unfixed.
  //                     + the input bits that are in every possible fixing.

  // Check all candidates have the same output values.
  for (unsigned candidate = 0; candidate < bitWidth; candidate++)
  {
    bool first = true;
    bool setTo = false; // value that's never read. To quieten gcc.

    if (candidates[candidate])
    {
      for (unsigned shiftIT = 0; shiftIT < bitWidth; shiftIT++)
      {
        // If the shift isn't possible continue.
        if (!possibleShift[shiftIT])
          continue;

        unsigned idx = candidate + shiftIT;

        if (!output.isFixed(idx))
        {
          candidates[candidate] = false;
          break;
        }
        else
        {
          if (first)
          {
            first = false;
            setTo = output.getValue(idx);
          }
          else
          {
            if (setTo != output.getValue(idx))
            {
              candidates[candidate] = false;
              break;
            }
          }
        }
      }
    }

    if (candidates[candidate])
    {
      assert(!op.isFixed(candidate));
      op.setFixed(candidate, true);
      op.setValue(candidate, setTo);
    }
  }

  // done.

  // Go through each of the possible shifts. If the same value is fixed
  // at every location. Then it's fixed too in the result.
  for (unsigned column = 0; column < bitWidth; column++)
  {
    bool allFixedToSame = true;
    bool allFixedTo = false; // value that's never read. To quieten gcc.
    bool first = true;

    for (unsigned shiftIt = minShift;
         (shiftIt < numberOfPossibleShifts) && allFixedToSame; shiftIt++)
    {
      if (possibleShift[shiftIt])
      {
        // Will have shifted in zeroes.
        if (shiftIt > column)
        {
          if (first)
          {
            allFixedTo = false;
            first = false;
          }
          else
          {
            if (allFixedTo)
            {
              allFixedToSame = false;
            }
          }
        }
        else
        {
          unsigned index = column - shiftIt;
          if (!op.isFixed(index))
            allFixedToSame = false;
          else if (first && op.isFixed(index))
          {
            first = false;
            allFixedTo = op.getValue(index);
          }
          if (op.isFixed(index) && allFixedTo != op.getValue(index))
            allFixedToSame = false;
        }
      }
    }

    // If it can be just one possible value. Then we can fix 'em.
    if (allFixedToSame)
    {
      if (output.isFixed(column) && (output.getValue(column) != allFixedTo))
        return CONFLICT;
      if (!output.isFixed(column))
      {
        output.setFixed(column, true);
        output.setValue(column, allFixedTo);
      }
    }
  }

  /*
  // If there is only one possible shift value. Then, we can push from the
  output back.
  if (1 == nOfPossibleShifts)
  {
    for (unsigned i = shiftIndex; i < bitWidth; i++)
    {
      if (!op.isFixed(i - shiftIndex) && output.isFixed(i))
      {
        op.setFixed(i - shiftIndex, true);
        op.setValue(i - shiftIndex, output.getValue(i));
        result = CHANGED;
      }
    }
  }
*/

  return NOT_IMPLEMENTED;
}
}
}

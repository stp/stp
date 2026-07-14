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
  PackedBits(const PackedBits&);
  PackedBits& operator=(const PackedBits&);
};

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

// Converts the array of possible shifts into a set that represents the values.
FixedBits getPossible(unsigned bitWidth, bool possibleShift[],
                      unsigned numberOfPossibleShifts, const FixedBits& shift)
{
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

  unsigned firstShift;
  for (firstShift = 0; firstShift < numberOfPossibleShifts; firstShift++)
    if (possibleShift[firstShift])
      break;

  // The top most entry of the shift table is special. It means all values of
  // shift
  // that fill it completely with zeroes /ones. We take the union of all of the
  // values >bitWidth
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
      if (firstShift == numberOfPossibleShifts - 1) // no less shifts possible.
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
    cerr << "Set of possible shifts:" << v << endl;

  return v;
}

unsigned getMaxShiftFromValueViaAlternation(const unsigned bitWidth,
                                            const FixedBits& output)
{
  unsigned maxShiftFromValue = UINT_MAX;

  // The shift must be less than the position of the first alternation.
  bool foundTrue = false;
  bool foundFalse = false;
  for (int i = bitWidth - 1; i >= 0; i--)
  {
    if (output.isFixed(i))
    {
      if (output.getValue(i) && foundFalse)
      {
        maxShiftFromValue = i;
        break;
      }
      if (!output.getValue(i) && foundTrue)
      {
        maxShiftFromValue = i;
        break;
      }
      if (output.getValue(i))
        foundTrue = true;
      else if (!output.getValue(i))
        foundFalse = true;
    }
  }

  if (maxShiftFromValue != UINT_MAX)
    maxShiftFromValue = bitWidth - 2 - maxShiftFromValue;

  return maxShiftFromValue;
}

Result bvArithmeticRightShiftBothWays(vector<FixedBits*>& children,
                                      FixedBits& output)
{
  const unsigned bitWidth = output.getWidth();
  assert(2 == children.size());
  assert(bitWidth > 0);
  assert(children[0]->getWidth() == children[1]->getWidth());
  const unsigned MSBIndex = bitWidth - 1;

  FixedBits& op = *children[0];
  FixedBits& shift = *children[1];

  // The output's MSB always equals the operand's (whatever the shift is),
  // so copy it over before considering the case split below: the branch
  // with the opposite MSB would only conflict.
  if (!op.isFixed(MSBIndex) && output.isFixed(MSBIndex))
  {
    op.setFixed(MSBIndex, true);
    op.setValue(MSBIndex, output.getValue(MSBIndex));
  }

  // If the MSB isn't set, create a copy with it set each way and take the meet.
  if (!op.isFixed(MSBIndex))
  {
    vector<FixedBits*> children1;
    vector<FixedBits*> children2;
    FixedBits op1(op);
    FixedBits op2(op);
    FixedBits shift1(shift);
    FixedBits shift2(shift);
    FixedBits output1(output);
    FixedBits output2(output);

    children1.push_back(&op1);
    children1.push_back(&shift1);
    op1.setFixed(MSBIndex, true);
    op1.setValue(MSBIndex, true);

    children2.push_back(&op2);
    children2.push_back(&shift2);
    op2.setFixed(MSBIndex, true);
    op2.setValue(MSBIndex, false);

    Result r1 = bvArithmeticRightShiftBothWays(children1, output1);
    Result r2 = bvArithmeticRightShiftBothWays(children2, output2);

    if (r1 == CONFLICT && r2 == CONFLICT)
      return CONFLICT;

    if (r1 == CONFLICT)
    {
      op = op2;
      shift = shift2;
      output = output2;
      return r2;
    }

    if (r2 == CONFLICT)
    {
      op = op1;
      shift = shift1;
      output = output1;
      return r1;
    }

    op = FixedBits::meet(op1, op2);
    shift = FixedBits::meet(shift1, shift2);
    output = FixedBits::meet(output1, output2);
    return r1;
  }

  assert(op.isFixed(MSBIndex));

  if (debug_shift)
  {
    cerr << "=========" << endl;
    cerr << op << " >a> ";
    cerr << shift;
    cerr << " = " << output << endl;
  }

  // The topmost number of possible shifts corresponds to all
  // the values of shift that shift out everything.
  // i.e. possibleShift[bitWidth+1] is the SET of all operations that shift past
  // the end.
  const unsigned numberOfPossibleShifts = bitWidth + 1;
  bool* possibleShift = (bool*)alloca(sizeof(bool) * numberOfPossibleShifts);
  for (unsigned i = 0; i < numberOfPossibleShifts; i++)
    possibleShift[i] = false;

  // If either of the top two bits are fixed they should be equal.
  if (op.isFixed(MSBIndex) ^ output.isFixed(MSBIndex))
  {
    if (op.isFixed(MSBIndex))
    {
      output.setFixed(MSBIndex, true);
      output.setValue(MSBIndex, op.getValue(MSBIndex));
    }

    if (output.isFixed(MSBIndex))
    {
      op.setFixed(MSBIndex, true);
      op.setValue(MSBIndex, output.getValue(MSBIndex));
    }
  }

  // Both the MSB of the operand and the output should be fixed now..
  assert(output.isFixed(MSBIndex));

  unsigned minShiftFromShift,
      maxShiftFromShift; // The range of the "shift" value.
  shift.getUnsignedMinMax(minShiftFromShift, maxShiftFromShift);

  // The shift can't be any bigger than the topmost alternation in the output.
  // For example if the output is 0.01000, then the shift can not be bigger than
  // 3.
  unsigned maxShiftFromOutput =
      getMaxShiftFromValueViaAlternation(bitWidth, output);

  maxShiftFromShift = std::min(maxShiftFromShift, (unsigned)maxShiftFromOutput);

  if (debug_shift)
  {
    cerr << "minshift:" << minShiftFromShift << endl;
    cerr << "maxshift:" << maxShiftFromShift << endl;
    cerr << "total:" << maxShiftFromShift << endl;
  }

  PackedBits packedOp(op);
  PackedBits packedOut(output);
  {
    const PackedBits packedShift(shift);
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

  // We have a list of all the possible shift amounts.
  // We take the union of all the bits that are possible.
  FixedBits setOfPossibleShifts =
      getPossible(bitWidth, possibleShift, numberOfPossibleShifts, shift);

  // Write in any fixed values to the shift.
  for (unsigned i = 0; i < bitWidth; i++)
  {
    if (setOfPossibleShifts.isFixed(i))
    {
      if (!shift.isFixed(i))
      {
        shift.setFixed(i, true);
        shift.setValue(i, setOfPossibleShifts.getValue(i));
      }
      else if (shift.isFixed(i) &&
               shift.getValue(i) != setOfPossibleShifts.getValue(i))
      {
        return CONFLICT;
      }
    }
  }

  // Collect the possible finite shift amounts once.
  const unsigned words = packedOut.words;
  unsigned* possibleList = (unsigned*)alloca(sizeof(unsigned) * bitWidth);
  unsigned nPossible = 0;
  for (unsigned s = 0; s < bitWidth; s++)
    if (possibleShift[s])
      possibleList[nPossible++] = s;
  const bool shiftOutPossible = possibleShift[bitWidth];

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
                               packedOut.widthMask(j, bitWidth);
      if (fixable == 0)
        continue;
      for (unsigned b = 0; b < 64; b++)
        if ((fixable >> b) & 1)
        {
          op.setFixed(j * 64 + b, true);
          op.setValue(j * 64 + b, (ref[j] >> b) & 1);
        }
      packedOp.fixBits(j, fixable, ref[j]);
    }
  }

  if (debug_shift)
  {
    cerr << op << " >a> ";
    cerr << shift;
    cerr << " = " << output << endl;
  }

  // Go through each of the possible shifts. If the same value is fixed
  // at every location, then it's fixed too in the result. The contribution
  // of shift s at column c is op[c+s] for c <= bitWidth-1-s, and the
  // (fixed) MSB for higher columns; a shift of >= bitWidth contributes the
  // MSB everywhere.
  const bool MSBValue = op.getValue(MSBIndex);
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
      const uint64_t agreed = agree[j] & packedOut.widthMask(j, bitWidth);
      if (agreed & packedOut.fixed[j] & (packedOut.value[j] ^ ref[j]))
        return CONFLICT;
      const uint64_t newFix = agreed & ~packedOut.fixed[j];
      if (newFix == 0)
        continue;
      for (unsigned b = 0; b < 64; b++)
        if ((newFix >> b) & 1)
        {
          output.setFixed(j * 64 + b, true);
          output.setValue(j * 64 + b, (ref[j] >> b) & 1);
        }
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

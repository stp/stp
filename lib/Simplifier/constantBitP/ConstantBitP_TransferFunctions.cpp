/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: November, 2010
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
#include "stp/Simplifier/constantBitP/ConstantBitP_Utility.h"
#include "stp/Util/BitOps.h"

namespace simplifier
{
namespace constantBitP
{

namespace stp
{
typedef unsigned int* CBV;
}

// Misc (easy) transfer functions.
// Trevor Hansen. BSD License.

// if the result is fixed to true. Then fix a==b.
// if the result is fixed to false, there is a single unspecied value, and all
// the rest are the same. Fix it to the opposite.

// if a==b then fix the result to true.
// if a!=b then fix the result to false.
// The four bit-loops of the general version become bitwise operations on
// the packed fixedness/value words. Each branch reads just the words it
// needs straight from the children — no staging buffers.
Result bvEqualsBothWays(FixedBits& a, FixedBits& b, FixedBits& output)
{
  assert(a.getWidth() == b.getWidth());
  assert(1 == output.getWidth());

  // A bit fixed on both sides but to different values fully determines the
  // propagation: the children are unequal, and no child bit can be derived.
  if (a.disagrees(b))
  {
    if (output.isFixed(0) && output.getValue(0))
      return CONFLICT;
    if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, false);
      return CHANGED;
    }
    return NO_CHANGE;
  }

  const unsigned width = a.getWidth();
  const unsigned words = (width + 63) / 64;
  // The packed words are zero above the width, so ~fixed needs masking in
  // the final word.
  const uint64_t topMask =
      (width % 64 == 0) ? ~0ULL : ((1ULL << (width % 64)) - 1);

  bool changed = false;

  // With no disagreement, the children are equal iff everything is fixed.
  bool allFixed = true;
  for (unsigned w = 0; w < words && allFixed; w++)
  {
    const uint64_t mask = (w == words - 1) ? topMask : ~0ULL;
    uint64_t fa, va, fb, vb;
    a.fillPackedWord(w, fa, va);
    b.fillPackedWord(w, fb, vb);
    allFixed = (fa & fb & mask) == mask;
  }

  if (allFixed)
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

  if (output.isFixed(0) && output.getValue(0)) // all should be the same.
  {
    for (unsigned w = 0; w < words; w++)
    {
      uint64_t fa, va, fb, vb;
      a.fillPackedWord(w, fa, va);
      b.fillPackedWord(w, fb, vb);

      const uint64_t onlyA = fa & ~fb;
      if (onlyA != 0)
      {
        b.fixWordBits(w, onlyA, va);
        changed = true;
      }

      const uint64_t onlyB = fb & ~fa;
      if (onlyB != 0)
      {
        a.fixWordBits(w, onlyB, vb);
        changed = true;
      }
    }
  }

  // If the result is fixed to false, there is a single unspecified value, and
  // all the rest are the same, fix it to the opposite.
  if (output.isFixed(0) && !output.getValue(0))
  {
    unsigned unknowns = 0;
    for (unsigned w = 0; w < words && unknowns < 2; w++)
    {
      const uint64_t mask = (w == words - 1) ? topMask : ~0ULL;
      uint64_t fa, va, fb, vb;
      a.fillPackedWord(w, fa, va);
      b.fillPackedWord(w, fb, vb);
      unknowns += ::stp::popCount64(~fa & mask) +
                  ::stp::popCount64(~fb & mask);
    }

    if (unknowns == 1)
    {
      for (unsigned w = 0; w < words; w++)
      {
        const uint64_t mask = (w == words - 1) ? topMask : ~0ULL;
        uint64_t fa, va, fb, vb;
        a.fillPackedWord(w, fa, va);
        b.fillPackedWord(w, fb, vb);
        const uint64_t unknownA = ~fa & mask;
        const uint64_t unknownB = ~fb & mask;
        if (unknownA != 0)
        {
          const unsigned bit = ::stp::countTrailingZeroes64(unknownA);
          a.setFixed(w * 64 + bit, true);
          a.setValue(w * 64 + bit, !((vb >> bit) & 1));
          changed = true;
          break;
        }
        if (unknownB != 0)
        {
          const unsigned bit = ::stp::countTrailingZeroes64(unknownB);
          b.setFixed(w * 64 + bit, true);
          b.setValue(w * 64 + bit, !((va >> bit) & 1));
          changed = true;
          break;
        }
      }
    }
  }

  return changed ? CHANGED : NO_CHANGE;
}

Result bvEqualsBothWays(vector<FixedBits*>& children, FixedBits& result)
{
  return bvEqualsBothWays(*(children[0]), *(children[1]), result);
}

Result bvZeroExtendBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 2);
  // The second argument is a junk size arugment.

  FixedBits& input = *children[0];
  const int inputBitWidth = input.getWidth();
  const int outputBitWidth = output.getWidth();

  Result result = makeEqual(input, output, 0, inputBitWidth);
  if (CONFLICT == result)
    return CONFLICT;

  // Fix all the topmost bits of the output to zero.
  for (int i = inputBitWidth; i < outputBitWidth; i++)
  {
    if (output.isFixed(i) && output.getValue(i))
      return CONFLICT; // set to one. Never right.
    else if (!output.isFixed(i))
    {
      output.setFixed(i, true);
      output.setValue(i, false);
      result = CHANGED;
    }
  }
  return result;
}

Result bvSignExtendBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 2);
  // The second argument is a junk size arugment.

  FixedBits& input = *children[0];
  const int inputBitWidth = input.getWidth();
  const int outputBitWidth = output.getWidth();
  assert(inputBitWidth <= outputBitWidth);

  Result result = makeEqual(input, output, 0, inputBitWidth);
  if (CONFLICT == result)
    return CONFLICT;

  // If any of the topmost bits of the output are fixed. Then they all should
  // be.
  // They should all be fixed to the same value.
  bool found = false;
  bool setTo;
  for (int i = inputBitWidth - /**/ 1 /**/; i < outputBitWidth; i++)
  {
    if (output.isFixed(i))
    {
      setTo = output.getValue(i);
      found = true;
      break;
    }
  }

  if (found)
  {
    for (int i = inputBitWidth - 1; i < outputBitWidth; i++)
    {
      if (output.isFixed(i) && (output.getValue(i) != setTo))
        return CONFLICT; // if any are set to the wrong value! bad.
      else if (!output.isFixed(i))
      {
        output.setFixed(i, true);
        output.setValue(i, setTo);
        result = CHANGED;
      }
    }

    Result result2 = makeEqual(input, output, 0, inputBitWidth);
    if (CONFLICT == result2)
      return CONFLICT;
  }
  return result;
}

Result bvExtractBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  const size_t numberOfChildren = children.size();
  const unsigned outputBitWidth = output.getWidth();

  Result result = NO_CHANGE;

  assert(3 == numberOfChildren);

  unsigned top = children[1]->getUnsignedValue();
  unsigned bottom = children[2]->getUnsignedValue();

  FixedBits& input = *(children[0]);

  assert(top >= bottom);
  assert(top - bottom + 1 == outputBitWidth);
  assert(top < input.getWidth());

  for (unsigned outputPosition = 0; outputPosition < outputBitWidth;
       outputPosition++)
  {
    unsigned inputPosition = outputPosition + bottom;

    if (input.isFixed(inputPosition) && output.isFixed(outputPosition))
      if (input.getValue(inputPosition) ^ output.getValue(outputPosition))
        return CONFLICT;

    if (input.isFixed(inputPosition) ^ output.isFixed(outputPosition))
    {
      if (input.isFixed(inputPosition))
      {
        output.setFixed(outputPosition, true);
        output.setValue(outputPosition, input.getValue(inputPosition));
        result = CHANGED;
      }
      else
      {
        input.setFixed(inputPosition, true);
        input.setValue(inputPosition, output.getValue(outputPosition));
        result = CHANGED;
      }
    }
  }

  // cerr << "extract[" << top << ":" << bottom << "]" << input << "=" <<
  // output<< endl;

  return result;
}

// UMINUS, is NEG followed by +1
// The relation y == -x is characterised entirely by the position t of the
// lowest one bit: bits below t are zero in both x and y, bit t is one in
// both, and above t the two are complements (with t == width standing for
// x == y == 0). Rather than looping a bitwise-not and a full addition
// propagation to a fixed point, compute the feasible set of t directly and
// take the union of the deductions each feasible t makes. That is
// maximally precise in one O(width) pass: the feasible-t structures are
// exactly the solutions, so the agreement over them is the ideal result.
namespace
{
// Bits of word w with global index below `bound`.
inline uint64_t bitsBelowWord(unsigned w, unsigned bound)
{
  const uint64_t base = (uint64_t)w * 64;
  if (base + 64 <= bound)
    return ~0ULL;
  if (base >= bound)
    return 0;
  return (1ULL << (bound - base)) - 1;
}
}

Result bvUnaryMinusBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 1);
  FixedBits& x = *children[0];
  FixedBits& y = output;
  const unsigned width = x.getWidth();
  assert(y.getWidth() == width);

  const unsigned words = (width + 63) / 64;
  uint64_t* buf = (uint64_t*)alloca(sizeof(uint64_t) * 4 * words);
  uint64_t* xF = buf;             // fixedness.
  uint64_t* xV = buf + words;     // fixed ones.
  uint64_t* yF = buf + 2 * words;
  uint64_t* yV = buf + 3 * words;
  x.fillPackedWords(xF, xV);
  y.fillPackedWords(yF, yV);

  // Nothing fixed anywhere: nothing can be deduced.
  {
    uint64_t any = 0;
    for (unsigned w = 0; w < words; w++)
      any |= xF[w] | yF[w];
    if (any == 0)
      return NO_CHANGE;
  }

  // The feasible t form an interval [lo, hi] with holes (t == width means
  // x == 0). A known one bounds t above; positions where both operands
  // are fixed pin t: equal-one means t is exactly there, equal-zero
  // pushes t above, complementary values push t below.
  unsigned lo = 0;
  unsigned hi = width;

  for (unsigned w = 0; w < words; w++)
  {
    const uint64_t knownOne = xV[w] | yV[w];
    const uint64_t both = xF[w] & yF[w];
    const uint64_t diff = both & (xV[w] ^ yV[w]);
    const uint64_t ones2 = xV[w] & yV[w];
    const uint64_t zeros2 = both & ~xV[w] & ~yV[w];
    const unsigned base = w * 64;

    if (knownOne)
      hi = std::min(hi, base + (unsigned)::stp::countTrailingZeroes64(knownOne));
    if (diff)
    {
      const unsigned i = base + (unsigned)::stp::countTrailingZeroes64(diff);
      if (i == 0)
        return CONFLICT; // bit zero is always shared.
      hi = std::min(hi, i - 1);
    }
    if (ones2)
    {
      lo = std::max(lo, base + 63 - (unsigned)::stp::countLeadingZeroes64(ones2));
      hi = std::min(hi, base + (unsigned)::stp::countTrailingZeroes64(ones2));
    }
    if (zeros2)
      lo = std::max(lo, base + 64 - (unsigned)::stp::countLeadingZeroes64(zeros2));
  }

  if (lo > hi)
    return CONFLICT;

  // Feasible finite t: within [lo, min(hi, width-1)], and not a hole
  // (a position fixed to zero on either side).
  const unsigned none = width + 1;
  unsigned L = none, H = none;
  for (unsigned w = 0; w < words; w++)
  {
    const uint64_t hole = (xF[w] & ~xV[w]) | (yF[w] & ~yV[w]);
    uint64_t feas = ~hole;
    feas &= ~bitsBelowWord(w, lo);
    feas &= bitsBelowWord(w, hi == width ? width : hi + 1);
    // Mask to the width (the top word may have slack bits).
    feas &= bitsBelowWord(w, width);
    if (feas)
    {
      const unsigned first = w * 64 + (unsigned)::stp::countTrailingZeroes64(feas);
      if (L == none)
        L = first;
      H = w * 64 + 63 - (unsigned)::stp::countLeadingZeroes64(feas);
    }
  }
  const bool widthFeasible = hi == width;

  if (L == none && !widthFeasible)
    return CONFLICT; // no position for the lowest one remains.

  bool changed = false;

  // Below every feasible t both operands are zero. (No conflicting fixed
  // one can exist here: it would have lowered hi below this region.)
  const unsigned zeroBelow = (L == none) ? width : L;
  for (unsigned w = 0; w < words && w * 64 < zeroBelow; w++)
  {
    const uint64_t region = bitsBelowWord(w, zeroBelow);
    uint64_t newX = region & ~xF[w];
    uint64_t newY = region & ~yF[w];
    changed |= (newX | newY) != 0;
    while (newX)
    {
      const unsigned b = ::stp::countTrailingZeroes64(newX);
      newX &= newX - 1;
      x.setFixed(w * 64 + b, true);
      x.setValue(w * 64 + b, false);
    }
    while (newY)
    {
      const unsigned b = ::stp::countTrailingZeroes64(newY);
      newY &= newY - 1;
      y.setFixed(w * 64 + b, true);
      y.setValue(w * 64 + b, false);
    }
  }

  if (L == none)
    return changed ? CHANGED : NO_CHANGE; // only x == 0 remains.

  // Between L and H inclusive, reason per bit over the categories
  // t < i / t == i / t > i, exactly as the solutions allow.
  bool anyFeasibleBelow = false;
  for (unsigned i = L; i <= H; i++)
  {
    const uint64_t bit = 1ULL << (i & 63);
    const unsigned w = i >> 6;
    const uint64_t hole = (xF[w] & ~xV[w]) | (yF[w] & ~yV[w]);
    const bool eqHere = i >= lo && i <= hi && !(hole & bit);
    const bool gtHere = i < H || widthFeasible;
    const bool ltHere = anyFeasibleBelow;

    const bool xIsF = (xF[w] & bit) != 0, xVal = (xV[w] & bit) != 0;
    const bool yIsF = (yF[w] & bit) != 0, yVal = (yV[w] & bit) != 0;

    bool xCan0 = false, xCan1 = false, yCan0 = false, yCan1 = false;
    if (gtHere)
    {
      xCan0 = true;
      yCan0 = true;
    }
    if (eqHere)
    {
      xCan1 = true;
      yCan1 = true;
    }
    if (ltHere)
    {
      if (xIsF)
      {
        (xVal ? xCan1 : xCan0) = true;
        (xVal ? yCan0 : yCan1) = true; // y_i = !x_i.
      }
      else if (yIsF)
      {
        (yVal ? yCan1 : yCan0) = true;
        (yVal ? xCan0 : xCan1) = true;
      }
      else
      {
        xCan0 = xCan1 = yCan0 = yCan1 = true;
      }
    }

    // Respect existing fixings (a fixed bit only admits its own value).
    if (xIsF)
    {
      xCan0 = xCan0 && !xVal;
      xCan1 = xCan1 && xVal;
    }
    if (yIsF)
    {
      yCan0 = yCan0 && !yVal;
      yCan1 = yCan1 && yVal;
    }

    if ((!xCan0 && !xCan1) || (!yCan0 && !yCan1))
      return CONFLICT;

    if (!xIsF && (xCan0 ^ xCan1))
    {
      x.setFixed(i, true);
      x.setValue(i, xCan1);
      changed = true;
    }
    if (!yIsF && (yCan0 ^ yCan1))
    {
      y.setFixed(i, true);
      y.setValue(i, yCan1);
      changed = true;
    }

    if (eqHere)
      anyFeasibleBelow = true;
  }

  // Above the highest feasible finite t the operands are complements,
  // unless a shift past every one (x == 0) is also possible, in which
  // case nothing is deducible there (no ones can be fixed above H then).
  if (!widthFeasible)
  {
    for (unsigned w = H / 64; w < words; w++)
    {
      const uint64_t region = ~bitsBelowWord(w, H + 1) & bitsBelowWord(w, width);
      uint64_t fromX = region & xF[w] & ~yF[w]; // y := !x.
      uint64_t fromY = region & yF[w] & ~xF[w]; // x := !y.
      changed |= (fromX | fromY) != 0;
      while (fromX)
      {
        const unsigned b = ::stp::countTrailingZeroes64(fromX);
        fromX &= fromX - 1;
        y.setFixed(w * 64 + b, true);
        y.setValue(w * 64 + b, !((xV[w] >> b) & 1));
      }
      while (fromY)
      {
        const unsigned b = ::stp::countTrailingZeroes64(fromY);
        fromY &= fromY - 1;
        x.setFixed(w * 64 + b, true);
        x.setValue(w * 64 + b, !((yV[w] >> b) & 1));
      }
    }
  }

  return changed ? CHANGED : NO_CHANGE;
}

Result bvConcatBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  Result r = NO_CHANGE;
  const size_t numberOfChildren = children.size();
  unsigned current = 0;
  for (int i = (int)numberOfChildren - 1; i >= 0;
       i--) // least significant is last.
  {
    FixedBits& child = *children[i];
    for (unsigned j = 0; j < child.getWidth(); j++)
    {
      // values are different. Bad.
      if (output.isFixed(current) && child.isFixed(j) &&
          (output.getValue(current) != child.getValue(j)))
        return CONFLICT;

      if (output.isFixed(current) && !child.isFixed(j))
      {
        // only output is fixed.
        child.setFixed(j, true);
        child.setValue(j, output.getValue(current));
        r = CHANGED;
      }
      else if (!output.isFixed(current) && child.isFixed(j))
      {
        // only input is fixed.
        output.setFixed(current, true);
        output.setValue(current, child.getValue(j));
        r = CHANGED;
      }
      current++;
    }
  }
  return r;
}

// If the guard is fixed, make equal the appropriate input and output.
// If one input can not possibly be the output. Then set the guard to make it
// the other one.
// If both values are the same. Set the output to that value.
Result bvITEBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  Result result = NO_CHANGE;

  assert(3 == children.size());
  const int bitWidth = output.getWidth();
  FixedBits& guard = *children[0];
  FixedBits& c1 = *children[1];
  FixedBits& c2 = *children[2];

  assert(c1.getWidth() == c2.getWidth());
  assert(output.getWidth() == c2.getWidth());

  if (guard.isFixed(0) && guard.getValue(0))
  { // guard fixed to true. So make (first arg == output)
    result = makeEqual(output, c1, 0, bitWidth);
    if (CONFLICT == result)
      return CONFLICT;
  }
  else if (guard.isFixed(0) && !guard.getValue(0))
  {
    result = makeEqual(output, c2, 0, bitWidth);
    if (CONFLICT == result)
      return CONFLICT;
  }
  else
  {
    for (int i = 0; i < bitWidth; i++)
    {
      if (c1.isFixed(i) && c2.isFixed(i) && (c1.getValue(i) == c2.getValue(i)))
      {

        if (output.isFixed(i) && (output.getValue(i) != c1.getValue(i)))
          return CONFLICT;

        if (!output.isFixed(i))
        {
          output.setFixed(i, true);
          output.setValue(i, c1.getValue(i));
          result = CHANGED;
        }
      }
    }
  }

  bool changed = false;
  if (CHANGED == result)
    changed = true;

  for (int i = 0; i < bitWidth; i++)
  {
    if (output.isFixed(i))
    {
      if (c1.isFixed(i) && (c1.getValue(i) != output.getValue(i)))
      {
        // c1 is fixed to a value that's not the same as the output.
        if (!guard.isFixed(0))
        {
          guard.setFixed(0, true);
          guard.setValue(0, false);
          result = bvITEBothWays(children, output);
          if (CONFLICT == result)
            return CONFLICT;
          changed = true;
        }
        else if (guard.getValue(0))
          return CONFLICT;
      }

      if (c2.isFixed(i) && (c2.getValue(i) != output.getValue(i)))
      {
        // c2 is fixed to a value that's not the same as the output.
        if (!guard.isFixed(0))
        {
          guard.setFixed(0, true);
          guard.setValue(0, true);
          result = bvITEBothWays(children, output);
          if (CONFLICT == result)
            return CONFLICT;
          changed = true;
        }
        else if (!guard.getValue(0))
          return CONFLICT;
      }
    }
  }

  if (result == CONFLICT)
    return CONFLICT;
  if (changed)
    return CHANGED;

  return result;
}
}
}

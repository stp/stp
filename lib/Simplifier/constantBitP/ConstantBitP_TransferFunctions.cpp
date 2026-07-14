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
#include "stp/Simplifier/constantBitP/ConstantBitP_Utility.h"

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
Result bvEqualsBothWays(FixedBits& a, FixedBits& b, FixedBits& output)
{
  assert(a.getWidth() == b.getWidth());
  assert(1 == output.getWidth());

  const int childWidth = a.getWidth();

  Result r = NO_CHANGE;

  bool allSame = true;
  bool definatelyFalse = false;

  for (int i = 0; i < childWidth; i++)
  {
    // if both fixed
    if (a.isFixed(i) && b.isFixed(i))
    {
      // And have different values.
      if (a.getValue(i) != b.getValue(i))
      {
        definatelyFalse = true;
        break;
      }
      else
      {
        allSame &= true;
        continue;
      }
    }
    allSame &= false;
  }

  if (definatelyFalse)
  {
    if (output.isFixed(0) && output.getValue(0))
    {
      return CONFLICT;
    }
    else if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, false);
      r = CHANGED;
    }
  }
  else if (allSame)
  {
    if (output.isFixed(0) && !output.getValue(0))
    {
      return CONFLICT;
    }
    else if (!output.isFixed(0))
    {
      output.setFixed(0, true);
      output.setValue(0, true);
      r = CHANGED;
    }
  }

  if (output.isFixed(0) && output.getValue(0)) // all should be the same.
  {
    for (int i = 0; i < childWidth; i++)
    {
      if (a.isFixed(i) && b.isFixed(i))
      {
        if (a.getValue(i) != b.getValue(i))
        {
          return CONFLICT;
        }
      }
      else if (a.isFixed(i) != b.isFixed(i)) // both same but only one is fixed.
      {
        if (a.isFixed(i))
        {
          b.setFixed(i, true);
          b.setValue(i, a.getValue(i));
          r = CHANGED;
        }
        else
        {
          a.setFixed(i, true);
          a.setValue(i, b.getValue(i));
          r = CHANGED;
        }
      }
    }
  }

  // if the result is fixed to false, there is a single unspecied value, and all
  // the rest are the same. Fix it to the opposite.
  if (output.isFixed(0) && !output.getValue(0))
  {
    int unknown = 0;

    for (int i = 0; i < childWidth && unknown < 2; i++)
    {
      if (!a.isFixed(i))
        unknown++;
      if (!b.isFixed(i))
        unknown++;
      else if (a.isFixed(i) && b.isFixed(i) && a.getValue(i) != b.getValue(i))
      {
        unknown = 10; // hack, don't do the next loop.
        break;
      }
    }

    if (1 == unknown)
    {
      for (int i = 0; i < childWidth; i++)
      {
        if (!a.isFixed(i))
        {
          a.setFixed(i, true);
          a.setValue(i, !b.getValue(i));
          r = CHANGED;
        }
        if (!b.isFixed(i))
        {
          b.setFixed(i, true);
          b.setValue(i, !a.getValue(i));
          r = CHANGED;
        }
      }
    }
  }
  return r;
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
inline unsigned long long bitsBelowWord(unsigned w, unsigned bound)
{
  const unsigned long long base = (unsigned long long)w * 64;
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

  typedef unsigned long long u64;
  const unsigned words = (width + 63) / 64;
  u64* buf = (u64*)alloca(sizeof(u64) * 4 * words);
  u64* xF = buf;             // fixedness.
  u64* xV = buf + words;     // fixed ones.
  u64* yF = buf + 2 * words;
  u64* yV = buf + 3 * words;
  x.fillPackedWords(xF, xV);
  y.fillPackedWords(yF, yV);

  // Nothing fixed anywhere: nothing can be deduced.
  {
    u64 any = 0;
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
    const u64 knownOne = xV[w] | yV[w];
    const u64 both = xF[w] & yF[w];
    const u64 diff = both & (xV[w] ^ yV[w]);
    const u64 ones2 = xV[w] & yV[w];
    const u64 zeros2 = both & ~xV[w] & ~yV[w];
    const unsigned base = w * 64;

    if (knownOne)
      hi = std::min(hi, base + (unsigned)__builtin_ctzll(knownOne));
    if (diff)
    {
      const unsigned i = base + (unsigned)__builtin_ctzll(diff);
      if (i == 0)
        return CONFLICT; // bit zero is always shared.
      hi = std::min(hi, i - 1);
    }
    if (ones2)
    {
      lo = std::max(lo, base + 63 - (unsigned)__builtin_clzll(ones2));
      hi = std::min(hi, base + (unsigned)__builtin_ctzll(ones2));
    }
    if (zeros2)
      lo = std::max(lo, base + 64 - (unsigned)__builtin_clzll(zeros2));
  }

  if (lo > hi)
    return CONFLICT;

  // Feasible finite t: within [lo, min(hi, width-1)], and not a hole
  // (a position fixed to zero on either side).
  const unsigned none = width + 1;
  unsigned L = none, H = none;
  for (unsigned w = 0; w < words; w++)
  {
    const u64 hole = (xF[w] & ~xV[w]) | (yF[w] & ~yV[w]);
    u64 feas = ~hole;
    feas &= ~bitsBelowWord(w, lo);
    feas &= bitsBelowWord(w, hi == width ? width : hi + 1);
    // Mask to the width (the top word may have slack bits).
    feas &= bitsBelowWord(w, width);
    if (feas)
    {
      const unsigned first = w * 64 + (unsigned)__builtin_ctzll(feas);
      if (L == none)
        L = first;
      H = w * 64 + 63 - (unsigned)__builtin_clzll(feas);
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
    const u64 region = bitsBelowWord(w, zeroBelow);
    u64 newX = region & ~xF[w];
    u64 newY = region & ~yF[w];
    changed |= (newX | newY) != 0;
    while (newX)
    {
      const unsigned b = __builtin_ctzll(newX);
      newX &= newX - 1;
      x.setFixed(w * 64 + b, true);
      x.setValue(w * 64 + b, false);
    }
    while (newY)
    {
      const unsigned b = __builtin_ctzll(newY);
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
    const u64 bit = 1ULL << (i & 63);
    const unsigned w = i >> 6;
    const u64 hole = (xF[w] & ~xV[w]) | (yF[w] & ~yV[w]);
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
      const u64 region = ~bitsBelowWord(w, H + 1) & bitsBelowWord(w, width);
      u64 fromX = region & xF[w] & ~yF[w]; // y := !x.
      u64 fromY = region & yF[w] & ~xF[w]; // x := !y.
      changed |= (fromX | fromY) != 0;
      while (fromX)
      {
        const unsigned b = __builtin_ctzll(fromX);
        fromX &= fromX - 1;
        y.setFixed(w * 64 + b, true);
        y.setValue(w * 64 + b, !((xV[w] >> b) & 1));
      }
      while (fromY)
      {
        const unsigned b = __builtin_ctzll(fromY);
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

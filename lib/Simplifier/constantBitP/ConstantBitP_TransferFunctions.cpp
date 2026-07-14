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
Result bvUnaryMinusBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  assert(children.size() == 1);
  FixedBits& x = *children[0];
  FixedBits& y = output;
  const unsigned width = x.getWidth();
  assert(y.getWidth() == width);

  const unsigned initialFixedCount = x.countFixed() + y.countFixed();

  // The feasible t form an interval [lo, hi] with holes.
  unsigned lo = 0;
  unsigned hi = width; // t == width means x == 0.

  for (unsigned i = 0; i < width; i++)
  {
    // A known one at i (in either operand) means the lowest one is at or
    // below i.
    if (x.isFixedToOne(i) || y.isFixedToOne(i))
      hi = std::min(hi, i);

    if (x.isFixed(i) && y.isFixed(i))
    {
      if (x.getValue(i) != y.getValue(i))
        hi = std::min(hi, i == 0 ? 0 : i - 1); // complements: t < i.
      else if (x.getValue(i))
        lo = std::max(lo, i); // both one: t == i (with hi <= i from above).
      else
        lo = std::max(lo, i + 1); // both zero: t > i.
      if (x.getValue(i) != y.getValue(i) && i == 0)
        return CONFLICT; // bit zero is always shared.
    }
  }

  // Holes: t == i needs both bits able to be one.
  // nextFeasible[i]: the smallest feasible t >= i (width + 1 if none).
  const unsigned none = width + 1;
  unsigned* nextFeasible = (unsigned*)alloca(sizeof(unsigned) * (width + 2));
  nextFeasible[width + 1] = none;
  for (int t = (int)width; t >= 0; t--)
  {
    const bool hole =
        t < (int)width && (x.isFixedToZero(t) || y.isFixedToZero(t));
    const bool inRange = (unsigned)t >= lo && (unsigned)t <= hi;
    nextFeasible[t] =
        (!hole && inRange) ? (unsigned)t : nextFeasible[t + 1];
  }

  if (nextFeasible[0] == none)
    return CONFLICT; // no position for the lowest one remains.

  // prevFeasible: is there a feasible t strictly below i? Tracked while
  // sweeping upwards.
  bool anyFeasibleBelow = false;

  for (unsigned i = 0; i < width; i++)
  {
    const bool eqHere = nextFeasible[i] == i;         // t == i possible.
    const bool gtHere = nextFeasible[i + 1] != none;  // t > i possible.
    const bool ltHere = anyFeasibleBelow;             // t < i possible.

    // Possible values for (x_i, y_i): t > i contributes (0,0); t == i
    // contributes (1,1); t < i contributes complementary pairs filtered
    // by whatever is already fixed.
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
      if (x.isFixed(i))
      {
        (x.getValue(i) ? xCan1 : xCan0) = true;
        (x.getValue(i) ? yCan0 : yCan1) = true; // y_i = !x_i.
      }
      else if (y.isFixed(i))
      {
        (y.getValue(i) ? yCan1 : yCan0) = true;
        (y.getValue(i) ? xCan0 : xCan1) = true;
      }
      else
      {
        xCan0 = xCan1 = yCan0 = yCan1 = true;
      }
    }

    // Respect existing fixings (a fixed bit only admits its own value).
    if (x.isFixed(i))
    {
      xCan0 = xCan0 && !x.getValue(i);
      xCan1 = xCan1 && x.getValue(i);
    }
    if (y.isFixed(i))
    {
      yCan0 = yCan0 && !y.getValue(i);
      yCan1 = yCan1 && y.getValue(i);
    }

    if ((!xCan0 && !xCan1) || (!yCan0 && !yCan1))
      return CONFLICT;

    if (!x.isFixed(i) && (xCan0 ^ xCan1))
    {
      x.setFixed(i, true);
      x.setValue(i, xCan1);
    }
    if (!y.isFixed(i) && (yCan0 ^ yCan1))
    {
      y.setFixed(i, true);
      y.setValue(i, yCan1);
    }

    if (eqHere)
      anyFeasibleBelow = true;
  }

  return (x.countFixed() + y.countFixed() == initialFixedCount) ? NO_CHANGE
                                                                : CHANGED;
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

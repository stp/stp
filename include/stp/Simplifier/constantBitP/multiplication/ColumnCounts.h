/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: 24/03/2010
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

#ifndef COLUMNCOUNTS_H_
#define COLUMNCOUNTS_H_

#include <cstdint>
#include <iostream>

namespace simplifier
{
namespace constantBitP
{

extern std::ostream& log;

struct ColumnCounts
{
  signed* columnH; // maximum number of true partial products.
  signed* columnL; // minimum  ""            ""
  signed* sumH;
  signed* sumL;
  unsigned int bitWidth;
  const FixedBits& output;

  // With initialise false the caller provides already-set-up column arrays
  // (e.g. restored from a saved copy).
  ColumnCounts(signed _columnH[], signed _columnL[], signed _sumH[],
               signed _sumL[], unsigned _bitWidth, FixedBits& output_,
               bool initialise = true)
      : columnH(_columnH), columnL(_columnL), sumH(_sumH), sumL(_sumL),
        output(output_)
  {
    // setup the low and highs.
    bitWidth = _bitWidth;
    if (initialise)
      for (unsigned i = 0; i < bitWidth; i++)
      {
        columnL[i] = 0;
        columnH[i] = i + 1;
      }
  }

  // Halve a sum bound. They are always non-negative, so this is /2 without
  // the negative-rounding correction a signed divide pays for.
  static int half(int x)
  {
    assert(x >= 0);
    return (int)((unsigned)x >> 1);
  }

  // Returns CONFLICT if a column's counts are crossed (e.g. adjustColumns
  // found more necessary ones than the column can hold) or a snap emptied a
  // sum interval; the sums are unusable then.
  Result rebuildSums()
  {
    if (columnH[0] < columnL[0] || columnL[0] < 0)
      return CONFLICT;
    // Initialise sums.
    sumL[0] = columnL[0];
    sumH[0] = columnH[0];
    if (snapTo(0) == CONFLICT)
      return CONFLICT;

    uint64_t fixed = 0, value = 0;
    output.fillPackedWord(0, fixed, value);
    for (unsigned i = /**/ 1 /**/; i < bitWidth; i++)
    {
      if (columnH[i] < columnL[i] || columnL[i] < 0)
        return CONFLICT;
      sumH[i] = columnH[i] + half(sumH[i - 1]);
      sumL[i] = columnL[i] + half(sumL[i - 1]);

      const unsigned b = i & 63;
      if (b == 0)
        output.fillPackedWord(i >> 6, fixed, value);
      if ((fixed >> b) & 1)
      {
        const int expected = (int)((value >> b) & 1);
        if ((sumH[i] & 1) != expected)
          sumH[i]--;
        if ((sumL[i] & 1) != expected)
          sumL[i]++;
        if ((sumH[i] < sumL[i]) || (sumL[i] < 0))
          return CONFLICT;
      }
    }
    return NO_CHANGE;
  }

  void print(std::string message)
  {
    log << message << std::endl;
    log << " columnL:";
    for (unsigned i = 0; i < bitWidth; i++)
    {
      log << columnL[bitWidth - 1 - i] << " ";
    }
    log << std::endl;
    log << " columnH:";
    for (unsigned i = 0; i < bitWidth; i++)
    {
      log << columnH[bitWidth - 1 - i] << " ";
    }
    log << std::endl;
    log << " sumL:   ";

    for (unsigned i = 0; i < bitWidth; i++)
    {
      log << sumL[bitWidth - 1 - i] << " ";
    }
    log << std::endl;
    log << " sumH:   ";
    for (unsigned i = 0; i < bitWidth; i++)
    {
      log << sumH[bitWidth - 1 - i] << " ";
    }
    log << std::endl;
  }

  Result snapTo(int i)
  {
    Result r = NO_CHANGE;
    if (output.isFixed(i))
    {
      // bool changed = false;
      int expected = output.getValue(i) ? 1 : 0;

      // output is true. So the maximum and minimum can only be even.
      if ((sumH[i] & 1) != expected)
      {
        sumH[i]--;
        r = CHANGED;
      }
      if ((sumL[i] & 1) != expected)
      {
        sumL[i]++;
        r = CHANGED;
      }

      if (((sumH[i] < sumL[i]) || (sumL[i] < 0)))
        return CONFLICT;
    }
    return r;
  }

  // update the sum of a column to the parity of the output for that column.
  // e.g. [0,2] if the answer is 1, goes to [1,1].
  Result snapTo()
  {
    Result r = NO_CHANGE;

    // Make sure each fixed column's sum is consistent with the output;
    // snapTo(i) is a no-op on unfixed columns, so visit only the fixed
    // bits, straight off the packed words.
    const unsigned words = (bitWidth + 63) / 64;
    for (unsigned w = 0; w < words; w++)
    {
      uint64_t fixed, value;
      output.fillPackedWord(w, fixed, value);
      while (fixed != 0)
      {
        const unsigned b = ctz64(fixed);
        fixed &= fixed - 1;
        const unsigned i = w * 64 + b;

        const int expected = (int)((value >> b) & 1);
        if ((sumH[i] & 1) != expected)
        {
          sumH[i]--;
          r = CHANGED;
        }
        if ((sumL[i] & 1) != expected)
        {
          sumL[i]++;
          r = CHANGED;
        }
        if ((sumH[i] < sumL[i]) || (sumL[i] < 0))
          return CONFLICT;
      }
    }
    return r;
  }

  static unsigned ctz64(uint64_t v)
  {
    assert(v != 0);
    return (unsigned)__builtin_ctzll(v);
  }

  bool inConflict()
  {
    for (unsigned i = 0; i < bitWidth; i++)
      if ((sumL[i] > sumH[i]) || (columnL[i] > columnH[i]))
        return true;
    return false;
  }

  // The caller must have run rebuildSums (and stopped on CONFLICT from it)
  // first: it guarantees the entry state has no crossed intervals.
  Result fixedPoint()
  {
    bool changed = true;
    bool totalChanged = false;

    while (changed)
    {
      changed = false;

      // propagate before snapTo: the caller runs rebuildSums first, which
      // already snaps each fixed column as it builds, so an initial snapTo
      // sweep would find nothing. The fixpoint reached is the same in
      // either order.
      Result r = propagate();
      if (r == CHANGED)
        changed = true;
      if (r == CONFLICT)
        return CONFLICT;

      r = snapTo();
      if (r == CHANGED)
        changed = true;
      if (r == CONFLICT)
        return CONFLICT;

      if (changed)
        totalChanged = true;
    }

    // No closing conflict scan: rebuildSums guarantees a clean entry state,
    // and propagate/snapTo report any interval they empty themselves.
    assert(!inConflict());
    assert(propagate() == NO_CHANGE);
    assert(snapTo() == NO_CHANGE);

    if (totalChanged)
      return CHANGED;
    else
      return NO_CHANGE;
  }

  // Make column i consistent with sum i and sum i-1 (i >= 1), tightening
  // any of the three intervals. Most columns are already consistent, so
  // the guards are cheap well-predicted branches; the conflict test only
  // runs when something fired.
  // Returns changed (bit 0) and conflict — an interval emptied — (bit 1).
  int propagateAt(unsigned i)
  {
    const int cl = half(sumL[i - 1]); // snapshots: the writes below
    const int ch = half(sumH[i - 1]); // deliberately don't rebuild them.
    bool changed = false;

    if (sumL[i] < columnL[i] + cl)
    {
      sumL[i] = columnL[i] + cl;
      changed = true;
    }

    if (sumH[i] > columnH[i] + ch)
    {
      sumH[i] = columnH[i] + ch;
      changed = true;
    }

    if (sumL[i] - columnH[i] > cl)
    {
      sumL[i - 1] = (sumL[i] - columnH[i]) * 2;
      changed = true;
    }

    if (sumH[i] - columnL[i] < ch)
    {
      sumH[i - 1] = (sumH[i] - columnL[i]) * 2 + 1;
      changed = true;
    }

    if (sumL[i] - ch > columnL[i])
    {
      columnL[i] = sumL[i] - ch;
      changed = true;
    }

    if (sumH[i] - cl < columnH[i])
    {
      columnH[i] = sumH[i] - cl;
      changed = true;
    }

    if (!changed)
      return 0;
    const bool conflict = (sumL[i] > sumH[i]) | (columnL[i] > columnH[i]) |
                          (sumL[i - 1] > sumH[i - 1]);
    return 1 | ((int)conflict << 1);
  }

  // Returns changed (bit 0) and conflict (bit 1), like propagateAt.
  int syncColumnZero()
  {
    bool changed = false;
    if (sumL[0] > columnL[0])
    {
      columnL[0] = sumL[0];
      changed = true;
    }
    if (sumL[0] < columnL[0])
    {
      sumL[0] = columnL[0];
      changed = true;
    }
    if (sumH[0] < columnH[0])
    {
      columnH[0] = sumH[0];
      changed = true;
    }
    if (sumH[0] > columnH[0])
    {
      sumH[0] = columnH[0];
      changed = true;
    }
    return (int)changed | ((sumL[0] > sumH[0]) ? 2 : 0);
  }

  // Assert that all the counts are consistent.
  Result propagate()
  {
    int flags = syncColumnZero();

    for (unsigned i = 1; i < bitWidth; i++)
      flags |= propagateAt(i);

    if (flags & 2)
      return CONFLICT;
    if (flags & 1)
      return CHANGED;
    return NO_CHANGE;
  }
};
}
}

#endif /* COLUMNCOUNTS_H_ */

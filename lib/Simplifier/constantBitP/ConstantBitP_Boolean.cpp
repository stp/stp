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

// AND, OR, XOR, NOT Transfer functions.
// Trevor Hansen. BSD License.

namespace simplifier
{
namespace constantBitP
{

// A word at a time: one pass over the children computes the parity of the
// fixed ones and classifies each bit (all children fixed, exactly one
// unfixed); a second pass runs only when child bits need fixing.
Result bvXorBothWays(vector<FixedBits*>& operands, FixedBits& output)
{
  Result result = NO_CHANGE;
  const unsigned width = output.getWidth();
  const unsigned words = (width + 63) / 64;
  const unsigned n = operands.size();
#ifndef NDEBUG
  for (unsigned j = 0; j < n; j++)
    assert(operands[j]->getWidth() == width);
#endif

  const uint64_t top =
      (width % 64 == 0) ? ~0ULL : ((1ULL << (width % 64)) - 1);

  for (unsigned w = 0; w < words; w++)
  {
    const uint64_t mask = (w == words - 1) ? top : ~0ULL;

    uint64_t fo, vo;
    output.fillPackedWord(w, fo, vo);

    uint64_t parity = 0;   // XOR of the children's fixed ones
    uint64_t unfixed1 = 0; // at least one child unfixed
    uint64_t unfixed2 = 0; // at least two children unfixed
    for (unsigned j = 0; j < n; j++)
    {
      uint64_t f, v;
      operands[j]->fillPackedWord(w, f, v);
      parity ^= v;
      const uint64_t unf = ~f & mask;
      unfixed2 |= unfixed1 & unf;
      unfixed1 |= unf;

      // Two or more unfixed children everywhere: no bit can be derived
      // in either direction, and no conflict is possible.
      if (unfixed2 == mask)
        break;
    }

    if (unfixed2 == mask)
      continue;

    const uint64_t allFixed = ~unfixed1 & mask;

    // All children fixed and the output disagrees with their parity.
    const uint64_t conflict = allFixed & fo & (vo ^ parity);

    uint64_t outFix = allFixed & ~fo;
    // Exactly one unfixed child, output known: that child's bit is the
    // parity of everything else XORed with the output.
    uint64_t childFix = unfixed1 & ~unfixed2 & fo;

    if (conflict != 0)
    {
      // The bit-at-a-time original still applies fixes below the first
      // conflicting bit before reporting the conflict.
      const uint64_t below = (1ULL << __builtin_ctzll(conflict)) - 1;
      outFix &= below;
      childFix &= below;
    }

    if (outFix != 0)
    {
      output.fixWordBits(w, outFix, parity);
      result = CHANGED;
    }

    if (childFix != 0)
    {
      for (unsigned j = 0; j < n; j++)
      {
        uint64_t f, v;
        operands[j]->fillPackedWord(w, f, v);
        const uint64_t fix = ~f & childFix;
        if (fix != 0)
        {
          operands[j]->fixWordBits(w, fix, parity ^ vo);
          result = CHANGED;
        }
      }
    }

    if (conflict != 0)
      return CONFLICT;
  }
  return result;
}

// if output bit is true. Fix all the operands.
// if all the operands are fixed. Fix the output.
// given 1,1,1,- == 0, fix - to 0.
// A word at a time: one pass over the children classifies every bit of the
// word (any child fixed zero, all children fixed one, exactly one child
// unfixed); a second pass runs only when child bits need fixing.
Result bvAndBothWays(vector<FixedBits*>& operands, FixedBits& output)
{
  Result result = NO_CHANGE;
  const unsigned width = output.getWidth();
  const unsigned words = (width + 63) / 64;
  const unsigned n = operands.size();
#ifndef NDEBUG
  for (unsigned j = 0; j < n; j++)
    assert(operands[j]->getWidth() == width);
#endif

  const uint64_t top =
      (width % 64 == 0) ? ~0ULL : ((1ULL << (width % 64)) - 1);

  for (unsigned w = 0; w < words; w++)
  {
    const uint64_t mask = (w == words - 1) ? top : ~0ULL;

    uint64_t fo, vo;
    output.fillPackedWord(w, fo, vo);

    uint64_t anyZero = 0;    // some child fixed to zero
    uint64_t allOne = mask;  // every child fixed to one
    uint64_t unfixed1 = 0;   // at least one child unfixed
    uint64_t unfixed2 = 0;   // at least two children unfixed
    for (unsigned j = 0; j < n; j++)
    {
      uint64_t f, v;
      operands[j]->fillPackedWord(w, f, v);
      anyZero |= f & ~v;
      allOne &= v;
      const uint64_t unf = ~f & mask;
      unfixed2 |= unfixed1 & unf;
      unfixed1 |= unf;

      // Once every bit has a zero-entailing child and no output bit is
      // fixed to one, nothing further can change: allOne and anyZero are
      // disjoint (the child that zeroes a bit also drops it from allOne),
      // so the all-ones cases are dead, child fixes need output ones, and
      // the output can only become zero, which is already entailed
      // everywhere. This makes the boolean AND (width one, huge arity)
      // stop at its first false conjunct instead of scanning them all.
      if (vo == 0 && anyZero == mask)
        break;
    }

    // Output fixed to one against a child fixed to zero; output fixed to
    // zero with every child fixed to one.
    const uint64_t conflict = (vo & anyZero) | ((fo & ~vo) & allOne);

    // Output one: all children become one. Output zero, no fixed zero and a
    // single unfixed child: it becomes zero.
    uint64_t childTo1 = vo & unfixed1;
    uint64_t childTo0 = (fo & ~vo) & ~anyZero & unfixed1 & ~unfixed2;
    uint64_t outTo0 = ~fo & anyZero & mask;
    uint64_t outTo1 = ~fo & allOne;

    if (conflict != 0)
    {
      // The bit-at-a-time original still applies fixes below the first
      // conflicting bit before reporting the conflict.
      const uint64_t below = (1ULL << __builtin_ctzll(conflict)) - 1;
      childTo1 &= below;
      childTo0 &= below;
      outTo0 &= below;
      outTo1 &= below;
    }

    if ((childTo1 | childTo0) != 0)
    {
      for (unsigned j = 0; j < n; j++)
      {
        uint64_t f, v;
        operands[j]->fillPackedWord(w, f, v);
        const uint64_t unf = ~f & mask;
        const uint64_t to1 = childTo1 & unf;
        const uint64_t to0 = childTo0 & unf;
        if ((to1 | to0) != 0)
        {
          operands[j]->fixWordBits(w, to1 | to0, to1);
          result = CHANGED;
        }
      }
    }

    if ((outTo0 | outTo1) != 0)
    {
      output.fixWordBits(w, outTo0 | outTo1, outTo1);
      result = CHANGED;
    }

    if (conflict != 0)
      return CONFLICT;
  }
  return result;
}

// The dual of bvAndBothWays: a word at a time, with the same second-pass
// and early-exit structure.
Result bvOrBothWays(vector<FixedBits*>& children, FixedBits& output)
{
  Result r = NO_CHANGE;
  const unsigned width = output.getWidth();
  const unsigned words = (width + 63) / 64;
  const unsigned n = children.size();
#ifndef NDEBUG
  for (unsigned j = 0; j < n; j++)
    assert(children[j]->getWidth() == width);
#endif

  const uint64_t top =
      (width % 64 == 0) ? ~0ULL : ((1ULL << (width % 64)) - 1);

  for (unsigned w = 0; w < words; w++)
  {
    const uint64_t mask = (w == words - 1) ? top : ~0ULL;

    uint64_t fo, vo;
    output.fillPackedWord(w, fo, vo);

    uint64_t anyOne = 0;     // some child fixed to one
    uint64_t allZero = mask; // every child fixed to zero
    uint64_t unfixed1 = 0;   // at least one child unfixed
    uint64_t unfixed2 = 0;   // at least two children unfixed
    for (unsigned j = 0; j < n; j++)
    {
      uint64_t f, v;
      children[j]->fillPackedWord(w, f, v);
      anyOne |= v;
      allZero &= f & ~v;
      const uint64_t unf = ~f & mask;
      unfixed2 |= unfixed1 & unf;
      unfixed1 |= unf;

      // Once every bit has a one-entailing child and no output bit is
      // fixed to zero, nothing further can change: anyOne and allZero are
      // disjoint (the child that sets a bit also drops it from allZero),
      // so the all-zeroes cases are dead, child fixes need output zeros,
      // and the output can only become one, which is already entailed
      // everywhere. This makes the boolean OR (width one, huge arity)
      // stop at its first true disjunct instead of scanning them all.
      if ((fo & ~vo) == 0 && anyOne == mask)
        break;
    }

    // Output fixed to zero against a child fixed to one; output fixed to
    // one with every child fixed to zero.
    const uint64_t conflict = ((fo & ~vo) & anyOne) | (vo & allZero);

    // Output zero: all children become zero. Output one, no fixed one and
    // a single unfixed child: it becomes one.
    uint64_t childTo0 = (fo & ~vo) & unfixed1;
    uint64_t childTo1 = vo & ~anyOne & unfixed1 & ~unfixed2;
    uint64_t outTo1 = ~fo & anyOne & mask;
    uint64_t outTo0 = ~fo & allZero;

    if (conflict != 0)
    {
      // The bit-at-a-time original still applies fixes below the first
      // conflicting bit before reporting the conflict.
      const uint64_t below = (1ULL << __builtin_ctzll(conflict)) - 1;
      childTo0 &= below;
      childTo1 &= below;
      outTo1 &= below;
      outTo0 &= below;
    }

    if ((childTo0 | childTo1) != 0)
    {
      for (unsigned j = 0; j < n; j++)
      {
        uint64_t f, v;
        children[j]->fillPackedWord(w, f, v);
        const uint64_t unf = ~f & mask;
        const uint64_t to0 = childTo0 & unf;
        const uint64_t to1 = childTo1 & unf;
        if ((to0 | to1) != 0)
        {
          children[j]->fixWordBits(w, to0 | to1, to1);
          r = CHANGED;
        }
      }
    }

    if ((outTo1 | outTo0) != 0)
    {
      output.fixWordBits(w, outTo1 | outTo0, outTo1);
      r = CHANGED;
    }

    if (conflict != 0)
      return CONFLICT;
  }
  return r;
}

Result bvNotBothWays(vector<FixedBits*>& children, FixedBits& result)
{
  return bvNotBothWays(*(children[0]), result);
}

Result bvImpliesBothWays(vector<FixedBits*>& children, FixedBits& result)
{

  FixedBits& a = (*children[0]);
  FixedBits& b = (*children[1]);

  assert(a.getWidth() == result.getWidth());
  const int bitWidth = a.getWidth();
  assert(bitWidth == 1);

  Result r = NO_CHANGE;

  int i = 0;

  //  (false -> something) is always true.
  //  (something -> true ) is always true.
  if (a.isFixedToZero(i) || b.isFixedToOne(i))
  {
    if (!result.isFixed(i))
    {
      result.setFixed(i, true);
      result.setValue(i, true);
      r = CHANGED;
    }
    else if (result.isFixedToZero(i))
      return CONFLICT;
  }

  // If the result is false. it must be (true -> false)
  if (result.isFixedToZero(i))
  {
    if (a.isFixedToZero(i) || b.isFixedToOne(i))
      return CONFLICT;

    if (!a.isFixed(i))
    {
      a.setFixed(i, true);
      a.setValue(i, true);
      r = CHANGED;
    }
    if (!b.isFixed(i))
    {
      b.setFixed(i, true);
      b.setValue(i, false);
      r = CHANGED;
    }
  }

  if (result.isFixedToOne(i))
  {
    if (a.isFixedToOne(i))
    {
      if (!b.isFixed(i))
      {
        b.setFixed(i, true);
        b.setValue(i, true);
        r = CHANGED;
      }
      else if (b.isFixedToZero(i))
        return CONFLICT;
    }

    if (b.isFixedToZero(i))
    {
      if (!a.isFixed(i))
      {
        a.setFixed(i, true);
        a.setValue(i, false);
        r = CHANGED;
      }
    }
  }

  if (a.isFixedToOne(i) && b.isFixedToZero(i))
  {
    if (result.isFixedToOne(i))
      return CONFLICT;
    if (!result.isFixed(i))
    {
      result.setFixed(i, true);
      result.setValue(i, false);
      r = CHANGED;
    }
  }

  return r;
}

Result bvNotBothWays(FixedBits& a, FixedBits& output)
{
  assert(a.getWidth() == output.getWidth());
  const unsigned width = a.getWidth();
  const unsigned words = (width + 63) / 64;

  Result result = NO_CHANGE;

  for (unsigned w = 0; w < words; w++)
  {
    uint64_t fa, va, fo, vo;
    a.fillPackedWord(w, fa, va);
    output.fillPackedWord(w, fo, vo);

    // Error where both are fixed to the same value.
    const uint64_t conflict = fa & fo & ~(va ^ vo);

    uint64_t addOut = fa & ~fo;
    uint64_t addA = fo & ~fa;

    if (conflict != 0)
    {
      // Match the bit-at-a-time original: bits below the first conflicting
      // one are still fixed before the conflict is reported.
      const uint64_t below = (1ULL << __builtin_ctzll(conflict)) - 1;
      addOut &= below;
      addA &= below;
    }

    if (addOut != 0)
    {
      output.fixWordBits(w, addOut, ~va);
      result = CHANGED;
    }
    if (addA != 0)
    {
      a.fixWordBits(w, addA, ~vo);
      result = CHANGED;
    }

    if (conflict != 0)
      return CONFLICT;
  }
  return result;
}
}
}

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
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_Utility.h"
#include <cstdint>
#include <set>
#include <stdexcept>

namespace simplifier
{
namespace constantBitP
{
using std::endl;
using std::pair;
using std::set;

const bool debug_division = false;
extern std::ostream& log;

using stp::STPMgr;

enum WhatIsOutput
{
  REMAINDER_IS_OUTPUT,
  QUOTIENT_IS_OUTPUT
};

enum Operation
{
  SIGNED_DIVISION,
  SIGNED_REMAINDER
};

// For unsigned 3-bit exhaustive, there are 1119 differences for unsigned
// division.

// a/b and a%b. a=bq +r. Where b!=0 implies r<b. Multiplication and addition
// don't overflow.

// returning true = conflict.
// Fix value of a to b.
bool fix(FixedBits& a, const FixedBits& b, const int i)
{
  if (!b.isFixed(i))
    return false;

  if (a.isFixed(i) && b.isFixed(i) && (a.getValue(i) ^ b.getValue(i)))
    return true;

  if (!a.isFixed(i) && b.isFixed(i))
  {
    a.setFixed(i, true);
    a.setValue(i, b.getValue(i));
    return false;
  }

  return false;
}

FixedBits cbvToFixedBits(stp::CBV low, unsigned width)
{
  FixedBits lowBits(width, false);
  for (int i = width - 1; i >= 0; i--)
  {
    if (CONSTANTBV::BitVector_bit_test(low, i))
    {
      lowBits.setFixed(i, true);
      lowBits.setValue(i, true);
    }
    else
    {
      lowBits.setFixed(i, true);
      lowBits.setValue(i, false);
    }
  }
  return lowBits;
}

namespace
{
// Bits of word w with global index below `bound`.
inline uint64_t rangeBelow(unsigned w, unsigned bound)
{
  const uint64_t base = (uint64_t)w * 64;
  if (base + 64 <= bound)
    return ~(uint64_t)0;
  if (base >= bound)
    return 0;
  return ((uint64_t)1 << (bound - base)) - 1;
}
}

// The value "b" is in the range [low,high] inclusive.
// This computes directly what the two maximally precise comparison
// propagations (b <= high, then low <= b) and the shared-prefix rule
// deduce. An unfixed bit is forced to zero exactly when raising it pushes
// the minimum admitted value past high (2^i > high - minAdmitted), and
// forced to one exactly when clearing it drops the maximum admitted value
// below low (2^i > maxAdmitted - low); the leading bits where low and
// high agree are then fixed outright.
// Like its predecessor it's not idempotent: <....1> [5,6] doesn't
// completely set it.
Result fix(FixedBits& b, stp::CBV low, stp::CBV high)
{
  static_assert(sizeof(unsigned int) == 4, "CBV units are 32-bit");
  const unsigned width = b.getWidth();
  const unsigned words = (width + 63) / 64;
  const unsigned units = (width + 31) / 32;

  uint64_t* buf = (uint64_t*)alloca(sizeof(uint64_t) * 5 * words);
  uint64_t* bF = buf;             // fixedness.
  uint64_t* bV = buf + words;     // fixed ones = the minimum admitted value.
  uint64_t* maxAdm = buf + 2 * words;
  uint64_t* lowW = buf + 3 * words;
  uint64_t* highW = buf + 4 * words;
  b.fillPackedWords(bF, bV);

  for (unsigned w = 0; w < words; w++)
  {
    uint64_t lo = low[2 * w], hi = high[2 * w];
    if (2 * w + 1 < units)
    {
      lo |= (uint64_t)low[2 * w + 1] << 32;
      hi |= (uint64_t)high[2 * w + 1] << 32;
    }
    lowW[w] = lo;
    highW[w] = hi;
    maxAdm[w] = (bV[w] | ~bF[w]) & rangeBelow(w, width);
  }

  // Lexicographic multiword comparisons, top word first.
  int minVsHigh = 0, maxVsLow = 0;
  for (int w = (int)words - 1; w >= 0; w--)
  {
    if (minVsHigh == 0 && bV[w] != highW[w])
      minVsHigh = bV[w] < highW[w] ? -1 : 1;
    if (maxVsLow == 0 && maxAdm[w] != lowW[w])
      maxVsLow = maxAdm[w] < lowW[w] ? -1 : 1;
  }
  if (minVsHigh > 0 || maxVsLow < 0)
    return CONFLICT; // no admitted value lies in the range.

  bool changed = false;

  // b <= high: bits that cannot be one. diff = high - minAdmitted; any
  // unfixed bit at or above diff's bit-length would overshoot.
  {
    unsigned bitLen = 0;
    uint64_t borrow = 0;
    for (unsigned w = 0; w < words; w++)
    {
      const uint64_t hw = highW[w], sub = bV[w];
      const uint64_t d1 = hw - sub;
      const bool under1 = hw < sub;
      const uint64_t d = d1 - borrow;
      const bool under2 = d1 < borrow;
      borrow = (under1 || under2) ? 1 : 0;
      if (d != 0)
        bitLen = w * 64 + 64 - (unsigned)__builtin_clzll(d);
    }
    for (unsigned w = 0; w < words; w++)
    {
      uint64_t forced0 = ~bF[w] & ~rangeBelow(w, bitLen) & rangeBelow(w, width);
      if (forced0 == 0)
        continue;
      changed = true;
      bF[w] |= forced0;
      maxAdm[w] &= ~forced0;
      while (forced0)
      {
        const unsigned bit = __builtin_ctzll(forced0);
        forced0 &= forced0 - 1;
        b.setFixed(w * 64 + bit, true);
        b.setValue(w * 64 + bit, false);
      }
    }
  }

  // low <= b, on the updated maximum: bits that cannot be zero.
  {
    // Re-check: forcing zeros can only lower the maximum.
    int cmp = 0;
    for (int w = (int)words - 1; w >= 0 && cmp == 0; w--)
      if (maxAdm[w] != lowW[w])
        cmp = maxAdm[w] < lowW[w] ? -1 : 1;
    if (cmp < 0)
      return CONFLICT;

    unsigned bitLen = 0;
    uint64_t borrow = 0;
    for (unsigned w = 0; w < words; w++)
    {
      const uint64_t mw = maxAdm[w], sub = lowW[w];
      const uint64_t d1 = mw - sub;
      const bool under1 = mw < sub;
      const uint64_t d = d1 - borrow;
      const bool under2 = d1 < borrow;
      borrow = (under1 || under2) ? 1 : 0;
      if (d != 0)
        bitLen = w * 64 + 64 - (unsigned)__builtin_clzll(d);
    }
    for (unsigned w = 0; w < words; w++)
    {
      uint64_t forced1 = ~bF[w] & ~rangeBelow(w, bitLen) & rangeBelow(w, width);
      if (forced1 == 0)
        continue;
      changed = true;
      bF[w] |= forced1;
      bV[w] |= forced1;
      while (forced1)
      {
        const unsigned bit = __builtin_ctzll(forced1);
        forced1 &= forced1 - 1;
        b.setFixed(w * 64 + bit, true);
        b.setValue(w * 64 + bit, true);
      }
    }
  }

  // The leading bits where low and high agree are the value's bits.
  {
    unsigned firstDiffer = 0; // the prefix covers bits above this.
    for (int w = (int)words - 1; w >= 0; w--)
    {
      const uint64_t d = (lowW[w] ^ highW[w]) & rangeBelow(w, width);
      if (d != 0)
      {
        firstDiffer = w * 64 + 64 - (unsigned)__builtin_clzll(d);
        break;
      }
    }
    for (unsigned w = 0; w < words; w++)
    {
      const uint64_t prefix =
          ~rangeBelow(w, firstDiffer) & rangeBelow(w, width);
      if (prefix == 0)
        continue;
      if (prefix & bF[w] & (bV[w] ^ lowW[w]))
        return CONFLICT; // fixed to the other value.
      uint64_t newFix = prefix & ~bF[w];
      changed |= newFix != 0;
      while (newFix)
      {
        const unsigned bit = __builtin_ctzll(newFix);
        newFix &= newFix - 1;
        b.setFixed(w * 64 + bit, true);
        b.setValue(w * 64 + bit, (lowW[w] >> bit) & 1);
      }
    }
  }

  return changed ? CHANGED : NO_CHANGE;
}

Result bvUnsignedQuotientAndRemainder2(vector<FixedBits*>& children,
                                       FixedBits& output, STPMgr* bm,
                                       WhatIsOutput whatIs);

Result bvUnsignedQuotientAndRemainder(vector<FixedBits*>& children,
                                      FixedBits& output, STPMgr* bm,
                                      WhatIsOutput whatIs)
{
  assert(output.getWidth() == children[0]->getWidth());
  assert(output.getWidth() == children[1]->getWidth());
  assert(children.size() == 2);

  if (whatIs != QUOTIENT_IS_OUTPUT)
  {
    return bvUnsignedQuotientAndRemainder2(children, output, bm, whatIs);
  }

  FixedBits& a = *children[0];
  FixedBits& b = *children[1];

  const unsigned width = a.getWidth();

  stp::CBV minTop = CONSTANTBV::BitVector_Create(width, true);
  stp::CBV maxTop = CONSTANTBV::BitVector_Create(width, true);

  setUnsignedMinMax(a, minTop, maxTop);

  stp::CBV minBottom = CONSTANTBV::BitVector_Create(width, true);
  stp::CBV maxBottom = CONSTANTBV::BitVector_Create(width, true);

  setUnsignedMinMax(b, minBottom, maxBottom);

  stp::CBV minQuotient = CONSTANTBV::BitVector_Create(width, true);
  stp::CBV maxQuotient = CONSTANTBV::BitVector_Create(width, true);

  stp::CBV minRemainder = CONSTANTBV::BitVector_Create(width, true);
  stp::CBV maxRemainder = CONSTANTBV::BitVector_Create(width, true);

  if (whatIs == QUOTIENT_IS_OUTPUT)
  {
    setUnsignedMinMax(output, minQuotient, maxQuotient);

    for (unsigned i = 0; i < width; i++)
      CONSTANTBV::BitVector_Bit_On(maxRemainder, i);
  }
  else
  {
    setUnsignedMinMax(output, minRemainder, maxRemainder);

    for (unsigned i = 0; i < width; i++)
      CONSTANTBV::BitVector_Bit_On(maxQuotient, i);
  }

  // need to clean up these at end.
  stp::CBV one = CONSTANTBV::BitVector_Create(width, true);
  CONSTANTBV::BitVector_increment(one);

  stp::CBV max = CONSTANTBV::BitVector_Create(width, true);
  CONSTANTBV::BitVector_Fill(max);

  // quotient and remainder.
  stp::CBV q = CONSTANTBV::BitVector_Create(width, true);
  stp::CBV r = CONSTANTBV::BitVector_Create(width, true);
  // misc.
  stp::CBV copy = CONSTANTBV::BitVector_Create(width, true);
  stp::CBV copy2 = CONSTANTBV::BitVector_Create(width, true);
  stp::CBV multR = CONSTANTBV::BitVector_Create(width, true);

  if (debug_division)
  {
    log << "--" << endl;
    log << "initial" << endl;
    log << "a:[" << *minTop << "," << *maxTop << "]";
    log << " / b:[" << *minBottom << "," << *maxBottom << "] = ";
    log << "[" << *minQuotient << "," << *maxQuotient << "]";
    log << " rem [" << *minRemainder << "," << *maxRemainder << "]";
    log << endl;
  }

  // If a bit is changed, then we fixed point again.
  bool bitEverChanged = false;
  bool bitJustChanged = true;
  Result result = NO_CHANGE;

  // We loop. There are 6 cases.
  while (bitJustChanged)
  {
    bitJustChanged = false;

    bool changed = true;

    int iteration = 0;
    while (changed)
    {
      changed = false;
      CONSTANTBV::ErrCode e;

      // The main loop doesn't work if there is a division by zero possible.
      // If the minimum bottom is zero, but the minimum quotient is > 111.1111, then in
      // our semantics of a/0 = 1..1, it can't be zero.
      if (CONSTANTBV::BitVector_is_empty(minBottom) &&
          CONSTANTBV::BitVector_Lexicompare(maxQuotient, max) < 0)
      {
        CONSTANTBV::BitVector_increment(minBottom);
        if (CONSTANTBV::BitVector_Lexicompare(minBottom, maxBottom) > 0)
        {
          result = CONFLICT;
          goto end;
        }
      }

      if (CONSTANTBV::BitVector_is_empty(minBottom))
      {
        goto end; // Possible division by zero. Hard to work with..
      }

      bool carry_1 = false;
      CONSTANTBV::BitVector_sub(copy, minTop, minRemainder, &carry_1);
      if (!carry_1) // Not sure if it goes negative.
      {
        e = CONSTANTBV::BitVector_Div_Pos(q, copy, maxBottom, r);
        assert(e == CONSTANTBV::ErrCode_Ok);

        if (CONSTANTBV::BitVector_Lexicompare(minQuotient, q) < 0)
        {
          if (debug_division)
          {
            log << "1 minQ) " << *minTop;
            log << " / " << *maxBottom;
            log << " = " << *q;
            log << " r " << *r << endl;
          }

          // min quotient is bigger. Bring in.
          CONSTANTBV::BitVector_Copy(minQuotient, q);
          changed = true;
        }
      }

      CONSTANTBV::BitVector_Copy(copy, maxTop);
      // bool carry_2 = false;
      // CONSTANTBV::BitVector_sub(copy,maxTop,minRemainder,&carry_2);
      // assert(!carry_1); // Not sure if it goes negative.

      e = CONSTANTBV::BitVector_Div_Pos(q, copy, minBottom, r);
      assert(e == CONSTANTBV::ErrCode_Ok);

      if (CONSTANTBV::BitVector_Lexicompare(maxQuotient, q) > 0)
      {
        if (debug_division)
        {
          log << "2 maxQ) " << *maxTop;
          log << " / " << *minBottom;
          log << " = " << *q;
          log << " r " << *r << endl;
        }

        CONSTANTBV::BitVector_Copy(maxQuotient,
                                   q); // copy the reduced value in.
        changed = true;
      }

      CONSTANTBV::BitVector_Copy(copy, maxQuotient);
      e = CONSTANTBV::BitVector_Mul_Pos(multR, copy, maxBottom, true);
      bool carry = false;
      CONSTANTBV::BitVector_sub(copy, maxBottom, one, &carry);
      CONSTANTBV::BitVector_add(copy2, multR, copy, &carry);
      CONSTANTBV::BitVector_Copy(multR, copy2);
      // The add discards the carry. That is safe: the strict multiply
      // reports an error once the product reaches bit (width - 1), so when
      // e is ok and maxBottom >= 1,
      //   maxQuotient * maxBottom + (maxBottom - 1) <= 2^width - 2,
      // and nothing wraps. If maxBottom is 0 the subtract borrows and the
      // sum is wrong, but then the range of the bottom is empty (minBottom
      // is at least one here), so no solutions exist and the resulting
      // clamping is vacuous.

      if (e == CONSTANTBV::ErrCode_Ok &&
          CONSTANTBV::BitVector_Lexicompare(maxTop, multR) > 0)
      {
        if (debug_division)
        {
          log << "3 maxT) " << *maxQuotient;
          log << " * " << *maxBottom;
          log << " = " << *multR << endl;
        }
        CONSTANTBV::BitVector_Copy(maxTop, multR);
        changed = true;
      }

      CONSTANTBV::BitVector_Copy(copy, minBottom);

      //  If this is strict then it seems to be treated as signed, so it is
      //  considered to overflow
      // if a bit moves into the top of multR.
      e = CONSTANTBV::BitVector_Mul_Pos(multR, copy, minQuotient, false);
      // cerr << e << endl;

      if (e == CONSTANTBV::ErrCode_Ok &&
          CONSTANTBV::BitVector_Lexicompare(minTop, multR) < 0)
      {
        if (debug_division)
        {
          log << "4 minT) " << *minQuotient;
          log << " * " << *minBottom;
          log << " = " << *multR << endl;
        }
        CONSTANTBV::BitVector_Copy(minTop, multR);
        changed = true;
      }

      if (CONSTANTBV::BitVector_Lexicompare(minQuotient, one) >= 0)
      {
        // not going to divide by zero.

        CONSTANTBV::BitVector_Copy(copy, maxTop);
        e = CONSTANTBV::BitVector_Div_Pos(q, copy, minQuotient, r);
        assert(e == CONSTANTBV::ErrCode_Ok);

        if (CONSTANTBV::BitVector_Lexicompare(maxBottom, q) > 0)
        {
          if (debug_division)
          {
            log << "5 maxB) " << *maxTop;
            log << " / " << *minQuotient;
            log << " = " << *q;
            log << " r " << *r << endl;
          }

          // min quotient is bigger. Bring in.
          CONSTANTBV::BitVector_Copy(maxBottom, q);
          changed = true;
        }
      }

      // This rule increases the minimum of the bottom.
      //  let a be the min of the top,
      //  let q be the maximum of the quotient,
      //  let b be the min. of the bottom.
      // then a= bq +r
      // so a = bq + (b-1)  // if the max. of r is one less than b.
      // so (1+a) / (q+1) = b.
      // We round the division up.
      {
        bool carry = false;
        CONSTANTBV::BitVector_add(copy, minTop, one, &carry);
        bool carry2 = false;
        CONSTANTBV::BitVector_add(copy2, maxQuotient, one, &carry2);
        if (!carry && !carry2)
        {
          e = CONSTANTBV::BitVector_Div_Pos(q, copy, copy2, r);
          assert(e == CONSTANTBV::ErrCode_Ok);
          if (CONSTANTBV::BitVector_Lexicompare(q, one) >= 0)
          {
            CONSTANTBV::BitVector_add(copy, q, one, &carry);
            if (!carry && (CONSTANTBV::BitVector_Lexicompare(minBottom, q) < 0))
            {

              if (debug_division)
              {
                log << "6 min_3_B) ";
                log << "minBottom" << *minBottom << " ";
                log << "q" << *q << endl;
              }

              // min quotient is bigger. Bring in.
              CONSTANTBV::BitVector_Copy(minBottom, q);
              changed = true;
            }
          }
        }
      }

      // Don't know why we don't need to check the intervals on the others?
      if (CONSTANTBV::BitVector_Lexicompare(minQuotient, maxQuotient) > 0)
      {
        if (debug_division)
        {
          log << "conflict" << endl;
          log << "a:[" << *minTop << "," << *maxTop << "]";
          log << " / b:[" << *minBottom << "," << *maxBottom << "] = ";
          log << "[" << *minQuotient << "," << *maxQuotient << "]";
          log << endl;
        }

        result = CONFLICT;
        goto end;
      }

      if (debug_division)
      {
        log << "intermediate" << endl;
        log << "a:[" << *minTop << "," << *maxTop << "]";
        log << " / b:[" << *minBottom << "," << *maxBottom << "] = ";
        log << "[" << *minQuotient << "," << *maxQuotient << "]";
        log << endl;
      }
      iteration++;
      // if (iteration==2 && changed)
      // exit(1);
    }

    if (debug_division)
    {
      log << "final" << endl;
      log << "a:[" << *minTop << "," << *maxTop << "]";
      log << " / b:[" << *minBottom << "," << *maxBottom << "] = ";
      log << "[" << *minQuotient << "," << *maxQuotient << "]";
      log << endl;
    }

    {
      Result r1 = fix(a, minTop, maxTop);
      if (r1 == CHANGED)
        r1 = merge(r1, fix(a, minTop, maxTop));

      Result r2 = fix(b, minBottom, maxBottom);
      if (r2 ==
          CHANGED) // We call is a second time because it's not idepotent..
        r2 = merge(r2, fix(b, minBottom, maxBottom));

      Result r3;
      if (whatIs == QUOTIENT_IS_OUTPUT)
      {
        r3 = fix(output, minQuotient, maxQuotient);
        if (r3 == CHANGED)
          r3 = merge(r3, fix(output, minQuotient, maxQuotient));
      }
      else
        r3 = fix(output, minRemainder, maxRemainder);

      if (r1 == CONFLICT || r2 == CONFLICT || r3 == CONFLICT)
      {
        result = CONFLICT;
        goto end;
      }
      assert(result != CONFLICT);

      if (r1 == CHANGED || r2 == CHANGED || r3 == CHANGED)
        result = CHANGED;
    }

    // check that fixing bits hasn't tightened intervals. If it has we need to
    // resolve.
    if (result == CHANGED)
    {
      bool tightened = false;

      setUnsignedMinMax(output, copy, copy2);

      if (whatIs == QUOTIENT_IS_OUTPUT)
      {
        if (CONSTANTBV::BitVector_Lexicompare(minQuotient, copy) < 0 ||
            CONSTANTBV::BitVector_Lexicompare(maxQuotient, copy2) > 0)
          tightened = true;
      }
      else
      {
        if (CONSTANTBV::BitVector_Lexicompare(minRemainder, copy) < 0 ||
            CONSTANTBV::BitVector_Lexicompare(maxRemainder, copy2) > 0)
          tightened = true;
      }

      setUnsignedMinMax(b, copy, copy2);
      if (CONSTANTBV::BitVector_Lexicompare(minBottom, copy) < 0 ||
          CONSTANTBV::BitVector_Lexicompare(maxBottom, copy2) > 0)
        tightened = true;

      setUnsignedMinMax(a, copy, copy2);
      if (CONSTANTBV::BitVector_Lexicompare(minTop, copy) < 0 ||
          CONSTANTBV::BitVector_Lexicompare(maxTop, copy2) > 0)
        tightened = true;

      if (tightened)
      {
        setUnsignedMinMax(a, minTop, maxTop);
        setUnsignedMinMax(b, minBottom, maxBottom);
        if (whatIs == QUOTIENT_IS_OUTPUT)
          setUnsignedMinMax(output, minQuotient, maxQuotient);
        else
          setUnsignedMinMax(output, minRemainder, maxRemainder);

        bitEverChanged = true;
        bitJustChanged = true;
      }
    }
  }

end:
  // Destroy range variables.
  CONSTANTBV::BitVector_Destroy(minTop);
  CONSTANTBV::BitVector_Destroy(maxTop);
  CONSTANTBV::BitVector_Destroy(minBottom);
  CONSTANTBV::BitVector_Destroy(maxBottom);
  CONSTANTBV::BitVector_Destroy(minQuotient);
  CONSTANTBV::BitVector_Destroy(maxQuotient);
  CONSTANTBV::BitVector_Destroy(minRemainder);
  CONSTANTBV::BitVector_Destroy(maxRemainder);

  // Destroy helpers.
  CONSTANTBV::BitVector_Destroy(copy);
  CONSTANTBV::BitVector_Destroy(copy2);
  CONSTANTBV::BitVector_Destroy(multR);
  CONSTANTBV::BitVector_Destroy(q);
  CONSTANTBV::BitVector_Destroy(r);
  CONSTANTBV::BitVector_Destroy(one);
  CONSTANTBV::BitVector_Destroy(max);

  if (result == CONFLICT)
    return CONFLICT;

  if (bitEverChanged)
    return CHANGED;
  return result;
}

// (a/b) = q
// Solving: (a = q * b + r) AND (r < b).
Result bvUnsignedQuotientAndRemainder2(vector<FixedBits*>& children,
                                       FixedBits& output, STPMgr* bm,
                                       WhatIsOutput whatIs)
{
  assert(output.getWidth() == children[0]->getWidth());
  assert(output.getWidth() == children[1]->getWidth());
  assert(children.size() == 2);

  unsigned int newWidth = 2 * output.getWidth();
  // Create Widenend copies.
  FixedBits a(newWidth, false);
  FixedBits b(newWidth, false);

  FixedBits q(newWidth, false);
  FixedBits r(newWidth, false);

  // intermediate values.
  FixedBits times(newWidth, false);

  a.copyIn(*children[0]);
  b.copyIn(*children[1]);

  assert(!b.containsZero());

  if (whatIs == QUOTIENT_IS_OUTPUT)
    q.copyIn(output);
  else if (whatIs == REMAINDER_IS_OUTPUT)
    r.copyIn(output);
  else
    throw std::runtime_error("sdjjfas");

  // Bits are only ever fixed, so a changed count means changed bits: cheap
  // change detection for the dependency-driven loop below.
  unsigned bCount, rCount, timesCount;

  // Times and plus must not overflow.
  for (unsigned i = (unsigned)output.getWidth(); i < newWidth; i++)
  {
    // No overflow.
    times.setFixed(i, true);
    times.setValue(i, false);

    // Everything is zero extended.
    a.setFixed(i, true);
    a.setValue(i, false);
    b.setFixed(i, true);
    b.setValue(i, false);

    // Multiplication must not overflow.
    r.setFixed(i, true);
    r.setValue(i, false);
    q.setFixed(i, true);
    q.setValue(i, false);
  }

  // True bit.
  FixedBits trueBit(1, true);
  trueBit.setFixed(0, true);
  trueBit.setValue(0, true);

  Result result = NO_CHANGE;

  vector<FixedBits*> addChildren;
  addChildren.push_back(&times);
  addChildren.push_back(&r);

  vector<FixedBits*> multiplicationChildren;
  multiplicationChildren.push_back(&q);
  multiplicationChildren.push_back(&b);

  // Run the three transfer functions to a joint fixed point, but only
  // re-run one when an operand it reads has changed since it last ran:
  // each is deterministic and reaches its own fixed point, so re-running
  // it on unchanged inputs cannot add anything, and the loop still ends
  // at the same joint fixed point as re-running everything every time.
  // The multiplication at double width dominates the cost, so the skipped
  // runs (including the final all-quiet confirmation pass) matter.
  bool ltDirty = true, multDirty = true, addDirty = true;
  while (ltDirty || multDirty || addDirty)
  {
    if (debug_division)
    {
      log << "p1:" << a << "/" << b << "=" << q << "rem(" << r << ")" << endl;
      log << "times" << times << endl;
    }

    if (ltDirty)
    {
      ltDirty = false;
      rCount = r.countFixed();
      bCount = b.countFixed();
      result = bvLessThanBothWays(r, b, trueBit); // (r < b)
      if (result == CONFLICT)
        return CONFLICT;
      if (r.countFixed() != rCount)
        addDirty = true; // r feeds the addition.
      if (b.countFixed() != bCount)
        multDirty = true; // b feeds the multiplication.
    }

    if (multDirty)
    {
      multDirty = false;
      bCount = b.countFixed();
      timesCount = times.countFixed();
      result = bvMultiplyBothWays(multiplicationChildren, times, bm); // q*b
      if (result == CONFLICT)
        return CONFLICT;
      if (b.countFixed() != bCount)
        ltDirty = true; // b feeds the less-than.
      if (times.countFixed() != timesCount)
        addDirty = true; // times feeds the addition.
    }

    if (addDirty)
    {
      addDirty = false;
      rCount = r.countFixed();
      timesCount = times.countFixed();
      result = bvAddBothWays(addChildren, a); // times + r = a
      if (result == CONFLICT)
        return CONFLICT;
      if (r.countFixed() != rCount)
        ltDirty = true; // r feeds the less-than.
      if (times.countFixed() != timesCount)
        multDirty = true; // times feeds the multiplication.
    }
  }

  bool conflict = false;
  for (unsigned i = 0; i < output.getWidth(); i++)
  {
    if (whatIs == QUOTIENT_IS_OUTPUT)
      conflict |= fix(output, q, i);
    else if (whatIs == REMAINDER_IS_OUTPUT)
      conflict |= fix(output, r, i);
    else
      throw std::runtime_error("sdjjfas");

    conflict |= fix(*children[0], a, i);
    conflict |= fix(*children[1], b, i);
  }

  if (debug_division)
    cerr << endl;

  if (conflict)
    return CONFLICT;

  return NOT_IMPLEMENTED;
}

Result bvUnsignedModulusBothWays(vector<FixedBits*>& children,
                                 FixedBits& output, STPMgr* bm)
{

  Result r1 = NO_CHANGE;
  vector<FixedBits*> v;
  v.push_back(&output);
  v.push_back(children[0]);
  FixedBits truN(1, true);
  truN.setFixed(0, true);
  truN.setValue(0, true);
  r1 = bvLessThanEqualsBothWays(v, truN);

  if (children[1]->containsZero())
    return r1;

  if (debug_division)
    log << *(children[0]) << "bvmod" << *(children[1]) << "=" << output << endl;

  Result r =
      bvUnsignedQuotientAndRemainder(children, output, bm, REMAINDER_IS_OUTPUT);

  // Doesn't even do constant propagation.
  // <10>bvmod<11>=<-->
  if (r != CONFLICT && children[0]->isTotallyFixed() &&
      children[1]->isTotallyFixed() && !output.isTotallyFixed())
  {

    if (debug_division)
    {
      log << "Not even constant prop!" << *(children[0]) << "bvmod"
          << *(children[1]) << "=" << output << endl;
    }

    // assert(output.isTotallyFixed());
  }

  // bvUnsignedQuotientAndRemainder can fix bits yet report NOT_IMPLEMENTED,
  // so never let a NO_CHANGE from the comparison above win over it: the
  // propagation loop trusts NO_CHANGE and would skip rescheduling.
  return merge(r, r1);
}

Result bvUnsignedDivisionBothWays(vector<FixedBits*>& children,
                                  FixedBits& output, STPMgr* bm)
{
  Result r0 = NO_CHANGE;

  if (children[1]->containsZero())
    return r0; // TODO fix so we learn something if we might be dividing by zero..

  // Enforce that the output must be less than the numerator.
  for (int i = children[0]->getWidth() - 1; i >= 0; i--)
  {
    if (children[0]->isFixedToZero(i))
    {
      if (output.isFixedToOne(i))
        return CONFLICT;
      else if (!output.isFixed(i))
      {
        output.setFixed(i, true);
        output.setValue(i, false);
        r0 = CHANGED;
      }
    }
    else
    {
      break;
    }
  }

  Result r =
      bvUnsignedQuotientAndRemainder(children, output, bm, QUOTIENT_IS_OUTPUT);

  return merge(r0, r);
}

bool canBe(const FixedBits& b, int index, bool value)
{
  if (!b.isFixed(index))
    return true;
  else
    return (!(b.getValue(index) ^ value));
}

// This provides a way to call the process function with fewer arguments.
struct Data
{
  FixedBits& tempA;
  FixedBits& tempB;
  FixedBits& tempOutput;
  FixedBits& workingA;
  FixedBits& workingB;
  FixedBits& workingOutput;
  unsigned int signBit;

  Data(FixedBits& _tempA, FixedBits& _tempB, FixedBits& _tempOutput,
       FixedBits& _workingA, FixedBits& _workingB, FixedBits& _workingOutput)
      : tempA(_tempA), tempB(_tempB), tempOutput(_tempOutput),
        workingA(_workingA), workingB(_workingB), workingOutput(_workingOutput)
  {
    signBit = tempOutput.getWidth() - 1;
  }

  void process(bool& first)
  {
    if (first)
    {
      workingA = tempA;
      workingB = tempB;
      workingOutput = tempOutput;
    }
    else
    {
      workingA = FixedBits::meet(workingA, tempA);
      workingB = FixedBits::meet(workingB, tempB);
      workingOutput = FixedBits::meet(workingOutput, tempOutput);
    }
    first = false;
  }

  void set(const FixedBits& a, const FixedBits& b, const FixedBits& output,
           bool aTop, bool bTop)
  {
    tempA = a;
    tempB = b;
    tempOutput = output;
    tempA.setFixed(signBit, true);
    tempA.setValue(signBit, aTop);

    tempB.setFixed(signBit, true);
    tempB.setValue(signBit, bTop);
  }

  void print()
  {
    cerr << "Working: ";
    cerr << workingA << "/";
    cerr << workingB << "=";
    cerr << workingOutput << endl;

    cerr << "Temps:    ";
    cerr << tempA << "/";
    cerr << tempB << "=";
    cerr << tempOutput << endl;
  }
};

Result negate(FixedBits& input, FixedBits& output)
{
  vector<FixedBits*> negChildren;

  negChildren.push_back(&input);
  return bvUnaryMinusBothWays(negChildren, output);
}

// This is preposterously complicated. We execute four cases then take the union
// of them.
//
Result bvSignedDivisionRemainderBothWays(vector<FixedBits*>& children,
                                         FixedBits& output, STPMgr* bm,
                                         Result (*tf)(vector<FixedBits*>&,
                                                      FixedBits&, STPMgr* bm),
                                         const Operation op)
{
  assert(output.getWidth() == children[0]->getWidth());
  assert(output.getWidth() == children[1]->getWidth());
  assert(children.size() == 2);

  const FixedBits& a = *children[0];
  const FixedBits& b = *children[1];

  assert(&a != &b);

  const unsigned int inputWidth = output.getWidth();
  const unsigned int signBit = output.getWidth() - 1;

  FixedBits workingA(inputWidth, false);
  FixedBits workingB(inputWidth, false);
  FixedBits workingOutput(inputWidth, false);

  FixedBits tempA = a;
  FixedBits tempB = b;
  FixedBits tempOutput = output;

  vector<FixedBits*> tempChildren;
  tempChildren.push_back(&tempA);
  tempChildren.push_back(&tempB);
  Result r = NO_CHANGE;

  if (b.containsZero())
    return NO_CHANGE;

  Data data(tempA, tempB, tempOutput, workingA, workingB, workingOutput);

  while (true)
  {
    if (debug_division)
    {
      cerr << "start:";
      cerr << a << "/";
      cerr << b << "=";
      cerr << output << endl;
    }

    bool first = true;

    if (canBe(a, signBit, false) && canBe(b, signBit, false))
    {
      //     (bvudiv s t)
      r = NO_CHANGE;
      data.set(a, b, output, false, false);

      r = tf(tempChildren, tempOutput, bm);
      if (r != CONFLICT)
      {
        if (debug_division)
          cerr << "case A" << endl;
        data.process(first);
      }
    }

    if (canBe(a, signBit, true) && canBe(b, signBit, false))
    {
      // (bvneg (bvudiv (bvneg a) b))
      r = NO_CHANGE;
      data.set(a, b, output, true, false);

      FixedBits negA(inputWidth, false);

      vector<FixedBits*> negChildren;
      negChildren.push_back(&negA);
      r = bvUnaryMinusBothWays(negChildren, tempA); // get NegA
      // cerr << negA << " " << tempA << endl;
      assert(r != CONFLICT);

      FixedBits wO(tempOutput);

      FixedBits negOutput(inputWidth, false);
      negChildren.clear();
      negChildren.push_back(&negOutput);
      r = bvUnaryMinusBothWays(negChildren, wO);
      assert(r != CONFLICT);

      negChildren.clear();
      negChildren.push_back(&negA);
      negChildren.push_back(&tempB);

      r = tf(negChildren, negOutput, bm);
      if (r != CONFLICT)
      {
        negChildren.clear();
        negChildren.push_back(&wO);
        r = bvUnaryMinusBothWays(negChildren, negOutput);

        if (r != CONFLICT)
        {
          tempOutput = wO;

          if (r != CONFLICT)
          {
            negChildren.clear();
            negChildren.push_back(&tempA);
            // cerr << negA << " " << tempA << endl;
            r = bvUnaryMinusBothWays(negChildren, negA);
            // data.print();
            if (r != CONFLICT)
            {

              if (debug_division)
                cerr << "case B" << endl;

              data.process(first);
            }
          }
        }
      }
    }

    if (canBe(a, signBit, false) && canBe(b, signBit, true))
    {
      // (bvneg (bvudiv a (bvneg b)))
      r = NO_CHANGE;
      data.set(a, b, output, false, true);

      FixedBits negB(inputWidth, false);
      // FixedBits negA(inputWidth, false);

      vector<FixedBits*> negChildren;
      negChildren.push_back(&negB);
      r = bvUnaryMinusBothWays(negChildren, tempB); // get NegB
      assert(r != CONFLICT);

      // Create a negated version of the output if necessary. The remainder
      // isn't negated. The division is.
      FixedBits wO(inputWidth, false);
      if (op == SIGNED_DIVISION)
      {
        r = negate(tempOutput, wO);
        assert(r != CONFLICT);
      }
      else if (op == SIGNED_REMAINDER)
        wO = tempOutput;

      negChildren.clear();
      negChildren.push_back(&tempA);
      negChildren.push_back(&negB);

      r = tf(negChildren, wO, bm);
      if (r != CONFLICT)
      {
        FixedBits t(wO);

        if (r != CONFLICT)
        {
          if (op == SIGNED_DIVISION)
          {
            r = negate(tempOutput, t);
          }
          else if (op == SIGNED_REMAINDER)
          {
            tempOutput = t;
          }

          if (r != CONFLICT)
          {
            negChildren.clear();
            negChildren.push_back(&tempB);
            r = bvUnaryMinusBothWays(negChildren, negB);
            if (r != CONFLICT)
            {
              if (debug_division)
                cerr << "case C" << endl;

              data.process(first);
            }
          }
        }
      }
    }

    if (canBe(a, signBit, true) && canBe(b, signBit, true))
    {
      //   (bvudiv (bvneg a) (bvneg b)))))))
      r = NO_CHANGE;
      data.set(a, b, output, true, true);

      FixedBits negA(inputWidth, false);
      FixedBits negB(inputWidth, false);

      vector<FixedBits*> negChildren;
      negChildren.push_back(&negA);
      r = bvUnaryMinusBothWays(negChildren, tempA); // get NegA
      assert(r != CONFLICT);

      negChildren.clear();
      negChildren.push_back(&negB);
      r = bvUnaryMinusBothWays(negChildren, tempB); // get NegB
      assert(r != CONFLICT);

      negChildren.clear();
      negChildren.push_back(&negA);
      negChildren.push_back(&negB);

      FixedBits wO(inputWidth, false);
      if (op == SIGNED_REMAINDER)
      {
        r = negate(tempOutput, wO);
        assert(r != CONFLICT);
      }
      else if (op == SIGNED_DIVISION)
        wO = tempOutput;

      r = tf(negChildren, wO, bm);
      if (r != CONFLICT)
      {
        negChildren.clear();
        negChildren.push_back(&tempB);
        r = bvUnaryMinusBothWays(negChildren, negB);

        if (r != CONFLICT)
        {
          negChildren.clear();
          negChildren.push_back(&tempA);
          r = bvUnaryMinusBothWays(negChildren, negA);
          // data.print();
          if (r != CONFLICT)
          {
            if (op == SIGNED_REMAINDER)
            {
              r = negate(tempOutput, wO);
            }
            else if (op == SIGNED_DIVISION)
              tempOutput = wO;

            if (r != CONFLICT)
            {
              if (debug_division)
                cerr << "case D" << endl;

              data.process(first);
            }
          }
        }
      }
    }

    if (first)
      return CONFLICT; // All are conflicts.

    // The results be subsets of the originals.
    assert(FixedBits::in(workingA, *children[0]));
    assert(FixedBits::in(workingB, *children[1]));
    assert(FixedBits::in(workingOutput, output));

    if (FixedBits::equals(a, workingA) && FixedBits::equals(b, workingB) &&
        FixedBits::equals(output, workingOutput))
      break;
    else
    {
      *children[0] = workingA;
      *children[1] = workingB;
      output = workingOutput;
    }
  }

  return NOT_IMPLEMENTED;
}

// --- Signed modulus ---------------------------------------------------
//
// bvsmod, per the current SMT-LIB definition:
//
//   (bvsmod s t) abbreviates
//     (let ((?msb_s ((_ extract |m-1| |m-1|) s))
//           (?msb_t ((_ extract |m-1| |m-1|) t)))
//       (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
//             (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
//         (let ((u (bvurem abs_s abs_t)))
//           (ite (= u (_ bv0 m)) u
//           (ite (and (= ?msb_s #b0) (= ?msb_t #b0)) u
//           (ite (and (= ?msb_s #b1) (= ?msb_t #b0)) (bvadd (bvneg u) t)
//           (ite (and (= ?msb_s #b0) (= ?msb_t #b1)) (bvadd u t)
//           (bvneg u))))))))
//
// Note the (= u 0) guard. The earlier SMT-LIB definition lacked it, giving
// the wrong answer whenever the remainder is zero, and the previous
// implementation here modelled that earlier definition; it was unsound
// against the constant evaluator, quite apart from being slow.
//
// So: bvsmod s 0 = s, and otherwise the result is either zero or takes the
// sign of the divisor, with |result| < |divisor|.

// Fix bit i of x to v. Returns false if that contradicts an existing fixing.
static bool fixBitTo(FixedBits& x, unsigned i, bool v)
{
  if (x.isFixed(i))
    return x.getValue(i) == v;
  x.setFixed(i, true);
  x.setValue(i, v);
  return true;
}

static bool canBeAllZero(const FixedBits& x)
{
  for (unsigned i = 0; i < x.getWidth(); i++)
    if (x.isFixedToOne(i))
      return false;
  return true;
}

// O(width) structural rules; these run even when the divisor may be zero.
static Result bvSignedModulusStructural(vector<FixedBits*>& children,
                                        FixedBits& output, STPMgr* bm)
{
  FixedBits& a = *children[0];
  FixedBits& b = *children[1];
  const unsigned width = output.getWidth();
  const unsigned sign = width - 1;

  const unsigned before =
      a.countFixed() + b.countFixed() + output.countFixed();

  // Both inputs known: evaluate.
  if (a.isTotallyFixed() && b.isTotallyFixed())
  {
    stp::ASTVec c;
    c.push_back(bm->CreateBVConst(a.GetBVConst(), width));
    c.push_back(bm->CreateBVConst(b.GetBVConst(), width));
    const FixedBits result = FixedBits::concreteToAbstract(
        NonMemberBVConstEvaluator(bm, stp::SBVMOD, c, width));
    for (unsigned i = 0; i < width; i++)
      if (!fixBitTo(output, i, result.getValue(i)))
        return CONFLICT;
    return output.countFixed() + a.countFixed() + b.countFixed() == before
               ? NO_CHANGE
               : CHANGED;
  }

  // Divisor fixed to 1 or -1: the result is zero.
  if (b.isTotallyFixed())
  {
    bool isOne = b.getValue(0);
    bool isMinusOne = b.getValue(0);
    for (unsigned i = 1; i < width; i++)
    {
      isOne = isOne && !b.getValue(i);
      isMinusOne = isMinusOne && b.getValue(i);
    }
    if (isOne || isMinusOne)
      for (unsigned i = 0; i < width; i++)
        if (!fixBitTo(output, i, false))
          return CONFLICT;
  }

  // Divisor positive: 0 <= result < divisor.
  if (b.isFixedToZero(sign) && !b.containsZero())
  {
    if (!fixBitTo(output, sign, false))
      return CONFLICT;
    int highest = -1; // highest divisor bit that might be one.
    for (int i = (int)sign - 1; i >= 0; i--)
      if (!b.isFixedToZero(i))
      {
        highest = i;
        break;
      }
    assert(highest >= 0); // b is non-zero with a zero sign bit.
    // divisor <= 2^(highest+1)-1, so result <= 2^(highest+1)-2: the bits
    // above `highest` are zero.
    for (unsigned i = highest + 1; i < sign; i++)
      if (!fixBitTo(output, i, false))
        return CONFLICT;
  }

  // Divisor's sign is zero but it may be zero. If the numerator is also
  // non-negative, the result is non-negative in both cases
  // (bvsmod s 0 = s).
  if (b.isFixedToZero(sign) && b.containsZero() && a.isFixedToZero(sign))
    if (!fixBitTo(output, sign, false))
      return CONFLICT;

  // Divisor negative: the result is in (divisor, 0], so zero or negative.
  if (b.isFixedToOne(sign))
  {
    if (output.isFixedToZero(sign))
    {
      // A non-negative result must be zero.
      for (unsigned i = 0; i < width; i++)
        if (!fixBitTo(output, i, false))
          return CONFLICT;
    }
    else
    {
      bool nonZero = false;
      for (unsigned i = 0; i < sign; i++)
        if (output.isFixedToOne(i))
          nonZero = true;
      if (nonZero && !fixBitTo(output, sign, true))
        return CONFLICT;
    }
  }

  // Result negative: the divisor is negative, or zero with a negative
  // numerator.
  if (output.isFixedToOne(sign))
  {
    if (!b.containsZero())
    {
      if (!fixBitTo(b, sign, true))
        return CONFLICT;
    }
    else if (b.isFixedToZero(sign))
    {
      // The divisor must be zero, and then result == numerator.
      for (unsigned i = 0; i < width; i++)
        if (!fixBitTo(b, i, false))
          return CONFLICT;
      for (unsigned i = 0; i < width; i++)
      {
        if (a.isFixed(i) && !fixBitTo(output, i, a.getValue(i)))
          return CONFLICT;
        if (output.isFixed(i) && !fixBitTo(a, i, output.getValue(i)))
          return CONFLICT;
      }
    }
  }

  const unsigned after =
      a.countFixed() + b.countFixed() + output.countFixed();
  return after == before ? NO_CHANGE : CHANGED;
}

// The union, across the sign cases, of the propagated values.
namespace
{
struct SmodUnion
{
  bool any;
  FixedBits a, b, o;
  SmodUnion(unsigned w) : any(false), a(w, false), b(w, false), o(w, false) {}
  void add(const FixedBits& a_, const FixedBits& b_, const FixedBits& o_)
  {
    if (!any)
    {
      a = a_;
      b = b_;
      o = o_;
    }
    else
    {
      a = FixedBits::meet(a, a_);
      b = FixedBits::meet(b, b_);
      o = FixedBits::meet(o, o_);
    }
    any = true;
  }
};
}

static Result uremProp(FixedBits& x, FixedBits& y, FixedBits& out, STPMgr* bm)
{
  vector<FixedBits*> ch;
  ch.push_back(&x);
  ch.push_back(&y);
  return bvUnsignedModulusBothWays(ch, out, bm);
}

static Result addProp(FixedBits& x, FixedBits& y, FixedBits& out)
{
  vector<FixedBits*> ch;
  ch.push_back(&x);
  ch.push_back(&y);
  return bvAddBothWays(ch, out);
}

// One pass over the four sign cases of the SMT-LIB definition. Each
// feasible case is propagated through its bvurem/bvneg/bvadd pipeline, and
// the union of the surviving cases refines the operands. The (= u 0)
// branch of the definition is a separate sub-case where it matters.
// A zero divisor is handled correctly (bvurem x 0 = x makes the two
// t >= 0 pipelines evaluate to s when t == 0), so the caller's
// containsZero() early-out is purely on cost grounds.
static Result bvSignedModulusDecompose(vector<FixedBits*>& children,
                                       FixedBits& output, STPMgr* bm)
{
  FixedBits& a = *children[0];
  FixedBits& b = *children[1];
  const unsigned width = output.getWidth();
  const unsigned sign = width - 1;

  const unsigned before =
      a.countFixed() + b.countFixed() + output.countFixed();

  SmodUnion un(width);

  // Case (s >= 0, t >= 0): result = bvurem(s, t), non-negative.
  if (canBe(a, sign, false) && canBe(b, sign, false) &&
      canBe(output, sign, false))
  {
    FixedBits A(a), B(b), O(output);
    A.setFixed(sign, true);
    A.setValue(sign, false);
    B.setFixed(sign, true);
    B.setValue(sign, false);
    O.setFixed(sign, true);
    O.setValue(sign, false);
    if (CONFLICT != uremProp(A, B, O, bm))
      un.add(A, B, O);
  }

  // Case (s < 0, t < 0): u = bvurem(-s, -t); result = -u.
  // (-0 == 0, so the u == 0 guard changes nothing.) u < |t| <= 2^(w-1),
  // so u's sign bit is zero.
  if (canBe(a, sign, true) && canBe(b, sign, true))
  {
    FixedBits A(a), B(b), O(output);
    A.setFixed(sign, true);
    A.setValue(sign, true);
    B.setFixed(sign, true);
    B.setValue(sign, true);
    FixedBits negA(width, false), negB(width, false), u(width, false);
    u.setFixed(sign, true);
    u.setValue(sign, false);
    const bool ok = CONFLICT != negate(A, negA) &&
                    CONFLICT != negate(B, negB) &&
                    CONFLICT != negate(O, u) && // u = -O <=> O = -u
                    CONFLICT != uremProp(negA, negB, u, bm) &&
                    CONFLICT != negate(O, u) && // push refinements back out
                    CONFLICT != negate(A, negA) && CONFLICT != negate(B, negB);
    if (ok)
      un.add(A, B, O);
  }

  // Case (s < 0, t >= 0): u = bvurem(-s, t); result = 0 if u == 0
  // else t - u.
  if (canBe(a, sign, true) && canBe(b, sign, false))
  {
    // Sub-case u == 0: the result is zero.
    if (canBeAllZero(output))
    {
      FixedBits A(a), B(b);
      A.setFixed(sign, true);
      A.setValue(sign, true);
      B.setFixed(sign, true);
      B.setValue(sign, false);
      FixedBits negA(width, false);
      FixedBits zero(width, false);
      zero.fixToZero();
      const bool ok = CONFLICT != negate(A, negA) &&
                      CONFLICT != uremProp(negA, B, zero, bm) &&
                      CONFLICT != negate(A, negA);
      if (ok)
      {
        FixedBits O(output);
        O.fixToZero();
        un.add(A, B, O);
      }
    }
    // Sub-case u != 0: result = t - u. Leaving u unconstrained is a sound
    // over-approximation. If t cannot be zero the result here is
    // non-negative (u != 0, t > 0 gives a result in (0, t)).
    {
      FixedBits A(a), B(b), O(output);
      A.setFixed(sign, true);
      A.setValue(sign, true);
      B.setFixed(sign, true);
      B.setValue(sign, false);
      bool feasible = true;
      if (!B.containsZero())
        feasible = fixBitTo(O, sign, false);
      if (feasible)
      {
        FixedBits negA(width, false), u(width, false), negU(width, false);
        const bool ok = CONFLICT != negate(A, negA) &&
                        CONFLICT != addProp(negU, B, O) && // backward
                        CONFLICT != negate(u, negU) &&     // negU = -u
                        CONFLICT != uremProp(negA, B, u, bm) &&
                        CONFLICT != negate(u, negU) &&
                        CONFLICT != addProp(negU, B, O) &&
                        CONFLICT != negate(A, negA);
        if (ok)
          un.add(A, B, O);
      }
    }
  }

  // Case (s >= 0, t < 0): u = bvurem(s, -t); result = 0 if u == 0
  // else u + t.
  if (canBe(a, sign, false) && canBe(b, sign, true))
  {
    // Sub-case u == 0: the result is zero.
    if (canBeAllZero(output))
    {
      FixedBits A(a), B(b);
      A.setFixed(sign, true);
      A.setValue(sign, false);
      B.setFixed(sign, true);
      B.setValue(sign, true);
      FixedBits negB(width, false);
      FixedBits zero(width, false);
      zero.fixToZero();
      const bool ok = CONFLICT != negate(B, negB) &&
                      CONFLICT != uremProp(A, negB, zero, bm) &&
                      CONFLICT != negate(B, negB);
      if (ok)
      {
        FixedBits O(output);
        O.fixToZero();
        un.add(A, B, O);
      }
    }
    // Sub-case u != 0: result = u + t, strictly negative
    // (u in (0, -t) gives a result in (t, 0)).
    {
      FixedBits A(a), B(b), O(output);
      A.setFixed(sign, true);
      A.setValue(sign, false);
      B.setFixed(sign, true);
      B.setValue(sign, true);
      if (fixBitTo(O, sign, true))
      {
        FixedBits negB(width, false), u(width, false);
        u.setFixed(sign, true);
        u.setValue(sign, false); // u < |t| <= 2^(w-1)
        const bool ok = CONFLICT != negate(B, negB) &&
                        CONFLICT != addProp(u, B, O) && // backward into u
                        CONFLICT != uremProp(A, negB, u, bm) &&
                        CONFLICT != addProp(u, B, O) &&
                        CONFLICT != negate(B, negB);
        if (ok)
          un.add(A, B, O);
      }
    }
  }

  if (!un.any)
    return CONFLICT;

  // The union must be a refinement of the inputs.
  assert(FixedBits::in(un.a, a));
  assert(FixedBits::in(un.b, b));
  assert(FixedBits::in(un.o, output));

  a = un.a;
  b = un.b;
  output = un.o;

  const unsigned after =
      a.countFixed() + b.countFixed() + output.countFixed();
  return after == before ? NO_CHANGE : CHANGED;
}

Result bvSignedModulusBothWays(vector<FixedBits*>& children, FixedBits& output,
                               STPMgr* bm)
{
  assert(children.size() == 2);
  assert(output.getWidth() == children[0]->getWidth());
  assert(output.getWidth() == children[1]->getWidth());

  if (children[0] == children[1]) // same pointer: x smod x = 0.
  {
    Result r = NO_CHANGE;
    for (unsigned i = 0; i < output.getWidth(); i++)
    {
      if (output.isFixedToOne(i))
        return CONFLICT;
      if (!output.isFixed(i))
      {
        output.setFixed(i, true);
        output.setValue(i, false);
        r = CHANGED;
      }
    }
    return r;
  }

  const Result r0 = bvSignedModulusStructural(children, output, bm);
  if (CONFLICT == r0)
    return CONFLICT;

  // The sign-case decomposition is expensive and deduces little when the
  // divisor may be zero; bail out early like the other signed operations.
  if (children[1]->containsZero())
    return r0;

  const Result r1 = bvSignedModulusDecompose(children, output, bm);
  if (CONFLICT == r1)
    return CONFLICT;
  return merge(r0, r1);
}

Result bvSignedRemainderBothWays(vector<FixedBits*>& children,
                                 FixedBits& output, STPMgr* bm)
{
  /*
   (bvsrem s t) abbreviates
   (let (?msb_s (extract[|m-1|:|m-1|] s))
   (let (?msb_t (extract[|m-1|:|m-1|] t))
   (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
   (bvurem s t)
   (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
   (bvneg (bvurem (bvneg s) t))
   (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
   (bvurem s (bvneg t)))
   (bvneg (bvurem (bvneg s) (bvneg t)))))))
   */

  if (children[0] == children[1]) // same pointer.
  {
    return NO_CHANGE;
  }

  return bvSignedDivisionRemainderBothWays(
      children, output, bm, bvUnsignedModulusBothWays, SIGNED_REMAINDER);
}

Result bvSignedDivisionBothWays(vector<FixedBits*>& children, FixedBits& output,
                                STPMgr* bm)
{
  /*
   * (bvsdiv s t) abbreviates
   (let (?msb_s (extract[|m-1|:|m-1|] s))
   (let (?msb_t (extract[|m-1|:|m-1|] t))
   (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
   (bvudiv s t)
   (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
   (bvneg (bvudiv (bvneg s) t))
   (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
   (bvneg (bvudiv s (bvneg t)))
   (bvudiv (bvneg s) (bvneg t)))))))
   *
   */

  if (children[0] == children[1]) // same pointer.
  {
    return NO_CHANGE;
  }

  // unsigned division propagates much better than signed division does!
  const int top = children[0]->getWidth();
  if ((*children[0])[top - 1] == '0' && (*children[1])[top - 1] == '0')
    return bvUnsignedDivisionBothWays(children, output, bm);
  else
    return bvSignedDivisionRemainderBothWays(
        children, output, bm, bvUnsignedDivisionBothWays, SIGNED_DIVISION);
}
}
}

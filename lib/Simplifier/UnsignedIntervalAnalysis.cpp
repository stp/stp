/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Februrary, 2011
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

/*
 * Performs a basic unsigned interval analysis.
 * The analysis is only bottom up (without assuming that the root node is true).
 * Some of the transfer functions are approximations (they're marked with comments).
 */

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/StrengthReduction.h"
#include <iostream>
#include <map>

using std::map;

namespace stp
{

  using NodeToUnsignedIntervalMap = std::unordered_map<const ASTNode, UnsignedInterval*, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>;

  void UnsignedIntervalAnalysis::stats()
  {
    std::cerr << "{UnsignedIntervalAnalysis} TODO propagator not implemented: "
              << propagatorNotImplemented << std::endl;
    std::cerr << "{UnsignedIntervalAnalysis} Iterations: " << iterations
              << std::endl;
  }

  using std::make_pair;

  namespace
  {
    // Reads a shift amount, capped at the width. Shifting by the width or
    // more discards (or sign-fills) everything, so larger amounts behave the
    // same as shifting by the width.
    unsigned cappedShiftAmount(const CBV shift, unsigned width)
    {
      // Set_Max is the index of the highest set bit (negative if none).
      if (CONSTANTBV::Set_Max(shift) >= (signed long)(8 * sizeof(unsigned)))
        return width; // Too big to read out, so certainly >= the width.

      const unsigned amount = *shift; // The value fits into the first word.
      return std::min(amount, width);
    }

    // Sets bit i and clears the bits below it: (x | 2^i) & -(2^i).
    void setBitClearBelow(CBV x, unsigned i)
    {
      CONSTANTBV::BitVector_Bit_On(x, i);
      for (unsigned j = 0; j < i; j++)
        CONSTANTBV::BitVector_Bit_Off(x, j);
    }

    // Clears bit i and sets the bits below it: (x - 2^i) | (2^i - 1).
    void clearBitSetBelow(CBV x, unsigned i)
    {
      CONSTANTBV::BitVector_Bit_Off(x, i);
      for (unsigned j = 0; j < i; j++)
        CONSTANTBV::BitVector_Bit_On(x, j);
    }

    // The six functions below are from section 4-3 of Hacker's Delight.
    // Each gives the exact bound of a bitwise operation over the intervals
    // x in [a, b] and y in [c, d]. The caller owns the returned bitvector.

    // The smallest x | y.
    CBV minOR(const CBV a0, const CBV b, const CBV c0, const CBV d)
    {
      CBV a = CONSTANTBV::BitVector_Clone(a0);
      CBV c = CONSTANTBV::BitVector_Clone(c0);

      for (unsigned i = bits_(a); i-- > 0;)
      {
        const bool aBit = CONSTANTBV::BitVector_bit_test(a, i);
        const bool cBit = CONSTANTBV::BitVector_bit_test(c, i);

        if (!aBit && cBit)
        {
          // Raising a to supply this bit lets everything below it be zero.
          CBV temp = CONSTANTBV::BitVector_Clone(a);
          setBitClearBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, b) <= 0)
          {
            CONSTANTBV::BitVector_Destroy(a);
            a = temp;
            break;
          }
          CONSTANTBV::BitVector_Destroy(temp);
        }
        else if (aBit && !cBit)
        {
          CBV temp = CONSTANTBV::BitVector_Clone(c);
          setBitClearBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, d) <= 0)
          {
            CONSTANTBV::BitVector_Destroy(c);
            c = temp;
            break;
          }
          CONSTANTBV::BitVector_Destroy(temp);
        }
      }

      CBV result = CONSTANTBV::BitVector_Create(bits_(a), true);
      CONSTANTBV::Set_Union(result, a, c);
      CONSTANTBV::BitVector_Destroy(a);
      CONSTANTBV::BitVector_Destroy(c);
      return result;
    }

    // The biggest x | y.
    CBV maxOR(const CBV a, const CBV b0, const CBV c, const CBV d0)
    {
      CBV b = CONSTANTBV::BitVector_Clone(b0);
      CBV d = CONSTANTBV::BitVector_Clone(d0);

      for (unsigned i = bits_(b); i-- > 0;)
      {
        if (CONSTANTBV::BitVector_bit_test(b, i) &&
            CONSTANTBV::BitVector_bit_test(d, i))
        {
          // One operand can donate this bit; lowering the other one sets
          // every bit below it.
          CBV temp = CONSTANTBV::BitVector_Clone(b);
          clearBitSetBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, a) >= 0)
          {
            CONSTANTBV::BitVector_Destroy(b);
            b = temp;
            break;
          }
          CONSTANTBV::BitVector_Destroy(temp);

          temp = CONSTANTBV::BitVector_Clone(d);
          clearBitSetBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, c) >= 0)
          {
            CONSTANTBV::BitVector_Destroy(d);
            d = temp;
            break;
          }
          CONSTANTBV::BitVector_Destroy(temp);
        }
      }

      CBV result = CONSTANTBV::BitVector_Create(bits_(b), true);
      CONSTANTBV::Set_Union(result, b, d);
      CONSTANTBV::BitVector_Destroy(b);
      CONSTANTBV::BitVector_Destroy(d);
      return result;
    }

    // The smallest x & y.
    CBV minAND(const CBV a0, const CBV b, const CBV c0, const CBV d)
    {
      CBV a = CONSTANTBV::BitVector_Clone(a0);
      CBV c = CONSTANTBV::BitVector_Clone(c0);

      for (unsigned i = bits_(a); i-- > 0;)
      {
        if (!CONSTANTBV::BitVector_bit_test(a, i) &&
            !CONSTANTBV::BitVector_bit_test(c, i))
        {
          // The bit is zero in both minimums, so it is zero in the result;
          // raising one minimum past it lets everything below be zero.
          CBV temp = CONSTANTBV::BitVector_Clone(a);
          setBitClearBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, b) <= 0)
          {
            CONSTANTBV::BitVector_Destroy(a);
            a = temp;
            break;
          }
          CONSTANTBV::BitVector_Destroy(temp);

          temp = CONSTANTBV::BitVector_Clone(c);
          setBitClearBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, d) <= 0)
          {
            CONSTANTBV::BitVector_Destroy(c);
            c = temp;
            break;
          }
          CONSTANTBV::BitVector_Destroy(temp);
        }
      }

      CBV result = CONSTANTBV::BitVector_Create(bits_(a), true);
      CONSTANTBV::Set_Intersection(result, a, c);
      CONSTANTBV::BitVector_Destroy(a);
      CONSTANTBV::BitVector_Destroy(c);
      return result;
    }

    // The biggest x & y.
    CBV maxAND(const CBV a, const CBV b0, const CBV c, const CBV d0)
    {
      CBV b = CONSTANTBV::BitVector_Clone(b0);
      CBV d = CONSTANTBV::BitVector_Clone(d0);

      for (unsigned i = bits_(b); i-- > 0;)
      {
        const bool bBit = CONSTANTBV::BitVector_bit_test(b, i);
        const bool dBit = CONSTANTBV::BitVector_bit_test(d, i);

        if (bBit && !dBit)
        {
          // The bit can't survive the AND; giving it up sets every bit
          // below it.
          CBV temp = CONSTANTBV::BitVector_Clone(b);
          clearBitSetBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, a) >= 0)
          {
            CONSTANTBV::BitVector_Destroy(b);
            b = temp;
            break;
          }
          CONSTANTBV::BitVector_Destroy(temp);
        }
        else if (!bBit && dBit)
        {
          CBV temp = CONSTANTBV::BitVector_Clone(d);
          clearBitSetBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, c) >= 0)
          {
            CONSTANTBV::BitVector_Destroy(d);
            d = temp;
            break;
          }
          CONSTANTBV::BitVector_Destroy(temp);
        }
      }

      CBV result = CONSTANTBV::BitVector_Create(bits_(b), true);
      CONSTANTBV::Set_Intersection(result, b, d);
      CONSTANTBV::BitVector_Destroy(b);
      CONSTANTBV::BitVector_Destroy(d);
      return result;
    }

    // ---- Helpers for the multiplication bounds. The bitvectors in this
    // group share one width, chosen wide enough that nothing overflows. ----

    CBV zeroOf(unsigned width)
    {
      return CONSTANTBV::BitVector_Create(width, true);
    }

    // A fresh copy of x at a bigger width.
    CBV widenTo(const CBV x, unsigned width)
    {
      assert(width >= bits_(x));
      CBV r = zeroOf(width);
      CONSTANTBV::BitVector_Interval_Copy(r, x, 0, 0, bits_(x));
      return r;
    }

    void replaceCBV(CBV& x, CBV fresh)
    {
      CONSTANTBV::BitVector_Destroy(x);
      x = fresh;
    }

    CBV addFresh(const CBV x, const CBV y)
    {
      CBV r = zeroOf(bits_(x));
      bool carry = false;
      CONSTANTBV::BitVector_add(r, x, y, &carry);
      assert(!carry);
      return r;
    }

    // x - y, requiring x >= y.
    CBV subFresh(const CBV x, const CBV y)
    {
      assert(CONSTANTBV::BitVector_Lexicompare(x, y) >= 0);
      CBV r = zeroOf(bits_(x));
      bool carry = false;
      CONSTANTBV::BitVector_sub(r, x, y, &carry);
      return r;
    }

    CBV mulFresh(const CBV x, const CBV y)
    {
      CBV r = zeroOf(bits_(x));
      CBV tmp = CONSTANTBV::BitVector_Clone(x); // Mul_Pos destroys this one.
      CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Mul_Pos(r, tmp, y, true);
      assert(0 == e);
      CONSTANTBV::BitVector_Destroy(tmp);
      return r;
    }

    // Fresh quotient and remainder of x / y; y >= 1.
    void divmodFresh(const CBV x, const CBV y, CBV& quotient, CBV& remainder)
    {
      quotient = zeroOf(bits_(x));
      remainder = zeroOf(bits_(x));
      CBV tmp = CONSTANTBV::BitVector_Clone(x); // Div_Pos destroys this one.
      CONSTANTBV::ErrCode e =
          CONSTANTBV::BitVector_Div_Pos(quotient, tmp, y, remainder);
      assert(0 == e);
      CONSTANTBV::BitVector_Destroy(tmp);
    }

    // The sum over 0 <= i < n of floor((a*i + b) / m); m >= 1. This is the
    // AtCoder Library's floor_sum. The shared width must be big enough
    // that a*n + b and the sum can't overflow.
    CBV floorSum(const CBV n0, const CBV m0, const CBV a0, const CBV b0)
    {
      const unsigned width = bits_(n0);
      CBV n = CONSTANTBV::BitVector_Clone(n0);
      CBV m = CONSTANTBV::BitVector_Clone(m0);
      CBV a = CONSTANTBV::BitVector_Clone(a0);
      CBV b = CONSTANTBV::BitVector_Clone(b0);
      CBV ans = zeroOf(width);
      CBV one = zeroOf(width);
      CONSTANTBV::BitVector_increment(one);

      while (true)
      {
        if (CONSTANTBV::BitVector_Lexicompare(a, m) >= 0)
        {
          CBV q, r;
          divmodFresh(a, m, q, r);
          // ans += n * (n - 1) / 2 * q
          CBV t = subFresh(n, one);
          replaceCBV(t, mulFresh(n, t));
          CONSTANTBV::BitVector_shift_right(t, 0); // n*(n-1) is even.
          replaceCBV(t, mulFresh(t, q));
          replaceCBV(ans, addFresh(ans, t));
          CONSTANTBV::BitVector_Destroy(t);
          CONSTANTBV::BitVector_Destroy(q);
          replaceCBV(a, r);
        }

        if (CONSTANTBV::BitVector_Lexicompare(b, m) >= 0)
        {
          CBV q, r;
          divmodFresh(b, m, q, r);
          CBV t = mulFresh(n, q);
          replaceCBV(ans, addFresh(ans, t));
          CONSTANTBV::BitVector_Destroy(t);
          CONSTANTBV::BitVector_Destroy(q);
          replaceCBV(b, r);
        }

        CBV y = mulFresh(a, n);
        replaceCBV(y, addFresh(y, b));
        if (CONSTANTBV::BitVector_Lexicompare(y, m) < 0)
        {
          CONSTANTBV::BitVector_Destroy(y);
          break;
        }

        CBV q, r;
        divmodFresh(y, m, q, r);
        CONSTANTBV::BitVector_Destroy(y);
        replaceCBV(n, q);
        replaceCBV(b, r);
        std::swap(m, a);
      }

      CONSTANTBV::BitVector_Destroy(n);
      CONSTANTBV::BitVector_Destroy(m);
      CONSTANTBV::BitVector_Destroy(a);
      CONSTANTBV::BitVector_Destroy(b);
      CONSTANTBV::BitVector_Destroy(one);
      return ans;
    }

    // How many i in [0, n) have (a*i + b) mod m <= x. floor(t/m) minus
    // floor((t - x - 1)/m) is one exactly when t mod m <= x; when the
    // shifted offset would be negative, a multiple of m is added and the
    // total corrected by n. 'total' is floorSum(n, m, a, b), precomputed
    // because it doesn't change across a binary search.
    CBV countAtMost(const CBV x, const CBV total, const CBV n, const CBV m,
                    const CBV a, const CBV b)
    {
      CBV count = CONSTANTBV::BitVector_Clone(total);

      CBV xPlus1 = CONSTANTBV::BitVector_Clone(x);
      CONSTANTBV::BitVector_increment(xPlus1);

      CBV shifted;
      if (CONSTANTBV::BitVector_Lexicompare(b, xPlus1) >= 0)
        shifted = subFresh(b, xPlus1);
      else
      {
        shifted = addFresh(b, m);
        replaceCBV(shifted, subFresh(shifted, xPlus1));
        replaceCBV(count, addFresh(count, n));
      }

      CBV fewer = floorSum(n, m, a, shifted);
      replaceCBV(count, subFresh(count, fewer));

      CONSTANTBV::BitVector_Destroy(fewer);
      CONSTANTBV::BitVector_Destroy(shifted);
      CONSTANTBV::BitVector_Destroy(xPlus1);
      return count;
    }

    // The minimum (or maximum) of (a*i + b) mod m over 0 <= i < n: the
    // smallest x whose count reaches one (or reaches n), found by binary
    // search on the counting function.
    CBV progressionBound(bool wantMaximum, const CBV n, const CBV m,
                         const CBV a, const CBV b)
    {
      const unsigned width = bits_(n);
      CBV total = floorSum(n, m, a, b);

      CBV lo = zeroOf(width);
      CBV hi = CONSTANTBV::BitVector_Clone(m);
      CONSTANTBV::BitVector_decrement(hi);

      while (CONSTANTBV::BitVector_Lexicompare(lo, hi) < 0)
      {
        CBV mid = addFresh(lo, hi);
        CONSTANTBV::BitVector_shift_right(mid, 0);

        CBV count = countAtMost(mid, total, n, m, a, b);
        const bool enough =
            wantMaximum ? (CONSTANTBV::BitVector_Lexicompare(count, n) >= 0)
                        : !CONSTANTBV::BitVector_is_empty(count);
        CONSTANTBV::BitVector_Destroy(count);

        if (enough)
          replaceCBV(hi, mid);
        else
        {
          CONSTANTBV::BitVector_increment(mid);
          replaceCBV(lo, mid);
        }
      }

      CONSTANTBV::BitVector_Destroy(hi);
      CONSTANTBV::BitVector_Destroy(total);
      return lo;
    }

    // The progression search runs a binary search full of divisions, so
    // it's only worth it at the widths solvers commonly use.
    const unsigned progressionWidthLimit = 64;

    // The bounds of x*y (mod 2^width) with x in [a, b] and y in [c, d],
    // written into resultMin/resultMax; both stay null if nothing is
    // known. Exact when the bound products land in the same 2^width block,
    // and when one operand is constant (below the width limit).
    void multiplyPair(const CBV a, const CBV b, const CBV c, const CBV d,
                      unsigned width, CBV& resultMin, CBV& resultMax)
    {
      resultMin = nullptr;
      resultMax = nullptr;

      // Wide enough for the products and everything inside floorSum.
      const unsigned wide = 3 * width + 4;

      CBV aW = widenTo(a, wide);
      CBV bW = widenTo(b, wide);
      CBV cW = widenTo(c, wide);
      CBV dW = widenTo(d, wide);

      CBV lowProduct = mulFresh(aW, cW);
      CBV highProduct = mulFresh(bW, dW);

      bool sameBlock = true;
      for (unsigned i = width; i < wide && sameBlock; i++)
        if (CONSTANTBV::BitVector_bit_test(lowProduct, i) !=
            CONSTANTBV::BitVector_bit_test(highProduct, i))
          sameBlock = false;

      if (sameBlock)
      {
        // Every product sits between the bound products, which agree above
        // the width, so the low bits run between the bounds' low bits
        // without wrapping: exact.
        resultMin = zeroOf(width);
        resultMax = zeroOf(width);
        for (unsigned i = 0; i < width; i++)
        {
          if (CONSTANTBV::BitVector_bit_test(lowProduct, i))
            CONSTANTBV::BitVector_Bit_On(resultMin, i);
          if (CONSTANTBV::BitVector_bit_test(highProduct, i))
            CONSTANTBV::BitVector_Bit_On(resultMax, i);
        }
      }
      else
      {
        const bool constantY = (CONSTANTBV::BitVector_Lexicompare(c, d) == 0);
        const bool constantX = (CONSTANTBV::BitVector_Lexicompare(a, b) == 0);

        if ((constantX || constantY) && width <= progressionWidthLimit)
        {
          // With one operand constant the products are the arithmetic
          // progression a*c, a*c + step, ... mod 2^width, whose extremes
          // the progression search finds: exact.
          CBV modulus = zeroOf(wide);
          CONSTANTBV::BitVector_Bit_On(modulus, width);

          CBV count = constantY ? subFresh(bW, aW) : subFresh(dW, cW);
          CONSTANTBV::BitVector_increment(count);

          const CBV step = constantY ? cW : aW;

          CBV apMin = progressionBound(false, count, modulus, step,
                                       lowProduct);
          CBV apMax = progressionBound(true, count, modulus, step,
                                       lowProduct);

          resultMin = zeroOf(width);
          resultMax = zeroOf(width);
          for (unsigned i = 0; i < width; i++)
          {
            if (CONSTANTBV::BitVector_bit_test(apMin, i))
              CONSTANTBV::BitVector_Bit_On(resultMin, i);
            if (CONSTANTBV::BitVector_bit_test(apMax, i))
              CONSTANTBV::BitVector_Bit_On(resultMax, i);
          }

          CONSTANTBV::BitVector_Destroy(apMin);
          CONSTANTBV::BitVector_Destroy(apMax);
          CONSTANTBV::BitVector_Destroy(count);
          CONSTANTBV::BitVector_Destroy(modulus);
        }
        // Otherwise the products can wrap in ways intervals can't follow.
      }

      CONSTANTBV::BitVector_Destroy(aW);
      CONSTANTBV::BitVector_Destroy(bW);
      CONSTANTBV::BitVector_Destroy(cW);
      CONSTANTBV::BitVector_Destroy(dW);
      CONSTANTBV::BitVector_Destroy(lowProduct);
      CONSTANTBV::BitVector_Destroy(highProduct);
    }

    // The smallest x ^ y. Like minOR, but a bit supplied to cancel one in
    // the other operand keeps helping at the lower bits, so keep scanning.
    CBV minXOR(const CBV a0, const CBV b, const CBV c0, const CBV d)
    {
      CBV a = CONSTANTBV::BitVector_Clone(a0);
      CBV c = CONSTANTBV::BitVector_Clone(c0);

      for (unsigned i = bits_(a); i-- > 0;)
      {
        const bool aBit = CONSTANTBV::BitVector_bit_test(a, i);
        const bool cBit = CONSTANTBV::BitVector_bit_test(c, i);

        if (!aBit && cBit)
        {
          CBV temp = CONSTANTBV::BitVector_Clone(a);
          setBitClearBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, b) <= 0)
          {
            CONSTANTBV::BitVector_Destroy(a);
            a = temp;
          }
          else
            CONSTANTBV::BitVector_Destroy(temp);
        }
        else if (aBit && !cBit)
        {
          CBV temp = CONSTANTBV::BitVector_Clone(c);
          setBitClearBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, d) <= 0)
          {
            CONSTANTBV::BitVector_Destroy(c);
            c = temp;
          }
          else
            CONSTANTBV::BitVector_Destroy(temp);
        }
      }

      CBV result = CONSTANTBV::BitVector_Create(bits_(a), true);
      CONSTANTBV::Set_ExclusiveOr(result, a, c);
      CONSTANTBV::BitVector_Destroy(a);
      CONSTANTBV::BitVector_Destroy(c);
      return result;
    }

    // The biggest x ^ y. Like maxOR, but a shared bit cancels out, so
    // giving it up in one operand keeps helping at the lower bits.
    CBV maxXOR(const CBV a, const CBV b0, const CBV c, const CBV d0)
    {
      CBV b = CONSTANTBV::BitVector_Clone(b0);
      CBV d = CONSTANTBV::BitVector_Clone(d0);

      for (unsigned i = bits_(b); i-- > 0;)
      {
        if (CONSTANTBV::BitVector_bit_test(b, i) &&
            CONSTANTBV::BitVector_bit_test(d, i))
        {
          CBV temp = CONSTANTBV::BitVector_Clone(b);
          clearBitSetBelow(temp, i);
          if (CONSTANTBV::BitVector_Lexicompare(temp, a) >= 0)
          {
            CONSTANTBV::BitVector_Destroy(b);
            b = temp;
          }
          else
          {
            CONSTANTBV::BitVector_Destroy(temp);
            temp = CONSTANTBV::BitVector_Clone(d);
            clearBitSetBelow(temp, i);
            if (CONSTANTBV::BitVector_Lexicompare(temp, c) >= 0)
            {
              CONSTANTBV::BitVector_Destroy(d);
              d = temp;
            }
            else
              CONSTANTBV::BitVector_Destroy(temp);
          }
        }
      }

      CBV result = CONSTANTBV::BitVector_Create(bits_(b), true);
      CONSTANTBV::Set_ExclusiveOr(result, b, d);
      CONSTANTBV::BitVector_Destroy(b);
      CONSTANTBV::BitVector_Destroy(d);
      return result;
    }
  }

  UnsignedInterval* UnsignedIntervalAnalysis::freshUnsignedInterval(unsigned width)
  {
    width = std::max((unsigned)1, width);
    UnsignedInterval* it = createInterval(getEmptyCBV(width), getEmptyCBV(width));
    CONSTANTBV::BitVector_Fill(it->maxV);
    return it;
  }

  // Doesn't take ownership of the CBVs.
  // Doesn't own the returned.
  UnsignedInterval* UnsignedIntervalAnalysis::createInterval(CBV min, CBV max)
  {
    return new UnsignedInterval(CONSTANTBV::BitVector_Clone(min), CONSTANTBV::BitVector_Clone(max));
  }

  // readonly.
  CBV UnsignedIntervalAnalysis::getEmptyCBV(unsigned width)
  {
    width = std::max(width, (unsigned)1);

    if (emptyCBV.find(width) == emptyCBV.end())
    {
      emptyCBV[width] = CONSTANTBV::BitVector_Create(width, true);
    }
    
    assert(CONSTANTBV::BitVector_is_empty(emptyCBV[width]));  
    return emptyCBV[width];
  }

  //readonly
  UnsignedInterval* UnsignedIntervalAnalysis::getEmptyInterval(const ASTNode& n)
  {
    const auto width = std::max((unsigned)1,n.GetValueWidth());

    if (emptyIntervals.find(width) == emptyIntervals.end())
    {
      stp::CBV min = CONSTANTBV::BitVector_Create(width, true);
      stp::CBV max = CONSTANTBV::BitVector_Create(width, true);
      CONSTANTBV::BitVector_Fill(max);
      emptyIntervals[width] = new UnsignedInterval(min,max);
    }

    UnsignedInterval* r = emptyIntervals[width];
    assert(r->isComplete());
    return r;
  }

  // Replace some of the things that unsigned intervals can figure out for us.
  ASTNode UnsignedIntervalAnalysis::topLevel(const ASTNode& top)
  {
    propagatorNotImplemented = 0;
    iterations=0;

    bm.GetRunTimes()->start(RunTimes::IntervalPropagation);

    NodeToUnsignedIntervalMap visited;
    visit(top, visited);

    if (bm.UserFlags.stats_flag)
      stats();

    StrengthReduction sr(bm.defaultNodeFactory, &bm.UserFlags);
    ASTNode result = sr.topLevel(top, visited);

    // The intervals are only read during strength reduction, delete them now.
    for (const auto& pair : visited)
      delete pair.second;

    bm.GetRunTimes()->stop(RunTimes::IntervalPropagation);

    return result;
  }

  UnsignedInterval* UnsignedIntervalAnalysis::dispatchToTransferFunctions(const ASTNode&n, const vector<const UnsignedInterval*>& _children)
  {
    const auto number_children = n.Degree();
    const auto width = n.GetValueWidth();

    assert(number_children == _children.size());

    const bool knownC0 = number_children < 1 ? false : (_children[0] != NULL);
    const bool knownC1 = number_children < 2 ? false : (_children[1] != NULL);
    const bool knownC2 = number_children < 3 ? false : (_children[2] != NULL);

    // Put in temporary null ones for any we're missing.
    auto children = _children;
    for (unsigned i =0 ; i < number_children; i++)
    {
      if (children[i] == nullptr)
        children[i] = getEmptyInterval(n[i]);
    }

    iterations++;

    UnsignedInterval* result = nullptr;

    switch (n.GetKind())
    {
      case BVCONST:
      case BITVECTOR:
      {
        // the CBV doesn't leak. it is a copy of the cbv inside the node.
        CBV cbv = n.GetBVConst();
        result = createInterval(cbv, cbv);
      }
      break;

      case TRUE:
        result = createInterval(littleOne, littleOne);
        break;

      case FALSE:
        result = createInterval(littleZero, littleZero);
        break;

      case NOT:
        if (knownC0)
        {
          assert(children[0]->isConstant());
          if (!CONSTANTBV::BitVector_Lexicompare(children[0]->minV, littleOne))
            result = createInterval(littleZero, littleZero);
          else
            result = createInterval(littleOne, littleOne);
        }
        break;

      case EQ:
        if (knownC0 && knownC1)
        {
          if ((CONSTANTBV::BitVector_Lexicompare(children[1]->minV,
                                                 children[0]->maxV) > 0) ||
              (CONSTANTBV::BitVector_Lexicompare(children[0]->minV,
                                                 children[1]->maxV) > 0))
            result = createInterval(littleZero, littleZero);

          else if (children[0]->isConstant() && children[1]->isConstant() &&
                   CONSTANTBV::BitVector_Lexicompare(children[0]->minV,
                                                     children[1]->minV) == 0)
          {
            result = createInterval(littleOne, littleOne);
          }
        }
        break;

      case BVGT:
        {
          const UnsignedInterval *c0 = children[0];
          const UnsignedInterval *c1 = children[1];

          if (CONSTANTBV::BitVector_Lexicompare(c0->minV, c1->maxV) > 0)
            result = createInterval(littleOne, littleOne);

          if (CONSTANTBV::BitVector_Lexicompare(c1->minV, c0->maxV) >= 0)
            result = createInterval(littleZero, littleZero);
        }

        break;

      case BVSGT: 
        {
          vector<UnsignedInterval*> a_vec, b_vec;
          UnsignedInterval::split(children[0],a_vec); // split at the poles
          UnsignedInterval::split(children[1],b_vec); 
             
          bool one = false;
          bool zero = false;        
          for (const auto& a : a_vec)
            for (const auto& b : b_vec) /// compare all pairs.
            {
              if (CONSTANTBV::BitVector_Compare(a->minV, b->maxV) > 0) // signed comparison.
                one = true;
              else if (CONSTANTBV::BitVector_Compare(b->minV, a->maxV) >= 0)
                zero = true;
              else
              {
                one = true;
                zero = true;
                break;
              }
            }

          if (one && !zero)
            result = createInterval(littleOne, littleOne);

          if (!one && zero)
            result = createInterval(littleZero, littleZero);

          for (const auto& a : a_vec)
            delete a;
          for (const auto& b : b_vec)
            delete b;     
        }
        break;

      case BVDIV:
      {
        const UnsignedInterval* top = children[0];
        const UnsignedInterval* c1 = children[1];

        result = freshUnsignedInterval(width);

        if (CONSTANTBV::BitVector_is_empty(c1->maxV))
        {
          // Dividing by the constant zero gives all ones.
          CONSTANTBV::BitVector_Fill(result->minV);
          break; // result is [1111..111, 11...11111]
        }

        CBV remainder = CONSTANTBV::BitVector_Create(width, true);

        // The minimum is the smallest dividend divided by the largest
        // divisor. Division by zero gives all ones, so this lower bound
        // holds even if the divisor might be zero.
        CBV dividend = CONSTANTBV::BitVector_Clone(top->minV);
        CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(
            result->minV, dividend, c1->maxV, remainder);
        assert(0 == e);
        CONSTANTBV::BitVector_Destroy(dividend);

        if (!CONSTANTBV::BitVector_is_empty(c1->minV))
        {
          // The divisor can't be zero, so the maximum is the largest
          // dividend divided by the smallest divisor.
          dividend = CONSTANTBV::BitVector_Clone(top->maxV);
          e = CONSTANTBV::BitVector_Div_Pos(result->maxV, dividend, c1->minV,
                                            remainder);
          assert(0 == e);
          CONSTANTBV::BitVector_Destroy(dividend);
        }

        CONSTANTBV::BitVector_Destroy(remainder);

        break;
      }

      case BVMOD: //OVER-APPROXIMATION
        if (knownC1)
        {
          if (CONSTANTBV::BitVector_is_empty(children[1]->maxV))
          {
            // Remainder by the constant zero is the identity.
            if (knownC0)
              result = createInterval(children[0]->minV, children[0]->maxV);
          }
          else if (children[1]->isConstant())
          {
            // A constant non-zero divisor is exact: the dividend runs over
            // every value between its bounds, so if the bounds have the
            // same quotient the remainders run from one bound's to the
            // other's, and otherwise a multiple of the divisor is crossed
            // and every remainder is reachable.
            const CBV divisor = children[1]->minV;
            CBV remainderMin = CONSTANTBV::BitVector_Create(width, true);
            CBV remainderMax = CONSTANTBV::BitVector_Create(width, true);
            CBV quotientMin = CONSTANTBV::BitVector_Create(width, true);
            CBV quotientMax = CONSTANTBV::BitVector_Create(width, true);

            CBV dividend = CONSTANTBV::BitVector_Clone(children[0]->minV);
            CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(
                quotientMin, dividend, divisor, remainderMin);
            assert(0 == e);
            CONSTANTBV::BitVector_Destroy(dividend);

            dividend = CONSTANTBV::BitVector_Clone(children[0]->maxV);
            e = CONSTANTBV::BitVector_Div_Pos(quotientMax, dividend, divisor,
                                              remainderMax);
            assert(0 == e);
            CONSTANTBV::BitVector_Destroy(dividend);

            if (CONSTANTBV::BitVector_Lexicompare(quotientMin, quotientMax) ==
                0)
            {
              result = createInterval(remainderMin, remainderMax);
            }
            else
            {
              CBV divisorLess1 = CONSTANTBV::BitVector_Clone(divisor);
              CONSTANTBV::BitVector_decrement(divisorLess1);
              result = createInterval(getEmptyCBV(width), divisorLess1);
              CONSTANTBV::BitVector_Destroy(divisorLess1);
            }

            CONSTANTBV::BitVector_Destroy(remainderMin);
            CONSTANTBV::BitVector_Destroy(remainderMax);
            CONSTANTBV::BitVector_Destroy(quotientMin);
            CONSTANTBV::BitVector_Destroy(quotientMax);
          }
          else if (!CONSTANTBV::BitVector_is_empty(children[1]->minV))
          {
            // The divisor can't be zero.
            if (knownC0 &&
                CONSTANTBV::BitVector_Lexicompare(children[0]->maxV,
                                                  children[1]->minV) < 0)
            {
              // The dividend is always below the divisor, so the remainder
              // is the dividend.
              result = createInterval(children[0]->minV, children[0]->maxV);
            }
            else
            {
              // The remainder is less than the largest divisor.
              result = freshUnsignedInterval(width);
              CONSTANTBV::BitVector_Copy(result->maxV, children[1]->maxV);
              CONSTANTBV::BitVector_decrement(result->maxV);

              // The remainder never exceeds the dividend.
              if (knownC0 &&
                  CONSTANTBV::BitVector_Lexicompare(children[0]->maxV,
                                                    result->maxV) < 0)
                CONSTANTBV::BitVector_Copy(result->maxV, children[0]->maxV);
            }
          }
          else if (knownC0)
          {
            // The divisor might be zero. The remainder never exceeds the
            // dividend, and dividing the biggest dividend by zero reaches
            // that bound, so the maximum is the dividend's maximum.
            result = freshUnsignedInterval(width);
            CONSTANTBV::BitVector_Copy(result->maxV, children[0]->maxV);
          }
        }
        break;

      case BVSX:
        if (knownC0)
        {
          result = freshUnsignedInterval(n.GetValueWidth());
          CONSTANTBV::BitVector_Empty(result->maxV);

          // Copy the max/min into the new bigger answer.
          for (unsigned i = 0; i < n[0].GetValueWidth(); i++)
          {
            if (CONSTANTBV::BitVector_bit_test(children[0]->maxV, i))
              CONSTANTBV::BitVector_Bit_On(result->maxV, i);

            if (CONSTANTBV::BitVector_bit_test(children[0]->minV, i))
              CONSTANTBV::BitVector_Bit_On(result->minV, i);
          }
          for (unsigned i = n[0].GetValueWidth(); i < n.GetValueWidth(); i++)
          {
            if (CONSTANTBV::BitVector_bit_test(children[0]->maxV,
                                               n[0].GetValueWidth() - 1))
              CONSTANTBV::BitVector_Bit_On(result->maxV, i);

            if (CONSTANTBV::BitVector_bit_test(children[0]->minV,
                                               n[0].GetValueWidth() - 1))
              CONSTANTBV::BitVector_Bit_On(result->minV, i);
          }
        }
        break;

      case BVNOT:
        if (knownC0) // NOT of the bitvector.
        {
          result = freshUnsignedInterval(width);
          CONSTANTBV::BitVector_Copy(result->maxV, children[0]->minV);
          CONSTANTBV::BitVector_Flip(result->maxV);
          CONSTANTBV::BitVector_Copy(result->minV, children[0]->maxV);
          CONSTANTBV::BitVector_Flip(result->minV);
        }
        break;

      case BVUMINUS:
        if (knownC0)
        {
          // Imagine it's {00, 01},  the unary minus of these is: {00,11},
          // i.e. it's everything. When there's a zero, (except for [0,0]),
          // it will be everything.

          if (!CONSTANTBV::BitVector_is_empty(children[0]->minV))
          {
            result = freshUnsignedInterval(width);
            CONSTANTBV::BitVector_Copy(result->maxV, children[0]->minV);
            CONSTANTBV::BitVector_Flip(result->maxV);
            CONSTANTBV::BitVector_increment(result->maxV);

            CONSTANTBV::BitVector_Copy(result->minV, children[0]->maxV);
            CONSTANTBV::BitVector_Flip(result->minV);
            CONSTANTBV::BitVector_increment(result->minV);
          }
          if ((CONSTANTBV::BitVector_is_empty(children[0]->minV)) &&
              (CONSTANTBV::BitVector_is_empty(children[0]->maxV)))
          {
            result = freshUnsignedInterval(width);
            CONSTANTBV::BitVector_Empty(result->maxV);
            CONSTANTBV::BitVector_Empty(result->minV);
          }
        }
        break;

      case ITE:
        if (knownC0)
        {
          result = freshUnsignedInterval(width);
          if (CONSTANTBV::BitVector_bit_test(children[0]->minV, 0) &&
              knownC1)
          {
            CONSTANTBV::BitVector_Copy(result->minV, children[1]->minV);
            CONSTANTBV::BitVector_Copy(result->maxV, children[1]->maxV);
          }
          else if (!CONSTANTBV::BitVector_bit_test(children[0]->minV, 0) &&
                   knownC2)
          {
            CONSTANTBV::BitVector_Copy(result->minV, children[2]->minV);
            CONSTANTBV::BitVector_Copy(result->maxV, children[2]->maxV);
          }
        }
        else if (knownC1 && knownC2)
        {
          // Both terms and propositions.
          result = freshUnsignedInterval(width);
          CBV min, max;
          if (CONSTANTBV::BitVector_Lexicompare(children[1]->minV,
                                                children[2]->minV) > 0)
            min = children[2]->minV;
          else
            min = children[1]->minV;

          if (CONSTANTBV::BitVector_Lexicompare(children[1]->maxV,
                                                children[2]->maxV) > 0)
            max = children[1]->maxV;
          else
            max = children[2]->maxV;

          CONSTANTBV::BitVector_Copy(result->minV, min);
          CONSTANTBV::BitVector_Copy(result->maxV, max);
        }
        break;

      case BVMULT: // OVER-APPROXIMATION
      {
        // Folded pairwise: exact for two children, sound beyond.
        CBV min = CONSTANTBV::BitVector_Clone(children[0]->minV);
        CBV max = CONSTANTBV::BitVector_Clone(children[0]->maxV);

        for (unsigned i = 1; i < children.size() && min != nullptr; i++)
        {
          CBV newMin, newMax;
          multiplyPair(min, max, children[i]->minV, children[i]->maxV, width,
                       newMin, newMax);
          CONSTANTBV::BitVector_Destroy(min);
          CONSTANTBV::BitVector_Destroy(max);
          min = newMin;
          max = newMax;
        }

        if (min != nullptr)
        {
          result = createInterval(min, max);
          CONSTANTBV::BitVector_Destroy(min);
          CONSTANTBV::BitVector_Destroy(max);
        }
        break;
      }

      case AND:
      {
        // If any are definately zero then the answer is zero.
        for (unsigned i = 0; i < children.size(); i++)
          if (CONSTANTBV::BitVector_is_empty(children[i]->maxV))
          {
            result = createInterval(littleZero, littleZero);
            break;
          }
        // If all are definately one the answer is one.
        bool allok = true;
        for (unsigned i = 0; i < children.size(); i++)
          if (CONSTANTBV::BitVector_is_empty(children[i]->minV))
          {
            allok = false;
            break;
          }
        if (allok)
          result = createInterval(littleOne, littleOne);
      }
      break;

      case OR:
      {
        // If any are definately one then the answer is  one.
        for (unsigned i = 0; i < children.size(); i++)
          if (CONSTANTBV::BitVector_is_full(children[i]->minV))
          {
            result = createInterval(littleOne, littleOne);
            break;
          }
        // If all are definately false the answer is false.
        bool allfalse = true;
        for (unsigned i = 0; i < children.size(); i++)
          if (CONSTANTBV::BitVector_is_full(children[i]->maxV))
          {
            allfalse = false;
            break;
          }
        if (allfalse)
          result = createInterval(littleZero, littleZero);
      }
      break;

      case XOR:
      {
        bool allOK = true;
        unsigned count = 0;
        for (unsigned i = 0; i < children.size(); i++)
          if (children[i]->isConstant())
          {
            if (!CONSTANTBV::BitVector_is_empty(children[i]->maxV))
              count++;
          }
          else
          {
            allOK = false;
            break;
          }

        if (allOK && (count % 2) == 0)
          result = createInterval(littleZero, littleZero);
        if (allOK && (count % 2) == 1)
          result = createInterval(littleOne, littleOne);

        break;
      }

      case BVAND:
      case BVOR:
      case BVXOR:
      {
        // Hacker's Delight gives the exact bounds of the bitwise operations
        // over intervals. Exact for two children; more children are folded
        // in pairwise, which is sound but may over-approximate.
        CBV min = CONSTANTBV::BitVector_Clone(children[0]->minV);
        CBV max = CONSTANTBV::BitVector_Clone(children[0]->maxV);

        for (unsigned i = 1; i < children.size(); i++)
        {
          CBV newMin, newMax;
          if (n.GetKind() == BVAND)
          {
            newMin = minAND(min, max, children[i]->minV, children[i]->maxV);
            newMax = maxAND(min, max, children[i]->minV, children[i]->maxV);
          }
          else if (n.GetKind() == BVOR)
          {
            newMin = minOR(min, max, children[i]->minV, children[i]->maxV);
            newMax = maxOR(min, max, children[i]->minV, children[i]->maxV);
          }
          else
          {
            newMin = minXOR(min, max, children[i]->minV, children[i]->maxV);
            newMax = maxXOR(min, max, children[i]->minV, children[i]->maxV);
          }

          CONSTANTBV::BitVector_Destroy(min);
          CONSTANTBV::BitVector_Destroy(max);
          min = newMin;
          max = newMax;
        }

        result = createInterval(min, max);
        CONSTANTBV::BitVector_Destroy(min);
        CONSTANTBV::BitVector_Destroy(max);
        break;
      }

      case BVEXTRACT:
      {
        // The value is (child >> low) mod 2^width. This transfer function
        // is exact. The index children are always constants; the guard
        // matters because the shift amount must be the real one.
        if (knownC2)
        {
          // The lowest bit of the extract is how far the child shifts right.
          unsigned shift_amount = *(children[2]->minV);

          CBV min = CONSTANTBV::BitVector_Clone(children[0]->minV);
          CBV max = CONSTANTBV::BitVector_Clone(children[0]->maxV);
          while (shift_amount-- > 0)
          {
            CONSTANTBV::BitVector_shift_right(min, 0);
            CONSTANTBV::BitVector_shift_right(max, 0);
          }

          // The shifted child takes every value between the shifted bounds,
          // so if the bounds agree above the extract's width, the low bits
          // run from the minimum's to the maximum's without wrapping.
          // Otherwise the result wraps: it reaches both zero and all ones,
          // and only the complete interval contains it.
          bool sameBlock = true;
          for (unsigned i = width; i < n[0].GetValueWidth() && sameBlock; i++)
            if (CONSTANTBV::BitVector_bit_test(min, i) !=
                CONSTANTBV::BitVector_bit_test(max, i))
              sameBlock = false;

          if (sameBlock)
          {
            CBV newMin = CONSTANTBV::BitVector_Create(width, true);
            CBV newMax = CONSTANTBV::BitVector_Create(width, true);
            for (unsigned i = 0; i < width; i++)
            {
              if (CONSTANTBV::BitVector_bit_test(min, i))
                CONSTANTBV::BitVector_Bit_On(newMin, i);
              if (CONSTANTBV::BitVector_bit_test(max, i))
                CONSTANTBV::BitVector_Bit_On(newMax, i);
            }

            result = createInterval(newMin, newMax);
            CONSTANTBV::BitVector_Destroy(newMin);
            CONSTANTBV::BitVector_Destroy(newMax);
          }

          CONSTANTBV::BitVector_Destroy(min);
          CONSTANTBV::BitVector_Destroy(max);
        }
        break;
      }

      case BVRIGHTSHIFT:
        if (knownC0 || knownC1)
        {
          result = freshUnsignedInterval(width);

          const UnsignedInterval* c0 = children[0];
          const UnsignedInterval* c1 = children[1];

          const unsigned minShift = cappedShiftAmount(c1->minV, width);
          const unsigned maxShift = cappedShiftAmount(c1->maxV, width);

          // The maximum result is the maximum >> (minimum shift).
          CONSTANTBV::BitVector_Copy(result->maxV, c0->maxV);
          for (unsigned i = 0; i < minShift; i++)
            CONSTANTBV::BitVector_shift_right(result->maxV, 0);

          // The minimum result is the minimum >> (maximum shift).
          CONSTANTBV::BitVector_Copy(result->minV, c0->minV);
          for (unsigned i = 0; i < maxShift; i++)
            CONSTANTBV::BitVector_shift_right(result->minV, 0);
        }
        break;

      case BVLEFTSHIFT:
      {
        // The value is (x << s) mod 2^width, which keeps the low
        // (width - s) bits of x and shifts them up. This transfer function
        // is exact: for each of the at most width+1 effective shift
        // amounts, x's surviving low bits run contiguously (the same
        // reasoning as BVEXTRACT), giving an exact hull per shift, and the
        // result is the union over the reachable shifts.
        const UnsignedInterval* c0 = children[0];
        const UnsignedInterval* c1 = children[1];

        const unsigned minShift = cappedShiftAmount(c1->minV, width);
        const unsigned maxShift = cappedShiftAmount(c1->maxV, width);

        CBV bestMin = nullptr;
        CBV bestMax = nullptr;

        for (unsigned s = minShift; s <= maxShift; s++)
        {
          // The hull for this shift amount. Shifting by the width or more
          // gives zero, so the capped amount stands in for all of those.
          CBV sMin = CONSTANTBV::BitVector_Create(width, true);
          CBV sMax = CONSTANTBV::BitVector_Create(width, true);

          if (s < width)
          {
            const unsigned surviving = width - s;

            // If the bounds agree above the surviving bits, the low bits
            // run from the minimum's to the maximum's without wrapping.
            bool sameBlock = true;
            for (unsigned i = surviving; i < width && sameBlock; i++)
              if (CONSTANTBV::BitVector_bit_test(c0->minV, i) !=
                  CONSTANTBV::BitVector_bit_test(c0->maxV, i))
                sameBlock = false;

            if (sameBlock)
            {
              for (unsigned i = 0; i < surviving; i++)
              {
                if (CONSTANTBV::BitVector_bit_test(c0->minV, i))
                  CONSTANTBV::BitVector_Bit_On(sMin, i + s);
                if (CONSTANTBV::BitVector_bit_test(c0->maxV, i))
                  CONSTANTBV::BitVector_Bit_On(sMax, i + s);
              }
            }
            else
            {
              // The surviving bits wrap: they reach both zero and all
              // ones, so this shift contributes [0, 11..1 << s].
              for (unsigned i = s; i < width; i++)
                CONSTANTBV::BitVector_Bit_On(sMax, i);
            }
          }

          if (bestMin == nullptr)
          {
            bestMin = sMin;
            bestMax = sMax;
          }
          else
          {
            if (CONSTANTBV::BitVector_Lexicompare(sMin, bestMin) < 0)
            {
              CONSTANTBV::BitVector_Destroy(bestMin);
              bestMin = sMin;
            }
            else
              CONSTANTBV::BitVector_Destroy(sMin);

            if (CONSTANTBV::BitVector_Lexicompare(sMax, bestMax) > 0)
            {
              CONSTANTBV::BitVector_Destroy(bestMax);
              bestMax = sMax;
            }
            else
              CONSTANTBV::BitVector_Destroy(sMax);
          }
        }

        result = createInterval(bestMin, bestMax);
        CONSTANTBV::BitVector_Destroy(bestMin);
        CONSTANTBV::BitVector_Destroy(bestMax);
        break;
      }

      case BVSRSHIFT:
        if (knownC0 || knownC1)
        {
          const UnsignedInterval* c0 = children[0];
          const UnsignedInterval* c1 = children[1];

          const unsigned minShift = cappedShiftAmount(c1->minV, width);
          const unsigned maxShift = cappedShiftAmount(c1->maxV, width);

          // An arithmetic shift keeps the sign, and is monotone in the
          // value, so the result's extremes come from shifting the bounds.
          // Shifting moves values towards zero if the sign bit is clear
          // (bigger shift, smaller result), and towards all ones if it is
          // set (bigger shift, bigger result).
          const bool minNegative =
              CONSTANTBV::BitVector_bit_test(c0->minV, width - 1);
          const bool maxNegative =
              CONSTANTBV::BitVector_bit_test(c0->maxV, width - 1);

          result = freshUnsignedInterval(width);

          CONSTANTBV::BitVector_Copy(result->minV, c0->minV);
          const unsigned minShifts = minNegative ? minShift : maxShift;
          for (unsigned i = 0; i < minShifts; i++)
            CONSTANTBV::BitVector_shift_right(result->minV, minNegative);

          CONSTANTBV::BitVector_Copy(result->maxV, c0->maxV);
          const unsigned maxShifts = maxNegative ? maxShift : minShift;
          for (unsigned i = 0; i < maxShifts; i++)
            CONSTANTBV::BitVector_shift_right(result->maxV, maxNegative);
        }
        break;

      case BVPLUS:
        if (knownC0 && knownC1)
        {
          //  >=2 arity.
          result = freshUnsignedInterval(width);
          CONSTANTBV::BitVector_Flip(result->maxV); // make the max zero too.

          bool min_carry;
          bool max_carry;

          for (size_t i = 0; i < children.size(); i++)
          {
            if (children[i]->isComplete())
            {
              delete result;
              result = nullptr;
              break;
            }

            max_carry = false;
            min_carry = false;

            CONSTANTBV::BitVector_add(result->maxV, result->maxV,
                                      children[i]->maxV, &max_carry);
            CONSTANTBV::BitVector_add(result->minV, result->minV,
                                      children[i]->minV, &min_carry);
            if (min_carry != max_carry)
            {
              delete result;
              result = nullptr;
              break;
            }
          }
        }
        break;

      case BVCONCAT:
        if ((knownC0 || knownC1))
        {
          const UnsignedInterval* c0 = children[0];
          const UnsignedInterval* c1 = children[1];

          CBV min = CONSTANTBV::BitVector_Concat(c0->minV, c1->minV);
          CBV max = CONSTANTBV::BitVector_Concat(c0->maxV, c1->maxV);

          result = createInterval(min, max);

          CONSTANTBV::BitVector_Destroy(min);
          CONSTANTBV::BitVector_Destroy(max);
        }
        break;

      // TODO
      case SBVDIV:
      case SBVREM:
      case SBVMOD:
      default:
        propagatorNotImplemented++;
        break;
    }

    if (result != NULL && result->isComplete())
    {
      delete result;
      result = NULL;
    }

    if (result != NULL)
    {
      result->checkUnsignedInvariant();
    }

    return result;
  }

  UnsignedInterval* UnsignedIntervalAnalysis::visit(const ASTNode& n,
                          NodeToUnsignedIntervalMap& visited)
  {
    {
      NodeToUnsignedIntervalMap::iterator it;
      if ((it = visited.find(n)) != visited.end())
        return it->second;
    }

    if (n.GetKind() == SYMBOL || n.GetKind() == WRITE || n.GetKind() == READ)
    {
      // Never know anything about these.
      visited.insert({n, NULL});
      return NULL;
    }

    const auto number_children = n.Degree();
    vector<const UnsignedInterval*> children;

    children.reserve(number_children);

    for (unsigned i = 0; i < number_children; i++)
    {
      UnsignedInterval* r = visit(n[i], visited);
      if (r != NULL)
      {
        assert(!r->isComplete());
      }
      children.push_back(r);
    }

    UnsignedInterval* result = dispatchToTransferFunctions(n,children);

    // result will often be null (which we take to mean the maximum range).
    visited.insert({n, result});
    return result;
  }

  UnsignedIntervalAnalysis::UnsignedIntervalAnalysis(STPMgr& _bm) : bm(_bm)
  {
    littleZero = getEmptyCBV(1);
    littleOne = CONSTANTBV::BitVector_Create(1, true);
    CONSTANTBV::BitVector_Fill(littleOne);
  }

  UnsignedIntervalAnalysis::~UnsignedIntervalAnalysis()
  {
    for (auto it : emptyIntervals)
      if (it.second != NULL)
        delete it.second;

    for (auto it : emptyCBV)
      if (it.second != NULL)
        CONSTANTBV::BitVector_Destroy(it.second);

    CONSTANTBV::BitVector_Destroy(littleOne);
  }
}

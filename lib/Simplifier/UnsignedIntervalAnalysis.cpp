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

    // ---- The six bounds of the bitwise operations over the intervals
    // x in [a, b] and y in [c, d], from section 4-3 of Hacker's Delight.
    // Each scans candidate positions from the top, trying to raise a
    // minimum (clearing every bit below) or lower a maximum (setting
    // every bit below), keeping a candidate when it stays inside its
    // operand's interval. The scans run on 64-bit chunks read straight
    // from the bitvector storage: the whole-vector comparison a
    // candidate needs factors into "are the chunks above still equal to
    // the bound's" (the drivers track that) plus one word comparison in
    // the current chunk, because the candidate's chunks above are
    // untouched and its chunks below are all-zero against an upper
    // bound or all-one against a lower bound. ----

    // The 64 bits of x starting at any bit offset, as a machine word.
    // Chunk_Read clamps at the vector's width and reads zero past it, so
    // no guards are needed. Two 32-bit reads because Chunk_Read is
    // capped at the bits of an unsigned long, which isn't 64 everywhere.
    uint64_t chunkAt(const CBV x, unsigned offset)
    {
      uint64_t r = CONSTANTBV::BitVector_Chunk_Read(x, 32, offset);
      r |= (uint64_t)CONSTANTBV::BitVector_Chunk_Read(x, 32, offset + 32)
           << 32;
      return r;
    }

    // Bits [64k, 64k+63] of x as a machine word.
    uint64_t chunk64(const CBV x, unsigned k)
    {
      return chunkAt(x, 64 * k);
    }

    // The inverse of chunk64. The value's bits above the vector's width
    // must be zero.
    void setChunk64(CBV x, unsigned k, uint64_t value)
    {
      const unsigned offset = 64 * k;
      CONSTANTBV::BitVector_Chunk_Store(x, 32, offset, value);
      CONSTANTBV::BitVector_Chunk_Store(x, 32, offset + 32, value >> 32);
    }

    // Which operand a chunk kernel changed.
    enum class Changed
    {
      None,
      First,
      Second
    };

    // One chunk of the minOR scan; a and c are the operands' chunks and
    // cw the chunk's bit count. bEff/dEff are the accept bounds: the
    // bound's own chunk while the chunks above are all equal to it,
    // otherwise all-ones because a higher chunk already decided the
    // comparison in the candidate's favour.
    Changed minORChunk(uint64_t& a, uint64_t bEff, uint64_t& c,
                       uint64_t dEff, unsigned cw)
    {
      for (unsigned i = cw; i-- > 0;)
      {
        const uint64_t m = (uint64_t)1 << i;
        if (!(a & m) && (c & m))
        {
          // Raising a to supply this bit lets everything below it be zero.
          const uint64_t raised = (a | m) & ~(m - 1);
          if (raised <= bEff)
          {
            a = raised;
            return Changed::First;
          }
        }
        else if ((a & m) && !(c & m))
        {
          const uint64_t raised = (c | m) & ~(m - 1);
          if (raised <= dEff)
          {
            c = raised;
            return Changed::Second;
          }
        }
      }
      return Changed::None;
    }

    // For the maximums the accept bounds flip: aEff/cEff are the
    // minimum's chunk while the chunks above are all equal, otherwise
    // zero because the comparison is already won.
    Changed maxORChunk(uint64_t& b, uint64_t aEff, uint64_t& d,
                       uint64_t cEff, unsigned cw)
    {
      for (unsigned i = cw; i-- > 0;)
      {
        const uint64_t m = (uint64_t)1 << i;
        if ((b & m) && (d & m))
        {
          // One operand can donate this bit; lowering the other one sets
          // every bit below it.
          uint64_t lowered = (b & ~m) | (m - 1);
          if (lowered >= aEff)
          {
            b = lowered;
            return Changed::First;
          }
          lowered = (d & ~m) | (m - 1);
          if (lowered >= cEff)
          {
            d = lowered;
            return Changed::Second;
          }
        }
      }
      return Changed::None;
    }

    Changed minANDChunk(uint64_t& a, uint64_t bEff, uint64_t& c,
                        uint64_t dEff, unsigned cw)
    {
      for (unsigned i = cw; i-- > 0;)
      {
        const uint64_t m = (uint64_t)1 << i;
        if (!(a & m) && !(c & m))
        {
          // The bit is zero in both minimums, so it is zero in the result;
          // raising one minimum past it lets everything below be zero.
          uint64_t raised = (a | m) & ~(m - 1);
          if (raised <= bEff)
          {
            a = raised;
            return Changed::First;
          }
          raised = (c | m) & ~(m - 1);
          if (raised <= dEff)
          {
            c = raised;
            return Changed::Second;
          }
        }
      }
      return Changed::None;
    }

    Changed maxANDChunk(uint64_t& b, uint64_t aEff, uint64_t& d,
                        uint64_t cEff, unsigned cw)
    {
      for (unsigned i = cw; i-- > 0;)
      {
        const uint64_t m = (uint64_t)1 << i;
        if ((b & m) && !(d & m))
        {
          // The bit can't survive the AND; giving it up sets every bit
          // below it.
          const uint64_t lowered = (b & ~m) | (m - 1);
          if (lowered >= aEff)
          {
            b = lowered;
            return Changed::First;
          }
        }
        else if (!(b & m) && (d & m))
        {
          const uint64_t lowered = (d & ~m) | (m - 1);
          if (lowered >= cEff)
          {
            d = lowered;
            return Changed::Second;
          }
        }
      }
      return Changed::None;
    }

    // One chunk of the minXOR scan. Unlike OR/AND a kept candidate keeps
    // helping at the lower bits, so the scan continues and the flags
    // report which operands changed. Only positions where a and c differ
    // can act, so the loop jumps between those with count-leading-zeros.
    void minXORChunk(uint64_t& a, uint64_t bEff, uint64_t& c,
                     uint64_t dEff, unsigned cw, bool& aChanged,
                     bool& cChanged)
    {
      const uint64_t chunkMask =
          (cw >= 64) ? ~(uint64_t)0 : (((uint64_t)1 << cw) - 1);
      uint64_t candidates = (a ^ c) & chunkMask;
      while (candidates != 0)
      {
        const uint64_t m = (uint64_t)1 << (63 - __builtin_clzll(candidates));
        if (c & m) // and not a: raising a can cancel c's bit
        {
          const uint64_t raised = (a | m) & ~(m - 1);
          if (raised <= bEff)
          {
            a = raised;
            aChanged = true;
            candidates = (a ^ c) & (m - 1);
            continue;
          }
        }
        else // a has the bit, c doesn't
        {
          const uint64_t raised = (c | m) & ~(m - 1);
          if (raised <= dEff)
          {
            c = raised;
            cChanged = true;
            candidates = (a ^ c) & (m - 1);
            continue;
          }
        }
        candidates &= m - 1;
      }
    }

    // Only positions where both maximums have the bit do anything: the
    // shared bit cancels in the XOR, and giving it up in one operand
    // sets everything below it.
    void maxXORChunk(uint64_t& b, uint64_t aEff, uint64_t& d,
                     uint64_t cEff, unsigned cw, bool& bChanged,
                     bool& dChanged)
    {
      const uint64_t chunkMask =
          (cw >= 64) ? ~(uint64_t)0 : (((uint64_t)1 << cw) - 1);
      uint64_t candidates = b & d & chunkMask;
      while (candidates != 0)
      {
        const uint64_t m = (uint64_t)1 << (63 - __builtin_clzll(candidates));
        uint64_t lowered = (b & ~m) | (m - 1);
        if (lowered >= aEff)
        {
          b = lowered;
          bChanged = true;
        }
        else
        {
          lowered = (d & ~m) | (m - 1);
          if (lowered >= cEff)
          {
            d = lowered;
            dChanged = true;
          }
        }
        candidates = b & d & (m - 1);
      }
    }

    unsigned chunksOf(unsigned width)
    {
      return (width + 63) / 64;
    }

    // Chunk k of x << s, before any masking at the width: the target
    // bits [64k, 64k+63] come from the source bits 64k-s upward, which
    // is an offset read, a zero, or a partial low read shifted up.
    uint64_t shlChunk(const CBV x, unsigned s, unsigned k)
    {
      const unsigned off = 64 * k;
      if (off + 64 <= s)
        return 0;
      if (off >= s)
        return chunkAt(x, off - s);
      return chunkAt(x, 0) << (s - off);
    }

    // Chunk k of x >> s at the given width, filling the vacated top
    // bits with ones when the value is negative (the stores clamp at
    // the width, so bits set past it are harmless).
    uint64_t shrChunk(const CBV x, unsigned s, unsigned k, unsigned width,
                      bool negative)
    {
      uint64_t v = chunkAt(x, 64 * k + s);
      if (negative)
      {
        const unsigned off = 64 * k;
        const unsigned fillStart = width - s; // s is capped at the width
        if (off >= fillStart)
          v = ~(uint64_t)0;
        else if (off + 64 > fillStart)
          v |= ~(uint64_t)0 << (fillStart - off);
      }
      return v;
    }

    // Lexicographic comparison of two equal-length chunk arrays, most
    // significant chunk first.
    int compareChunks(const uint64_t* x, const uint64_t* y, unsigned K)
    {
      for (unsigned k = K; k-- > 0;)
        if (x[k] != y[k])
          return x[k] < y[k] ? -1 : 1;
      return 0;
    }

    // The smallest x | y. The caller owns the returned bitvector, as
    // with all six drivers.
    CBV minOR(const CBV a, const CBV b, const CBV c, const CBV d)
    {
      const unsigned width = bits_(a);
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      bool eqAB = true, eqCD = true;
      for (unsigned k = chunksOf(width); k-- > 0;)
      {
        const unsigned cw = std::min(64u, width - 64 * k);
        const uint64_t aK = chunk64(a, k), bK = chunk64(b, k);
        const uint64_t cK = chunk64(c, k), dK = chunk64(d, k);
        uint64_t aM = aK, cM = cK;
        const Changed changed =
            minORChunk(aM, eqAB ? bK : ~(uint64_t)0, cM,
                       eqCD ? dK : ~(uint64_t)0, cw);
        setChunk64(result, k, aM | cM);
        if (changed != Changed::None)
        {
          // The kept candidate cleared everything below it, so the
          // changed operand contributes nothing to the lower chunks.
          for (unsigned j = k; j-- > 0;)
            setChunk64(result, j,
                       changed == Changed::First ? chunk64(c, j)
                                                 : chunk64(a, j));
          return result;
        }
        eqAB = eqAB && (aK == bK);
        eqCD = eqCD && (cK == dK);
      }
      return result;
    }

    // The biggest x | y.
    CBV maxOR(const CBV a, const CBV b, const CBV c, const CBV d)
    {
      const unsigned width = bits_(a);
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      bool eqBA = true, eqDC = true;
      for (unsigned k = chunksOf(width); k-- > 0;)
      {
        const unsigned cw = std::min(64u, width - 64 * k);
        const uint64_t aK = chunk64(a, k), bK = chunk64(b, k);
        const uint64_t cK = chunk64(c, k), dK = chunk64(d, k);
        uint64_t bM = bK, dM = dK;
        const Changed changed =
            maxORChunk(bM, eqBA ? aK : 0, dM, eqDC ? cK : 0, cw);
        setChunk64(result, k, bM | dM);
        if (changed != Changed::None)
        {
          // The kept candidate set everything below it: all ones. Only
          // full 64-bit chunks can sit below another chunk.
          for (unsigned j = k; j-- > 0;)
            setChunk64(result, j, ~(uint64_t)0);
          return result;
        }
        eqBA = eqBA && (bK == aK);
        eqDC = eqDC && (dK == cK);
      }
      return result;
    }

    // The smallest x & y.
    CBV minAND(const CBV a, const CBV b, const CBV c, const CBV d)
    {
      const unsigned width = bits_(a);
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      bool eqAB = true, eqCD = true;
      for (unsigned k = chunksOf(width); k-- > 0;)
      {
        const unsigned cw = std::min(64u, width - 64 * k);
        const uint64_t aK = chunk64(a, k), bK = chunk64(b, k);
        const uint64_t cK = chunk64(c, k), dK = chunk64(d, k);
        uint64_t aM = aK, cM = cK;
        const Changed changed =
            minANDChunk(aM, eqAB ? bK : ~(uint64_t)0, cM,
                        eqCD ? dK : ~(uint64_t)0, cw);
        setChunk64(result, k, aM & cM);
        if (changed != Changed::None)
        {
          // The changed operand is zero below this chunk, and so is the
          // AND: the fresh result vector is already clear there.
          return result;
        }
        eqAB = eqAB && (aK == bK);
        eqCD = eqCD && (cK == dK);
      }
      return result;
    }

    // The biggest x & y.
    CBV maxAND(const CBV a, const CBV b, const CBV c, const CBV d)
    {
      const unsigned width = bits_(a);
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      bool eqBA = true, eqDC = true;
      for (unsigned k = chunksOf(width); k-- > 0;)
      {
        const unsigned cw = std::min(64u, width - 64 * k);
        const uint64_t aK = chunk64(a, k), bK = chunk64(b, k);
        const uint64_t cK = chunk64(c, k), dK = chunk64(d, k);
        uint64_t bM = bK, dM = dK;
        const Changed changed =
            maxANDChunk(bM, eqBA ? aK : 0, dM, eqDC ? cK : 0, cw);
        setChunk64(result, k, bM & dM);
        if (changed != Changed::None)
        {
          // The changed operand is all ones below this chunk, so the
          // AND is the other operand there.
          for (unsigned j = k; j-- > 0;)
            setChunk64(result, j,
                       changed == Changed::First ? chunk64(d, j)
                                                 : chunk64(b, j));
          return result;
        }
        eqBA = eqBA && (bK == aK);
        eqDC = eqDC && (dK == cK);
      }
      return result;
    }

    // The smallest x ^ y. Like minOR, but a bit supplied to cancel one in
    // the other operand keeps helping at the lower bits, so the scan
    // continues; once an operand was raised its lower chunks are zero.
    CBV minXOR(const CBV a, const CBV b, const CBV c, const CBV d)
    {
      const unsigned width = bits_(a);
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      bool eqAB = true, eqCD = true;
      bool aCleared = false, cCleared = false;
      for (unsigned k = chunksOf(width); k-- > 0;)
      {
        const unsigned cw = std::min(64u, width - 64 * k);
        const uint64_t aK = aCleared ? 0 : chunk64(a, k);
        const uint64_t cK = cCleared ? 0 : chunk64(c, k);
        const uint64_t bK = chunk64(b, k), dK = chunk64(d, k);
        uint64_t aM = aK, cM = cK;
        bool aChanged = false, cChanged = false;
        minXORChunk(aM, eqAB ? bK : ~(uint64_t)0, cM,
                    eqCD ? dK : ~(uint64_t)0, cw, aChanged, cChanged);
        setChunk64(result, k, aM ^ cM);
        aCleared = aCleared || aChanged;
        cCleared = cCleared || cChanged;
        // The prefixes compare against the operands as modified.
        eqAB = eqAB && (aM == bK);
        eqCD = eqCD && (cM == dK);
      }
      return result;
    }

    // The biggest x ^ y. Like maxOR, but a shared bit cancels out, so
    // giving it up in one operand keeps helping at the lower bits; once
    // an operand was lowered its lower chunks are all ones.
    CBV maxXOR(const CBV a, const CBV b, const CBV c, const CBV d)
    {
      const unsigned width = bits_(a);
      CBV result = CONSTANTBV::BitVector_Create(width, true);
      bool eqBA = true, eqDC = true;
      bool bFilled = false, dFilled = false;
      for (unsigned k = chunksOf(width); k-- > 0;)
      {
        const unsigned cw = std::min(64u, width - 64 * k);
        const uint64_t chunkMask =
            (cw >= 64) ? ~(uint64_t)0 : (((uint64_t)1 << cw) - 1);
        const uint64_t bK = bFilled ? chunkMask : chunk64(b, k);
        const uint64_t dK = dFilled ? chunkMask : chunk64(d, k);
        const uint64_t aK = chunk64(a, k), cK = chunk64(c, k);
        uint64_t bM = bK, dM = dK;
        bool bChanged = false, dChanged = false;
        maxXORChunk(bM, eqBA ? aK : 0, dM, eqDC ? cK : 0, cw, bChanged,
                    dChanged);
        setChunk64(result, k, bM ^ dM);
        bFilled = bFilled || bChanged;
        dFilled = dFilled || dChanged;
        // The prefixes compare against the operands as modified.
        eqBA = eqBA && (bM == aK);
        eqDC = eqDC && (dM == cK);
      }
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

    CBV mulFresh(const CBV x, const CBV y)
    {
      CBV r = zeroOf(bits_(x));
      CBV tmp = CONSTANTBV::BitVector_Clone(x); // Mul_Pos destroys this one.
      CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Mul_Pos(r, tmp, y, true);
      assert(0 == e);
      CONSTANTBV::BitVector_Destroy(tmp);
      return r;
    }

    typedef unsigned __int128 uint128;

    // The low (up to 64) bits of x as a machine word.
    uint64_t low64(const CBV x)
    {
      return chunk64(x, 0);
    }

    // A fresh CBV holding a machine word. Needs value < 2^width.
    CBV cbvFromU64(unsigned width, uint64_t value)
    {
      CBV r = CONSTANTBV::BitVector_Create(width, true);
      setChunk64(r, 0, value);
      return r;
    }

    // The minimum of (a*i + b) mod m over 0 <= i < n; requires n >= 1,
    // a < m and b < m, with m <= 2^64 so nothing here can overflow.
    // Between wraps the values only grow, so the minimum is b or a
    // post-wrap residue; the residues just after each wrap follow the
    // progression b1 + j*((-m) mod a) inside [0, a), which the loop
    // chases Euclid-style: O(log m) iterations.
    uint128 minlin(uint128 n, uint128 m, uint128 a, uint128 b)
    {
      uint128 best = b;
      while (true)
      {
        if (b < best)
          best = b; // the value at i = 0 of this level
        if (a == 0 || n == 1)
          return best;
        const uint128 firstWrap = (m - b + a - 1) / a;
        if (firstWrap >= n)
          return best; // never wraps, so the values only grow from b
        const uint128 wraps = (b + (n - 1) * a) / m;
        const uint128 afterWrap = b + firstWrap * a - m; // in [0, a)
        n = wraps;
        b = afterWrap;
        const uint128 step = (a - m % a) % a;
        m = a;
        a = step;
      }
    }

    // The maximum, by reflection: max(v) = m-1 - min(m-1-v), and
    // m-1-(a*i+b) mod m is the progression ((m-a)*i + (m-1-b)) mod m.
    uint128 maxlin(uint128 n, uint128 m, uint128 a, uint128 b)
    {
      return m - 1 - minlin(n, m, (m - a) % m, m - 1 - b);
    }

    // The exact bounds of the progression start, start + step, ...
    // (count terms, mod m), where m is a power of two, step < m and
    // start < m.
    void progressionHull(uint128 start, uint128 step, uint128 count,
                         uint128 m, uint128& mn, uint128& mx)
    {
      if (step == 0)
      {
        mn = mx = start;
        return;
      }
      // The progression repeats with period m / gcd; a count covering a
      // full period hits exactly the residues congruent to start modulo
      // the gcd.
      const uint128 gcd = (uint128)1 << __builtin_ctzll((uint64_t)step);
      if (count >= m / gcd)
      {
        mn = start & (gcd - 1);
        mx = m - gcd + mn;
      }
      else
      {
        mn = minlin(count, m, step, start);
        mx = maxlin(count, m, step, start);
      }
    }

    // Enumerating one operand's values is exact but linear in how many
    // it has, so only do it when that side is small.
    const uint64_t smallSideLimit = 16;

    // The bounds of x*y (mod 2^width) with x in [a, b] and y in [c, d],
    // written into resultMin/resultMax; both stay null if nothing is
    // known. Exact when the bound products land in the same 2^width block,
    // and when either operand has at most smallSideLimit values (at
    // widths up to 64).
    void multiplyPair(const CBV a, const CBV b, const CBV c, const CBV d,
                      unsigned width, CBV& resultMin, CBV& resultMax)
    {
      resultMin = nullptr;
      resultMax = nullptr;

      if (width <= 64)
      {
        const uint64_t aV = low64(a), bV = low64(b);
        const uint64_t cV = low64(c), dV = low64(d);
        const uint128 m = (uint128)1 << width;

        const uint128 lowProduct = (uint128)aV * cV;
        const uint128 highProduct = (uint128)bV * dV;

        uint128 apMin, apMax;
        bool known = false;

        if ((lowProduct >> width) == (highProduct >> width))
        {
          // Every product sits between the bound products, which agree
          // above the width, so the low bits run between the bounds' low
          // bits without wrapping: exact.
          apMin = lowProduct & (m - 1);
          apMax = highProduct & (m - 1);
          known = true;
        }
        else
        {
          // For each value of one operand the products form an arithmetic
          // progression, so when either operand has few enough values the
          // merge of their progressions' hulls is the exact hull of the
          // product set. A constant operand is the one-progression case.
          const bool xSmall = (bV - aV) <= (dV - cV);
          const uint64_t fixedLo = xSmall ? aV : cV;
          const uint64_t fixedHi = xSmall ? bV : dV;
          const uint64_t movingLo = xSmall ? cV : aV;
          const uint128 movingCount =
              (uint128)(xSmall ? dV - cV : bV - aV) + 1;

          if (fixedHi - fixedLo < smallSideLimit)
          {
            apMin = m - 1;
            apMax = 0;
            for (uint64_t v = fixedLo;; v++)
            {
              uint128 pmn, pmx;
              progressionHull(((uint128)v * movingLo) & (m - 1), v,
                              movingCount, m, pmn, pmx);
              if (pmn < apMin)
                apMin = pmn;
              if (pmx > apMax)
                apMax = pmx;
              if (v == fixedHi)
                break; // tested after the body: fixedHi may be the top value
            }
            known = true;
          }
          // Otherwise the products can wrap in ways intervals can't follow.
        }

        if (known)
        {
          resultMin = zeroOf(width);
          resultMax = zeroOf(width);
          for (unsigned i = 0; i < width; i++)
          {
            if ((apMin >> i) & 1)
              CONSTANTBV::BitVector_Bit_On(resultMin, i);
            if ((apMax >> i) & 1)
              CONSTANTBV::BitVector_Bit_On(resultMax, i);
          }
        }
        return;
      }

      // Bignum fallback for widths over 64: the same-block case only.
      // Wide enough for the bound products.
      const unsigned wide = 2 * width + 2;

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

      CONSTANTBV::BitVector_Destroy(aW);
      CONSTANTBV::BitVector_Destroy(bW);
      CONSTANTBV::BitVector_Destroy(cW);
      CONSTANTBV::BitVector_Destroy(dW);
      CONSTANTBV::BitVector_Destroy(lowProduct);
      CONSTANTBV::BitVector_Destroy(highProduct);
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
          // Copy the child's chunks and fill everything from its top bit
          // up with its sign: an arithmetic shift by zero seen at the
          // child's width, stored into the wider vector.
          const unsigned childWidth = n[0].GetValueWidth();
          const CBV childMin = children[0]->minV;
          const CBV childMax = children[0]->maxV;
          const bool minNegative =
              CONSTANTBV::BitVector_bit_test(childMin, childWidth - 1);
          const bool maxNegative =
              CONSTANTBV::BitVector_bit_test(childMax, childWidth - 1);

          CBV mn = CONSTANTBV::BitVector_Create(width, true);
          CBV mx = CONSTANTBV::BitVector_Create(width, true);
          for (unsigned k = 0; k < chunksOf(width); k++)
          {
            setChunk64(mn, k,
                       shrChunk(childMin, 0, k, childWidth, minNegative));
            setChunk64(mx, k,
                       shrChunk(childMax, 0, k, childWidth, maxNegative));
          }
          // The interval takes ownership of the fresh bitvectors.
          result = new UnsignedInterval(mn, mx);
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
        CBV min = children[0]->minV;
        CBV max = children[0]->maxV;
        CBV foldedMin = nullptr; // the fold's own intermediates
        CBV foldedMax = nullptr;

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

          if (foldedMin != nullptr)
          {
            CONSTANTBV::BitVector_Destroy(foldedMin);
            CONSTANTBV::BitVector_Destroy(foldedMax);
          }
          foldedMin = min = newMin;
          foldedMax = max = newMax;
        }

        if (foldedMin == nullptr) // a single child passes through
        {
          foldedMin = CONSTANTBV::BitVector_Clone(min);
          foldedMax = CONSTANTBV::BitVector_Clone(max);
        }

        // The interval takes ownership of the fresh bitvectors.
        result = new UnsignedInterval(foldedMin, foldedMax);
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
          const unsigned shift = *(children[2]->minV);
          const unsigned childWidth = n[0].GetValueWidth();
          const CBV childMin = children[0]->minV;
          const CBV childMax = children[0]->maxV;

          // The shifted child takes every value between the shifted bounds,
          // so if the bounds agree above the extract's width, the low bits
          // run from the minimum's to the maximum's without wrapping.
          // Otherwise the result wraps: it reaches both zero and all ones,
          // and only the complete interval contains it.
          bool sameBlock = true;
          for (unsigned off = width; shift + off < childWidth && sameBlock;
               off += 64)
            if (chunkAt(childMin, shift + off) !=
                chunkAt(childMax, shift + off))
              sameBlock = false;

          if (sameBlock)
          {
            CBV mn = CONSTANTBV::BitVector_Create(width, true);
            CBV mx = CONSTANTBV::BitVector_Create(width, true);
            for (unsigned k = 0; k < chunksOf(width); k++)
            {
              setChunk64(mn, k, chunkAt(childMin, shift + 64 * k));
              setChunk64(mx, k, chunkAt(childMax, shift + 64 * k));
            }
            // The interval takes ownership of the fresh bitvectors.
            result = new UnsignedInterval(mn, mx);
          }
        }
        break;
      }

      case BVRIGHTSHIFT:
        if (knownC0 || knownC1)
        {
          const UnsignedInterval* c0 = children[0];
          const UnsignedInterval* c1 = children[1];

          const unsigned minShift = cappedShiftAmount(c1->minV, width);
          const unsigned maxShift = cappedShiftAmount(c1->maxV, width);

          // The maximum result is the maximum >> (minimum shift), and
          // the minimum result the minimum >> (maximum shift): the
          // shifted chunks are offset reads.
          CBV mn = CONSTANTBV::BitVector_Create(width, true);
          CBV mx = CONSTANTBV::BitVector_Create(width, true);
          for (unsigned k = 0; k < chunksOf(width); k++)
          {
            setChunk64(mn, k, shrChunk(c0->minV, maxShift, k, width, false));
            setChunk64(mx, k, shrChunk(c0->maxV, minShift, k, width, false));
          }
          // The interval takes ownership of the fresh bitvectors.
          result = new UnsignedInterval(mn, mx);
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

        const unsigned K = chunksOf(width);
        const unsigned topBits = width - 64 * (K - 1);
        const uint64_t topMask =
            (topBits >= 64) ? ~(uint64_t)0 : (((uint64_t)1 << topBits) - 1);

        // The highest bit where the child's bounds differ decides every
        // shift's block test at once: the bounds agree on the bits that
        // survive the shift exactly when this bit doesn't survive.
        int highestDiff = -1;
        for (unsigned k = K; k-- > 0 && highestDiff < 0;)
        {
          const uint64_t diff = chunk64(c0->minV, k) ^ chunk64(c0->maxV, k);
          if (diff != 0)
            highestDiff = 64 * k + 63 - __builtin_clzll(diff);
        }

        // Four chunk buffers; on the stack for widths up to 1024.
        uint64_t stackBuf[64];
        std::vector<uint64_t> heapBuf;
        uint64_t* buf = stackBuf;
        if (4 * K > 64)
        {
          heapBuf.resize(4 * K);
          buf = heapBuf.data();
        }
        uint64_t* bestMin = buf;
        uint64_t* bestMax = buf + K;
        uint64_t* sMin = buf + 2 * K;
        uint64_t* sMax = buf + 3 * K;

        for (unsigned s = minShift; s <= maxShift; s++)
        {
          // The hull for this shift amount. Shifting by the width or more
          // gives zero, so the capped amount stands in for all of those.
          if (s >= width)
          {
            for (unsigned k = 0; k < K; k++)
              sMin[k] = sMax[k] = 0;
          }
          else if (highestDiff < (int)(width - s))
          {
            // The bounds agree above the surviving bits, so the low bits
            // run from the minimum's to the maximum's without wrapping.
            for (unsigned k = 0; k < K; k++)
            {
              sMin[k] = shlChunk(c0->minV, s, k);
              sMax[k] = shlChunk(c0->maxV, s, k);
            }
            sMin[K - 1] &= topMask;
            sMax[K - 1] &= topMask;
          }
          else
          {
            // The surviving bits wrap: they reach both zero and all
            // ones, so this shift contributes [0, 11..1 << s].
            for (unsigned k = 0; k < K; k++)
            {
              const unsigned off = 64 * k;
              sMin[k] = 0;
              sMax[k] = (off + 64 <= s)
                            ? 0
                            : (off >= s) ? ~(uint64_t)0
                                         : (~(uint64_t)0 << (s - off));
            }
            sMax[K - 1] &= topMask;
          }

          if (s == minShift || compareChunks(sMin, bestMin, K) < 0)
            std::swap(bestMin, sMin);
          if (s == minShift || compareChunks(sMax, bestMax, K) > 0)
            std::swap(bestMax, sMax);
        }

        CBV mn = CONSTANTBV::BitVector_Create(width, true);
        CBV mx = CONSTANTBV::BitVector_Create(width, true);
        for (unsigned k = 0; k < K; k++)
        {
          setChunk64(mn, k, bestMin[k]);
          setChunk64(mx, k, bestMax[k]);
        }
        // The interval takes ownership of the fresh bitvectors.
        result = new UnsignedInterval(mn, mx);
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

          const unsigned minShifts = minNegative ? minShift : maxShift;
          const unsigned maxShifts = maxNegative ? maxShift : minShift;

          CBV mn = CONSTANTBV::BitVector_Create(width, true);
          CBV mx = CONSTANTBV::BitVector_Create(width, true);
          for (unsigned k = 0; k < chunksOf(width); k++)
          {
            setChunk64(mn, k,
                       shrChunk(c0->minV, minShifts, k, width, minNegative));
            setChunk64(mx, k,
                       shrChunk(c0->maxV, maxShifts, k, width, maxNegative));
          }
          // The interval takes ownership of the fresh bitvectors.
          result = new UnsignedInterval(mn, mx);
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

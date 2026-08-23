/***********
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
**********************/

/*
 * The widened-comparison narrowing rules, checked by exhaustive enumeration
 * at (3, 4) inside (5, 9): every predicate and operand order against
 * sampled wide constants (all specials, every exponent-field boundary of
 * both signs, a deterministic random fill) on all 2^7 operand values; the
 * both-widened form on all operand pairs under several rounding modes; a
 * firing check and a no-fire gate check.
 */

#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>
#include <vector>

using namespace stp;

namespace
{

const unsigned TE = 3, TS = 4, SE = 5, SS = 9;
const unsigned TW = TE + TS, SW = SE + SS;

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* hf;

  Context() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;
    mgr.defaultNodeFactory = &snf;
    hf = mgr.hashingNodeFactory;
  }

  ASTNode rm(unsigned mode = symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN)
  {
    return mgr.CreateRMConst(mode);
  }

  ASTNode widen(NodeFactory* nf, const ASTNode& x, const ASTNode& mode)
  {
    return nf->CreateTerm(FP_TOFP, SW,
                          ASTVec{mgr.CreateBVConst(32, SE),
                                 mgr.CreateBVConst(32, SS), mode, x});
  }

  ASTNode fpc(unsigned bits, unsigned eb, unsigned sb)
  {
    return mgr.CreateFPConst(mgr.CreateBVConst(eb + sb, bits), eb, sb);
  }

  ASTNode eval(const ASTNode& n, const ASTNode& sym, const ASTNode& value)
  {
    ASTNodeMap assignment;
    assignment.insert({sym, value});
    ASTNodeMap cache;
    ASTNode s = SubstitutionMap::replace(n, assignment, cache, &snf);
    if (s.isConstant())
      return s;
    return NonMemberBVConstEvaluator(&mgr, s);
  }

  bool contains(Kind k, const ASTNode& n)
  {
    if (n.GetKind() == k)
      return true;
    for (const auto& c : n)
      if (contains(k, c))
        return true;
    return false;
  }
};

std::vector<unsigned> constantSample()
{
  std::vector<unsigned> cs;
  // Every exponent-field boundary of both signs: the significand all-zero
  // and all-one patterns cover the powers of two, the subnormal edges, the
  // infinities and a NaN.
  for (unsigned sign = 0; sign < 2; sign++)
    for (unsigned exp = 0; exp < (1u << SE); exp++)
    {
      const unsigned base = (sign << (SW - 1)) | (exp << (SS - 1));
      cs.push_back(base);
      cs.push_back(base | ((1u << (SS - 1)) - 1));
    }
  unsigned lcg = 99991;
  for (int i = 0; i < 200; i++)
  {
    lcg = lcg * 1103515245 + 12345;
    cs.push_back(lcg % (1u << SW));
  }
  return cs;
}

TEST(NarrowWidenedFPComparison, constant_side_exhaustive)
{
  Context c;
  const ASTNode x =
      c.mgr.CreateSourceSymbol("x", SourceSort::floatingPoint(TE, TS));

  const Kind kinds[] = {FP_GT, FP_GEQ, FP_LT, FP_LEQ};
  unsigned fired = 0, total = 0;

  for (const unsigned cbits : constantSample())
  {
    const ASTNode wide = c.fpc(cbits, SE, SS);
    for (const Kind k : kinds)
      for (int constLeft = 0; constLeft < 2; constLeft++)
      {
        // Original meaning, built without simplification.
        const ASTNode xw = c.widen(c.hf, x, c.rm());
        const ASTNode original =
            constLeft ? c.hf->CreateNode(k, wide, xw)
                      : c.hf->CreateNode(k, xw, wide);
        // What the simplifying factory makes of it.
        const ASTNode xs = c.widen(&c.snf, x, c.rm());
        const ASTNode simplified =
            constLeft ? c.snf.CreateNode(k, wide, xs)
                      : c.snf.CreateNode(k, xs, wide);

        total++;
        if (!c.contains(FP_TOFP, simplified))
          fired++;

        for (unsigned xv = 0; xv < (1u << TW); xv++)
        {
          const ASTNode value = c.fpc(xv, TE, TS);
          ASSERT_EQ(c.eval(original, x, value),
                    c.eval(simplified, x, value))
              << "kind " << k << " constLeft " << constLeft << " c=" << cbits
              << " x=" << xv;
        }
      }
  }

  // Require broad firing rather than an exact count (NaN constants fold
  // to false outright and never carry a conversion).
  EXPECT_GT(fired, total / 2)
      << "the narrowing fired on too few comparisons";
}

TEST(NarrowWidenedFPComparison, both_widened_exhaustive)
{
  Context c;
  const ASTNode x =
      c.mgr.CreateSourceSymbol("x", SourceSort::floatingPoint(TE, TS));
  const ASTNode y =
      c.mgr.CreateSourceSymbol("y", SourceSort::floatingPoint(TE, TS));

  const unsigned modes[] = {symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN,
                            symbolic_fp::ROUND_TOWARD_ZERO};
  for (const unsigned m : modes)
    for (const Kind k : {FP_GT, FP_GEQ})
    {
      const ASTNode original = c.hf->CreateNode(
          k, c.widen(c.hf, x, c.rm(m)), c.widen(c.hf, y, c.rm()));
      const ASTNode simplified = c.snf.CreateNode(
          k, c.widen(&c.snf, x, c.rm(m)), c.widen(&c.snf, y, c.rm()));
      EXPECT_FALSE(c.contains(FP_TOFP, simplified));

      for (unsigned xv = 0; xv < (1u << TW); xv++)
      {
        ASTNodeMap assignment;
        assignment.insert({x, c.fpc(xv, TE, TS)});
        for (unsigned yv = 0; yv < (1u << TW); yv++)
        {
          ASTNodeMap a = assignment;
          a.insert({y, c.fpc(yv, TE, TS)});
          ASTNodeMap a2 = a;
          ASTNodeMap cache, cache2;
          ASTNode o = SubstitutionMap::replace(original, a, cache, &c.snf);
          ASTNode s = SubstitutionMap::replace(simplified, a2, cache2, &c.snf);
          if (!o.isConstant())
            o = NonMemberBVConstEvaluator(&c.mgr, o);
          if (!s.isConstant())
            s = NonMemberBVConstEvaluator(&c.mgr, s);
          ASSERT_EQ(o, s) << "kind " << k << " mode " << m << " x=" << xv
                          << " y=" << yv;
        }
      }
    }
}

// Directed narrowing of every wide constant, held to the defining property
// of the directed rounding -- downward: r <= c < nextUp(r), mirrored
// upward -- using exact widenings and constant comparisons, with the
// neighbour computed here from the packed bits as an independent oracle.
// The rewrite trusts these folds at runtime (plus assertion-build checks),
// so this test is what holds the narrowing conversion to account; the
// format pairs include exponent-shrinking targets down to a two-bit
// exponent, the class symfpu once mis-rounded (vendored patch 0001).
TEST(NarrowWidenedFPComparison, directed_narrowing_property)
{
  Context c;
  struct FormatPair
  {
    unsigned se, ss, te, ts;
  };
  const FormatPair pairs[] = {
      {5, 9, 3, 4}, {4, 6, 3, 4}, {5, 9, 4, 6}, {4, 11, 2, 5}, {6, 6, 3, 5},
      {4, 9, 3, 8}};

  for (const FormatPair& p : pairs)
  {
    const unsigned sw = p.se + p.ss, tw = p.te + p.ts;
    const unsigned signBit = 1u << (tw - 1);
    const auto isNaNBits = [&](unsigned bits, unsigned eb, unsigned sb) {
      const unsigned expMask = ((1u << eb) - 1) << (sb - 1);
      const unsigned sigMask = (1u << (sb - 1)) - 1;
      return (bits & expMask) == expMask && (bits & sigMask) != 0;
    };
    // The neighbouring value by packed-bit stepping (see fpConstAdjacent).
    const auto adjacentBits = [&](unsigned bits, bool up) {
      if ((bits & ~signBit) == 0) // a zero
        return up ? 1u : (signBit | 1u);
      const bool negative = (bits & signBit) != 0;
      return (up != negative) ? bits + 1 : bits - 1;
    };

    const auto widenBack = [&](const ASTNode& v) {
      return c.snf.CreateTerm(
          FP_TOFP, sw,
          ASTVec{c.mgr.CreateBVConst(32, p.se), c.mgr.CreateBVConst(32, p.ss),
                 c.rm(), v});
    };

    for (unsigned bits = 0; bits < (1u << sw); bits++)
    {
      if (isNaNBits(bits, p.se, p.ss))
        continue;
      const ASTNode wide = c.fpc(bits, p.se, p.ss);
      for (int up = 0; up < 2; up++)
      {
        const ASTNode narrow = c.snf.CreateTerm(
            FP_TOFP, tw,
            ASTVec{c.mgr.CreateBVConst(32, p.te),
                   c.mgr.CreateBVConst(32, p.ts),
                   c.rm(up ? symbolic_fp::ROUND_TOWARD_POSITIVE
                           : symbolic_fp::ROUND_TOWARD_NEGATIVE),
                   wide});
        ASSERT_EQ(BVCONST, narrow.GetKind())
            << "conversion did not fold: pair (" << p.se << "," << p.ss
            << ")->(" << p.te << "," << p.ts << ") bits=" << bits;
        const unsigned rBits = (unsigned)narrow.GetUnsignedConst();
        ASSERT_FALSE(isNaNBits(rBits, p.te, p.ts))
            << "finite value narrowed to NaN at bits=" << bits;

        // An exact representation is its own rounding both ways and has
        // no neighbour to test against.
        const ASTNode w = widenBack(narrow);
        if (w == wide)
          continue;

        // On the correct side of the wide value...
        const ASTNode side = up ? c.snf.CreateNode(FP_GEQ, w, wide)
                                : c.snf.CreateNode(FP_GEQ, wide, w);
        ASSERT_EQ(TRUE, side.GetKind())
            << "wrong side: pair (" << p.se << "," << p.ss << ")->(" << p.te
            << "," << p.ts << ") bits=" << bits << " up=" << up;

        // ...with no narrow value strictly between them.
        const ASTNode adjacent =
            c.fpc(adjacentBits(rBits, !up), p.te, p.ts);
        const ASTNode wa = widenBack(adjacent);
        const ASTNode tight = up ? c.snf.CreateNode(FP_GT, wide, wa)
                                 : c.snf.CreateNode(FP_GT, wa, wide);
        ASSERT_EQ(TRUE, tight.GetKind())
            << "not adjacent: pair (" << p.se << "," << p.ss << ")->(" << p.te
            << "," << p.ts << ") bits=" << bits << " up=" << up;
      }
    }
  }
}

// Known-value regressions for the float-to-float conversion defect the
// vendored symfpu patch 0001 fixes (issue #782): a conversion into a
// format whose unpacked exponent is not narrower was misclassified as a
// strict promotion and returned unrounded and unclamped. Every expected
// value below is computed by hand from the IEEE definitions; against an
// unpatched symfpu the tie and overflow rows fold to the wrong constants.
TEST(NarrowWidenedFPComparison, conversion_folds_known_values)
{
  Context c;
  struct Row
  {
    unsigned se, ss, inBits;
    unsigned te, ts;
    unsigned mode;
    unsigned expectBits;
  };
  const Row rows[] = {
      // 3/32 from (3,4) into (2,5) is the exact midpoint of the target
      // subnormals 1/16 and 2/16.
      {3, 4, 3, 2, 5, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN, 2},
      {3, 4, 3, 2, 5, symbolic_fp::ROUND_TOWARD_POSITIVE, 2},
      {3, 4, 3, 2, 5, symbolic_fp::ROUND_TOWARD_NEGATIVE, 1},
      {3, 4, 3, 2, 5, symbolic_fp::ROUND_TOWARD_ZERO, 1},
      // 2^5 from (4,4) overflows (3,7), whose largest finite is under 16:
      // to the infinity nearest-to-even and toward +oo, to the largest
      // finite toward zero.
      {4, 4, 96, 3, 7, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN, 448},
      {4, 4, 96, 3, 7, symbolic_fp::ROUND_TOWARD_POSITIVE, 448},
      {4, 4, 96, 3, 7, symbolic_fp::ROUND_TOWARD_ZERO, 447},
  };
  for (const Row& r : rows)
  {
    const ASTNode wide = c.fpc(r.inBits, r.se, r.ss);
    const ASTNode narrow = c.snf.CreateTerm(
        FP_TOFP, r.te + r.ts,
        ASTVec{c.mgr.CreateBVConst(32, r.te), c.mgr.CreateBVConst(32, r.ts),
               c.rm(r.mode), wide});
    ASSERT_EQ(BVCONST, narrow.GetKind());
    EXPECT_EQ(r.expectBits, (unsigned)narrow.GetUnsignedConst())
        << "(" << r.se << "," << r.ss << ") bits=" << r.inBits << " -> ("
        << r.te << "," << r.ts << ") mode=" << r.mode;
  }
}

TEST(NarrowWidenedFPComparison, gates_hold)
{
  Context c;
  // A narrowing conversion is not a widening: the comparison keeps it.
  const ASTNode wide_operand =
      c.mgr.CreateSourceSymbol("w", SourceSort::floatingPoint(SE, SS));
  const ASTNode shrink = c.hf->CreateTerm(
      FP_TOFP, TW,
      ASTVec{c.mgr.CreateBVConst(32, TE), c.mgr.CreateBVConst(32, TS),
             c.rm(), wide_operand});
  const ASTNode narrow_const = c.fpc(0x15, TE, TS);
  const ASTNode kept =
      c.snf.CreateNode(FP_GT, shrink, narrow_const);
  EXPECT_TRUE(c.contains(FP_TOFP, kept));
}

} // namespace

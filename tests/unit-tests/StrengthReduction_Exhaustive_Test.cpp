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
 * Checks that strength reduction extracts all of the information the
 * domains provide, and nothing more:
 *
 * 1) When an interval / the fixed bits determine a node completely, the
 *    node is replaced by exactly that constant; when they don't, the node
 *    is left alone. This is checked exhaustively at small bit-widths.
 *
 * 2) When the domains justify a reduction (signed -> unsigned division,
 *    comparison, shift; plus -> or; sign-extension -> concat), the reduced
 *    node is checked, by enumerating every assignment that's consistent
 *    with the domain, to be equivalent to the original.
 */

#include "stp/cpp_interface.h"
#include "stp/Parser/parser.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/StrengthReduction.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include <gtest/gtest.h>

using simplifier::constantBitP::FixedBits;

static stp::CBV makeCBV(unsigned width, unsigned value)
{
  stp::CBV result = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width; i++)
    if ((value >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(result, i);
  return result;
}

// Fix just the most significant bit.
static FixedBits msbFixed(unsigned width, bool value)
{
  FixedBits result(width, false);
  result.setFixed(width - 1, true);
  result.setValue(width - 1, value);
  return result;
}

struct Context
{
  stp::STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* nf; // base-class pointer, for the convenience overloads.
  stp::StrengthReduction sr;

  Context() : snf(*(mgr.hashingNodeFactory), mgr), sr(&snf, &mgr.UserFlags)
  {
    mgr.defaultNodeFactory = &snf;
    nf = &snf;
  }

  ASTNode symbol(const char* name, unsigned width)
  {
    return mgr.CreateSymbol(name, 0, width);
  }

  ASTNode constant(unsigned width, unsigned value)
  {
    return mgr.CreateBVConst(width, value);
  }

  bool present(const stp::Kind k, const ASTNode& n)
  {
    if (n.GetKind() == k)
      return true;

    for (const auto& c : n)
      if (present(k, c))
        return true;

    return false;
  }

  // Evaluate "n" with the symbols replaced by the constants in "assignment".
  ASTNode eval(const ASTNode& n, stp::ASTNodeMap assignment)
  {
    stp::ASTNodeMap cache;
    ASTNode substituted =
        stp::SubstitutionMap::replace(n, assignment, cache, &snf);
    if (substituted.isConstant())
      return substituted;
    return stp::NonMemberBVConstEvaluator(&mgr, substituted);
  }

  // Check that "before" and "after" agree on every assignment of x and y
  // that the predicates accept.
  template <typename XOk, typename YOk>
  void checkEquivalent(const ASTNode& before, const ASTNode& after,
                       const ASTNode& x, const ASTNode& y, unsigned width,
                       XOk xOk, YOk yOk)
  {
    for (unsigned xv = 0; xv < (1u << width); xv++)
    {
      if (!xOk(xv))
        continue;
      for (unsigned yv = 0; yv < (1u << width); yv++)
      {
        if (!yOk(yv))
          continue;
        stp::ASTNodeMap assignment;
        assignment.insert({x, constant(width, xv)});
        assignment.insert({y, constant(width, yv)});
        ASSERT_EQ(eval(before, assignment), eval(after, assignment))
            << "differ on x=" << xv << " y=" << yv;
      }
    }
  }
};

/////////////////////////////////////////////////////////////////////////////
// A node is replaced by a constant if, and only if, the domain has narrowed
// it to a single value. Exhaustive over the domain at a small width.
/////////////////////////////////////////////////////////////////////////////

// Every point interval becomes exactly that constant; every wider interval
// leaves the node untouched.
TEST(StrengthReduction_Exhaustive_Test, interval_narrows_iff_constant)
{
  CONSTANTBV::BitVector_Boot();
  Context c;

  const unsigned width = 3;
  ASTNode x = c.symbol("x", width);

  for (unsigned lo = 0; lo < (1u << width); lo++)
    for (unsigned hi = lo; hi < (1u << width); hi++)
    {
      stp::UnsignedInterval interval(makeCBV(width, lo), makeCBV(width, hi));
      stp::NodeToUnsignedIntervalMap map;
      map.insert({x, &interval});

      ASTNode result = c.sr.topLevel(x, map);

      if (lo == hi)
        ASSERT_EQ(result, c.constant(width, lo));
      else
        ASSERT_EQ(result, x);
    }
}

// Every one of the 3^width fixings {0,1,*}^width is either totally fixed
// (and becomes exactly that constant), or leaves the node untouched.
TEST(StrengthReduction_Exhaustive_Test, fixedbits_narrow_iff_totally_fixed)
{
  Context c;

  const unsigned width = 3;
  ASTNode x = c.symbol("x", width);

  unsigned patterns = 1;
  for (unsigned i = 0; i < width; i++)
    patterns *= 3;

  for (unsigned p = 0; p < patterns; p++)
  {
    FixedBits bits(width, false);
    unsigned value = 0;
    bool totallyFixed = true;

    unsigned rest = p;
    for (unsigned i = 0; i < width; i++)
    {
      const unsigned digit = rest % 3; // 0: fixed zero, 1: fixed one, 2: unfixed
      rest /= 3;
      if (digit == 2)
      {
        totallyFixed = false;
        continue;
      }
      bits.setFixed(i, true);
      bits.setValue(i, digit == 1);
      value |= (digit << i);
    }

    stp::NodeToFixedBitsMap map;
    map.insert({x, &bits});

    ASTNode result = c.sr.topLevel(x, map);

    if (totallyFixed)
      ASSERT_EQ(result, c.constant(width, value));
    else
      ASSERT_EQ(result, x);
  }
}

// A boolean node whose interval is a point becomes true/false.
TEST(StrengthReduction_Exhaustive_Test, interval_narrows_boolean)
{
  for (unsigned value = 0; value <= 1; value++)
  {
    Context c;
    ASTNode x = c.symbol("x", 3);
    ASTNode y = c.symbol("y", 3);
    ASTNode n = c.nf->CreateNode(stp::BVGT, x, y);

    stp::UnsignedInterval interval(makeCBV(1, value), makeCBV(1, value));
    stp::NodeToUnsignedIntervalMap map;
    map.insert({n, &interval});

    ASTNode result = c.sr.topLevel(n, map);
    ASSERT_EQ(result, value == 1 ? c.mgr.ASTTrue : c.mgr.ASTFalse);
  }
}

// A boolean node whose bit is fixed becomes true/false.
TEST(StrengthReduction_Exhaustive_Test, fixedbits_narrow_boolean)
{
  for (unsigned value = 0; value <= 1; value++)
  {
    Context c;
    ASTNode x = c.symbol("x", 3);
    ASTNode y = c.symbol("y", 3);
    ASTNode n = c.nf->CreateNode(stp::BVGT, x, y);

    FixedBits bits(1, true);
    bits.setFixed(0, true);
    bits.setValue(0, value == 1);

    stp::NodeToFixedBitsMap map;
    map.insert({n, &bits});

    ASTNode result = c.sr.topLevel(n, map);
    ASSERT_EQ(result, value == 1 ? c.mgr.ASTTrue : c.mgr.ASTFalse);
  }
}

/////////////////////////////////////////////////////////////////////////////
// When the domains justify a reduction, the reduction is applied, and the
// reduced node agrees with the original on every consistent assignment.
/////////////////////////////////////////////////////////////////////////////

// bvsgt reduces to bvugt when the fixed bits give both operands the same
// sign. Equivalent for every assignment with those signs.
TEST(StrengthReduction_Exhaustive_Test, sgt_to_ugt_via_fixedbits)
{
  const unsigned width = 3;

  for (unsigned sign = 0; sign <= 1; sign++)
  {
    Context c;
    ASTNode x = c.symbol("x", width);
    ASTNode y = c.symbol("y", width);
    ASTNode n = c.nf->CreateNode(stp::BVSGT, x, y);
    ASSERT_EQ(n.GetKind(), stp::BVSGT);

    FixedBits xBits = msbFixed(width, sign == 1);
    FixedBits yBits = msbFixed(width, sign == 1);

    stp::NodeToFixedBitsMap map;
    map.insert({n, nullptr});
    map.insert({x, &xBits});
    map.insert({y, &yBits});

    ASTNode result = c.sr.topLevel(n, map);
    ASSERT_FALSE(c.present(stp::BVSGT, result));
    ASSERT_TRUE(c.present(stp::BVGT, result));

    auto consistent = [sign, width](unsigned v) {
      return ((v >> (width - 1)) & 1) == sign;
    };
    c.checkEquivalent(n, result, x, y, width, consistent, consistent);
  }
}

// bvsgt reduces to bvugt when both intervals exclude the top bit.
// Equivalent for every assignment inside the intervals.
TEST(StrengthReduction_Exhaustive_Test, sgt_to_ugt_via_intervals)
{
  const unsigned width = 3;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode y = c.symbol("y", width);
  ASTNode n = c.nf->CreateNode(stp::BVSGT, x, y);
  ASSERT_EQ(n.GetKind(), stp::BVSGT);

  stp::UnsignedInterval xInterval(makeCBV(width, 0), makeCBV(width, 3));
  stp::UnsignedInterval yInterval(makeCBV(width, 1), makeCBV(width, 2));

  stp::NodeToUnsignedIntervalMap map;
  map.insert({n, nullptr});
  map.insert({x, &xInterval});
  map.insert({y, &yInterval});

  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_FALSE(c.present(stp::BVSGT, result));
  ASSERT_TRUE(c.present(stp::BVGT, result));

  c.checkEquivalent(
      n, result, x, y, width, [](unsigned v) { return v <= 3; },
      [](unsigned v) { return v >= 1 && v <= 2; });
}

// bvsdiv reduces to bvudiv (with negations) once both sign bits are fixed,
// for all four sign combinations. Equivalent for every consistent
// assignment, including division by zero.
TEST(StrengthReduction_Exhaustive_Test, sdiv_to_udiv_via_fixedbits)
{
  const unsigned width = 3;

  for (unsigned xSign = 0; xSign <= 1; xSign++)
    for (unsigned ySign = 0; ySign <= 1; ySign++)
    {
      Context c;
      ASTNode x = c.symbol("x", width);
      ASTNode y = c.symbol("y", width);
      ASTNode n = c.nf->CreateTerm(stp::SBVDIV, width, x, y);
      ASSERT_EQ(n.GetKind(), stp::SBVDIV);

      FixedBits xBits = msbFixed(width, xSign == 1);
      FixedBits yBits = msbFixed(width, ySign == 1);

      stp::NodeToFixedBitsMap map;
      map.insert({n, nullptr});
      map.insert({x, &xBits});
      map.insert({y, &yBits});

      ASTNode result = c.sr.topLevel(n, map);
      ASSERT_FALSE(c.present(stp::SBVDIV, result));
      ASSERT_TRUE(c.present(stp::BVDIV, result));

      c.checkEquivalent(
          n, result, x, y, width,
          [xSign, width](unsigned v) {
            return ((v >> (width - 1)) & 1) == xSign;
          },
          [ySign, width](unsigned v) {
            return ((v >> (width - 1)) & 1) == ySign;
          });
    }
}

// bvsrem reduces to bvurem (with negations) once both sign bits are fixed.
TEST(StrengthReduction_Exhaustive_Test, srem_to_urem_via_fixedbits)
{
  const unsigned width = 3;

  for (unsigned xSign = 0; xSign <= 1; xSign++)
    for (unsigned ySign = 0; ySign <= 1; ySign++)
    {
      Context c;
      ASTNode x = c.symbol("x", width);
      ASTNode y = c.symbol("y", width);
      ASTNode n = c.nf->CreateTerm(stp::SBVREM, width, x, y);
      ASSERT_EQ(n.GetKind(), stp::SBVREM);

      FixedBits xBits = msbFixed(width, xSign == 1);
      FixedBits yBits = msbFixed(width, ySign == 1);

      stp::NodeToFixedBitsMap map;
      map.insert({n, nullptr});
      map.insert({x, &xBits});
      map.insert({y, &yBits});

      ASTNode result = c.sr.topLevel(n, map);
      ASSERT_FALSE(c.present(stp::SBVREM, result));
      ASSERT_TRUE(c.present(stp::BVMOD, result));

      c.checkEquivalent(
          n, result, x, y, width,
          [xSign, width](unsigned v) {
            return ((v >> (width - 1)) & 1) == xSign;
          },
          [ySign, width](unsigned v) {
            return ((v >> (width - 1)) & 1) == ySign;
          });
    }
}

// bvsge reduces to bvuge when the fixed bits give both operands the same
// sign. The node is built with the hashing factory because the
// simplifying factory rewrites bvsge on creation.
TEST(StrengthReduction_Exhaustive_Test, sge_to_uge_via_fixedbits)
{
  const unsigned width = 3;

  for (unsigned sign = 0; sign <= 1; sign++)
  {
    Context c;
    ASTNode x = c.symbol("x", width);
    ASTNode y = c.symbol("y", width);
    ASTNode n =
        c.mgr.hashingNodeFactory->CreateNode(stp::BVSGE, stp::ASTVec{x, y});
    ASSERT_EQ(n.GetKind(), stp::BVSGE);

    FixedBits xBits = msbFixed(width, sign == 1);
    FixedBits yBits = msbFixed(width, sign == 1);

    stp::NodeToFixedBitsMap map;
    map.insert({n, nullptr});
    map.insert({x, &xBits});
    map.insert({y, &yBits});

    // The created BVGE is rewritten to NOT(BVGT ...) by the simplifying
    // factory, so check for the BVGT.
    ASTNode result = c.sr.topLevel(n, map);
    ASSERT_FALSE(c.present(stp::BVSGE, result));
    ASSERT_FALSE(c.present(stp::BVSGT, result));
    ASSERT_TRUE(c.present(stp::BVGT, result));

    auto consistent = [sign, width](unsigned v) {
      return ((v >> (width - 1)) & 1) == sign;
    };
    c.checkEquivalent(n, result, x, y, width, consistent, consistent);
  }
}

// bvsmod reduces to bvurem (with negations, and an adjustment when the
// signs differ) once both sign bits are fixed. Equivalent for every
// consistent assignment, including remainder by zero.
TEST(StrengthReduction_Exhaustive_Test, smod_to_urem_via_fixedbits)
{
  const unsigned width = 3;

  for (unsigned xSign = 0; xSign <= 1; xSign++)
    for (unsigned ySign = 0; ySign <= 1; ySign++)
    {
      Context c;
      ASTNode x = c.symbol("x", width);
      ASTNode y = c.symbol("y", width);
      ASTNode n = c.nf->CreateTerm(stp::SBVMOD, width, x, y);
      ASSERT_EQ(n.GetKind(), stp::SBVMOD);

      FixedBits xBits = msbFixed(width, xSign == 1);
      FixedBits yBits = msbFixed(width, ySign == 1);

      stp::NodeToFixedBitsMap map;
      map.insert({n, nullptr});
      map.insert({x, &xBits});
      map.insert({y, &yBits});

      ASTNode result = c.sr.topLevel(n, map);
      ASSERT_FALSE(c.present(stp::SBVMOD, result));
      ASSERT_TRUE(c.present(stp::BVMOD, result));

      c.checkEquivalent(
          n, result, x, y, width,
          [xSign, width](unsigned v) {
            return ((v >> (width - 1)) & 1) == xSign;
          },
          [ySign, width](unsigned v) {
            return ((v >> (width - 1)) & 1) == ySign;
          });
    }
}

// bvsmod reduces to bvurem when both intervals exclude the top bit.
TEST(StrengthReduction_Exhaustive_Test, smod_to_urem_via_intervals)
{
  const unsigned width = 3;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode y = c.symbol("y", width);
  ASTNode n = c.nf->CreateTerm(stp::SBVMOD, width, x, y);
  ASSERT_EQ(n.GetKind(), stp::SBVMOD);

  // y's interval includes zero, checking remainder by zero as well.
  stp::UnsignedInterval xInterval(makeCBV(width, 0), makeCBV(width, 3));
  stp::UnsignedInterval yInterval(makeCBV(width, 0), makeCBV(width, 3));

  stp::NodeToUnsignedIntervalMap map;
  map.insert({n, nullptr});
  map.insert({x, &xInterval});
  map.insert({y, &yInterval});

  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_FALSE(c.present(stp::SBVMOD, result));
  ASSERT_TRUE(c.present(stp::BVMOD, result));

  c.checkEquivalent(
      n, result, x, y, width, [](unsigned v) { return v <= 3; },
      [](unsigned v) { return v <= 3; });
}

// bvadd reduces to bvor when the fixed bits show the operands can't both
// have a one in any position (no carries are possible).
TEST(StrengthReduction_Exhaustive_Test, plus_to_or_via_fixedbits)
{
  const unsigned width = 4;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode y = c.symbol("y", width);
  ASTNode n = c.nf->CreateTerm(stp::BVPLUS, width, x, y);
  ASSERT_EQ(n.GetKind(), stp::BVPLUS);

  // x's high half is zero, y's low half is zero.
  FixedBits xBits(width, false);
  xBits.setFixed(2, true);
  xBits.setValue(2, false);
  xBits.setFixed(3, true);
  xBits.setValue(3, false);

  FixedBits yBits(width, false);
  yBits.setFixed(0, true);
  yBits.setValue(0, false);
  yBits.setFixed(1, true);
  yBits.setValue(1, false);

  stp::NodeToFixedBitsMap map;
  map.insert({n, nullptr});
  map.insert({x, &xBits});
  map.insert({y, &yBits});

  // The SimplifyingNodeFactory rewrites the created BVOR into
  // BVNOT(BVAND(BVNOT ...)), so check the plus is gone, not that an OR
  // appears.
  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_FALSE(c.present(stp::BVPLUS, result));
  ASSERT_NE(result, n);

  c.checkEquivalent(
      n, result, x, y, width, [](unsigned v) { return v <= 3; },
      [](unsigned v) { return (v & 3) == 0; });
}

// bvxor reduces to bvor under the same disjointness condition.
TEST(StrengthReduction_Exhaustive_Test, xor_to_or_via_fixedbits)
{
  const unsigned width = 4;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode y = c.symbol("y", width);
  ASTNode n = c.nf->CreateTerm(stp::BVXOR, width, x, y);
  ASSERT_EQ(n.GetKind(), stp::BVXOR);

  FixedBits xBits(width, false);
  xBits.setFixed(2, true);
  xBits.setValue(2, false);
  xBits.setFixed(3, true);
  xBits.setValue(3, false);

  FixedBits yBits(width, false);
  yBits.setFixed(0, true);
  yBits.setValue(0, false);
  yBits.setFixed(1, true);
  yBits.setValue(1, false);

  stp::NodeToFixedBitsMap map;
  map.insert({n, nullptr});
  map.insert({x, &xBits});
  map.insert({y, &yBits});

  // As above, the created BVOR is rewritten by the node factory, so just
  // check the xor is gone.
  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_FALSE(c.present(stp::BVXOR, result));
  ASSERT_NE(result, n);

  c.checkEquivalent(
      n, result, x, y, width, [](unsigned v) { return v <= 3; },
      [](unsigned v) { return (v & 3) == 0; });
}

// bvashr reduces to bvlshr when the interval keeps the value non-negative.
TEST(StrengthReduction_Exhaustive_Test, ashr_to_lshr_via_interval)
{
  const unsigned width = 3;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode y = c.symbol("y", width);
  ASTNode n = c.nf->CreateTerm(stp::BVSRSHIFT, width, x, y);
  ASSERT_EQ(n.GetKind(), stp::BVSRSHIFT);

  stp::UnsignedInterval xInterval(makeCBV(width, 0), makeCBV(width, 3));

  stp::NodeToUnsignedIntervalMap map;
  map.insert({n, nullptr});
  map.insert({x, &xInterval});

  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_FALSE(c.present(stp::BVSRSHIFT, result));
  ASSERT_TRUE(c.present(stp::BVRIGHTSHIFT, result));

  c.checkEquivalent(
      n, result, x, y, width, [](unsigned v) { return v <= 3; },
      [](unsigned) { return true; });
}

// bvashr reduces to bvlshr when the shift's own top bit is fixed to zero.
TEST(StrengthReduction_Exhaustive_Test, ashr_to_lshr_via_fixedbits)
{
  const unsigned width = 3;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode y = c.symbol("y", width);
  ASTNode n = c.nf->CreateTerm(stp::BVSRSHIFT, width, x, y);
  ASSERT_EQ(n.GetKind(), stp::BVSRSHIFT);

  FixedBits nBits = msbFixed(width, false);

  stp::NodeToFixedBitsMap map;
  map.insert({n, &nBits});

  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_FALSE(c.present(stp::BVSRSHIFT, result));
  ASSERT_TRUE(c.present(stp::BVRIGHTSHIFT, result));

  // The result's top bit is zero exactly when x is non-negative.
  c.checkEquivalent(
      n, result, x, y, width, [](unsigned v) { return v <= 3; },
      [](unsigned) { return true; });
}

// Sign-extension becomes a concat with zeroes when the interval keeps the
// operand non-negative.
TEST(StrengthReduction_Exhaustive_Test, bvsx_to_zero_concat_via_interval)
{
  const unsigned width = 3;
  const unsigned extendedWidth = 6;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode n = c.nf->CreateTerm(stp::BVSX, extendedWidth, x,
                               c.mgr.CreateBVConst(32, extendedWidth));
  ASSERT_EQ(n.GetKind(), stp::BVSX);

  stp::UnsignedInterval xInterval(makeCBV(width, 0), makeCBV(width, 3));

  stp::NodeToUnsignedIntervalMap map;
  map.insert({n, nullptr});
  map.insert({x, &xInterval});

  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_FALSE(c.present(stp::BVSX, result));

  for (unsigned xv = 0; xv <= 3; xv++)
  {
    stp::ASTNodeMap assignment;
    assignment.insert({x, c.constant(width, xv)});
    stp::ASTNodeMap copy = assignment;
    ASSERT_EQ(c.eval(n, assignment), c.eval(result, copy));
  }
}

// Sign-extension becomes a concat with ones when its own top bit is fixed
// to one.
TEST(StrengthReduction_Exhaustive_Test, bvsx_to_ones_concat_via_fixedbits)
{
  const unsigned width = 3;
  const unsigned extendedWidth = 6;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode n = c.nf->CreateTerm(stp::BVSX, extendedWidth, x,
                               c.mgr.CreateBVConst(32, extendedWidth));
  ASSERT_EQ(n.GetKind(), stp::BVSX);

  FixedBits nBits = msbFixed(extendedWidth, true);

  stp::NodeToFixedBitsMap map;
  map.insert({n, &nBits});

  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_FALSE(c.present(stp::BVSX, result));

  // The extension's top bit is one exactly when x is negative.
  for (unsigned xv = 4; xv <= 7; xv++)
  {
    stp::ASTNodeMap assignment;
    assignment.insert({x, c.constant(width, xv)});
    stp::ASTNodeMap copy = assignment;
    ASSERT_EQ(c.eval(n, assignment), c.eval(result, copy));
  }
}

// A division whose dividend has fixed leading zero bits narrows to the
// remaining width, guarded on the divisor's leading bits. The divisor
// must be provably non-zero.
TEST(StrengthReduction_Exhaustive_Test, div_narrowed_via_fixedbits)
{
  const unsigned width = 4;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode y = c.symbol("y", width);
  ASTNode n = c.nf->CreateTerm(stp::BVDIV, width, x, y);
  ASSERT_EQ(n.GetKind(), stp::BVDIV);

  // x: the top two bits are fixed zero. y: the lowest bit is fixed one.
  FixedBits xBits(width, false);
  xBits.setFixed(3, true);
  xBits.setValue(3, false);
  xBits.setFixed(2, true);
  xBits.setValue(2, false);
  FixedBits yBits(width, false);
  yBits.setFixed(0, true);
  yBits.setValue(0, true);

  stp::NodeToFixedBitsMap map;
  map.insert({n, nullptr});
  map.insert({x, &xBits});
  map.insert({y, &yBits});

  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_EQ(result.GetKind(), stp::ITE);
  ASSERT_FALSE(c.present(stp::BVDIV, result[2]));

  c.checkEquivalent(
      n, result, x, y, width, [](unsigned v) { return v < 4; },
      [](unsigned v) { return (v & 1) == 1; });
}

// The remainder version narrows without needing a non-zero divisor: a
// remainder by zero is the dividend, which the untaken branch recreates.
TEST(StrengthReduction_Exhaustive_Test, mod_narrowed_via_fixedbits)
{
  const unsigned width = 4;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode y = c.symbol("y", width);
  ASTNode n = c.nf->CreateTerm(stp::BVMOD, width, x, y);
  ASSERT_EQ(n.GetKind(), stp::BVMOD);

  FixedBits xBits(width, false);
  xBits.setFixed(3, true);
  xBits.setValue(3, false);
  xBits.setFixed(2, true);
  xBits.setValue(2, false);
  FixedBits yBits(width, false);

  stp::NodeToFixedBitsMap map;
  map.insert({n, nullptr});
  map.insert({x, &xBits});
  map.insert({y, &yBits});

  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_EQ(result.GetKind(), stp::ITE);
  ASSERT_EQ(result[2], x);

  c.checkEquivalent(
      n, result, x, y, width, [](unsigned v) { return v < 4; },
      [](unsigned) { return true; });
}

// Division is left alone when the divisor might be zero.
TEST(StrengthReduction_Exhaustive_Test, div_not_narrowed_when_divisor_may_be_zero)
{
  const unsigned width = 4;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode y = c.symbol("y", width);
  ASTNode n = c.nf->CreateTerm(stp::BVDIV, width, x, y);

  FixedBits xBits(width, false);
  xBits.setFixed(3, true);
  xBits.setValue(3, false);
  FixedBits yBits(width, false);

  stp::NodeToFixedBitsMap map;
  map.insert({n, nullptr});
  map.insert({x, &xBits});
  map.insert({y, &yBits});

  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_EQ(result, n);
}

// A remainder whose dividend's interval sits below the divisor's is the
// dividend.
TEST(StrengthReduction_Exhaustive_Test, mod_below_divisor_via_intervals)
{
  const unsigned width = 4;

  Context c;
  ASTNode x = c.symbol("x", width);
  ASTNode y = c.symbol("y", width);
  ASTNode n = c.nf->CreateTerm(stp::BVMOD, width, x, y);
  ASSERT_EQ(n.GetKind(), stp::BVMOD);

  stp::UnsignedInterval xInterval(makeCBV(width, 0), makeCBV(width, 4));
  stp::UnsignedInterval yInterval(makeCBV(width, 5), makeCBV(width, 15));

  stp::NodeToUnsignedIntervalMap map;
  map.insert({n, nullptr});
  map.insert({x, &xInterval});
  map.insert({y, &yInterval});

  ASTNode result = c.sr.topLevel(n, map);
  ASSERT_EQ(result, x);

  c.checkEquivalent(
      n, result, x, y, width, [](unsigned v) { return v <= 4; },
      [](unsigned v) { return v >= 5; });
}

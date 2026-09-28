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
 * The widened-equality narrowing rules. The preimage-or-false dichotomy is
 * checked structurally for EVERY wide constant against an enumeration of
 * the narrow format (all values that widen, memoised); end-to-end semantic
 * equivalence is checked on sampled constants over all operand values; the
 * both-widened drop on all operand pairs; and the classification commutes
 * for the five sound predicates, with the normal/subnormal pair pinned as
 * non-commuting.
 */

#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>
#include <map>
#include <vector>

using namespace stp;

namespace
{

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

  ASTNode widen(NodeFactory* nf, const ASTNode& x, unsigned se, unsigned ss,
                const ASTNode& mode)
  {
    return nf->CreateTerm(FP_TOFP, se + ss,
                          ASTVec{mgr.CreateBVConst(32, se),
                                 mgr.CreateBVConst(32, ss), mode, x});
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

struct FormatPair
{
  unsigned se, ss, te, ts;
};

std::vector<unsigned> constantSample(unsigned se, unsigned ss, unsigned n)
{
  const unsigned sw = se + ss;
  std::vector<unsigned> cs;
  for (unsigned sign = 0; sign < 2; sign++)
    for (unsigned exp = 0; exp < (1u << se); exp++)
    {
      const unsigned base = (sign << (sw - 1)) | (exp << (ss - 1));
      cs.push_back(base);
      cs.push_back(base | 1u);
      cs.push_back(base | ((1u << (ss - 1)) - 1));
    }
  unsigned lcg = 424243;
  for (unsigned i = 0; i < n; i++)
  {
    lcg = lcg * 1103515245 + 12345;
    cs.push_back(lcg % (1u << sw));
  }
  return cs;
}

// Every wide constant either has the exact narrow preimage the enumeration
// finds -- and then the rewritten equality must not be constant false --
// or has none, and then it must fold to exactly ASTFalse.
TEST(NarrowWidenedFPEquality, preimage_or_false_exhaustive)
{
  const FormatPair pairs[] = {{5, 9, 3, 4}, {4, 9, 4, 5}};
  for (const FormatPair& p : pairs)
  {
    Context c;
    const ASTNode x =
        c.mgr.CreateSourceSymbol("x", SourceSort::floatingPoint(p.te, p.ts));

    // widen(d) for every narrow value, memoised once.
    std::map<unsigned, unsigned> widenedToNarrow; // wide bits -> narrow bits
    bool preimageClash = false;
    for (unsigned d = 0; d < (1u << (p.te + p.ts)); d++)
    {
      // Interning canonicalises NaN payloads; enumerate value-distinct
      // narrow constants only, or every payload's widening collides.
      const ASTNode nd = c.fpc(d, p.te, p.ts);
      if ((unsigned)nd.GetUnsignedConst() != d)
        continue;
      const ASTNode wd = c.widen(&c.snf, nd, p.se, p.ss, c.rm());
      if (wd.GetKind() != BVCONST)
        continue;
      const unsigned wbits = (unsigned)wd.GetUnsignedConst();
      if (widenedToNarrow.count(wbits))
        preimageClash = true; // NaN payloads canonicalise; nothing else may
      widenedToNarrow[wbits] = d;
    }
    ASSERT_FALSE(preimageClash);

    for (unsigned cb = 0; cb < (1u << (p.se + p.ss)); cb++)
    {
      const ASTNode wide = c.fpc(cb, p.se, p.ss);
      // Interning canonicalises NaN payloads: enumerate value-distinct
      // constants only.
      if ((unsigned)wide.GetUnsignedConst() != cb)
        continue;
      const bool hasPreimage =
          widenedToNarrow.count((unsigned)wide.GetUnsignedConst()) > 0;
      const ASTNode eq = c.snf.CreateNode(
          FP_SMT_EQ, c.widen(&c.snf, x, p.se, p.ss, c.rm()), wide);
      if (hasPreimage)
        ASSERT_NE(FALSE, eq.GetKind())
            << "(" << p.se << "," << p.ss << ")->(" << p.te << "," << p.ts
            << ") c=" << cb << " lost its preimage";
      else
        ASSERT_EQ(FALSE, eq.GetKind())
            << "(" << p.se << "," << p.ss << ")->(" << p.te << "," << p.ts
            << ") c=" << cb << " should have folded to false";
    }
  }
}

TEST(NarrowWidenedFPEquality, constant_side_sampled_semantics)
{
  const FormatPair pairs[] = {{5, 9, 3, 4}, {4, 9, 4, 5}};
  const unsigned samples[] = {200, 64};
  for (unsigned pi = 0; pi < 2; pi++)
  {
    const FormatPair& p = pairs[pi];
    Context c;
    const ASTNode x =
        c.mgr.CreateSourceSymbol("x", SourceSort::floatingPoint(p.te, p.ts));
    for (const unsigned cb : constantSample(p.se, p.ss, samples[pi]))
    {
      const ASTNode wide = c.fpc(cb, p.se, p.ss);
      for (const Kind k : {FP_EQ, FP_SMT_EQ})
        for (int constLeft = 0; constLeft < 2; constLeft++)
        {
          const ASTNode xwh = c.widen(c.hf, x, p.se, p.ss, c.rm());
          const ASTNode original = constLeft
                                       ? c.hf->CreateNode(k, wide, xwh)
                                       : c.hf->CreateNode(k, xwh, wide);
          const ASTNode xws = c.widen(&c.snf, x, p.se, p.ss, c.rm());
          const ASTNode simplified = constLeft
                                         ? c.snf.CreateNode(k, wide, xws)
                                         : c.snf.CreateNode(k, xws, wide);
          for (unsigned xv = 0; xv < (1u << (p.te + p.ts)); xv++)
          {
            const ASTNode value = c.fpc(xv, p.te, p.ts);
            ASSERT_EQ(c.eval(original, x, value),
                      c.eval(simplified, x, value))
                << "kind " << k << " constLeft " << constLeft << " c=" << cb
                << " x=" << xv;
          }
        }
    }
  }
}

TEST(NarrowWidenedFPEquality, both_widened_exhaustive)
{
  const unsigned SE = 5, SS = 9, TE = 3, TS = 4, TW = TE + TS;
  Context c;
  const ASTNode x =
      c.mgr.CreateSourceSymbol("x", SourceSort::floatingPoint(TE, TS));
  const ASTNode y =
      c.mgr.CreateSourceSymbol("y", SourceSort::floatingPoint(TE, TS));

  for (const Kind k : {FP_EQ, FP_SMT_EQ})
  {
    const ASTNode original =
        c.hf->CreateNode(k, c.widen(c.hf, x, SE, SS, c.rm()),
                         c.widen(c.hf, y, SE, SS,
                                 c.rm(symbolic_fp::ROUND_TOWARD_ZERO)));
    const ASTNode simplified =
        c.snf.CreateNode(k, c.widen(&c.snf, x, SE, SS, c.rm()),
                         c.widen(&c.snf, y, SE, SS,
                                 c.rm(symbolic_fp::ROUND_TOWARD_ZERO)));
    EXPECT_FALSE(c.contains(FP_TOFP, simplified));

    for (unsigned xv = 0; xv < (1u << TW); xv++)
      for (unsigned yv = 0; yv < (1u << TW); yv++)
      {
        ASTNodeMap a;
        a.insert({x, c.fpc(xv, TE, TS)});
        a.insert({y, c.fpc(yv, TE, TS)});
        ASTNodeMap a2 = a;
        ASTNodeMap cache, cache2;
        ASTNode o = SubstitutionMap::replace(original, a, cache, &c.snf);
        ASTNode s = SubstitutionMap::replace(simplified, a2, cache2, &c.snf);
        if (!o.isConstant())
          o = NonMemberBVConstEvaluator(&c.mgr, o);
        if (!s.isConstant())
          s = NonMemberBVConstEvaluator(&c.mgr, s);
        ASSERT_EQ(o, s) << "kind " << k << " x=" << xv << " y=" << yv;
      }
  }
}

TEST(NarrowWidenedFPEquality, classifications_commute)
{
  const unsigned SE = 5, SS = 9, TE = 3, TS = 4, TW = TE + TS;
  Context c;
  const ASTNode x =
      c.mgr.CreateSourceSymbol("x", SourceSort::floatingPoint(TE, TS));

  for (const Kind k : {FP_ISNAN, FP_ISZERO, FP_ISINFINITE, FP_ISNEGATIVE,
                       FP_ISPOSITIVE})
  {
    const ASTNode original =
        c.hf->CreateNode(k, c.widen(c.hf, x, SE, SS, c.rm()));
    const ASTNode simplified =
        c.snf.CreateNode(k, c.widen(&c.snf, x, SE, SS, c.rm()));
    EXPECT_FALSE(c.contains(FP_TOFP, simplified)) << "kind " << k;
    for (unsigned xv = 0; xv < (1u << TW); xv++)
    {
      const ASTNode value = c.fpc(xv, TE, TS);
      ASSERT_EQ(c.eval(original, x, value), c.eval(simplified, x, value))
          << "kind " << k << " x=" << xv;
    }
  }

  // The pair a widening does not preserve: a narrow subnormal widens to a
  // wide normal, so these must keep their conversion (and stay correct).
  for (const Kind k : {FP_ISNORMAL, FP_ISSUBNORMAL})
  {
    const ASTNode original =
        c.hf->CreateNode(k, c.widen(c.hf, x, SE, SS, c.rm()));
    const ASTNode simplified =
        c.snf.CreateNode(k, c.widen(&c.snf, x, SE, SS, c.rm()));
    for (unsigned xv = 0; xv < (1u << TW); xv++)
    {
      const ASTNode value = c.fpc(xv, TE, TS);
      ASSERT_EQ(c.eval(original, x, value), c.eval(simplified, x, value))
          << "kind " << k << " x=" << xv;
    }
  }
}

TEST(NarrowWidenedFPEquality, gates_hold)
{
  const unsigned SE = 5, SS = 9, TE = 3, TS = 4;
  Context c;
  // A narrowing conversion is not a widening: the equality keeps it.
  const ASTNode w =
      c.mgr.CreateSourceSymbol("w", SourceSort::floatingPoint(SE, SS));
  const ASTNode shrink = c.hf->CreateTerm(
      FP_TOFP, TE + TS,
      ASTVec{c.mgr.CreateBVConst(32, TE), c.mgr.CreateBVConst(32, TS),
             c.rm(), w});
  const ASTNode kept =
      c.snf.CreateNode(FP_SMT_EQ, shrink, c.fpc(0x15, TE, TS));
  EXPECT_TRUE(c.contains(FP_TOFP, kept));
}

} // namespace

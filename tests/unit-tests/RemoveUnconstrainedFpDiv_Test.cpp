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
 * The FP_DIV arm of RemoveUnconstrained, checked from both directions at
 * (3, 4) inside (5, 9): substituting u's recorded witness back into the
 * original quotient must reproduce the replacement on all 2^7 x 2^7
 * (x, fresh) assignments, and every value the original quotient attains
 * must pass the replacement's classification filter (all numerators
 * against every divisor exponent boundary, every special, and a random
 * sample). Plus firing and no-fire gate checks.
 */

#include "stp/AST/MutableASTNode.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Simplifier/RemoveUnconstrained.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <functional>
#include <gtest/gtest.h>
#include <vector>

using namespace stp;

namespace
{

// (3, 4) in (5, 9): the smallest pair the rule's format-gap test admits
// that stays clear of symfpu's small-format trouble spots.
const unsigned TE = 3, TS = 4, SE = 5, SS = 9;
const unsigned TW = TE + TS, SW = SE + SS;

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* hf; // hashing factory: builds inputs without pre-simplifying.
  SubstitutionMap sm;
  Simplifier simp;

  Context() : snf(*(mgr.hashingNodeFactory), mgr), sm(&mgr), simp(&mgr, &sm)
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

  ASTNode fpSymbol(const char* name, unsigned eb, unsigned sb)
  {
    return mgr.CreateSourceSymbol(name, SourceSort::floatingPoint(eb, sb));
  }

  // to_fp[te,ts](rmN, fp.div(rmD, to_fp[se,ss](rmW, x), u))
  ASTNode narrowedDiv(const ASTNode& x, const ASTNode& u, const ASTNode& rmN,
                      const ASTNode& rmD, unsigned te = TE, unsigned ts = TS,
                      unsigned se = SE, unsigned ss = SS)
  {
    const ASTNode widened = hf->CreateTerm(
        FP_TOFP, se + ss,
        ASTVec{mgr.CreateBVConst(32, se), mgr.CreateBVConst(32, ss), rm(), x});
    const ASTNode divided =
        hf->CreateTerm(FP_DIV, se + ss, ASTVec{rmD, widened, u});
    return hf->CreateTerm(
        FP_TOFP, te + ts,
        ASTVec{mgr.CreateBVConst(32, te), mgr.CreateBVConst(32, ts), rmN,
               divided});
  }

  // EQ(t, quotient), with a hashing-factory tautology keeping t a second use
  // so no other rule eliminates it.
  ASTNode topFor(const ASTNode& t, const ASTNode& quotient)
  {
    const ASTNode isnan = hf->CreateNode(FP_ISNAN, t);
    return hf->CreateNode(
        AND, hf->CreateNode(EQ, t, quotient),
        hf->CreateNode(OR, isnan, hf->CreateNode(NOT, isnan)));
  }

  ASTNode run(const ASTNode& f)
  {
    RemoveUnconstrained r(mgr);
    return r.topLevel(f, &simp);
  }

  bool present(Kind k, const ASTNode& n)
  {
    if (n.GetKind() == k)
      return true;
    for (const auto& c : n)
      if (present(k, c))
        return true;
    return false;
  }

  // The replacement: in AND(EQ(t, R), taut), the EQ operand that is not t.
  ASTNode replacementFrom(const ASTNode& result, const ASTNode& t)
  {
    EXPECT_EQ(AND, result.GetKind());
    for (const auto& c : result)
      if (c.GetKind() == EQ)
        return (c[0] == t) ? c[1] : c[0];
    ADD_FAILURE() << "no equality in the rewritten formula";
    return result;
  }

  ASTNode backSubstitute(const ASTNode& n)
  {
    ASTNode cur = n;
    for (int i = 0; i < 64; i++)
    {
      DenseNodeMap fromTo = *simp.Return_SolverMap();
      DenseNodeMap cache;
      ASTNode next = SubstitutionMap::replace(cur, fromTo, cache, &snf);
      if (next == cur)
        return cur;
      cur = next;
    }
    ADD_FAILURE() << "back-substitution did not reach a fixed point";
    return cur;
  }

  ASTNode eval(const ASTNode& n, ASTNodeMap assignment /*by value*/)
  {
    ASTNodeMap cache;
    ASTNode s = SubstitutionMap::replace(n, assignment, cache, &snf);
    if (s.isConstant())
      return s;
    return NonMemberBVConstEvaluator(&mgr, s);
  }

  // Interning canonicalises NaN payloads, which is also STP's semantics
  // for them, so enumerating packed encodings enumerates values.
  ASTNode packed(unsigned bits, unsigned eb, unsigned sb)
  {
    return mgr.CreateFPConst(mgr.CreateBVConst(eb + sb, bits), eb, sb);
  }
};

TEST(RemoveUnconstrainedFpDiv, fires_and_removes_the_division)
{
  Context c;
  const ASTNode x = c.fpSymbol("x", TE, TS);
  const ASTNode u = c.fpSymbol("u", SE, SS);
  const ASTNode t = c.fpSymbol("t", TE, TS);
  const ASTNode top = c.topFor(t, c.narrowedDiv(x, u, c.rm(), c.rm()));

  const ASTNode result = c.run(top);

  EXPECT_FALSE(c.present(FP_DIV, result));
  EXPECT_TRUE(c.simp.Return_SolverMap()->find(u) !=
              c.simp.Return_SolverMap()->end())
      << "the eliminated divisor needs a definition for model construction";
}

TEST(RemoveUnconstrainedFpDiv, witness_reproduces_the_quotient_exhaustively)
{
  Context c;
  const ASTNode x = c.fpSymbol("x", TE, TS);
  const ASTNode u = c.fpSymbol("u", SE, SS);
  const ASTNode t = c.fpSymbol("t", TE, TS);
  const ASTNode quotient = c.narrowedDiv(x, u, c.rm(), c.rm());
  const ASTNode result = c.run(c.topFor(t, quotient));
  ASSERT_FALSE(c.present(FP_DIV, result));

  const ASTNode replacement = c.replacementFrom(result, t);

  // The one symbol of the replacement that is neither x nor t is the fresh
  // variable.
  ASTNode fresh;
  std::function<void(const ASTNode&)> find = [&](const ASTNode& n) {
    if (n.GetKind() == SYMBOL && n != x && n != t)
      fresh = n;
    for (const auto& ch : n)
      find(ch);
  };
  find(replacement);
  ASSERT_FALSE(fresh.IsNull());

  // Original quotient with u's definition written through: a function of
  // (x, fresh) that must agree with the replacement everywhere.
  const ASTNode lifted = c.backSubstitute(quotient);

  for (unsigned xv = 0; xv < (1u << TW); xv++)
    for (unsigned vv = 0; vv < (1u << TW); vv++)
    {
      ASTNodeMap a;
      a.insert({x, c.packed(xv, TE, TS)});
      a.insert({fresh, c.packed(vv, TE, TS)});
      ASTNodeMap a2 = a;
      const ASTNode expected = c.eval(replacement, a);
      const ASTNode got = c.eval(lifted, a2);
      ASSERT_EQ(expected, got)
          << "witness disagrees at x=" << xv << " v=" << vv;
    }
}

TEST(RemoveUnconstrainedFpDiv, every_original_quotient_is_reachable)
{
  Context c;
  const ASTNode x = c.fpSymbol("x", TE, TS);
  const ASTNode u = c.fpSymbol("u", SE, SS);
  const ASTNode t = c.fpSymbol("t", TE, TS);
  const ASTNode quotient = c.narrowedDiv(x, u, c.rm(), c.rm());
  const ASTNode result = c.run(c.topFor(t, quotient));
  ASSERT_FALSE(c.present(FP_DIV, result));
  const ASTNode replacement = c.replacementFrom(result, t);

  ASTNode fresh;
  std::function<void(const ASTNode&)> find = [&](const ASTNode& n) {
    if (n.GetKind() == SYMBOL && n != x && n != t)
      fresh = n;
    for (const auto& ch : n)
      find(ch);
  };
  find(replacement);
  ASSERT_FALSE(fresh.IsNull());

  // All specials and significand-field boundaries, plus a deterministic
  // sample of the rest.
  std::vector<unsigned> divisors;
  for (unsigned sign = 0; sign < 2; sign++)
    for (unsigned exp = 0; exp < (1u << SE); exp++)
    {
      const unsigned base = (sign << (SW - 1)) | (exp << (SS - 1));
      divisors.push_back(base);
      divisors.push_back(base | ((1u << (SS - 1)) - 1));
    }
  unsigned lcg = 12345;
  for (int i = 0; i < 512; i++)
  {
    lcg = lcg * 1103515245 + 12345;
    divisors.push_back(lcg % (1u << SW));
  }

  for (unsigned xv = 0; xv < (1u << TW); xv++)
    for (const unsigned uv : divisors)
    {
      ASTNodeMap a;
      a.insert({x, c.packed(xv, TE, TS)});
      a.insert({u, c.packed(uv, SE, SS)});
      const ASTNode q = c.eval(quotient, a);

      ASTNodeMap b;
      b.insert({x, c.packed(xv, TE, TS)});
      b.insert({fresh, q});
      ASSERT_EQ(q, c.eval(replacement, b))
          << "quotient not reachable through the filter at x=" << xv
          << " u=" << uv;
    }
}

TEST(RemoveUnconstrainedFpDiv, gates_hold)
{
  // Every variant here must leave the division in place.
  {
    // Directed rounding on the narrowing.
    Context c;
    const ASTNode x = c.fpSymbol("x", TE, TS);
    const ASTNode u = c.fpSymbol("u", SE, SS);
    const ASTNode t = c.fpSymbol("t", TE, TS);
    const ASTNode top = c.topFor(
        t, c.narrowedDiv(x, u, c.rm(symbolic_fp::ROUND_TOWARD_ZERO), c.rm()));
    EXPECT_TRUE(c.present(FP_DIV, c.run(top)));
  }
  {
    // Directed rounding on the division.
    Context c;
    const ASTNode x = c.fpSymbol("x", TE, TS);
    const ASTNode u = c.fpSymbol("u", SE, SS);
    const ASTNode t = c.fpSymbol("t", TE, TS);
    const ASTNode top = c.topFor(
        t, c.narrowedDiv(x, u, c.rm(), c.rm(symbolic_fp::ROUND_TOWARD_ZERO)));
    EXPECT_TRUE(c.present(FP_DIV, c.run(top)));
  }
  {
    // Source significand not enough longer than the target's: (5, 8) has
    // only four extra bits.
    Context c;
    const ASTNode x = c.fpSymbol("x", TE, TS);
    const ASTNode u = c.fpSymbol("u", SE, SS - 1);
    const ASTNode t = c.fpSymbol("t", TE, TS);
    const ASTNode top =
        c.topFor(t, c.narrowedDiv(x, u, c.rm(), c.rm(), TE, TS, SE, SS - 1));
    EXPECT_TRUE(c.present(FP_DIV, c.run(top)));
  }
  {
    // Divisor used twice: not unconstrained.
    Context c;
    const ASTNode x = c.fpSymbol("x", TE, TS);
    const ASTNode u = c.fpSymbol("u", SE, SS);
    const ASTNode t = c.fpSymbol("t", TE, TS);
    const ASTNode top = c.hf->CreateNode(
        AND, c.topFor(t, c.narrowedDiv(x, u, c.rm(), c.rm())),
        c.hf->CreateNode(FP_ISNORMAL, u));
    EXPECT_TRUE(c.present(FP_DIV, c.run(top)));
  }
  {
    // No narrowing above the division: its value is consumed at the
    // division's own format, where the quotient grid has holes.
    Context c;
    const ASTNode x = c.fpSymbol("x", TE, TS);
    const ASTNode u = c.fpSymbol("u", SE, SS);
    const ASTNode t = c.fpSymbol("t", SE, SS);
    const ASTNode widened = c.hf->CreateTerm(
        FP_TOFP, SW,
        ASTVec{c.mgr.CreateBVConst(32, SE), c.mgr.CreateBVConst(32, SS),
               c.rm(), x});
    const ASTNode divided =
        c.hf->CreateTerm(FP_DIV, SW, ASTVec{c.rm(), widened, u});
    EXPECT_TRUE(c.present(FP_DIV, c.run(c.topFor(t, divided))));
  }
}

} // namespace

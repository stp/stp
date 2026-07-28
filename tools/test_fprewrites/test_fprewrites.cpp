/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July, 2026
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

// Exhaustive equivalence tests for the floating-point rewrite rules in the
// SimplifyingNodeFactory (the "cheap FP rewrites, applied before bit-blasting"
// in CreateNode/CreateTerm).
//
// The methodology follows tests/unit-tests/SimplifyingNodeFactory_Exhaustive_
// Test.cpp: build the inputs with the hashing factory (nothing pre-simplified),
// create the node through both the hashing and the simplifying factory, and
// require the two to agree on *every* float of a small format -- all bit
// patterns: zeros, subnormals, normals, infinities and NaNs. Where a rule is
// guaranteed to apply, the simplifying result must also differ structurally
// (the rule fired). It is a plain executable that exits non-zero on failure,
// matching the sibling test_fpbackend; both register directly with CTest.
//
// The oracle is independent of the rules under test. FP constant folding is
// NOT done by the factory (is_fp_operation bypasses it): each side is blasted
// once, through the hashing factory so nothing is rewritten on the way in,
// and the resulting pure bitvector/Boolean circuit is folded under every
// assignment of the free floats. A wrong rewrite surfaces as a disagreeing
// folded value. (Folding a pre-blasted circuit, rather than re-blasting a
// substituted tree per assignment, is what makes exhaustive enumeration
// affordable: circuit construction dwarfs circuit evaluation.)

#include "stp/AST/AST.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/symbolic_fp.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"

#include <cstdint>
#include <cstdio>
#include <string>
#include <vector>

using namespace stp;
using stp::symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN;
using stp::symbolic_fp::ROUND_TOWARD_NEGATIVE;
using stp::symbolic_fp::ROUND_TOWARD_ZERO;

static int g_checks = 0;
static int g_failures = 0;

static void report(const std::string& name, bool ok, const std::string& why = "")
{
  g_checks++;
  if (ok)
  {
    printf("  %-44s ok\n", name.c_str());
  }
  else
  {
    g_failures++;
    printf("  %-44s ** FAIL ** %s\n", name.c_str(), why.c_str());
  }
}

struct Ctx
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* nf; // simplifying factory: under test.
  NodeFactory* hf; // hashing factory: builds inputs without simplifying.
  unsigned counter = 0;

  Ctx() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    CONSTANTBV::BitVector_Boot();
    nf = &snf;
    hf = mgr.hashingNodeFactory;
    // The default factory is used to blast a float op during folding, and by
    // the blaster's singleton. Keep it the *hashing* factory: the simplifying
    // factory folds the constant AND/OR nodes the blaster emits as it builds
    // them, and a folded boolean there can carry a spurious float format that
    // sends the constant evaluator down its bit-vector path (GetBVConst on a
    // Boolean). Leaving the circuit un-folded lets the recursive evaluator
    // reduce it correctly. The rules under test are still exercised: they are
    // requested explicitly through `nf`.
    mgr.defaultNodeFactory = hf;
    // The float blaster's singleton reads GlobalParserBM (for ASTTrue and the
    // node factory) when NonMemberBVConstEvaluator first folds a float op.
    GlobalParserBM = &mgr;
    symbolic_fp::init(&mgr);
  }

  // A fresh float variable of format (eb, sb).
  ASTNode fp(unsigned eb, unsigned sb)
  {
    ASTNode s = mgr.CreateSymbol(("f" + std::to_string(counter++)).c_str(), 0,
                                 eb + sb);
    s.SetExpWidth(eb);
    s.SetSigWidth(sb);
    return s;
  }

  // The float of format (eb, sb) whose packed IEEE bits are `v`.
  ASTNode fpConst(unsigned eb, unsigned sb, uint64_t v)
  {
    ASTNode n = mgr.CreateBVConst(eb + sb, (unsigned long long)v);
    return mgr.CreateFPConst(n, eb, sb);
  }

  // A rounding-mode constant (a 5-bit bitvector, as the parser builds them).
  ASTNode rm(unsigned mode) { return mgr.CreateBVConst(5, mode); }

  // A unary float op, built the way the parser does.
  ASTNode unary(NodeFactory* f, Kind k, const ASTNode& x)
  {
    ASTNode n = f->CreateTerm(k, x.GetValueWidth(), x);
    n.SetExpWidth(x.GetExpWidth());
    n.SetSigWidth(x.GetSigWidth());
    return n;
  }

  // Give bare fp.min/fp.max the (+0, -0) choice child the blaster expects,
  // as FpTotalise does before a normal solve -- but as a *constant*, where
  // the real pass introduces a free array read (the solver's congruent free
  // choice), which the constant evaluator cannot fold. Pinning one choice is
  // sound here: a rewrite must preserve meaning for every choice, and a
  // constant is trivially congruent.
  ASTNode pinPartialOps(const ASTNode& n)
  {
    ASTVec children;
    children.reserve(n.Degree());
    bool changed = false;
    for (const ASTNode& ch : n)
    {
      const ASTNode nc = pinPartialOps(ch);
      changed |= (nc != ch);
      children.push_back(nc);
    }
    const Kind k = n.GetKind();
    if ((k == FP_MIN || k == FP_MAX) && n.Degree() == 2)
    {
      children.push_back(mgr.CreateOneConst(1));
      changed = true;
    }
    if (!changed)
      return n;
    ASTNode out = (n.GetType() == BOOLEAN_TYPE)
                      ? hf->CreateNode(k, children)
                      : hf->CreateTerm(k, n.GetValueWidth(), children);
    if (n.GetExpWidth() != 0)
    {
      out.SetExpWidth(n.GetExpWidth());
      out.SetSigWidth(n.GetSigWidth());
    }
    return out;
  }

  // Blast a (possibly symbolic) tree to a pure bitvector/Boolean circuit,
  // bottom-up, the way FloatBlast does in a real solve: each floating-point
  // operation is lowered after its children, and its operand format comes
  // from the node the caller built rather than from the bits its children
  // lowered to. Nothing is stamped -- a lowered float is a bitvector, and
  // saying otherwise on a hash-consed node is what FloatBlast exists to
  // avoid. The blaster builds through the manager's default factory -- the
  // *hashing* one here -- so no rewrite fires on the way.
  ASTNode blastTree(const ASTNode& n)
  {
    if (n.Degree() == 0)
      return n; // a float symbol or constant is already its packed bits
    ASTVec kids;
    kids.reserve(n.Degree());
    for (const ASTNode& ch : n)
      kids.push_back(blastTree(ch));

    const Kind k = n.GetKind();
    if (!is_FP_kind(k))
      return (n.GetType() == BOOLEAN_TYPE)
                 ? hf->CreateNode(k, kids)
                 : hf->CreateTerm(k, n.GetValueWidth(), kids);

    // From `n`, not from `kids`: the operands are bits by now.
    const std::pair<unsigned int, unsigned int> fmt =
        FloatBlaster::operandFormat(n);
    return FloatBlaster::BlastNode_TopLevel(&mgr, k, kids, fmt.first,
                                            fmt.second);
  }

  ASTNode blastOnce(const ASTNode& n)
  {
    const ASTNode s = pinPartialOps(n);
    if (s.isConstant())
      return s;
    return blastTree(s);
  }

  // Fold a blasted circuit to a constant under `memo`, which arrives seeded
  // with the assignment (symbol -> packed constant) and memoises every
  // shared subterm -- symfpu circuits are DAGs, and an uncached walk
  // re-evaluates the shared spine exponentially often. Per node,
  // NonMemberBVConstEvaluator does the arithmetic on the already-folded
  // children.
  ASTNode foldBlasted(const ASTNode& n, ASTNodeMap& memo)
  {
    if (n.isConstant())
      return n;
    const auto found = memo.find(n);
    if (found != memo.end())
      return found->second;
    ASTVec kids;
    kids.reserve(n.Degree());
    for (const ASTNode& ch : n)
      kids.push_back(foldBlasted(ch, memo));
    const ASTNode r =
        NonMemberBVConstEvaluator(&mgr, n.GetKind(), kids, n.GetValueWidth());
    memo.insert({n, r});
    return r;
  }

  // A comparable key for a folded result: Booleans get sentinels clear of
  // any packed float value; float/bitvector constants get their bits. The
  // format is passed in (a folded circuit's output is a bare bitvector and
  // carries none): zero widths mean the result denotes no float.
  static uint64_t key(const ASTNode& r, unsigned eb, unsigned sb)
  {
    const Kind rk = r.GetKind();
    if (rk == TRUE)
      return 1ull << 40;
    if (rk == FALSE)
      return 1ull << 41;
    if (rk != BVCONST)
      // An unexpected non-constant fold: flag it without crashing. Mix in
      // the node number so two *different* non-constant folds cannot
      // silently compare equal (two identical ones are genuinely equal).
      return (1ull << 43) | (uint64_t)(unsigned)r.GetNodeNum();
    uint64_t v = 0;
    const unsigned w = r.GetValueWidth();
    for (unsigned i = 0; i < w && i < 64; i++)
      if (CONSTANTBV::BitVector_bit_test(r.GetBVConst(), i))
        v |= (1ull << i);

    // SMT-LIB floating point has a single NaN value: all NaN bit patterns
    // denote it, so they must compare equal. (Payloads are not observable and
    // an operation may canonicalise them.) The five constants aside, +0 and -0
    // are distinct SMT-LIB values and are NOT collapsed.
    if (eb != 0 && sb != 0 && eb + sb == w)
    {
      const unsigned storedSig = sb - 1;
      const uint64_t expMask = (((1ull << eb) - 1) << storedSig);
      const uint64_t sigMask = ((1ull << storedSig) - 1);
      if ((v & expMask) == expMask && (v & sigMask) != 0)
        return (1ull << 42); // any NaN
    }
    return v;
  }

  void collectSymbols(const ASTNode& n, ASTNodeSet& out)
  {
    if (n.GetKind() == SYMBOL)
    {
      out.insert(n);
      return;
    }
    for (const auto& c : n)
      collectSymbols(c, out);
  }

  unsigned long domain(const ASTNode& s)
  {
    if (s.GetType() == BOOLEAN_TYPE)
      return 2;
    if (s.GetType() == FLOATINGPOINT_TYPE)
      return 1ul << (s.GetExpWidth() + s.GetSigWidth());
    return 1ul << s.GetValueWidth();
  }

  ASTNode valueFor(const ASTNode& s, unsigned long v)
  {
    if (s.GetType() == BOOLEAN_TYPE)
      return (v & 1) ? mgr.ASTTrue : mgr.ASTFalse;
    if (s.GetType() == FLOATINGPOINT_TYPE)
      return fpConst(s.GetExpWidth(), s.GetSigWidth(), v);
    return mgr.CreateBVConst(s.GetValueWidth(), (unsigned)v);
  }

  // `before` and `after` must evaluate equal on every assignment of their free
  // floats. Returns "" on success, else a description of the first mismatch.
  std::string firstDisagreement(const ASTNode& before, const ASTNode& after)
  {
    // Node-identical terms are trivially equivalent; skip the enumeration
    // (checkTerm calls this with expectFired=false checks where the factory
    // may legitimately have left the node alone).
    if (before == after)
      return "";

    ASTNodeSet symSet;
    collectSymbols(before, symSet);
    collectSymbols(after, symSet);
    std::vector<ASTNode> syms(symSet.begin(), symSet.end());

    unsigned long combos = 1;
    for (const auto& s : syms)
      combos *= domain(s);
    if (combos > (1ul << 18))
      return "too many assignments (" + std::to_string(combos) + ")";

    const ASTNode blastedBefore = blastOnce(before);
    const ASTNode blastedAfter = blastOnce(after);

    // For the NaN collapse in key(). A float term knows its format (derived
    // if need be); a Boolean check reads 0s and collapses nothing.
    const unsigned eb = before.GetExpWidth(), sb = before.GetSigWidth();

    for (unsigned long c = 0; c < combos; c++)
    {
      ASTNodeMap assignment;
      unsigned long rest = c;
      for (size_t i = 0; i < syms.size(); i++)
      {
        const unsigned long size = domain(syms[i]);
        assignment.insert({syms[i], valueFor(syms[i], rest % size)});
        rest /= size;
      }
      ASTNodeMap memoBefore(assignment);
      ASTNodeMap memoAfter(assignment);
      if (key(foldBlasted(blastedBefore, memoBefore), eb, sb) !=
          key(foldBlasted(blastedAfter, memoAfter), eb, sb))
        return "meaning changed at assignment " + std::to_string(c);
    }
    return "";
  }

  // Build a term through both factories; require equivalent, and (when
  // expectFired) structurally different.
  void checkTerm(const std::string& name, Kind k, unsigned width,
                 const ASTVec& children, bool expectFired = true)
  {
    ASTNode plain = hf->CreateTerm(k, width, children);
    ASTNode simplified = nf->CreateTerm(k, width, children);
    if (expectFired && plain == simplified)
    {
      report(name, false, "rule did not fire");
      return;
    }
    const std::string why = firstDisagreement(plain, simplified);
    report(name, why.empty(), why);
  }

  // A rule that must NOT fire (the node is unchanged), but is trivially still
  // equivalent to itself.
  void checkUnchanged(const std::string& name, Kind k, const ASTVec& children)
  {
    ASTNode plain = hf->CreateNode(k, children);
    ASTNode simplified = nf->CreateNode(k, children);
    report(name, plain == simplified, "node was unexpectedly rewritten");
  }
};

// Small formats that still contain zeros, subnormals, normals, infinities and
// NaNs. (eb, sb): sb counts the hidden bit, packed = eb + sb. sb must be at
// least 4: the pinned symfpu computes a too-small unpacked exponent width for
// sb <= 3 and dies on an unpack invariant (symfpu issue #14).
static const unsigned EB = 3, SB = 4;   // 128 values
static const unsigned SEB = 2, SSB = 4; // 64 values, for the ternary FMA

// A small, independent floating-point decoder. The Boolean rules are checked
// against this rather than by folding a float predicate through the blaster:
// the blaster's constant-folding of the Boolean circuit it emits is fragile
// (that is a separate finding). The classification and self-comparison facts
// it encodes are pure IEEE/SMT-LIB and easy to get right directly.
struct RefFp
{
  bool sign, nan, inf, zero, sub, norm;
};

static RefFp refDecode(unsigned eb, unsigned sb, uint64_t v)
{
  const unsigned storedSig = sb - 1;
  const uint64_t sig = v & ((1ull << storedSig) - 1);
  const uint64_t exp = (v >> storedSig) & ((1ull << eb) - 1);
  const bool allOnes = (exp == ((1ull << eb) - 1));
  RefFp d;
  d.sign = (v >> (eb + sb - 1)) & 1;
  d.nan = allOnes && sig != 0;
  d.inf = allOnes && sig == 0;
  d.zero = (exp == 0 && sig == 0);
  d.sub = (exp == 0 && sig != 0);
  d.norm = !allOnes && exp != 0;
  return d;
}

static bool refClassify(Kind k, const RefFp& d)
{
  switch (k)
  {
    case FP_ISNAN: return d.nan;
    case FP_ISINFINITE: return d.inf;
    case FP_ISZERO: return d.zero;
    case FP_ISSUBNORMAL: return d.sub;
    case FP_ISNORMAL: return d.norm;
    default: return false;
  }
}

static void run(Ctx& c)
{
  // abs(abs x) = abs(neg x) = abs x
  {
    ASTNode x = c.fp(EB, SB);
    c.checkTerm("abs(abs x) = abs x", FP_ABS, x.GetValueWidth(),
                {c.unary(c.hf, FP_ABS, x)});
    c.checkTerm("abs(neg x) = abs x", FP_ABS, x.GetValueWidth(),
                {c.unary(c.hf, FP_NEG, x)});
  }

  // neg(neg x) = x
  {
    ASTNode x = c.fp(EB, SB);
    c.checkTerm("neg(neg x) = x", FP_NEG, x.GetValueWidth(),
                {c.unary(c.hf, FP_NEG, x)});
  }

  // min(x, x) = max(x, x) = x
  {
    ASTNode x = c.fp(EB, SB);
    c.checkTerm("min(x, x) = x", FP_MIN, x.GetValueWidth(), {x, x});
    c.checkTerm("max(x, x) = x", FP_MAX, x.GetValueWidth(), {x, x});
  }

  // Classification predicates ignore the sign, so a wrapping abs/neg is
  // dropped. Check that the factory drops it (the result equals the predicate
  // on x) and, via the reference, that each predicate really is
  // sign-independent over every float.
  {
    ASTNode x = c.fp(EB, SB);
    ASTNode absx = c.unary(c.hf, FP_ABS, x);
    ASTNode negx = c.unary(c.hf, FP_NEG, x);
    const char* nm[] = {"isNormal", "isSubnormal", "isZero", "isInfinite",
                        "isNaN"};
    Kind ks[] = {FP_ISNORMAL, FP_ISSUBNORMAL, FP_ISZERO, FP_ISINFINITE,
                 FP_ISNAN};
    const uint64_t N = 1ull << (EB + SB);
    const uint64_t signBit = 1ull << (EB + SB - 1);
    for (int i = 0; i < 5; i++)
    {
      const ASTNode want = c.hf->CreateNode(ks[i], {x});
      const bool fires = c.nf->CreateNode(ks[i], {absx}) == want &&
                         c.nf->CreateNode(ks[i], {negx}) == want;
      bool sound = true;
      for (uint64_t v = 0; v < N && sound; v++)
      {
        const bool p = refClassify(ks[i], refDecode(EB, SB, v));
        const bool pAbs = refClassify(ks[i], refDecode(EB, SB, v & ~signBit));
        const bool pNeg = refClassify(ks[i], refDecode(EB, SB, v ^ signBit));
        sound = (p == pAbs && p == pNeg);
      }
      report(std::string(nm[i]) + "(abs/neg x) = " + nm[i] + "(x)",
             fires && sound);
    }
    // isPositive/isNegative DO depend on the sign: must not be rewritten.
    c.checkUnchanged("isPositive keeps abs", FP_ISPOSITIVE, {absx});
    c.checkUnchanged("isNegative keeps neg", FP_ISNEGATIVE, {negx});
  }

  // Folding a *constant* classification used to stamp a float format on the
  // Boolean result, poisoning the shared TRUE/FALSE constant and later tripping
  // the constant evaluator. It must return a clean Boolean matching the
  // reference, for every value and abs/neg wrapping.
  {
    Kind ks[] = {FP_ISNORMAL, FP_ISSUBNORMAL, FP_ISZERO, FP_ISINFINITE,
                 FP_ISNAN};
    const char* nm[] = {"isNormal", "isSubnormal", "isZero", "isInfinite",
                        "isNaN"};
    const uint64_t N = 1ull << (EB + SB);
    for (int i = 0; i < 5; i++)
    {
      bool ok = true;
      std::string why;
      for (uint64_t v = 0; v < N && ok; v++)
        for (int wrap = 0; wrap < 3 && ok; wrap++)
        {
          ASTNode k = c.fpConst(EB, SB, v);
          ASTNode arg = (wrap == 1)   ? c.unary(c.hf, FP_ABS, k)
                        : (wrap == 2) ? c.unary(c.hf, FP_NEG, k)
                                      : k;
          ASTNode r =
              NonMemberBVConstEvaluator(&c.mgr, c.hf->CreateNode(ks[i], {arg}));
          const bool cleanBool =
              (r.GetKind() == TRUE || r.GetKind() == FALSE) &&
              r.GetExpWidth() == 0 && r.GetSigWidth() == 0;
          const bool want = refClassify(ks[i], refDecode(EB, SB, v));
          if (!cleanBool)
          {
            ok = false;
            why = "result carries a spurious format at v=" + std::to_string(v);
          }
          else if ((r.GetKind() == TRUE) != want)
          {
            ok = false;
            why = "wrong value at v=" + std::to_string(v);
          }
        }
      report(std::string(nm[i]) + " constant fold clean + correct", ok, why);
    }
  }

  // x < x, x > x rewrite to false; x <= x, x >= x to (not isNaN x). Both facts
  // are IEEE-exact; check the factory produces those exact forms.
  {
    ASTNode x = c.fp(EB, SB);
    report("x < x -> false", c.nf->CreateNode(FP_LT, {x, x}) == c.mgr.ASTFalse);
    report("x > x -> false", c.nf->CreateNode(FP_GT, {x, x}) == c.mgr.ASTFalse);
    const ASTNode notNan =
        c.hf->CreateNode(NOT, {c.hf->CreateNode(FP_ISNAN, {x})});
    report("x <= x -> not isNaN(x)",
           c.nf->CreateNode(FP_LEQ, {x, x}) == notNan);
    report("x >= x -> not isNaN(x)",
           c.nf->CreateNode(FP_GEQ, {x, x}) == notNan);
  }

  // fp.eq / fp.smt_eq are symmetric; the factory canonicalises operand order so
  // that x ~ y and y ~ x are the same node (and share a blasted circuit).
  {
    ASTNode x = c.fp(EB, SB), y = c.fp(EB, SB);
    report("fp.eq operand order canonical",
           c.nf->CreateNode(FP_EQ, {x, y}) == c.nf->CreateNode(FP_EQ, {y, x}));
    report("fp.smt_eq operand order canonical",
           c.nf->CreateNode(FP_SMT_EQ, {x, y}) ==
               c.nf->CreateNode(FP_SMT_EQ, {y, x}));
  }

  // fp.add and fp.mul are commutative in their two float operands
  {
    ASTNode x = c.fp(EB, SB), y = c.fp(EB, SB);
    for (unsigned mode :
         {(unsigned)ROUND_NEAREST_TIES_TO_EVEN, (unsigned)ROUND_TOWARD_ZERO})
    {
      ASTNode r = c.rm(mode);
      c.checkTerm("fp.add commutative", FP_ADD, x.GetValueWidth(), {r, x, y},
                  false);
      c.checkTerm("fp.mul commutative", FP_MUL, x.GetValueWidth(), {r, x, y},
                  false);
    }
  }

  // fp.sub(rm, x, y) = fp.add(rm, x, neg y): exact for every rounding mode and
  // for signed zeros (round-toward-negative is the sensitive case).
  {
    ASTNode x = c.fp(EB, SB), y = c.fp(EB, SB);
    for (unsigned mode : {(unsigned)ROUND_NEAREST_TIES_TO_EVEN,
                          (unsigned)ROUND_TOWARD_NEGATIVE})
    {
      ASTNode r = c.rm(mode);
      c.checkTerm("fp.sub = fp.add(x, neg y)", FP_SUB, x.GetValueWidth(),
                  {r, x, y});
    }
  }

  // fp.fma commutative in its two multiplicands (children 1 and 2). The
  // addend reuses x so the exhaustive enumeration stays at two variables:
  // three would be 2^18 assignments of a blasted FMA.
  {
    ASTNode x = c.fp(SEB, SSB), y = c.fp(SEB, SSB);
    for (unsigned mode : {(unsigned)ROUND_NEAREST_TIES_TO_EVEN,
                          (unsigned)ROUND_TOWARD_ZERO})
    {
      ASTNode r = c.rm(mode);
      c.checkTerm("fp.fma multiplicands commute", FP_FMA, x.GetValueWidth(),
                  {r, x, y, x}, false);
    }
  }

  // rem(rem(a, b), b) = rem(a, b)
  {
    ASTNode a = c.fp(EB, SB), b = c.fp(EB, SB);
    ASTNode inner = c.hf->CreateTerm(FP_REM, a.GetValueWidth(), a, b);
    inner.SetExpWidth(EB);
    inner.SetSigWidth(SB);
    c.checkTerm("rem(rem(a, b), b) = rem(a, b)", FP_REM, a.GetValueWidth(),
                {inner, b});
  }

  // rem(a, -b) = rem(a, |b|) = rem(a, b)
  {
    ASTNode a = c.fp(EB, SB), b = c.fp(EB, SB);
    c.checkTerm("rem(a, -b) = rem(a, b)", FP_REM, a.GetValueWidth(),
                {a, c.unary(c.hf, FP_NEG, b)});
    c.checkTerm("rem(a, |b|) = rem(a, b)", FP_REM, a.GetValueWidth(),
                {a, c.unary(c.hf, FP_ABS, b)});
  }

  // rem(-a, b) = -rem(a, b)
  {
    ASTNode a = c.fp(EB, SB), b = c.fp(EB, SB);
    c.checkTerm("rem(-a, b) = -rem(a, b)", FP_REM, a.GetValueWidth(),
                {c.unary(c.hf, FP_NEG, a), b});
  }

  // Identity operands: x * 1.0 = x, x * -1.0 = -x (either operand may be the
  // constant, mul is commutative), and x / 1.0 = x (divisor only). All exact
  // for every value and rounding mode. Checked across the rounding modes,
  // including round-toward-negative, the one that pulls -x apart from x.
  {
    ASTNode x = c.fp(EB, SB);
    const uint64_t bias = (1ull << (EB - 1)) - 1;
    const uint64_t oneBits = bias << (SB - 1);                      // +1.0
    const uint64_t negOneBits = oneBits | (1ull << (EB + SB - 1));  // -1.0
    ASTNode one = c.fpConst(EB, SB, oneBits);
    ASTNode negOne = c.fpConst(EB, SB, negOneBits);
    const unsigned w = x.GetValueWidth();
    for (unsigned mode : {(unsigned)ROUND_NEAREST_TIES_TO_EVEN,
                          (unsigned)ROUND_TOWARD_ZERO,
                          (unsigned)ROUND_TOWARD_NEGATIVE})
    {
      ASTNode r = c.rm(mode);
      c.checkTerm("x * 1.0 = x", FP_MUL, w, {r, x, one});
      c.checkTerm("1.0 * x = x", FP_MUL, w, {r, one, x});
      c.checkTerm("x * -1.0 = neg x", FP_MUL, w, {r, x, negOne});
      c.checkTerm("-1.0 * x = neg x", FP_MUL, w, {r, negOne, x});
      c.checkTerm("x / 1.0 = x", FP_DIV, w, {r, x, one});
      // 1.0 / x is not x: the divisor-only rule must leave this unchanged (and
      // must not, in any case, change its meaning).
      c.checkTerm("1.0 / x unchanged", FP_DIV, w, {r, one, x}, false);
    }
  }
}

int main()
{
  setbuf(stdout, nullptr);
  printf("Exhaustive floating-point rewrite tests\n");
  Ctx c;
  run(c);
  printf("\n%d checks, %d failures\n", g_checks, g_failures);
  return g_failures == 0 ? 0 : 1;
}

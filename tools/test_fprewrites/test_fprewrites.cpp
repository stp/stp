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
#include "stp/FloatBlaster/FloatBlast.h"
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
using stp::symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY;
using stp::symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN;
using stp::symbolic_fp::ROUND_TOWARD_NEGATIVE;
using stp::symbolic_fp::ROUND_TOWARD_POSITIVE;
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
    ASTNode n = mgr.CreateBVConst(eb + sb, v);
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
  // through the same lowering pass a real solve uses -- so this tool cannot
  // drift from it, which is the point of testing the rewrites against the
  // blaster at all. The pass builds through the manager's default factory --
  // the *hashing* one here -- so no rewrite fires on the way.
  ASTNode blastTree(const ASTNode& n)
  {
    return FloatBlast::lowerOperation(&mgr, n);
  }

  ASTNode blastOnce(const ASTNode& n)
  {
    const ASTNode s = pinPartialOps(n);
    if (s.isConstant())
      return s;
    return blastTree(s);
  }

  // A blasted circuit flattened for repeated evaluation. Enumerating a rule
  // exhaustively folds the same DAG once per assignment, so everything that
  // does not depend on the assignment is hoisted out of that loop: the DAG is
  // linearised once into a topological order with child *indices*, and each
  // pass is then a flat sweep over an array -- no hashing, no recursion, and
  // no re-walking of the shared spine. Both sides of a rule go into ONE
  // Circuit, so subterms they share (which is most of the DAG for rules that
  // rewrite one operand) are evaluated once between them.
  struct Circuit
  {
    std::vector<ASTNode> node;             // topological: children first
    std::vector<uint32_t> kidStart;        // index into `kid`, size n+1
    std::vector<uint32_t> kid;             // child slots, concatenated
    std::vector<uint8_t> assignmentBound;  // slot's value varies per assignment
    std::vector<ASTNode> value;            // scratch: the current fold

    uint32_t size() const { return (uint32_t)node.size(); }
  };

  // Add `n` and everything below it to `c` (iteratively: blasted floating-point
  // circuits are deep enough that a recursive walk is a real stack risk), and
  // return its slot. `slotOf` carries over between calls so a second root
  // reuses the first one's slots.
  uint32_t linearise(const ASTNode& n, Circuit& c, ASTNodeCountMap& slotOf)
  {
    std::vector<std::pair<ASTNode, bool>> todo{{n, false}};
    while (!todo.empty())
    {
      const ASTNode cur = todo.back().first;
      const bool expanded = todo.back().second;
      todo.pop_back();
      if (slotOf.find(cur) != slotOf.end())
        continue;
      if (!expanded)
      {
        // Revisit `cur` once its children hold slots.
        todo.push_back({cur, true});
        for (const ASTNode& ch : cur)
          if (slotOf.find(ch) == slotOf.end())
            todo.push_back({ch, false});
        continue;
      }
      const uint32_t slot = c.size();
      c.node.push_back(cur);
      c.kidStart.push_back((uint32_t)c.kid.size());
      bool bound = false;
      for (const ASTNode& ch : cur)
      {
        const uint32_t ks = (uint32_t)slotOf.find(ch)->second;
        c.kid.push_back(ks);
        bound |= (c.assignmentBound[ks] != 0);
      }
      if (cur.GetKind() == SYMBOL)
        bound = true;
      c.assignmentBound.push_back(bound ? 1 : 0);
      slotOf.insert({cur, (int32_t)slot});
    }
    return (uint32_t)slotOf.find(n)->second;
  }

  // Close the child table off with its end sentinel, once both roots are in.
  static void finalise(Circuit& c)
  {
    c.kidStart.push_back((uint32_t)c.kid.size());
  }

  // Fold every slot that does not depend on the assignment. Done once, before
  // the enumeration, so the constant subcircuits symfpu emits are not refolded
  // on every one of the (up to 2^18) passes.
  void foldInvariant(Circuit& c)
  {
    c.value.assign(c.size(), mgr.ASTUndefined);
    for (uint32_t i = 0; i < c.size(); i++)
      if (!c.assignmentBound[i])
        c.value[i] = evalSlot(c, i);
  }

  // Reused across every slot of every pass: the operand vector is otherwise a
  // heap allocation per node, which at millions of node-evaluations per rule
  // costs more than the arithmetic it carries.
  ASTVec evalKids;

  ASTNode evalSlot(const Circuit& c, uint32_t i)
  {
    const ASTNode& n = c.node[i];
    if (n.isConstant())
      return n;
    evalKids.clear();
    for (uint32_t k = c.kidStart[i]; k < c.kidStart[i + 1]; k++)
      evalKids.push_back(c.value[c.kid[k]]);
    return NonMemberBVConstEvaluator(&mgr, n.GetKind(), evalKids,
                                     n.GetValueWidth());
  }

  // One pass: the symbol slots already hold the assignment, so sweeping the
  // topological order in index order folds the whole circuit.
  void foldAssignment(Circuit& c)
  {
    for (uint32_t i = 0; i < c.size(); i++)
      if (c.assignmentBound[i] && c.node[i].GetKind() != SYMBOL)
        c.value[i] = evalSlot(c, i);
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

  // Number of values the symbol can take, saturated rather than shifted past
  // the width of the result: "1ul << 32" is fine on LP64 but undefined where
  // long is 32 bits, and the caller only needs to know that a wide symbol
  // exceeds its enumeration limit.
  uint64_t domain(const ASTNode& s)
  {
    if (s.GetType() == BOOLEAN_TYPE)
      return 2;
    const unsigned bits = (s.GetType() == FLOATINGPOINT_TYPE)
                              ? s.GetExpWidth() + s.GetSigWidth()
                              : s.GetValueWidth();
    return bits >= 64 ? UINT64_MAX : (UINT64_C(1) << bits);
  }

  ASTNode valueFor(const ASTNode& s, uint64_t v)
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

    // Tested before each multiply, so the product cannot itself overflow.
    const uint64_t maxCombos = UINT64_C(1) << 18;
    uint64_t combos = 1;
    for (const auto& s : syms)
    {
      const uint64_t d = domain(s);
      if (d > maxCombos || combos > maxCombos / d)
        return "too many assignments (over " + std::to_string(maxCombos) + ")";
      combos *= d;
    }

    Circuit circuit;
    ASTNodeCountMap slotOf;
    const uint32_t rootBefore = linearise(blastOnce(before), circuit, slotOf);
    const uint32_t rootAfter = linearise(blastOnce(after), circuit, slotOf);
    finalise(circuit);
    foldInvariant(circuit);

    // Where each symbol's value goes. A symbol absent from the blasted
    // circuit (a rewrite may drop one) simply has no slot.
    std::vector<uint32_t> symSlot(syms.size(), UINT32_MAX);
    for (size_t i = 0; i < syms.size(); i++)
    {
      const auto found = slotOf.find(syms[i]);
      if (found != slotOf.end())
        symSlot[i] = (uint32_t)found->second;
    }

    // For the NaN collapse in key(). A float term knows its format (derived
    // if need be); a Boolean check reads 0s and collapses nothing.
    const unsigned eb = before.GetExpWidth(), sb = before.GetSigWidth();

    for (uint64_t c = 0; c < combos; c++)
    {
      uint64_t rest = c;
      for (size_t i = 0; i < syms.size(); i++)
      {
        const uint64_t size = domain(syms[i]);
        const ASTNode v = valueFor(syms[i], rest % size);
        rest /= size;
        if (symSlot[i] != UINT32_MAX)
          circuit.value[symSlot[i]] = v;
      }
      foldAssignment(circuit);
      if (key(circuit.value[rootBefore], eb, sb) !=
          key(circuit.value[rootAfter], eb, sb))
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

  // Build through both factories; require the simplified result to BE
  // `expected`, and the plain original to agree with it on every assignment
  // of the free floats.
  void checkTermIs(const std::string& name, Kind k, unsigned width,
                   const ASTVec& children, const ASTNode& expected)
  {
    ASTNode plain = hf->CreateTerm(k, width, children);
    ASTNode simplified = nf->CreateTerm(k, width, children);
    if (simplified != expected)
    {
      report(name, false, "did not take the expected form");
      return;
    }
    const std::string why = firstDisagreement(plain, simplified);
    report(name, why.empty(), why);
  }

  void checkNodeIs(const std::string& name, Kind k, const ASTVec& children,
                   const ASTNode& expected)
  {
    ASTNode plain = hf->CreateNode(k, children);
    ASTNode simplified = nf->CreateNode(k, children);
    if (simplified != expected)
    {
      report(name, false, "did not take the expected form");
      return;
    }
    const std::string why = firstDisagreement(plain, simplified);
    report(name, why.empty(), why);
  }
};

// The packed bit patterns of the special constants, per format.
static uint64_t packNaN(unsigned eb, unsigned sb)
{
  return (((1ull << eb) - 1) << (sb - 1)) | 1;
}
static uint64_t packInf(unsigned eb, unsigned sb, bool neg)
{
  const uint64_t v = ((1ull << eb) - 1) << (sb - 1);
  return neg ? v | (1ull << (eb + sb - 1)) : v;
}
static uint64_t packZero(unsigned eb, unsigned sb, bool neg)
{
  return neg ? (1ull << (eb + sb - 1)) : 0;
}
static uint64_t packOne(unsigned eb, unsigned sb, bool neg)
{
  const uint64_t v = ((1ull << (eb - 1)) - 1) << (sb - 1);
  return neg ? v | (1ull << (eb + sb - 1)) : v;
}

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
    // isPositive/isNegative DO depend on the sign, so the peel above must
    // not apply -- instead each resolves against what abs/neg do to it:
    // an abs is never negative and positive iff not NaN; a neg swaps them.
    c.checkNodeIs("isPositive(abs x) -> not isNaN", FP_ISPOSITIVE, {absx},
                  c.hf->CreateNode(NOT, {c.hf->CreateNode(FP_ISNAN, {x})}));
    c.checkNodeIs("isNegative(abs x) -> false", FP_ISNEGATIVE, {absx},
                  c.mgr.ASTFalse);
    c.checkNodeIs("isNegative(neg x) -> isPositive x", FP_ISNEGATIVE, {negx},
                  c.hf->CreateNode(FP_ISPOSITIVE, {x}));
    c.checkNodeIs("isPositive(neg x) -> isNegative x", FP_ISPOSITIVE, {negx},
                  c.hf->CreateNode(FP_ISNEGATIVE, {x}));
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

  // The less-thans mirror onto the greater-thans (as BVLT does onto BVGT):
  // fp.lt(a, b) = fp.gt(b, a) and fp.leq(a, b) = fp.geq(b, a), exactly, NaN
  // included. Structural: the factory must produce the mirrored node.
  // Semantic: the mirror must agree with the un-normalised original on every
  // pair of floats, which is what makes the structural check trustworthy.
  {
    ASTNode x = c.fp(EB, SB), y = c.fp(EB, SB);

    const ASTNode lt = c.nf->CreateNode(FP_LT, {x, y});
    report("fp.lt(a, b) -> fp.gt(b, a)",
           lt == c.hf->CreateNode(FP_GT, {y, x}));
    std::string why = c.firstDisagreement(c.hf->CreateNode(FP_LT, {x, y}), lt);
    report("fp.lt mirror exact on all pairs", why.empty(), why);

    const ASTNode leq = c.nf->CreateNode(FP_LEQ, {x, y});
    report("fp.leq(a, b) -> fp.geq(b, a)",
           leq == c.hf->CreateNode(FP_GEQ, {y, x}));
    why = c.firstDisagreement(c.hf->CreateNode(FP_LEQ, {x, y}), leq);
    report("fp.leq mirror exact on all pairs", why.empty(), why);
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

  // The reflexive pair: `=` is reflexive on the abstract domain (one NaN
  // value), fp.eq is not (NaN compares equal to nothing, itself included).
  // The SMT equality folds immediately, and does so whatever the solver mode:
  // node construction is context-free.
  {
    ASTNode x = c.fp(EB, SB);
    report("x = x -> true",
           c.nf->CreateNode(FP_SMT_EQ, {x, x}) == c.mgr.ASTTrue);
    c.mgr.UserFlags.incremental_mode = UserDefinedFlags::IncrementalMode::ON;
    report("x = x -> true, incremental mode included",
           c.nf->CreateNode(FP_SMT_EQ, {x, x}) == c.mgr.ASTTrue);
    c.mgr.UserFlags.incremental_mode = UserDefinedFlags::IncrementalMode::AUTO;
    report("fp.eq(x, x) -> not isNaN(x)",
           c.nf->CreateNode(FP_EQ, {x, x}) ==
               c.hf->CreateNode(NOT, {c.hf->CreateNode(FP_ISNAN, {x})}));
  }

  // Strength reduction of fp.eq against a constant. The two equalities
  // disagree only on pairs holding a NaN or two zeros, so the constant
  // decides which of three forms is exact: false for a NaN, isZero for
  // either zero, and `=` for everything else -- the one worth having, since
  // `=` propagates as a substitution where fp.eq never may.
  //
  // Checked over EVERY constant of the format and both operand orders:
  // structurally (the expected node came out) and semantically (the folded
  // circuits agree on every value of the free operand, which is what makes
  // the structural expectation worth asserting).
  {
    ASTNode x = c.fp(EB, SB);
    const uint64_t N = 1ull << (EB + SB);
    const uint64_t signBit = 1ull << (EB + SB - 1);
    bool structOk = true, semOk = true;
    std::string why;
    for (uint64_t v = 0; v < N && semOk; v++)
    {
      const RefFp d = refDecode(EB, SB, v);
      const ASTNode k = c.fpConst(EB, SB, v);
      // Interning collapses every NaN pattern onto one; compare against the
      // constant the factory actually saw, not the pattern asked for.
      const ASTNode want =
          d.nan ? c.mgr.ASTFalse
          : d.zero
              ? c.hf->CreateNode(FP_ISZERO, {x})
              : c.nf->CreateNode(FP_SMT_EQ, {x, k});
      for (int order = 0; order < 2 && semOk; order++)
      {
        const ASTVec kids = order ? ASTVec{k, x} : ASTVec{x, k};
        const ASTNode got = c.nf->CreateNode(FP_EQ, kids);
        if (got != want)
        {
          structOk = false;
          why = "unexpected form at v=" + std::to_string(v);
        }
        const std::string bad =
            c.firstDisagreement(c.hf->CreateNode(FP_EQ, kids), got);
        if (!bad.empty())
        {
          semOk = false;
          why = bad + " (constant v=" + std::to_string(v) + ")";
        }
      }
    }
    report("fp.eq(x, const) exact for every constant", semOk, why);
    report("fp.eq(x, const) takes the expected form", structOk, why);

    // The three forms really are distinguishable: a NaN constant must not
    // become an equality, and a zero constant must catch the *other* zero.
    // (Rewriting fp.eq(x, +0) to `= x +0` would be the classic unsoundness.)
    const ASTNode posZero = c.fpConst(EB, SB, 0);
    const ASTNode negZero = c.fpConst(EB, SB, signBit);
    report("fp.eq(x, +0) and fp.eq(x, -0) agree",
           c.nf->CreateNode(FP_EQ, {x, posZero}) ==
               c.nf->CreateNode(FP_EQ, {x, negZero}));

    // `=` against a constant must NOT pick up any of this: it is already the
    // strong equality, and a zero constant there distinguishes the two zeros.
    // (Only the operand order may change, so compare kinds, not nodes.)
    report("smt = keeps its zero constant",
           c.nf->CreateNode(FP_SMT_EQ, {x, posZero}).GetKind() == FP_SMT_EQ &&
               c.nf->CreateNode(FP_SMT_EQ, {x, posZero}) !=
                   c.nf->CreateNode(FP_SMT_EQ, {x, negZero}));
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
      c.checkTerm("x / -1.0 = neg x", FP_DIV, w, {r, x, negOne});
      // 1.0 / x is not x: the divisor-only rule must leave this unchanged (and
      // must not, in any case, change its meaning).
      c.checkTerm("1.0 / x unchanged", FP_DIV, w, {r, one, x}, false);
    }
  }

  // ---- Constant-operand collapses (found by tools/fp_rewrite_gen). ----
  // Each check requires the factory to produce exactly the expected node AND
  // the unsimplified original to agree with it on every float of the format.

  {
    ASTNode x = c.fp(EB, SB);
    const unsigned w = x.GetValueWidth();
    ASTNode nan = c.fpConst(EB, SB, packNaN(EB, SB));
    ASTNode pinf = c.fpConst(EB, SB, packInf(EB, SB, false));
    ASTNode ninf = c.fpConst(EB, SB, packInf(EB, SB, true));
    ASTNode pz = c.fpConst(EB, SB, packZero(EB, SB, false));
    ASTNode nz = c.fpConst(EB, SB, packZero(EB, SB, true));

    // NaN absorbs through the arithmetic: either operand, every mode
    // (round-toward-negative is the usually-sensitive one).
    for (unsigned mode : {(unsigned)ROUND_NEAREST_TIES_TO_EVEN,
                          (unsigned)ROUND_TOWARD_NEGATIVE})
    {
      ASTNode r = c.rm(mode);
      c.checkTermIs("x + NaN = NaN", FP_ADD, w, {r, x, nan}, nan);
      c.checkTermIs("NaN + x = NaN", FP_ADD, w, {r, nan, x}, nan);
      c.checkTermIs("x - NaN = NaN", FP_SUB, w, {r, x, nan}, nan);
      c.checkTermIs("NaN - x = NaN", FP_SUB, w, {r, nan, x}, nan);
      c.checkTermIs("x * NaN = NaN", FP_MUL, w, {r, x, nan}, nan);
      c.checkTermIs("NaN * x = NaN", FP_MUL, w, {r, nan, x}, nan);
      c.checkTermIs("x / NaN = NaN", FP_DIV, w, {r, x, nan}, nan);
      c.checkTermIs("NaN / x = NaN", FP_DIV, w, {r, nan, x}, nan);
    }

    // The rm-guarded signed-zero identities: x + (-0) = x except under
    // round-toward-negative, and x + (+0) = x only there -- the sum of the
    // opposite zeros is the input that decides. Where the identity does not
    // apply, the zero must survive (only equivalence is required).
    {
      const unsigned modes[] = {
          (unsigned)ROUND_NEAREST_TIES_TO_EVEN,
          (unsigned)ROUND_NEAREST_TIES_TO_AWAY,
          (unsigned)ROUND_TOWARD_POSITIVE,
          (unsigned)ROUND_TOWARD_NEGATIVE,
          (unsigned)ROUND_TOWARD_ZERO,
      };
      const char* names[] = {"RNE", "RNA", "RTP", "RTN", "RTZ"};
      for (int i = 0; i < 5; i++)
      {
        ASTNode r = c.rm(modes[i]);
        const bool rtn = (modes[i] == (unsigned)ROUND_TOWARD_NEGATIVE);
        const std::string sfx = std::string(" [") + names[i] + "]";
        if (rtn)
        {
          c.checkTermIs("x + +0 = x" + sfx, FP_ADD, w, {r, x, pz}, x);
          c.checkTerm("x + -0 keeps the zero" + sfx, FP_ADD, w, {r, x, nz},
                      false);
        }
        else
        {
          c.checkTermIs("x + -0 = x" + sfx, FP_ADD, w, {r, x, nz}, x);
          c.checkTerm("x + +0 keeps the zero" + sfx, FP_ADD, w, {r, x, pz},
                      false);
        }
      }
      // Via the sub-to-add lowering: x - (+0) adds -0.
      ASTNode rne = c.rm(ROUND_NEAREST_TIES_TO_EVEN);
      c.checkTermIs("x - +0 = x [RNE]", FP_SUB, w, {rne, x, pz}, x);
    }

    // fp.rem's invalid operands are NaN whatever the other operand is.
    ASTNode b = c.fp(EB, SB);
    c.checkTermIs("rem(NaN, b) = NaN", FP_REM, w, {nan, b}, nan);
    c.checkTermIs("rem(a, NaN) = NaN", FP_REM, w, {x, nan}, nan);
    c.checkTermIs("rem(+oo, b) = NaN", FP_REM, w, {pinf, b}, nan);
    c.checkTermIs("rem(-oo, b) = NaN", FP_REM, w, {ninf, b}, nan);
    c.checkTermIs("rem(a, +0) = NaN", FP_REM, w, {x, pz}, nan);
    c.checkTermIs("rem(a, -0) = NaN", FP_REM, w, {x, nz}, nan);

    // fp.min/fp.max ignore a NaN operand, and the matching extreme absorbs.
    c.checkTermIs("min(x, NaN) = x", FP_MIN, w, {x, nan}, x);
    c.checkTermIs("min(NaN, x) = x", FP_MIN, w, {nan, x}, x);
    c.checkTermIs("max(x, NaN) = x", FP_MAX, w, {x, nan}, x);
    c.checkTermIs("max(NaN, x) = x", FP_MAX, w, {nan, x}, x);
    c.checkTermIs("min(x, -oo) = -oo", FP_MIN, w, {x, ninf}, ninf);
    c.checkTermIs("max(x, +oo) = +oo", FP_MAX, w, {x, pinf}, pinf);
    // The opposite extreme decides nothing (NaN breaks it): must survive.
    c.checkTerm("min(x, +oo) keeps both", FP_MIN, w, {x, pinf}, false);
    c.checkTerm("max(x, -oo) keeps both", FP_MAX, w, {x, ninf}, false);

    // Comparisons against NaN and the extremes. The lt/leq forms arrive at
    // the gt/geq rules through the mirroring, so both spellings are checked.
    const ASTNode notNan =
        c.hf->CreateNode(NOT, {c.hf->CreateNode(FP_ISNAN, {x})});
    c.checkNodeIs("fp.gt(x, NaN) -> false", FP_GT, {x, nan}, c.mgr.ASTFalse);
    c.checkNodeIs("fp.gt(NaN, x) -> false", FP_GT, {nan, x}, c.mgr.ASTFalse);
    c.checkNodeIs("fp.gt(-oo, x) -> false", FP_GT, {ninf, x}, c.mgr.ASTFalse);
    c.checkNodeIs("fp.gt(x, +oo) -> false", FP_GT, {x, pinf}, c.mgr.ASTFalse);
    c.checkNodeIs("fp.lt(x, NaN) -> false", FP_LT, {x, nan}, c.mgr.ASTFalse);
    c.checkNodeIs("fp.lt(x, -oo) -> false", FP_LT, {x, ninf}, c.mgr.ASTFalse);
    c.checkNodeIs("fp.lt(+oo, x) -> false", FP_LT, {pinf, x}, c.mgr.ASTFalse);
    c.checkNodeIs("fp.geq(NaN, x) -> false", FP_GEQ, {nan, x}, c.mgr.ASTFalse);
    c.checkNodeIs("fp.geq(x, NaN) -> false", FP_GEQ, {x, nan}, c.mgr.ASTFalse);
    c.checkNodeIs("fp.geq(+oo, x) -> not isNaN", FP_GEQ, {pinf, x}, notNan);
    c.checkNodeIs("fp.geq(x, -oo) -> not isNaN", FP_GEQ, {x, ninf}, notNan);
    c.checkNodeIs("fp.leq(-oo, x) -> not isNaN", FP_LEQ, {ninf, x}, notNan);
    c.checkNodeIs("fp.leq(x, +oo) -> not isNaN", FP_LEQ, {x, pinf}, notNan);

    // (= x NaN) is exactly (fp.isNaN x), but it is deliberately NOT
    // rewritten: PropagateEqualities substitutes through a `=` with a
    // constant side (x := NaN everywhere), which is strictly stronger than
    // holding the smaller predicate.
    report("= keeps its NaN constant",
           c.nf->CreateNode(FP_SMT_EQ, {x, nan}).GetKind() == FP_SMT_EQ);
  }

  // fp.fma at the smaller format (its circuits are much larger): NaN in any
  // operand absorbs, and an exact product -- a +-1.0 multiplicand, or two
  // constant multiplicands holding a zero -- reduces the fma to the fp.add
  // of the product, which then re-simplifies by the rules above. The
  // expected nodes are built through the simplifying factory so they take
  // the same post-rewrite form.
  {
    ASTNode y = c.fp(SEB, SSB), z = c.fp(SEB, SSB);
    const unsigned w = y.GetValueWidth();
    ASTNode nan = c.fpConst(SEB, SSB, packNaN(SEB, SSB));
    ASTNode pinf = c.fpConst(SEB, SSB, packInf(SEB, SSB, false));
    ASTNode pz = c.fpConst(SEB, SSB, packZero(SEB, SSB, false));
    ASTNode nz = c.fpConst(SEB, SSB, packZero(SEB, SSB, true));
    ASTNode one = c.fpConst(SEB, SSB, packOne(SEB, SSB, false));
    ASTNode negOne = c.fpConst(SEB, SSB, packOne(SEB, SSB, true));
    for (unsigned mode : {(unsigned)ROUND_NEAREST_TIES_TO_EVEN,
                          (unsigned)ROUND_TOWARD_NEGATIVE})
    {
      ASTNode r = c.rm(mode);
      c.checkTermIs("fma(rm, NaN, y, z) = NaN", FP_FMA, w, {r, nan, y, z},
                    nan);
      c.checkTermIs("fma(rm, y, NaN, z) = NaN", FP_FMA, w, {r, y, nan, z},
                    nan);
      c.checkTermIs("fma(rm, y, z, NaN) = NaN", FP_FMA, w, {r, y, z, nan},
                    nan);
      c.checkTermIs("fma(rm, 1, y, z) = y + z", FP_FMA, w, {r, one, y, z},
                    c.nf->CreateTerm(FP_ADD, w, {r, y, z}));
      c.checkTermIs("fma(rm, -1, y, z) = -y + z", FP_FMA, w,
                    {r, negOne, y, z},
                    c.nf->CreateTerm(FP_ADD, w,
                                     {r, c.unary(c.hf, FP_NEG, y), z}));
      c.checkTermIs("fma(rm, +0, +oo, z) = NaN", FP_FMA, w, {r, pz, pinf, z},
                    nan);
      c.checkTermIs("fma(rm, +0, -0, z) = -0 + z", FP_FMA, w, {r, pz, nz, z},
                    c.nf->CreateTerm(FP_ADD, w, {r, nz, z}));
    }
  }

  // ---- Depth-2 rules (found by fp_rewrite_gen's nested search). ----
  // Facts about the never-below-zero terms (abs, sqrt, a self-product),
  // classification predicates looking through value-preserving shapes, `=`
  // against NaN with a compound side, and roundToIntegral idempotence.

  {
    ASTNode x = c.fp(EB, SB);
    const unsigned w = x.GetValueWidth();
    ASTNode nan = c.fpConst(EB, SB, packNaN(EB, SB));
    ASTNode pz = c.fpConst(EB, SB, packZero(EB, SB, false));
    ASTNode nz = c.fpConst(EB, SB, packZero(EB, SB, true));
    ASTNode negOne = c.fpConst(EB, SB, packOne(EB, SB, true));
    ASTNode ninf = c.fpConst(EB, SB, packInf(EB, SB, true));
    const ASTNode notNanX =
        c.hf->CreateNode(NOT, {c.hf->CreateNode(FP_ISNAN, {x})});

    // The inner terms, built unsimplified. Both a "round" and a "directed"
    // mode for the ones that round.
    auto mk = [&](Kind k, const ASTVec& ch) {
      ASTNode n = c.hf->CreateTerm(k, w, ch);
      n.SetExpWidth(EB);
      n.SetSigWidth(SB);
      return n;
    };
    for (unsigned mode : {(unsigned)ROUND_NEAREST_TIES_TO_EVEN,
                          (unsigned)ROUND_TOWARD_NEGATIVE})
    {
      ASTNode r = c.rm(mode);
      ASTNode absx = c.unary(c.hf, FP_ABS, x);
      ASTNode sq = mk(FP_MUL, {r, x, x});
      ASTNode sqrtx = mk(FP_SQRT, {r, x});
      ASTNode dbl = mk(FP_ADD, {r, x, x});
      ASTNode rti = mk(FP_ROUNDTOINTEGRAL, {r, x});

      // Range facts: never-below-zero terms against sign-decided constants.
      c.checkNodeIs("gt(-1, |x|) -> false", FP_GT, {negOne, absx},
                    c.mgr.ASTFalse);
      c.checkNodeIs("gt(+0, sqrt x) -> false", FP_GT, {pz, sqrtx},
                    c.mgr.ASTFalse);
      c.checkNodeIs("gt(-0, x*x) -> false", FP_GT, {nz, sq}, c.mgr.ASTFalse);
      c.checkNodeIs("gt(|x|, -1) -> not isNaN x", FP_GT, {absx, negOne},
                    notNanX);
      c.checkNodeIs("gt(x*x, -oo) -> not isNaN x", FP_GT, {sq, ninf},
                    notNanX);
      c.checkNodeIs(
          "gt(sqrt x, -1) -> not isNaN(sqrt x)", FP_GT, {sqrtx, negOne},
          c.hf->CreateNode(NOT, {c.hf->CreateNode(FP_ISNAN, {sqrtx})}));
      c.checkNodeIs("geq(|x|, -0) -> not isNaN x", FP_GEQ, {absx, nz},
                    notNanX);
      c.checkNodeIs("geq(-1, x*x) -> false", FP_GEQ, {negOne, sq},
                    c.mgr.ASTFalse);
      c.checkNodeIs("geq(+0, |x|) -> isZero x", FP_GEQ, {pz, absx},
                    c.hf->CreateNode(FP_ISZERO, {x}));
      // isZero(x*x) does NOT reduce to isZero(x) -- a tiny square
      // underflows to +0 -- so the squeeze must stop at isZero(x*x).
      c.checkNodeIs("geq(-0, x*x) -> isZero(x*x)", FP_GEQ, {nz, sq},
                    c.hf->CreateNode(FP_ISZERO, {sq}));
      // The lt/leq spellings arrive through the mirror.
      c.checkNodeIs("lt(|x|, -1) -> false", FP_LT, {absx, negOne},
                    c.mgr.ASTFalse);
      c.checkNodeIs("leq(sqrt x, -0) -> isZero x", FP_LEQ, {sqrtx, nz},
                    c.hf->CreateNode(FP_ISZERO, {x}));

      // t against |t|, no constant involved.
      c.checkNodeIs("gt(x, |x|) -> false", FP_GT, {x, absx}, c.mgr.ASTFalse);
      c.checkNodeIs("lt(|x|, x) -> false", FP_LT, {absx, x}, c.mgr.ASTFalse);
      c.checkNodeIs("geq(|x|, x) -> not isNaN x", FP_GEQ, {absx, x},
                    notNanX);
      c.checkNodeIs("leq(x, |x|) -> not isNaN x", FP_LEQ, {x, absx},
                    notNanX);

      // Classification predicates looking through value-preserving shapes.
      const ASTNode isNanX = c.hf->CreateNode(FP_ISNAN, {x});
      c.checkNodeIs("isNaN(rti x) -> isNaN x", FP_ISNAN, {rti}, isNanX);
      c.checkNodeIs("isNaN(x+x) -> isNaN x", FP_ISNAN, {dbl}, isNanX);
      c.checkNodeIs("isNaN(x*x) -> isNaN x", FP_ISNAN, {sq}, isNanX);
      c.checkNodeIs("isZero(sqrt x) -> isZero x", FP_ISZERO, {sqrtx},
                    c.hf->CreateNode(FP_ISZERO, {x}));
      c.checkNodeIs("isZero(x+x) -> isZero x", FP_ISZERO, {dbl},
                    c.hf->CreateNode(FP_ISZERO, {x}));
      c.checkNodeIs("isInfinite(rti x) -> isInfinite x", FP_ISINFINITE,
                    {rti}, c.hf->CreateNode(FP_ISINFINITE, {x}));
      c.checkNodeIs("isSubnormal(rti x) -> false", FP_ISSUBNORMAL, {rti},
                    c.mgr.ASTFalse);
      c.checkNodeIs("isNegative(x*x) -> false", FP_ISNEGATIVE, {sq},
                    c.mgr.ASTFalse);
      c.checkNodeIs("isPositive(x*x) -> not isNaN x", FP_ISPOSITIVE, {sq},
                    notNanX);
      c.checkNodeIs("isNegative(rti x) -> isNegative x", FP_ISNEGATIVE,
                    {rti}, c.hf->CreateNode(FP_ISNEGATIVE, {x}));
      c.checkNodeIs("isPositive(sqrt x) -> isPositive x", FP_ISPOSITIVE,
                    {sqrtx}, c.hf->CreateNode(FP_ISPOSITIVE, {x}));
      c.checkNodeIs("isNegative(x+x) -> isNegative x", FP_ISNEGATIVE, {dbl},
                    c.hf->CreateNode(FP_ISNEGATIVE, {x}));
      c.checkNodeIs("isPositive(x+x) -> isPositive x", FP_ISPOSITIVE, {dbl},
                    c.hf->CreateNode(FP_ISPOSITIVE, {x}));

      // `=` against NaN with a compound side is the NaN test (the bare-x
      // spelling keeps its `=`, checked above); the created isNaN then
      // simplifies through the same rules.
      c.checkNodeIs("(= |x| NaN) -> isNaN x", FP_SMT_EQ, {absx, nan},
                    isNanX);
      c.checkNodeIs("(= NaN x*x) -> isNaN x", FP_SMT_EQ, {nan, sq}, isNanX);

      // abs of a self-product is a no-op.
      c.checkTermIs("abs(x*x) = x*x", FP_ABS, w, {sq}, sq);
    }

    // roundToIntegral idempotence must hold across DIFFERENT modes: the
    // inner result is integral (or a zero, infinity or NaN), and rounding
    // such a value is exact under every mode. The generator only verified
    // the shared-mode instances, so cross-mode is the case to pin here.
    {
      ASTNode inner = mk(FP_ROUNDTOINTEGRAL,
                         {c.rm(ROUND_TOWARD_NEGATIVE), x});
      c.checkTermIs("rti(RTP, rti(RTN, x)) = rti(RTN, x)",
                    FP_ROUNDTOINTEGRAL, w,
                    {c.rm(ROUND_TOWARD_POSITIVE), inner}, inner);
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

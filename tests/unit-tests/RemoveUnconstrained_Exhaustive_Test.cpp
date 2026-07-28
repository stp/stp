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
 * Exhaustive tests for unconstrained-variable elimination (RemoveUnconstrained).
 *
 * The pass is NOT an equivalence-preserving rewrite: it re-parameterises the
 * problem, replacing a use of an unconstrained (single-use) variable with a
 * fresh variable and recording a *definition* of the eliminated variable in the
 * substitution map. Soundness therefore means: substituting those definitions
 * back into the original formula reproduces exactly the rewritten formula, as a
 * function of the surviving/fresh variables. We check that identity
 * exhaustively at small bit-widths.
 *
 * Two groups:
 *
 *  1) Soundness (checkSound):
 *       result   = RemoveUnconstrained(F)
 *       back     = F with the substitution map applied to a fixed point
 *     `back` and `result` must agree on every assignment of their free
 *     variables. `back != result` syntactically (that's the whole point) but
 *     they must be equal functions. A surviving "anchor" variable keeps the
 *     check non-trivial (otherwise the pass collapses everything to true).
 *
 *  2) Collapse / missing-rule diagnostic (expectCollapse / expectNoCollapse):
 *     A top-level boolean built only from single-use unconstrained variables
 *     collapses all the way to `true` iff every operator on the path has a
 *     rule. `EQ(op(x,y), constant)` collapses to `true` exactly when `op` has
 *     an unconstrained rule, so it's a direct probe for missing rules.
 *
 *     Beyond the per-kind rules there is the generalised ground-path
 *     collapse (tryGroundPathCollapse + AchievableImage): when a variable's
 *     only use is a chain of operations against constants ending in a
 *     predicate against a constant -- e.g. ((x mod 4) == 2) -- the predicate
 *     is replaced by a fresh boolean when both its polarities are provably
 *     achievable. Those cases are tested in the _GroundPath groups below.
 */

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Parser/parser.h"
#include "stp/Simplifier/RemoveUnconstrained.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <functional>
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace stp;

namespace
{
const unsigned W = 3; // default bit-width for enumerated variables.

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* nf; // simplifying factory: what the pass itself uses.
  NodeFactory* hf; // hashing factory: builds inputs without pre-simplifying.
  SubstitutionMap sm;
  Simplifier simp;
  unsigned counter = 0;

  Context() : snf(*(mgr.hashingNodeFactory), mgr), sm(&mgr), simp(&mgr, &sm)
  {
    // The bit-vector library backs every constant; boot it once per process.
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;

    mgr.defaultNodeFactory = &snf;
    nf = &snf;
    hf = mgr.hashingNodeFactory;
  }

  ASTNode bv(unsigned width = W)
  {
    return mgr.CreateSymbol(("bv" + std::to_string(counter++)).c_str(), 0,
                            width);
  }

  ASTNode boolean()
  {
    return mgr.CreateSymbol(("b" + std::to_string(counter++)).c_str(), 0, 0);
  }

  ASTNode konst(unsigned value, unsigned width = W)
  {
    return mgr.CreateBVConst(width, value);
  }

  // Run the pass, returning the rewritten top-level formula. The definitions
  // of the eliminated variables are left in the substitution map.
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

  // Apply the substitution map produced by the pass to `n`, to a fixed point.
  // The pass uses UpdateSubstitutionMapFewChecks, so definitions can chain
  // (x := f(v), v := g(w), ...); iterate until nothing changes.
  ASTNode backSubstitute(const ASTNode& n)
  {
    ASTNode cur = n;
    for (int i = 0; i < 64; i++)
    {
      ASTNodeMap fromTo = *simp.Return_SolverMap(); // replace() mutates it.
      ASTNodeMap cache;
      ASTNode next = SubstitutionMap::replace(cur, fromTo, cache, &snf);
      if (next == cur)
        return cur;
      cur = next;
    }
    ADD_FAILURE() << "back-substitution did not reach a fixed point";
    return cur;
  }

  // Evaluate a fully-assigned node down to a constant.
  ASTNode eval(const ASTNode& n, ASTNodeMap assignment /*by value*/)
  {
    ASTNodeMap cache;
    ASTNode s = SubstitutionMap::replace(n, assignment, cache, &snf);
    if (s.isConstant())
      return s;
    return NonMemberBVConstEvaluator(&mgr, s);
  }

  ASTNode valueFor(const ASTNode& sym, unsigned v)
  {
    if (sym.GetType() == BOOLEAN_TYPE)
      return (v & 1) ? mgr.ASTTrue : mgr.ASTFalse;
    return konst(v, sym.GetValueWidth());
  }

  unsigned domainSize(const ASTNode& sym)
  {
    return (sym.GetType() == BOOLEAN_TYPE) ? 2u : (1u << sym.GetValueWidth());
  }

  // `before` and `after` must agree on every assignment of their (shared) free
  // variables.
  void checkEquivalent(const ASTNode& before, const ASTNode& after)
  {
    ASTNodeSet symSet;
    collectSymbols(before, symSet);
    collectSymbols(after, symSet);
    std::vector<ASTNode> syms(symSet.begin(), symSet.end());

    // Guard against an accidental combinatorial explosion.
    unsigned long combos = 1;
    for (const auto& s : syms)
      combos *= domainSize(s);
    ASSERT_LE(combos, 1u << 16)
        << "too many assignments (" << combos << ") -- lower the width";

    std::vector<unsigned> idx(syms.size(), 0);
    for (unsigned long c = 0; c < combos; c++)
    {
      ASTNodeMap assignment;
      unsigned long rest = c;
      for (size_t i = 0; i < syms.size(); i++)
      {
        const unsigned size = domainSize(syms[i]);
        assignment.insert({syms[i], valueFor(syms[i], rest % size)});
        rest /= size;
      }
      ASTNodeMap a2 = assignment; // eval() consumes the map.
      ASSERT_EQ(eval(before, assignment), eval(after, a2))
          << "unconstrained rewrite changed the meaning at assignment " << c;
    }
  }

  // Wrap the operator result so that (a) exactly the operator's rule is
  // exercised and (b) an anchor variable survives, keeping the equivalence
  // check non-trivial. `keep` is used twice (here and in the anchor) so it is
  // never itself unconstrained.
  // An anchor `BVLT(keep, 1)` (i.e. keep == 0) references `keep` without
  // folding it away, so `keep` keeps a second use and survives the pass.
  ASTNode anchorFor(const ASTNode& keep)
  {
    return hf->CreateNode(BVLT, keep, konst(1, keep.GetValueWidth()));
  }

  // Soundness of an arbitrary top-level formula, used as-is. The caller
  // supplies any anchor needed; unlike checkSound there is no EQ(op, keep)
  // wrapper, so a predicate whose other side is a constant stays ground and
  // exercises the ground-path collapse.
  void checkSoundTop(const ASTNode& top)
  {
    ASTNode result = run(top);
    ASTNode back = backSubstitute(top);
    checkEquivalent(back, result);
  }

  void checkSound(const ASTNode& opNode)
  {
    ASTNode top;
    if (opNode.GetType() == BOOLEAN_TYPE)
    {
      ASTNode keep = bv();
      top = hf->CreateNode(AND, opNode, anchorFor(keep));
    }
    else
    {
      // `keep` must match the operator's width so EQ(op, keep) is well typed.
      ASTNode keep = bv(opNode.GetValueWidth());
      top = hf->CreateNode(AND, hf->CreateNode(EQ, opNode, keep),
                           anchorFor(keep));
    }

    ASTNode result = run(top);
    ASTNode back = backSubstitute(top);
    checkEquivalent(back, result);
  }

  // Equisatisfiability with model mapping, for the image-constrained
  // rewrite: a fresh variable stands for a shared term, with a
  // membership constraint conjoined. The pointwise identity the
  // constant-witness rules satisfy does not hold off the image, so
  // instead check that (a) every assignment satisfying `result` also
  // satisfies the back-substituted original -- models map back -- and
  // (b) original and result are satisfiable together or not at all.
  void checkEquisat(const ASTNode& original, const ASTNode& result)
  {
    ASTNode back = backSubstitute(original);

    ASTNodeSet symSet;
    collectSymbols(result, symSet);
    collectSymbols(back, symSet);
    std::vector<ASTNode> syms(symSet.begin(), symSet.end());
    unsigned long combos = 1;
    for (const auto& s : syms)
      combos *= domainSize(s);
    ASSERT_LE(combos, 1u << 16) << "too many assignments";

    bool resultSat = false;
    for (unsigned long c = 0; c < combos; c++)
    {
      ASTNodeMap assignment;
      unsigned long rest = c;
      for (size_t i = 0; i < syms.size(); i++)
      {
        const unsigned size = domainSize(syms[i]);
        assignment.insert({syms[i], valueFor(syms[i], rest % size)});
        rest /= size;
      }
      ASTNodeMap a2 = assignment;
      if (eval(result, assignment) == mgr.ASTTrue)
      {
        resultSat = true;
        ASSERT_EQ(eval(back, a2), mgr.ASTTrue)
            << "a model of the result failed to map back at assignment " << c;
      }
    }

    ASTNodeSet oset;
    collectSymbols(original, oset);
    std::vector<ASTNode> osyms(oset.begin(), oset.end());
    unsigned long ocombos = 1;
    for (const auto& s : osyms)
      ocombos *= domainSize(s);
    ASSERT_LE(ocombos, 1u << 16);
    bool origSat = false;
    for (unsigned long c = 0; c < ocombos && !origSat; c++)
    {
      ASTNodeMap assignment;
      unsigned long rest = c;
      for (size_t i = 0; i < osyms.size(); i++)
      {
        const unsigned size = domainSize(osyms[i]);
        assignment.insert({osyms[i], valueFor(osyms[i], rest % size)});
        rest /= size;
      }
      origSat = (eval(original, assignment) == mgr.ASTTrue);
    }
    ASSERT_EQ(origSat, resultSat) << "satisfiability changed";
  }

  // As checkSound, but the operator takes the surviving `keep` as one operand
  // (used for the binary comparisons, which have a dedicated one-sided rule).
  void checkSoundWithKeep(Kind k, bool termLevel)
  {
    ASTNode x = bv();
    ASTNode keep = bv();
    ASTNode op = termLevel ? hf->CreateTerm(k, W, x, keep)
                           : hf->CreateNode(k, x, keep);
    ASTNode anchor = anchorFor(keep);
    ASTNode top =
        op.GetType() == BOOLEAN_TYPE
            ? hf->CreateNode(AND, op, anchor)
            : hf->CreateNode(AND, hf->CreateNode(EQ, op, keep), anchor);

    ASTNode result = run(top);
    ASTNode back = backSubstitute(top);
    checkEquivalent(back, result);
  }
};

// A top-level boolean built from single-use unconstrained variables collapses
// to `true` iff every operator on the path has an elimination rule.
void expectCollapse(std::function<ASTNode(Context&)> build)
{
  Context c;
  ASTNode top = build(c);
  ASSERT_EQ(top.GetType(), BOOLEAN_TYPE);
  ASTNode result = c.run(top);
  EXPECT_EQ(result, c.mgr.ASTTrue)
      << "expected the formula to reduce to true (rule present)";
}

void expectNoCollapse(std::function<ASTNode(Context&)> build)
{
  Context c;
  ASTNode top = build(c);
  ASTNode result = c.run(top);
  EXPECT_NE(result, c.mgr.ASTTrue)
      << "formula collapsed -- a rule now exists; move this operator up to the "
         "handled list";
}
} // namespace

/////////////////////////////////////////////////////////////////////////////
// 1) Soundness: back-substitution reproduces the rewritten formula.
/////////////////////////////////////////////////////////////////////////////

TEST(RemoveUnconstrained_Exhaustive, plus)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVPLUS, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, sub)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVSUB, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, bvxor)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVXOR, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, concat)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVCONCAT, 2 * W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, mult_both_unconstrained)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVMULT, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, mult_odd_constant)
{
  Context c;
  // The other operand is an odd constant, so the multiplicative-inverse rule
  // fires rather than the both-unconstrained one.
  c.checkSound(c.hf->CreateTerm(BVMULT, W, c.konst(3), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, udiv_both_unconstrained)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVDIV, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, urem_both_unconstrained)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVMOD, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, sdiv_both_unconstrained)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(SBVDIV, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, srem_both_unconstrained)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(SBVREM, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, smod_both_unconstrained)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(SBVMOD, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, shift_left)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVLEFTSHIFT, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, shift_right)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVRIGHTSHIFT, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, shift_arithmetic_right)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVSRSHIFT, W, c.bv(), c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, bvnot)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVNOT, W, c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, uminus)
{
  Context c;
  c.checkSound(c.hf->CreateTerm(BVUMINUS, W, c.bv()));
}

TEST(RemoveUnconstrained_Exhaustive, extract)
{
  Context c;
  // (_ extract 2 1) of a fresh 3-bit variable.
  c.checkSound(
      c.hf->CreateTerm(BVEXTRACT, 2, c.bv(), c.konst(2, 32), c.konst(1, 32)));
}

TEST(RemoveUnconstrained_Exhaustive, ite_then_branch)
{
  Context c;
  // condition + then-branch unconstrained.
  c.checkSound(c.hf->CreateTerm(ITE, W, c.boolean(), c.bv(), c.bv()));
}

// A variable all of whose uses are disjoint extracts goes through the separate
// splitExtractOnly() path (getDisjointExtractVariables), not the ordinary
// BVEXTRACT case. Build such a variable and check the whole rewrite is sound.
TEST(RemoveUnconstrained_Exhaustive, disjoint_extracts_full_cover)
{
  Context c;
  const unsigned w = 4;
  ASTNode x = c.bv(w);
  // Two disjoint extracts that together cover all of x: [1:0] and [3:2].
  ASTNode lo =
      c.hf->CreateTerm(BVEXTRACT, 2, x, c.konst(1, 32), c.konst(0, 32));
  ASTNode hi =
      c.hf->CreateTerm(BVEXTRACT, 2, x, c.konst(3, 32), c.konst(2, 32));
  ASTNode top = c.hf->CreateNode(
      BVLT, c.hf->CreateTerm(BVCONCAT, 4, hi, lo), c.konst(5, 4));

  ASTNode result = c.run(top);
  // Confirm the split actually fired: splitExtractOnly defines x := concat(...).
  ASSERT_EQ(c.simp.Return_SolverMap()->count(x), 1u)
      << "splitExtractOnly did not eliminate x";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

// As above but the extracts leave a gap (bit 2), exercising the fresh-padding
// branch of splitExtractOnly().
TEST(RemoveUnconstrained_Exhaustive, disjoint_extracts_with_gap)
{
  Context c;
  const unsigned w = 4;
  ASTNode x = c.bv(w);
  // [1:0] and [3:3]; bit 2 is never referenced.
  ASTNode lo =
      c.hf->CreateTerm(BVEXTRACT, 2, x, c.konst(1, 32), c.konst(0, 32));
  ASTNode hi =
      c.hf->CreateTerm(BVEXTRACT, 1, x, c.konst(3, 32), c.konst(3, 32));
  ASTNode top = c.hf->CreateNode(
      BVLT, c.hf->CreateTerm(BVCONCAT, 3, hi, lo), c.konst(5, 3));

  ASTNode result = c.run(top);
  ASSERT_EQ(c.simp.Return_SolverMap()->count(x), 1u)
      << "splitExtractOnly did not eliminate x";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

// The extracts cover the low bits but leave the top uncovered ([2:1] and
// [0:0], bit 3 free), exercising the trailing fresh-padding branch of
// splitExtractOnly() (padding appended after the last extracted piece).
TEST(RemoveUnconstrained_Exhaustive, disjoint_extracts_top_gap)
{
  Context c;
  const unsigned w = 4;
  ASTNode x = c.bv(w);
  ASTNode lo =
      c.hf->CreateTerm(BVEXTRACT, 1, x, c.konst(0, 32), c.konst(0, 32));
  ASTNode mid =
      c.hf->CreateTerm(BVEXTRACT, 2, x, c.konst(2, 32), c.konst(1, 32));
  ASTNode top = c.hf->CreateNode(
      BVLT, c.hf->CreateTerm(BVCONCAT, 3, mid, lo), c.konst(5, 3));

  ASTNode result = c.run(top);
  ASSERT_EQ(c.simp.Return_SolverMap()->count(x), 1u)
      << "splitExtractOnly did not eliminate x";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_Exhaustive, eq_term)
{
  Context c;
  // EQ where one side is an unconstrained variable and the other survives.
  c.checkSoundWithKeep(EQ, /*termLevel=*/false);
}

TEST(RemoveUnconstrained_Exhaustive, sgt_one_sided)
{
  Context c;
  c.checkSoundWithKeep(BVSGT, /*termLevel=*/false);
}

TEST(RemoveUnconstrained_Exhaustive, sge_one_sided)
{
  Context c;
  c.checkSoundWithKeep(BVSGE, /*termLevel=*/false);
}

TEST(RemoveUnconstrained_Exhaustive, ugt_one_sided)
{
  Context c;
  c.checkSoundWithKeep(BVGT, /*termLevel=*/false);
}

TEST(RemoveUnconstrained_Exhaustive, uge_one_sided)
{
  Context c;
  c.checkSoundWithKeep(BVGE, /*termLevel=*/false);
}

/////////////////////////////////////////////////////////////////////////////
// 2) Collapse diagnostic: which operators reduce a formula of unconstrained
//    variables all the way down to true. Missing rules show up as the
//    formula NOT collapsing.
/////////////////////////////////////////////////////////////////////////////

// --- Boolean operators: probed directly. ---

TEST(RemoveUnconstrained_Collapse, eq)
{
  expectCollapse([](Context& c) { return c.hf->CreateNode(EQ, c.bv(), c.bv()); });
}

TEST(RemoveUnconstrained_Collapse, sgt)
{
  expectCollapse(
      [](Context& c) { return c.hf->CreateNode(BVSGT, c.bv(), c.bv()); });
}

TEST(RemoveUnconstrained_Collapse, ugt)
{
  expectCollapse(
      [](Context& c) { return c.hf->CreateNode(BVGT, c.bv(), c.bv()); });
}

TEST(RemoveUnconstrained_Collapse, boolean_and)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(AND, c.boolean(), c.boolean());
  });
}

TEST(RemoveUnconstrained_Collapse, boolean_xor)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(XOR, c.boolean(), c.boolean());
  });
}

// --- Term operators: probed via EQ(op(x,y), constant). ---

TEST(RemoveUnconstrained_Collapse, plus)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(BVPLUS, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, sub)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(BVSUB, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, bvxor)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(BVXOR, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, mult)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(BVMULT, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, udiv)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(BVDIV, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, concat)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(
        EQ, c.hf->CreateTerm(BVCONCAT, 2 * W, c.bv(), c.bv()), c.konst(1, 2 * W));
  });
}

TEST(RemoveUnconstrained_Collapse, shift_left)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(
        EQ, c.hf->CreateTerm(BVLEFTSHIFT, W, c.bv(), c.bv()), c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, bvnot)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(BVNOT, W, c.bv()), c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, uminus)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(BVUMINUS, W, c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, ite)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(
        EQ, c.hf->CreateTerm(ITE, W, c.boolean(), c.bv(), c.bv()), c.konst(1));
  });
}

// --- Division / remainder, unsigned and signed. All handled: both-operand
//     unconstrained collapses to true. Remove a rule and the matching test
//     turns into a non-collapse. ---

TEST(RemoveUnconstrained_Collapse, urem)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(BVMOD, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, sdiv)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(SBVDIV, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, srem)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(SBVREM, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, smod)
{
  expectCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(SBVMOD, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

/////////////////////////////////////////////////////////////////////////////
// 3) Ground-path collapse: no per-kind rule fires (or could -- the ops are
//    not surjective), but the variable's only use is a chain of operations
//    against constants under a predicate against a constant, so the whole
//    predicate is replaced by a fresh boolean with
//    var := ITE(v, w_true, w_false) recorded.
/////////////////////////////////////////////////////////////////////////////

// A term-level `op` under EQ against `rhs`, collapse + soundness together.
// The soundness check runs the same shape conjoined with an anchor so the
// rewrite is exercised inside a surviving formula too.
void checkGroundPath(std::function<ASTNode(Context&)> build)
{
  expectCollapse(build);

  Context c;
  ASTNode pred = build(c);
  ASTNode keep = c.bv();
  c.checkSoundTop(c.hf->CreateNode(AND, pred, c.anchorFor(keep)));
}

TEST(RemoveUnconstrained_GroundPath, urem_by_constant)
{
  // The motivating case: (bvurem x 4) == 2. The BVMOD rule needs both
  // operands unconstrained, and x mod 4 isn't surjective, so only the
  // predicate-level collapse can eliminate x.
  checkGroundPath([](Context& c) {
    return c.hf->CreateNode(
        EQ, c.hf->CreateTerm(BVMOD, W, c.bv(), c.konst(4)), c.konst(2));
  });
}

TEST(RemoveUnconstrained_GroundPath, udiv_by_constant)
{
  checkGroundPath([](Context& c) {
    return c.hf->CreateNode(
        EQ, c.hf->CreateTerm(BVDIV, W, c.bv(), c.konst(2)), c.konst(1));
  });
}

TEST(RemoveUnconstrained_GroundPath, srem_by_constant)
{
  // Signed remainder has no exact interval transfer; the sample fallback
  // finds the witnesses.
  checkGroundPath([](Context& c) {
    return c.hf->CreateNode(
        EQ, c.hf->CreateTerm(SBVREM, W, c.bv(), c.konst(3)), c.konst(1));
  });
}

TEST(RemoveUnconstrained_GroundPath, chain_mod_plus_compare)
{
  // Two layers between the variable and the predicate:
  // ((x mod 5) + 2) >u 4.
  checkGroundPath([](Context& c) {
    ASTNode t = c.hf->CreateTerm(BVMOD, W, c.bv(), c.konst(5));
    t = c.hf->CreateTerm(BVPLUS, W, t, c.konst(2));
    return c.hf->CreateNode(BVGT, t, c.konst(4));
  });
}

TEST(RemoveUnconstrained_GroundPath, and_mask)
{
  // 5 isn't a low mask, so this goes through the sample fallback.
  checkGroundPath([](Context& c) {
    return c.hf->CreateNode(
        EQ, c.hf->CreateTerm(BVAND, W, c.bv(), c.konst(5)), c.konst(4));
  });
}

TEST(RemoveUnconstrained_GroundPath, shift_right_by_constant)
{
  checkGroundPath([](Context& c) {
    return c.hf->CreateNode(
        EQ, c.hf->CreateTerm(BVRIGHTSHIFT, W, c.bv(), c.konst(1)),
        c.konst(2));
  });
}

TEST(RemoveUnconstrained_GroundPath, shift_left_by_constant)
{
  checkGroundPath([](Context& c) {
    return c.hf->CreateNode(
        EQ, c.hf->CreateTerm(BVLEFTSHIFT, W, c.bv(), c.konst(1)),
        c.konst(4));
  });
}

TEST(RemoveUnconstrained_GroundPath, zero_extend_compare)
{
  checkGroundPath([](Context& c) {
    ASTNode zx = c.hf->CreateTerm(BVZX, 2 * W, c.bv(), c.konst(2 * W, 32));
    return c.hf->CreateNode(BVSGT, zx, c.konst(5, 2 * W));
  });
}

TEST(RemoveUnconstrained_GroundPath, sign_extend)
{
  // Historically a known gap: sign-extension of an unconstrained variable
  // is not itself unconstrained (the extended bits are determined), so
  // there is no term-level rule -- but the predicate collapses.
  checkGroundPath([](Context& c) {
    ASTNode sx = c.hf->CreateTerm(BVSX, 2 * W, c.bv(), c.konst(2 * W, 32));
    return c.hf->CreateNode(EQ, sx, c.konst(1, 2 * W));
  });
}

TEST(RemoveUnconstrained_GroundPath, concat_constant_high)
{
  // (concat 2bits(2) x) at width 5: image is [16, 23].
  checkGroundPath([](Context& c) {
    ASTNode t = c.hf->CreateTerm(BVCONCAT, W + 2, c.konst(2, 2), c.bv());
    return c.hf->CreateNode(EQ, t, c.konst(19, W + 2));
  });
}

TEST(RemoveUnconstrained_GroundPath, width_one_comparison)
{
  // Width-1 comparisons used to be skipped ("hard to get right"); the
  // ground-path collapse handles them.
  checkGroundPath([](Context& c) {
    return c.hf->CreateNode(BVGT, c.bv(1), c.konst(0, 1));
  });
}

TEST(RemoveUnconstrained_GroundPath, cascade_through_not)
{
  // The fresh boolean from the collapse is itself unconstrained; the NOT
  // rule then finishes the job.
  checkGroundPath([](Context& c) {
    ASTNode eq = c.hf->CreateNode(
        EQ, c.hf->CreateTerm(BVMOD, W, c.bv(), c.konst(4)), c.konst(2));
    return c.hf->CreateNode(NOT, eq);
  });
}

TEST(RemoveUnconstrained_GroundPath, square)
{
  // (zx(x) * zx(x)) == 4: the zero-extension is BOTH operands of the
  // multiply -- a unary function of x through a duplicated operand.
  // The dominant dup-path shape on the bench-hard set (Sage2 squaring).
  checkGroundPath([](Context& c) {
    ASTNode zx = c.hf->CreateTerm(BVZX, 2 * W, c.bv(), c.konst(2 * W, 32));
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(BVMULT, 2 * W, zx, zx),
                            c.konst(4, 2 * W));
  });
}

TEST(RemoveUnconstrained_GroundPath, hint_chain_through_wrapping_add)
{
  // (= 65515 (extract[15:0] (bvadd 0xFFFFFF75 (zx x)))): only x = 118
  // works, reachable only via the back-propagated hint chain. This was
  // a decline observed on Sage2/bench_14036.smt2.
  checkGroundPath([](Context& c) {
    ASTNode x = c.bv(8);
    ASTNode zx = c.hf->CreateTerm(BVZX, 32, x, c.konst(32, 32));
    ASTNode add =
        c.hf->CreateTerm(BVPLUS, 32, c.mgr.CreateBVConst(32, 0xFFFFFF75ull), zx);
    ASTNode ext = c.hf->CreateTerm(BVEXTRACT, 16, add, c.konst(15, 32),
                                   c.konst(0, 32));
    return c.hf->CreateNode(EQ, ext, c.konst(65515, 16));
  });
}

TEST(RemoveUnconstrained_GroundPath, shared_predicate)
{
  // The predicate node itself may have several parents: every occurrence
  // evaluates to the fresh boolean under the recorded definition.
  Context c;
  ASTNode pred = c.hf->CreateNode(
      EQ, c.hf->CreateTerm(BVMOD, W, c.bv(), c.konst(4)), c.konst(2));
  ASTNode keep = c.bv();
  ASTNode top = c.hf->CreateNode(
      AND, pred, c.hf->CreateNode(OR, pred, c.anchorFor(keep)));
  c.checkSoundTop(top);
}

// --- ITE distribution: the predicate distributes over a single ITE on
//     the path, P(g(ite(c, f(x), t))) => ite(c, v, P(g(t))). The result
//     keeps the else side, so these check x's elimination and soundness
//     rather than full collapse. ---

TEST(RemoveUnconstrained_GroundPath, ite_distribution)
{
  // (= (ite (= y 0) (bvurem x 4) y) 2)  =>  ite((= y 0), v, (= y 2))
  Context c;
  ASTNode x = c.bv();
  ASTNode y = c.bv();
  ASTNode cond = c.hf->CreateNode(EQ, y, c.konst(0));
  ASTNode ite = c.hf->CreateTerm(
      ITE, W, cond, c.hf->CreateTerm(BVMOD, W, x, c.konst(4)), y);
  ASTNode top = c.hf->CreateNode(EQ, ite, c.konst(2));

  ASTNode result = c.run(top);
  EXPECT_EQ(c.simp.Return_SolverMap()->count(x), 1u) << "x not eliminated";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_GroundPath, ite_distribution_with_suffix)
{
  // Ground steps above the ITE distribute too:
  // (= (bvadd (ite c (bvurem x 4) y) 1) 3) => ite(c, v, (= (bvadd y 1) 3))
  Context c;
  ASTNode x = c.bv();
  ASTNode y = c.bv();
  ASTNode cond = c.hf->CreateNode(EQ, y, c.konst(1));
  ASTNode ite = c.hf->CreateTerm(
      ITE, W, cond, c.hf->CreateTerm(BVMOD, W, x, c.konst(4)), y);
  ASTNode add = c.hf->CreateTerm(BVPLUS, W, ite, c.konst(1));
  ASTNode top = c.hf->CreateNode(EQ, add, c.konst(3));

  ASTNode result = c.run(top);
  EXPECT_EQ(c.simp.Return_SolverMap()->count(x), 1u) << "x not eliminated";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_GroundPath, ite_distribution_else_branch)
{
  // x in the else branch: ite(c, y, chain(x)).
  Context c;
  ASTNode x = c.bv();
  ASTNode y = c.bv();
  ASTNode cond = c.hf->CreateNode(EQ, y, c.konst(0));
  ASTNode ite = c.hf->CreateTerm(
      ITE, W, cond, y, c.hf->CreateTerm(BVAND, W, x, c.konst(5)));
  ASTNode top = c.hf->CreateNode(EQ, ite, c.konst(4));

  ASTNode result = c.run(top);
  EXPECT_EQ(c.simp.Return_SolverMap()->count(x), 1u) << "x not eliminated";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_GroundPath, ite_shared_no_distribution)
{
  // The ITE node is consumed twice: distributing from one consumer's
  // viewpoint would be unsound, so x must survive.
  Context c;
  ASTNode x = c.bv();
  ASTNode y = c.bv();
  ASTNode cond = c.hf->CreateNode(EQ, y, c.konst(0));
  ASTNode ite = c.hf->CreateTerm(
      ITE, W, cond, c.hf->CreateTerm(BVMOD, W, x, c.konst(4)), y);
  ASTNode top =
      c.hf->CreateNode(AND, c.hf->CreateNode(EQ, ite, c.konst(2)),
                       c.hf->CreateNode(BVGT, ite, c.konst(0)));

  ASTNode result = c.run(top);
  EXPECT_EQ(c.simp.Return_SolverMap()->count(x), 0u)
      << "x eliminated through a shared ITE";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_GroundPath, ite_nested_distributes)
{
  // Two ITE frames on one path: the predicate distributes over both,
  //   ite((= z 1), ite((= y 0), v, (= y 2)), (= z 2)).
  Context c;
  ASTNode x = c.bv();
  ASTNode y = c.bv();
  ASTNode z = c.bv();
  ASTNode inner = c.hf->CreateTerm(
      ITE, W, c.hf->CreateNode(EQ, y, c.konst(0)),
      c.hf->CreateTerm(BVMOD, W, x, c.konst(4)), y);
  ASTNode outer = c.hf->CreateTerm(
      ITE, W, c.hf->CreateNode(EQ, z, c.konst(1)), inner, z);
  ASTNode top = c.hf->CreateNode(EQ, outer, c.konst(2));

  ASTNode result = c.run(top);
  EXPECT_EQ(c.simp.Return_SolverMap()->count(x), 1u) << "x not eliminated";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_GroundPath, ite_three_frames_with_suffixes)
{
  // Three frames, mixed then/else positions, with ground steps between
  // them: each frame's else side gets the steps above it re-applied.
  Context c;
  ASTNode x = c.bv();
  ASTNode y = c.bv();
  ASTNode z = c.bv();
  ASTNode w2 = c.bv();
  ASTNode t = c.hf->CreateTerm(BVMOD, W, x, c.konst(4));
  t = c.hf->CreateTerm(ITE, W, c.hf->CreateNode(EQ, y, c.konst(0)), t, y);
  t = c.hf->CreateTerm(BVPLUS, W, t, c.konst(1));
  t = c.hf->CreateTerm(ITE, W, c.hf->CreateNode(EQ, z, c.konst(1)), z, t);
  t = c.hf->CreateTerm(ITE, W, c.hf->CreateNode(EQ, w2, c.konst(2)), t, w2);
  ASTNode top = c.hf->CreateNode(EQ, t, c.konst(3));

  ASTNode result = c.run(top);
  EXPECT_EQ(c.simp.Return_SolverMap()->count(x), 1u) << "x not eliminated";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_GroundPath, ite_frame_cap_declines)
{
  // Five stacked frames exceed MAX_ITE_FRAMES: x must survive. One
  // shared condition variable keeps the equivalence check enumerable.
  Context c;
  ASTNode x = c.bv();
  ASTNode y = c.bv();
  ASTNode t = c.hf->CreateTerm(BVMOD, W, x, c.konst(4));
  for (int i = 0; i < 5; i++)
    t = c.hf->CreateTerm(ITE, W, c.hf->CreateNode(EQ, y, c.konst(i)), t,
                         c.konst(7));
  ASTNode top = c.hf->CreateNode(EQ, t, c.konst(2));

  ASTNode result = c.run(top);
  EXPECT_EQ(c.simp.Return_SolverMap()->count(x), 0u)
      << "x eliminated past the frame cap";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

// --- Cases that must NOT collapse. ---

TEST(RemoveUnconstrained_GroundPath, one_polarity_no_collapse)
{
  // (zero_extend x) == 63 is simply false: only one polarity is
  // achievable, and this pass deliberately does no constant folding (it
  // is purely under-approximating; over-approximating analyses prove
  // constants). It must leave the formula alone.
  expectNoCollapse([](Context& c) {
    ASTNode zx = c.hf->CreateTerm(BVZX, 2 * W, c.bv(), c.konst(2 * W, 32));
    return c.hf->CreateNode(EQ, zx, c.konst(63, 2 * W));
  });
}

/////////////////////////////////////////////////////////////////////////////
// 4) Image-constrained fresh variables: a shared non-surjective
//    single-step term t(x) is replaced by a fresh v, "v in Image(t)" is
//    conjoined, and x := projection(v). Checked with checkEquisat, since
//    the pointwise identity doesn't hold off the image.
/////////////////////////////////////////////////////////////////////////////

// Runs the pass on `top`, requiring x to be eliminated and the rewrite
// to be equisatisfiable with mapping models.
static void checkImageConstrained(Context& c, const ASTNode& x,
                                  const ASTNode& top)
{
  ASTNode result = c.run(top);
  EXPECT_EQ(c.simp.Return_SolverMap()->count(x), 1u) << "x not eliminated";
  c.checkEquisat(top, result);
}

TEST(RemoveUnconstrained_ImageConstrained, shared_urem)
{
  // (x mod 4) used twice: no predicate-level collapse is possible, but
  // the term becomes v with (bvult v 4) conjoined and x := v.
  Context c;
  ASTNode x = c.bv();
  ASTNode t = c.hf->CreateTerm(BVMOD, W, x, c.konst(4));
  ASTNode top = c.hf->CreateNode(AND, c.hf->CreateNode(EQ, t, c.konst(2)),
                                 c.hf->CreateNode(BVGT, t, c.konst(1)));
  checkImageConstrained(c, x, top);
}

TEST(RemoveUnconstrained_ImageConstrained, shared_zero_extend)
{
  Context c;
  ASTNode x = c.bv();
  ASTNode t = c.hf->CreateTerm(BVZX, 2 * W, x, c.konst(2 * W, 32));
  ASTNode top =
      c.hf->CreateNode(AND, c.hf->CreateNode(EQ, t, c.konst(2, 2 * W)),
                       c.hf->CreateNode(BVGT, t, c.konst(1, 2 * W)));
  checkImageConstrained(c, x, top);
}

TEST(RemoveUnconstrained_ImageConstrained, shared_sign_extend)
{
  Context c;
  ASTNode x = c.bv();
  ASTNode t = c.hf->CreateTerm(BVSX, 2 * W, x, c.konst(2 * W, 32));
  ASTNode top =
      c.hf->CreateNode(AND, c.hf->CreateNode(EQ, t, c.konst(7, 2 * W)),
                       c.hf->CreateNode(BVSGT, t, c.konst(0, 2 * W)));
  checkImageConstrained(c, x, top);
}

TEST(RemoveUnconstrained_ImageConstrained, shared_concat_low_constant)
{
  // x ++ 2-bit constant, shared: low bits pinned, x := high extract.
  Context c;
  ASTNode x = c.bv();
  ASTNode t = c.hf->CreateTerm(BVCONCAT, W + 2, x, c.konst(2, 2));
  ASTNode top =
      c.hf->CreateNode(AND, c.hf->CreateNode(EQ, t, c.konst(6, W + 2)),
                       c.hf->CreateNode(BVGT, t, c.konst(1, W + 2)));
  checkImageConstrained(c, x, top);
}

TEST(RemoveUnconstrained_ImageConstrained, shared_even_multiply)
{
  // 6 = 2 * 3: image is the even values; x := (v >> 1) * inverse(3).
  Context c;
  ASTNode x = c.bv();
  ASTNode t = c.hf->CreateTerm(BVMULT, W, c.konst(6), x);
  ASTNode top = c.hf->CreateNode(AND, c.hf->CreateNode(EQ, t, c.konst(4)),
                                 c.hf->CreateNode(BVGT, t, c.konst(1)));
  checkImageConstrained(c, x, top);
}

TEST(RemoveUnconstrained_ImageConstrained, shared_ashr_not_rewritten)
{
  // Arithmetic right shift isn't in the shape table: x must survive.
  Context c;
  ASTNode x = c.bv();
  ASTNode t = c.hf->CreateTerm(BVSRSHIFT, W, x, c.konst(1));
  ASTNode top = c.hf->CreateNode(AND, c.hf->CreateNode(EQ, t, c.konst(2)),
                                 c.hf->CreateNode(BVGT, t, c.konst(1)));
  ASTNode result = c.run(top);
  EXPECT_EQ(c.simp.Return_SolverMap()->count(x), 0u);
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_ImageConstrained, shared_multi_step_not_rewritten)
{
  // The shared node sits two steps up ((x mod 4) + 1): single-step only.
  Context c;
  ASTNode x = c.bv();
  ASTNode t = c.hf->CreateTerm(
      BVPLUS, W, c.hf->CreateTerm(BVMOD, W, x, c.konst(4)), c.konst(1));
  ASTNode top = c.hf->CreateNode(AND, c.hf->CreateNode(EQ, t, c.konst(2)),
                                 c.hf->CreateNode(BVGT, t, c.konst(1)));
  ASTNode result = c.run(top);
  EXPECT_EQ(c.simp.Return_SolverMap()->count(x), 0u);
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

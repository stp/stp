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
 *     an unconstrained rule, so it's a direct probe for missing rules. The
 *     operators STP does NOT yet handle (bvurem, and the signed div/rem/mod
 *     family) are listed explicitly as expectNoCollapse -- if someone adds a
 *     rule, that test flips and is the reminder to move it up to the handled
 *     list.
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

// --- Missing rules: these currently do NOT collapse. Enabling a rule for any
//     of them (see the TODO in RemoveUnconstrained.cpp for bvurem) will flip
//     the corresponding test and prompt moving it up to the handled list. ---

TEST(RemoveUnconstrained_Collapse, urem_MISSING)
{
  expectNoCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(BVMOD, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, sdiv_MISSING)
{
  expectNoCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(SBVDIV, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, srem_MISSING)
{
  expectNoCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(SBVREM, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

TEST(RemoveUnconstrained_Collapse, smod_MISSING)
{
  expectNoCollapse([](Context& c) {
    return c.hf->CreateNode(EQ, c.hf->CreateTerm(SBVMOD, W, c.bv(), c.bv()),
                            c.konst(1));
  });
}

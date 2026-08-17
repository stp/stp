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
      DenseNodeMap fromTo = *simp.Return_SolverMap(); // replace() mutates it.
      DenseNodeMap cache;
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
    uint64_t combos = 1;
    for (const auto& s : syms)
      combos *= domainSize(s);
    ASSERT_LE(combos, 1u << 16)
        << "too many assignments (" << combos << ") -- lower the width";

    std::vector<unsigned> idx(syms.size(), 0);
    for (uint64_t c = 0; c < combos; c++)
    {
      ASTNodeMap assignment;
      uint64_t rest = c;
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

  //-------------------------------------------------------------------
  // Arrays.
  //
  // An array symbol has no scalar domain to enumerate, so the checks
  // above cannot see one. At the widths used here it has a small
  // explicit one: an index width of IW and an element width of VW makes
  // (2^VW)^(2^IW) distinct arrays -- four for the 1x1 arrays below. So
  // the same exhaustive identity is available, once array-sorted terms
  // can be evaluated under an assignment of concrete arrays.
  //
  // ground() does that by folding every array-rooted subterm away: a
  // read becomes the cell it selects and an array equality becomes a
  // constant, after which the formula is array-free and the existing
  // scalar evaluator finishes the job.
  //-------------------------------------------------------------------

  static constexpr unsigned IW = 1; // index width of the test arrays
  static constexpr unsigned VW = 1; // element width

  typedef std::vector<unsigned> Cells; // one entry per index, 2^IW of them
  typedef std::map<ASTNode, Cells> ArrayAssignment;

  ASTNode array(unsigned iw = IW, unsigned vw = VW)
  {
    return mgr.CreateSymbol(("a" + std::to_string(counter++)).c_str(), iw, vw);
  }

  unsigned evalConst(const ASTNode& groundScalar)
  {
    ASTNode c = groundScalar.isConstant()
                    ? groundScalar
                    : NonMemberBVConstEvaluator(&mgr, groundScalar);
    if (c.GetType() == BOOLEAN_TYPE)
      return c == mgr.ASTTrue ? 1 : 0;
    return c.GetUnsignedConst();
  }

  Cells arrayValue(const ASTNode& n, const ArrayAssignment& av)
  {
    if (n.GetKind() == SYMBOL)
    {
      auto it = av.find(n);
      EXPECT_NE(it, av.end()) << "no value for array symbol " << n;
      return it == av.end() ? Cells(1u << IW, 0) : it->second;
    }
    if (n.GetKind() == WRITE)
    {
      Cells v = arrayValue(n[0], av);
      v[evalConst(ground(n[1], av))] = evalConst(ground(n[2], av));
      return v;
    }
    if (n.GetKind() == ITE)
      return evalConst(ground(n[0], av)) ? arrayValue(n[1], av)
                                         : arrayValue(n[2], av);
    ADD_FAILURE() << "cannot evaluate array term of kind " << n.GetKind();
    return Cells(1u << IW, 0);
  }

  // `n` with every array-rooted subterm folded to a constant.
  ASTNode ground(const ASTNode& n, const ArrayAssignment& av)
  {
    if (n.GetKind() == READ)
    {
      const Cells cells = arrayValue(n[0], av);
      return konst(cells[evalConst(ground(n[1], av))], n.GetValueWidth());
    }
    if (n.GetKind() == ARRAY_EQ)
      return arrayValue(n[0], av) == arrayValue(n[1], av) ? mgr.ASTTrue
                                                          : mgr.ASTFalse;
    if (n.GetKind() == SYMBOL || n.isConstant() || n.Degree() == 0)
      return n;

    ASTVec children;
    children.reserve(n.Degree());
    for (const auto& c : n)
      children.push_back(ground(c, av));

    if (n.GetType() == BOOLEAN_TYPE)
      return nf->CreateNode(n.GetKind(), children);
    return nf->CreateTerm(n.GetKind(), n.GetValueWidth(), children);
  }

  // As checkEquivalent, but ranging over array symbols as well: every
  // assignment of concrete arrays, times every scalar assignment.
  //
  // The scalars are substituted first. A write's index and value are
  // ordinary scalar terms -- and the write rule exists precisely because
  // the value can be an unconstrained symbol -- so grounding an array
  // term needs them already settled.
  void checkEquivalentWithArrays(const ASTNode& before, const ASTNode& after)
  {
    ASTNodeSet symSet;
    collectSymbols(before, symSet);
    collectSymbols(after, symSet);

    std::vector<ASTNode> arrays, scalars;
    for (const auto& s : symSet)
      (s.GetIndexWidth() > 0 ? arrays : scalars).push_back(s);

    const unsigned cellCount = 1u << IW;
    const unsigned perArray = 1u << (cellCount * VW); // arrays of this sort
    uint64_t arrayCombos = 1;
    for (size_t i = 0; i < arrays.size(); i++)
      arrayCombos *= perArray;
    uint64_t scalarCombos = 1;
    for (const auto& s : scalars)
      scalarCombos *= domainSize(s);
    ASSERT_LE(arrayCombos * scalarCombos, 1u << 16)
        << "too many assignments -- lower the widths";

    for (uint64_t ac = 0; ac < arrayCombos; ac++)
    {
      ArrayAssignment av;
      uint64_t rest = ac;
      for (size_t i = 0; i < arrays.size(); i++)
      {
        unsigned code = rest % perArray;
        rest /= perArray;
        Cells cells(cellCount);
        for (unsigned j = 0; j < cellCount; j++)
        {
          cells[j] = code & ((1u << VW) - 1);
          code >>= VW;
        }
        av.insert({arrays[i], cells});
      }

      for (uint64_t sc = 0; sc < scalarCombos; sc++)
      {
        ASTNodeMap assignment;
        uint64_t srest = sc;
        for (size_t i = 0; i < scalars.size(); i++)
        {
          const unsigned size = domainSize(scalars[i]);
          assignment.insert({scalars[i], valueFor(scalars[i], srest % size)});
          srest /= size;
        }

        ASTNodeMap m1 = assignment, m2 = assignment, ca1, ca2, e1, e2;
        const ASTNode b =
            ground(SubstitutionMap::replace(before, m1, ca1, &snf), av);
        const ASTNode a =
            ground(SubstitutionMap::replace(after, m2, ca2, &snf), av);
        ASSERT_EQ(eval(b, e1), eval(a, e2))
            << "unconstrained rewrite changed the meaning at array "
            << "assignment " << ac << ", scalar assignment " << sc;
      }
    }
  }

  void checkSoundArrays(const ASTNode& top)
  {
    ASTNode result = run(top);
    ASTNode back = backSubstitute(top);
    checkEquivalentWithArrays(back, result);
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

TEST(RemoveUnconstrained_Exhaustive, mult_three_operands)
{
  Context c;
  // The BVMULT rules only exist for two operands; a wider multiply must be
  // skipped soundly, not taken apart.
  c.checkSound(c.hf->CreateTerm(BVMULT, W, c.bv(), c.bv(), c.bv()));
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

// --- Array rules. Each enumerates every concrete array as well as every
// scalar assignment; see checkEquivalentWithArrays. ---

TEST(RemoveUnconstrained_Exhaustive, array_read)
{
  Context c;
  // read(a, 0) with `a` used once. The read is free, so it stands in
  // for `keep`, which survives via the anchor.
  ASTNode a = c.array();
  ASTNode keep = c.bv(Context::VW);
  ASTNode read = c.hf->CreateTerm(READ, Context::VW, a, c.konst(0, Context::IW));
  c.checkSoundArrays(c.hf->CreateNode(
      AND, c.hf->CreateNode(EQ, read, keep), c.anchorFor(keep)));
}

TEST(RemoveUnconstrained_Exhaustive, array_read_constrained_array_untouched)
{
  Context c;
  // Two reads of the same array: it is not unconstrained, and neither
  // read may be replaced by a free value -- congruence has to hold.
  ASTNode a = c.array();
  ASTNode keep = c.bv(Context::VW);
  ASTNode r0 = c.hf->CreateTerm(READ, Context::VW, a, c.konst(0, Context::IW));
  ASTNode r1 = c.hf->CreateTerm(READ, Context::VW, a, c.konst(0, Context::IW));
  c.checkSoundArrays(c.hf->CreateNode(
      AND, c.hf->CreateNode(EQ, c.hf->CreateTerm(BVPLUS, Context::VW, r0, r1),
                            keep),
      c.anchorFor(keep)));
}

TEST(RemoveUnconstrained_Exhaustive, array_write)
{
  Context c;
  // write(a, 0, e) with both the base array and the written value free.
  ASTNode a = c.array();
  ASTNode e = c.bv(Context::VW);
  ASTNode keep = c.bv(Context::VW);
  ASTNode w = c.hf->CreateArrayTerm(WRITE, Context::IW, Context::VW, a,
                                    c.konst(0, Context::IW), e);
  ASTNode read = c.hf->CreateTerm(READ, Context::VW, w,
                                  c.konst(1 % (1u << Context::IW), Context::IW));
  c.checkSoundArrays(c.hf->CreateNode(
      AND, c.hf->CreateNode(EQ, read, keep), c.anchorFor(keep)));
}

TEST(RemoveUnconstrained_Exhaustive, array_write_constrained_value)
{
  Context c;
  // The value is a constant, so the write is pinned at index 0 and is
  // NOT a free array. This is the case the rule's value condition
  // exists for: a rule keyed on the base array alone would be unsound
  // here, and the enumeration would catch it.
  ASTNode a = c.array();
  ASTNode keep = c.bv(Context::VW);
  ASTNode w = c.hf->CreateArrayTerm(WRITE, Context::IW, Context::VW, a,
                                    c.konst(0, Context::IW),
                                    c.konst(1, Context::VW));
  ASTNode read =
      c.hf->CreateTerm(READ, Context::VW, w, c.konst(0, Context::IW));
  c.checkSoundArrays(c.hf->CreateNode(
      AND, c.hf->CreateNode(EQ, read, keep), c.anchorFor(keep)));
}

TEST(RemoveUnconstrained_Exhaustive, array_write_shared_value)
{
  Context c;
  // As above, but the written value is a symbol used a second time, so
  // it is constrained rather than constant. Dropping the rule's value
  // condition makes it fire here and answer wrongly -- the write
  // is pinned to whatever `e` turns out to be -- which the enumeration
  // below detects. (With a *constant* value the same mistake trips
  // replace()'s SYMBOL precondition instead, so this is the case that
  // keeps the guard honest.)
  ASTNode a = c.array();
  ASTNode e = c.bv(Context::VW);
  ASTNode keep = c.bv(Context::VW);
  ASTNode w = c.hf->CreateArrayTerm(WRITE, Context::IW, Context::VW, a,
                                    c.konst(0, Context::IW), e);
  ASTNode read =
      c.hf->CreateTerm(READ, Context::VW, w, c.konst(0, Context::IW));
  ASTVec conjuncts;
  conjuncts.push_back(c.hf->CreateNode(EQ, read, keep));
  conjuncts.push_back(c.hf->CreateNode(EQ, e, keep)); // second use of `e`
  conjuncts.push_back(c.anchorFor(keep));
  c.checkSoundArrays(c.hf->CreateNode(AND, conjuncts));
}

TEST(RemoveUnconstrained_Exhaustive, array_ite)
{
  Context c;
  // An if-then-else over two free arrays is itself free.
  ASTNode cond = c.boolean();
  ASTNode keep = c.bv(Context::VW);
  ASTNode ite = c.hf->CreateArrayTerm(ITE, Context::IW, Context::VW, cond,
                                      c.array(), c.array());
  ASTNode read =
      c.hf->CreateTerm(READ, Context::VW, ite, c.konst(0, Context::IW));
  c.checkSoundArrays(c.hf->CreateNode(
      AND, c.hf->CreateNode(EQ, read, keep), c.anchorFor(keep)));
}

TEST(RemoveUnconstrained_Collapse, array_equality)
{
  // The literature's rule set also eliminates an array equality with
  // one unconstrained side. STP deliberately does not -- see the header
  // comment in RemoveUnconstrained.cpp -- so this must NOT collapse. If
  // a rule is added back, this is the test that will say so.
  expectNoCollapse([](Context& c) {
    c.mgr.UserFlags.enable_array_equality = true;
    return c.hf->CreateNode(ARRAY_EQ, c.array(), c.array());
  });
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

TEST(RemoveUnconstrained_GroundPath, shared_interior_no_collapse)
{
  // (x mod 4) is used twice: forcing x to witness values would change the
  // second use, so the climb must refuse to step past a shared interior
  // node. Also check the pass stays sound on this shape.
  auto build = [](Context& c) {
    ASTNode t = c.hf->CreateTerm(BVMOD, W, c.bv(), c.konst(4));
    return c.hf->CreateNode(AND, c.hf->CreateNode(EQ, t, c.konst(2)),
                            c.hf->CreateNode(BVGT, t, c.konst(1)));
  };
  expectNoCollapse(build);

  Context c;
  c.checkSoundTop(build(c));
}

/////////////////////////////////////////////////////////////////////////////
// 4) Symbolic-side collapse: the predicate's other side is any term. The
//    predicate is rewritten into its invertibility condition over that term
//    joined with a fresh boolean, and x is defined to realise either truth
//    value -- EQ via the chain's pseudo-inverse, comparisons via the exact
//    enumerated extremes of the chain's image.
/////////////////////////////////////////////////////////////////////////////

namespace
{
// Run the pass on `top`, require that `x` was eliminated, and check the
// back-substituted original agrees with the result on every assignment.
void checkSymbolicFires(Context& c, const ASTNode& x, const ASTNode& top)
{
  ASTNode result = c.run(top);
  ASTNodeSet syms;
  c.collectSymbols(result, syms);
  EXPECT_EQ(syms.count(x), 0u) << "x survived the symbolic-side collapse";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}
} // namespace

TEST(RemoveUnconstrained_SymbolicSide, eq_and_mask)
{
  // (= (bvand x 5) t): the invertibility condition is (t & ~5) == 0.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode pred =
      c.hf->CreateNode(EQ, c.hf->CreateTerm(BVAND, W, x, c.konst(5)), t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));
  checkSymbolicFires(c, x, top);
}

TEST(RemoveUnconstrained_SymbolicSide, eq_bijective_chain_with_concat)
{
  // (= (bvadd (concat 2 (bvxor x 5)) 7) t): xor and plus invert exactly;
  // the concat contributes the condition that t's high slice inverts to
  // the constant 2.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv(5);
  ASTNode t = c.hf->CreateTerm(BVNOT, 5, keep);
  ASTNode inner = c.hf->CreateTerm(BVXOR, W, x, c.konst(5));
  ASTNode mid = c.hf->CreateTerm(BVCONCAT, 5, c.konst(2, 2), inner);
  ASTNode chain = c.hf->CreateTerm(BVPLUS, 5, mid, c.konst(7, 5));
  ASTNode pred = c.hf->CreateNode(EQ, chain, t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));
  checkSymbolicFires(c, x, top);
}

TEST(RemoveUnconstrained_SymbolicSide, eq_urem)
{
  // (= (bvurem x 5) t): condition t <u 5, witness x := t.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode pred =
      c.hf->CreateNode(EQ, c.hf->CreateTerm(BVMOD, W, x, c.konst(5)), t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));
  checkSymbolicFires(c, x, top);
}

TEST(RemoveUnconstrained_SymbolicSide, eq_shift_right_t_first)
{
  // (= t (bvlshr x 1)) with the term on the left: condition on t's top
  // bit, witness x := t << 1.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode pred = c.hf->CreateNode(
      EQ, t, c.hf->CreateTerm(BVRIGHTSHIFT, W, x, c.konst(1)));
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));
  checkSymbolicFires(c, x, top);
}

TEST(RemoveUnconstrained_SymbolicSide, eq_extract_bottom)
{
  // (= ((_ extract 2 1) x) t): every t is achievable; x pads with zeros.
  Context c;
  ASTNode x = c.bv(4);
  ASTNode keep = c.bv(2);
  ASTNode t = c.hf->CreateTerm(BVNOT, 2, keep);
  ASTNode ex =
      c.hf->CreateTerm(BVEXTRACT, 2, x, c.konst(2, 32), c.konst(1, 32));
  ASTNode pred = c.hf->CreateNode(EQ, ex, t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));
  checkSymbolicFires(c, x, top);
}

TEST(RemoveUnconstrained_SymbolicSide, ugt_concat_plus)
{
  // (bvugt (bvadd (concat 1 x) 3) t): enumerated exact extremes of the
  // chain's image drive the rewrite.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv(5);
  ASTNode t = c.hf->CreateTerm(BVNOT, 5, keep);
  ASTNode mid = c.hf->CreateTerm(BVCONCAT, 5, c.konst(1, 2), x);
  ASTNode chain = c.hf->CreateTerm(BVPLUS, 5, mid, c.konst(3, 5));
  ASTNode pred = c.hf->CreateNode(BVGT, chain, t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));
  checkSymbolicFires(c, x, top);
}

TEST(RemoveUnconstrained_SymbolicSide, ult_t_first_sext)
{
  // (bvult t (sign_extend x)): the path is the second operand, and the
  // sext image wraps in unsigned order, where an interval analysis loses
  // exactness; enumeration finds the true unsigned extremes regardless.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv(5);
  ASTNode t = c.hf->CreateTerm(BVNOT, 5, keep);
  ASTNode chain = c.hf->CreateTerm(BVSX, 5, x, c.konst(5, 32));
  ASTNode pred = c.hf->CreateNode(BVLT, t, chain);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));
  checkSymbolicFires(c, x, top);
}

TEST(RemoveUnconstrained_SymbolicSide, sgt_mult_chain)
{
  // (bvsgt (bvmul x 3) t): multiplication has no inverse entry, but the
  // comparison path only needs enumerated extremes, in signed order.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode chain = c.hf->CreateTerm(BVMULT, W, x, c.konst(3));
  ASTNode pred = c.hf->CreateNode(BVSGT, chain, t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));
  checkSymbolicFires(c, x, top);
}

TEST(RemoveUnconstrained_SymbolicSide, ite_frame_distributes)
{
  // (= (ite b (bvand x 5) keep) t): the ITE frame distributes and the
  // rewritten equality sits on x's branch.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode keep2 = c.bv();
  ASTNode b = c.boolean();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep2);
  ASTNode masked = c.hf->CreateTerm(BVAND, W, x, c.konst(5));
  ASTNode ite = c.hf->CreateTerm(ITE, W, b, masked, keep);
  ASTNode pred = c.hf->CreateNode(EQ, ite, t);
  ASTNode top = c.hf->CreateNode(
      AND, pred, c.hf->CreateNode(AND, c.anchorFor(keep), c.anchorFor(keep2)));
  checkSymbolicFires(c, x, top);
}

// --- Cases that must NOT fire. ---

TEST(RemoveUnconstrained_SymbolicSide, eq_lossy_above_lossy_refused)
{
  // (= (bvand (bvor x 1) 3) t): a lossy step above another step. The
  // walk's per-step conditions only characterise a lossy step's image
  // when its input is the free variable itself, so a non-bottom and/or
  // must be refused and x must survive.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode inner = c.hf->CreateTerm(BVOR, W, x, c.konst(1));
  ASTNode chain = c.hf->CreateTerm(BVAND, W, inner, c.konst(3));
  ASTNode pred = c.hf->CreateNode(EQ, chain, t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));

  ASTNode result = c.run(top);
  ASTNodeSet syms;
  c.collectSymbols(result, syms);
  EXPECT_EQ(syms.count(x), 1u) << "walk stepped past a non-bottom lossy step";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_SymbolicSide, eq_degenerate_mask_refused)
{
  // (= (bvand x 0) t): the image is {0}; the chain is a constant in
  // disguise and the rule must leave it to constant folding.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode pred =
      c.hf->CreateNode(EQ, c.hf->CreateTerm(BVAND, W, x, c.konst(0)), t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));

  ASTNode result = c.run(top);
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_SymbolicSide, shared_chain_refused)
{
  // The masked node is used twice; the climb must refuse to step past it.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode masked = c.hf->CreateTerm(BVAND, W, x, c.konst(5));
  ASTNode pred = c.hf->CreateNode(EQ, masked, t);
  ASTNode top = c.hf->CreateNode(
      AND, pred,
      c.hf->CreateNode(AND, c.hf->CreateNode(BVGT, masked, c.konst(1)),
                       c.anchorFor(keep)));

  ASTNode result = c.run(top);
  ASTNodeSet syms;
  c.collectSymbols(result, syms);
  EXPECT_EQ(syms.count(x), 1u) << "stepped past a shared interior node";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_SymbolicSide, eq_mult_odd_mid_chain)
{
  // (= (bvadd (bvmul x 5) 7) t): an odd multiplication is a bijection
  // (modular inverse), so it may sit anywhere on the chain.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode mul = c.hf->CreateTerm(BVMULT, W, x, c.konst(5));
  ASTNode chain = c.hf->CreateTerm(BVPLUS, W, mul, c.konst(7));
  ASTNode pred = c.hf->CreateNode(EQ, chain, t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));
  checkSymbolicFires(c, x, top);
}

TEST(RemoveUnconstrained_SymbolicSide, eq_mult_even_bottom)
{
  // (= (bvmul x 6) t): 6 = 3 * 2, so the image is exactly the even
  // values; condition t[0] == 0, witness x := inv(3) * (t >> 1).
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode pred =
      c.hf->CreateNode(EQ, c.hf->CreateTerm(BVMULT, W, x, c.konst(6)), t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));
  checkSymbolicFires(c, x, top);
}

TEST(RemoveUnconstrained_SymbolicSide, eq_mult_even_above_refused)
{
  // (= (bvmul (bvurem x 5) 6) t): the even multiplication is not at the
  // bottom (a bvnot inner step wouldn't do here: its per-kind rule fires
  // first and legitimately leaves the mult at the bottom of the fresh
  // variable's chain), so its free low preimage bits belong to the inner
  // chain and the walk must refuse.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode chain = c.hf->CreateTerm(
      BVMULT, W, c.hf->CreateTerm(BVMOD, W, x, c.konst(5)), c.konst(6));
  ASTNode pred = c.hf->CreateNode(EQ, chain, t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));

  ASTNode result = c.run(top);
  ASTNodeSet syms;
  c.collectSymbols(result, syms);
  EXPECT_EQ(syms.count(x), 1u) << "walk stepped past a non-bottom even mult";
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

TEST(RemoveUnconstrained_SymbolicSide, eq_mult_zero_refused)
{
  // (= (bvmul x 0) t): the image is {0}; leave it to constant folding.
  Context c;
  ASTNode x = c.bv();
  ASTNode keep = c.bv();
  ASTNode t = c.hf->CreateTerm(BVNOT, W, keep);
  ASTNode pred =
      c.hf->CreateNode(EQ, c.hf->CreateTerm(BVMULT, W, x, c.konst(0)), t);
  ASTNode top = c.hf->CreateNode(AND, pred, c.anchorFor(keep));

  ASTNode result = c.run(top);
  ASTNode back = c.backSubstitute(top);
  c.checkEquivalent(back, result);
}

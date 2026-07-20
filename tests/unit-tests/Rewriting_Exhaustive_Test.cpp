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
 * Exhaustive tests for the sharing-aware Rewriting pass.
 *
 * Unlike RemoveUnconstrained, Rewriting must be equivalence-preserving: for
 * every input formula F, Rewriting(F) and F must agree on every assignment of
 * their free variables. We check that identity exhaustively at small
 * bit-widths.
 *
 * The shapes below target the pass's pattern-match rules, each in two forms:
 *
 *   - the 2-arity form the rule was written for (the rule fires; the result
 *     must still be equivalent), and
 *   - a 3-arity form of the same operator. BVAND, BVOR, BVMULT, BVPLUS and
 *     boolean OR are n-ary in STP, and several rules rebuilt the node from
 *     c[0] and c[1] only, silently dropping the remaining operands. Found via
 *     a fuzzer-generated QF_ABV file whose BVAND(const, ITE, BVNOT(sbvrem))
 *     collapsed to the constant.
 *
 * Inputs are built with the hashing factory so the SimplifyingNodeFactory
 * doesn't pre-fold the shape away before the pass sees it; the pass itself
 * runs with the simplifying factory, as in the standard pipeline. Each
 * builder returns the operator node; the test wraps it so the rules (which
 * fire on the *children* of a visited node) actually see it.
 */

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Parser/parser.h"
#include "stp/Simplifier/Rewriting.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace stp;

namespace
{

struct Context
{
  STPMgr mgr;
  SimplifyingNodeFactory snf;
  NodeFactory* nf; // simplifying factory: what the pass itself uses.
  NodeFactory* hf; // hashing factory: builds inputs without pre-simplifying.
  unsigned counter = 0;

  Context() : snf(*(mgr.hashingNodeFactory), mgr)
  {
    static const bool booted = []() {
      CONSTANTBV::BitVector_Boot();
      return true;
    }();
    (void)booted;

    mgr.defaultNodeFactory = &snf;
    nf = &snf;
    hf = mgr.hashingNodeFactory;
  }

  ASTNode bv(unsigned width)
  {
    return mgr.CreateSymbol(("bv" + std::to_string(counter++)).c_str(), 0,
                            width);
  }

  ASTNode boolean()
  {
    return mgr.CreateSymbol(("b" + std::to_string(counter++)).c_str(), 0, 0);
  }

  ASTNode konst(unsigned value, unsigned width)
  {
    return mgr.CreateBVConst(width, value);
  }

  ASTNode run(ASTNode f)
  {
    Rewriting r(&mgr, nf);
    return r.topLevel(f);
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

  // `before` and `after` must agree on every assignment of their free
  // variables.
  void checkEquivalent(const ASTNode& before, const ASTNode& after)
  {
    ASTNodeSet symSet;
    collectSymbols(before, symSet);
    collectSymbols(after, symSet);
    std::vector<ASTNode> syms(symSet.begin(), symSet.end());

    unsigned long combos = 1;
    for (const auto& s : syms)
      combos *= domainSize(s);
    ASSERT_LE(combos, 1u << 16)
        << "too many assignments (" << combos << ") -- lower the width";

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
          << "rewriting changed the meaning at assignment " << c << "\nbefore:"
          << before << "\nafter:" << after;
    }
  }

  // Rules fire on the children of a visited node, never on the top node
  // itself, so give the operator node a boolean parent before running.
  void checkSoundTerm(const ASTNode& term)
  {
    ASTNode top = hf->CreateNode(EQ, term, bv(term.GetValueWidth()));
    checkEquivalent(top, run(top));
  }

  void checkSoundFormula(const ASTNode& f)
  {
    ASTNode top = hf->CreateNode(NOT, f);
    checkEquivalent(top, run(top));
  }
};

/* BVAND(const, ITE(p, k1, k2)) is pushed through the ITE. The 3-arity BVAND
   used to collapse to just ITE(p, const&k1, const&k2), dropping the third
   operand. */
TEST(Rewriting_Exhaustive, bvand_ite_arity2)
{
  Context c;
  ASTNode k = c.konst(9, 4), k1 = c.konst(14, 4), k2 = c.konst(15, 4);
  ASTNode p = c.boolean();
  ASTNode ite = c.hf->CreateTerm(ITE, 4, p, k1, k2);
  ASTNode band = c.hf->CreateTerm(BVAND, 4, k, ite);
  ASSERT_EQ(band.Degree(), 2u);
  c.checkSoundTerm(band);
}

TEST(Rewriting_Exhaustive, bvand_ite_arity3)
{
  Context c;
  ASTNode k = c.konst(9, 4), k1 = c.konst(14, 4), k2 = c.konst(15, 4);
  ASTNode p = c.boolean();
  ASTNode ite = c.hf->CreateTerm(ITE, 4, p, k1, k2);
  // The extra operand must not be a bare symbol: the hashing factory sorts
  // commutative children with arithless (constants, then symbols, then the
  // rest by node number), and the rule needs [const, ITE, ...]. A BVNOT
  // created after the ITE sorts last, like the BVNOT(SBVREM) in the original
  // fuzzer formula.
  ASTNode x = c.hf->CreateTerm(BVNOT, 4, c.bv(4));
  ASTNode band = c.hf->CreateTerm(BVAND, 4, k, ite, x);
  ASSERT_EQ(band.Degree(), 3u);
  ASSERT_EQ(band[0], k); // the shape the rule pattern-matches on.
  ASSERT_EQ(band[1], ite);
  c.checkSoundTerm(band);
}

/* BVMULT by a one-bit constant (a shift) over a BVCONCAT with a matching
   constant top is turned into a concat. The 3-arity BVMULT used to drop the
   third factor. */
TEST(Rewriting_Exhaustive, bvmult_concat_arity2)
{
  Context c;
  ASTNode k = c.konst(4, 4); // single one bit, at position 2.
  ASTNode ktop = c.konst(1, 2);
  ASTNode y = c.bv(2);
  ASTNode concat = c.hf->CreateTerm(BVCONCAT, 4, ktop, y);
  ASTNode mult = c.hf->CreateTerm(BVMULT, 4, k, concat);
  ASSERT_EQ(mult.Degree(), 2u);
  c.checkSoundTerm(mult);
}

TEST(Rewriting_Exhaustive, bvmult_concat_arity3)
{
  Context c;
  ASTNode k = c.konst(4, 4);
  ASTNode ktop = c.konst(1, 2);
  ASTNode y = c.bv(2);
  ASTNode concat = c.hf->CreateTerm(BVCONCAT, 4, ktop, y);
  ASTNode z = c.hf->CreateTerm(BVNOT, 4, c.bv(4)); // non-symbol: sorts last.
  ASTNode mult = c.hf->CreateTerm(BVMULT, 4, k, concat, z);
  ASSERT_EQ(mult.Degree(), 3u);
  ASSERT_EQ(mult[0], k);
  ASSERT_EQ(mult[1], concat);
  c.checkSoundTerm(mult);
}

/* BVOR with a zero first operand is replaced by its second operand. The
   3-arity BVOR used to drop the operands after the second. (BVOR rarely
   reaches the pass -- the simplifying factory rewrites it into NOT/BVAND --
   but the hashing factory keeps it, as would any caller that doesn't
   pre-simplify.) */
TEST(Rewriting_Exhaustive, bvor_zero_arity2)
{
  Context c;
  ASTNode zero = c.konst(0, 4);
  ASTNode x = c.bv(4);
  ASTNode bvor = c.hf->CreateTerm(BVOR, 4, zero, x);
  ASSERT_EQ(bvor.Degree(), 2u);
  c.checkSoundTerm(bvor);
}

TEST(Rewriting_Exhaustive, bvor_zero_arity3)
{
  Context c;
  ASTNode zero = c.konst(0, 4);
  ASTNode x = c.bv(4);
  ASTNode y = c.bv(4);
  ASTNode bvor = c.hf->CreateTerm(BVOR, 4, zero, x, y);
  ASSERT_EQ(bvor.Degree(), 3u);
  ASSERT_EQ(bvor[0], zero);
  c.checkSoundTerm(bvor);
}

/* Two constant-headed binary BVPLUS children have their constants combined.
   The rule checked the arity of both children but not of the node itself, so
   a 3-arity BVPLUS used to drop its third addend. */
TEST(Rewriting_Exhaustive, bvplus_bvplus_arity2)
{
  Context c;
  ASTNode k1 = c.konst(3, 3), k2 = c.konst(5, 3);
  ASTNode a = c.bv(3), b = c.bv(3);
  ASTNode p1 = c.hf->CreateTerm(BVPLUS, 3, k1, a);
  ASTNode p2 = c.hf->CreateTerm(BVPLUS, 3, k2, b);
  ASTNode plus = c.hf->CreateTerm(BVPLUS, 3, p1, p2);
  ASSERT_EQ(plus.Degree(), 2u);
  c.checkSoundTerm(plus);
}

TEST(Rewriting_Exhaustive, bvplus_bvplus_arity3)
{
  Context c;
  ASTNode k1 = c.konst(3, 3), k2 = c.konst(5, 3);
  ASTNode a = c.bv(3), b = c.bv(3);
  ASTNode p1 = c.hf->CreateTerm(BVPLUS, 3, k1, a);
  ASTNode p2 = c.hf->CreateTerm(BVPLUS, 3, k2, b);
  ASTNode z = c.hf->CreateTerm(BVNOT, 3, c.bv(3)); // non-symbol: sorts last.
  ASTNode plus = c.hf->CreateTerm(BVPLUS, 3, p1, p2, z);
  ASSERT_EQ(plus.Degree(), 3u);
  ASSERT_EQ(plus[0], p1);
  ASSERT_EQ(plus[1], p2);
  c.checkSoundTerm(plus);
}

/* OR(A, NOT(OR(A, B))) is simplified to OR(A, NOT B). The rule tested
   c[0].Degree() == 2 where it meant the node's own arity: it only ever fired
   when A itself had two children, and when the outer OR was n-ary it dropped
   the remaining disjuncts. A is built as a conjunction so the (mis)guard is
   actually exercised. */
TEST(Rewriting_Exhaustive, or_not_or_arity2)
{
  Context c;
  ASTNode a = c.hf->CreateNode(AND, c.boolean(), c.boolean());
  ASTNode b = c.boolean();
  ASTNode inner = c.hf->CreateNode(OR, a, b);
  ASTNode nt = c.hf->CreateNode(NOT, inner);
  ASTNode f = c.hf->CreateNode(OR, a, nt);
  ASSERT_EQ(f.Degree(), 2u);
  ASSERT_EQ(f[0], a);
  ASSERT_EQ(f[1], nt);
  c.checkSoundFormula(f);
}

TEST(Rewriting_Exhaustive, or_not_or_arity3)
{
  Context c;
  ASTNode a = c.hf->CreateNode(AND, c.boolean(), c.boolean());
  ASTNode b = c.boolean();
  ASTNode inner = c.hf->CreateNode(OR, a, b);
  ASTNode nt = c.hf->CreateNode(NOT, inner);
  ASTNode d = c.boolean();
  ASTNode f = c.hf->CreateNode(OR, a, nt, d);
  ASSERT_EQ(f.Degree(), 3u);
  ASSERT_EQ(f[0], a);
  ASSERT_EQ(f[1], nt);
  c.checkSoundFormula(f);
}

/* The original fuzzer shape: EQ(x, BVNOT(BVAND(const, BVNOT(ITE-of-consts),
   BVNOT(x)))), i.e. x == (const | ite | x). Rewriting the inner concat/bvnot
   manufactures the BVAND(const, ITE, rest) shape mid-pass. */
TEST(Rewriting_Exhaustive, bvand_ite_from_bvor_shape)
{
  Context c;
  ASTNode x = c.bv(4);
  ASTNode p = c.boolean();
  ASTNode k = c.konst(9, 4);
  ASTNode ite = c.hf->CreateTerm(ITE, 4, p, c.konst(14, 4), c.konst(15, 4));
  ASTNode band = c.hf->CreateTerm(
      BVAND, 4, k, c.hf->CreateTerm(BVNOT, 4, ite),
      c.hf->CreateTerm(BVNOT, 4, x));
  ASTNode bvor = c.hf->CreateTerm(BVNOT, 4, band);
  ASTNode top = c.hf->CreateNode(NOT, c.hf->CreateNode(EQ, x, bvor));
  c.checkEquivalent(top, c.run(top));
}

} // namespace

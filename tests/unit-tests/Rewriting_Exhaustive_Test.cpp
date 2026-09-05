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

    uint64_t combos = 1;
    for (const auto& s : syms)
      combos *= domainSize(s);
    ASSERT_LE(combos, 1u << 16)
        << "too many assignments (" << combos << ") -- lower the width";

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

/* The BVMULT-of-concat and BVOR-of-zero rules moved into the
   SimplifyingNodeFactory (see SimplifyingNodeFactory_Exhaustive_Test.cpp);
   their n-ary shapes remain covered there. */

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

/* The OR(A, NOT(OR(A, B))) rule also moved into the factory; see
   SimplifyingNodeFactory_Exhaustive_Test.cpp. */

/* 0 = (a + b) --> (bvuminus a) = b. One general rule; the factory then folds
   the bvuminus into a bvuminus operand, across the equality, or into a
   single-use ITE of constants. Each shape below exercises one of those. */
TEST(Rewriting_Exhaustive, eq_zero_plus_symbols)
{
  Context c;
  ASTNode zero = c.konst(0, 3);
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode plus = c.hf->CreateTerm(BVPLUS, 3, x, y);
  ASTNode f = c.hf->CreateNode(EQ, zero, plus);
  ASTNode top = c.hf->CreateNode(NOT, f);
  ASTNode result = c.run(top);
  EXPECT_NE(result, top); // the rule fired.
  c.checkEquivalent(top, result);
}

TEST(Rewriting_Exhaustive, eq_zero_plus_uminus_operand)
{
  Context c;
  ASTNode zero = c.konst(0, 3);
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode plusA =
      c.hf->CreateTerm(BVPLUS, 3, c.hf->CreateTerm(BVUMINUS, 3, x), y);
  ASTNode topA = c.hf->CreateNode(NOT, c.hf->CreateNode(EQ, zero, plusA));
  c.checkEquivalent(topA, c.run(topA));

  ASTNode plusB =
      c.hf->CreateTerm(BVPLUS, 3, x, c.hf->CreateTerm(BVUMINUS, 3, y));
  ASTNode topB = c.hf->CreateNode(NOT, c.hf->CreateNode(EQ, zero, plusB));
  c.checkEquivalent(topB, c.run(topB));
}

TEST(Rewriting_Exhaustive, eq_zero_plus_ite)
{
  Context c;
  ASTNode zero = c.konst(0, 3);
  ASTNode p = c.boolean();
  ASTNode ite = c.hf->CreateTerm(ITE, 3, p, c.konst(5, 3), c.konst(2, 3));
  ASTNode t = c.hf->CreateTerm(BVNOT, 3, c.bv(3)); // non-symbol: sorts last.
  ASTNode plus = c.hf->CreateTerm(BVPLUS, 3, ite, t);
  ASTNode top = c.hf->CreateNode(NOT, c.hf->CreateNode(EQ, zero, plus));
  ASTNode result = c.run(top);
  EXPECT_NE(result, top);
  c.checkEquivalent(top, result);
}

/* The comparison-vs-plus splits: k <> (k' + t) becomes two comparisons whose
   plus has been eliminated. Guarded on the plus being single-use. */
TEST(Rewriting_Exhaustive, comparison_plus_split_fires)
{
  Context c;
  ASTNode x = c.bv(3);
  ASTNode plus = c.hf->CreateTerm(BVPLUS, 3, c.konst(3, 3), x);

  for (const Kind k : {stp::BVSGT, stp::BVGT})
  {
    ASTNode top = c.hf->CreateNode(NOT, c.hf->CreateNode(k, c.konst(2, 3), plus));
    ASTNode result = c.run(top);
    EXPECT_NE(result, top); // the split fired.
    c.checkEquivalent(top, result);
  }

  // The plus-on-the-left variant.
  ASTNode top = c.hf->CreateNode(NOT, c.hf->CreateNode(stp::BVGT, plus, c.konst(4, 3)));
  ASTNode result = c.run(top);
  EXPECT_NE(result, top);
  c.checkEquivalent(top, result);
}

TEST(Rewriting_Exhaustive, comparison_plus_split_respects_sharing)
{
  Context c;
  ASTNode x = c.bv(3);
  ASTNode y = c.bv(3);
  ASTNode plus = c.hf->CreateTerm(BVPLUS, 3, c.konst(3, 3), x);
  // The plus is shared with the equality, so the split must not fire:
  // it would leave the plus alive and the extra comparison would be a
  // pure loss.
  ASTNode top = c.hf->CreateNode(
      AND, c.hf->CreateNode(NOT, c.hf->CreateNode(stp::BVGT, c.konst(2, 3), plus)),
      c.hf->CreateNode(EQ, y, plus));
  ASTNode result = c.run(top);
  EXPECT_EQ(result, top); // nothing fired.
  c.checkEquivalent(top, result);
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

/* (c1 * x) = c0 with odd c1: multiply through by the inverse; the
   multiplication disappears. 5^-1 mod 8 is 5, so x = 5*3 mod 8 = 7. */
TEST(Rewriting_Exhaustive, eq_mult_constant_inverse)
{
  Context c;
  ASTNode x = c.bv(3);
  ASTNode mult = c.hf->CreateTerm(BVMULT, 3, c.konst(5, 3), x);
  ASTNode top = c.hf->CreateNode(NOT, c.hf->CreateNode(EQ, mult, c.konst(3, 3)));
  EXPECT_NE(c.run(top), top);
  c.checkEquivalent(top, c.run(top));
}

/* (c1 * x) = (c2 * y) with odd c1 --> x = ((c1^-1 * c2) * y) */
TEST(Rewriting_Exhaustive, eq_mult_mult_inverse)
{
  Context c;
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode m1 = c.hf->CreateTerm(BVMULT, 3, c.konst(3, 3), x);
  ASTNode m2 = c.hf->CreateTerm(BVMULT, 3, c.konst(2, 3), y);
  ASTNode top = c.hf->CreateNode(NOT, c.hf->CreateNode(EQ, m1, m2));
  EXPECT_NE(c.run(top), top);
  c.checkEquivalent(top, c.run(top));
}

/* the mult is shared, so multiplying through would strand it: no fire */
TEST(Rewriting_Exhaustive, eq_mult_inverse_respects_sharing)
{
  Context c;
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode mult = c.hf->CreateTerm(BVMULT, 3, c.konst(5, 3), x);
  ASTNode eq1 = c.hf->CreateNode(EQ, mult, c.konst(3, 3));
  ASTNode eq2 = c.hf->CreateNode(EQ, mult, y);
  ASTNode top = c.hf->CreateNode(AND, eq1, eq2);
  EXPECT_EQ(c.run(top), top);
  c.checkEquivalent(top, c.run(top));
}

/* addends common to both sides of an equality cancel, one occurrence per
   side per match */
TEST(Rewriting_Exhaustive, eq_plus_plus_cancel)
{
  Context c;
  ASTNode a = c.bv(2), x = c.bv(2), y = c.bv(2), z = c.bv(2);

  ASTNode lhs = c.hf->CreateTerm(BVPLUS, 2, a, x, y);
  ASTNode rhs = c.hf->CreateTerm(BVPLUS, 2, a, z);
  ASTNode top = c.hf->CreateNode(NOT, c.hf->CreateNode(EQ, lhs, rhs));
  EXPECT_NE(c.run(top), top);
  c.checkEquivalent(top, c.run(top));

  // x + x = x + y cancels only one occurrence of x.
  ASTNode lhs2 = c.hf->CreateTerm(BVPLUS, 2, x, x);
  ASTNode rhs2 = c.hf->CreateTerm(BVPLUS, 2, x, y);
  ASTNode top2 = c.hf->CreateNode(NOT, c.hf->CreateNode(EQ, lhs2, rhs2));
  EXPECT_NE(c.run(top2), top2);
  c.checkEquivalent(top2, c.run(top2));

  // Identical sums cancel completely, to 0 = 0.
  ASTNode top3 = c.hf->CreateNode(
      NOT, c.hf->CreateNode(EQ, c.hf->CreateTerm(BVPLUS, 2, x, y),
                            c.hf->CreateTerm(BVPLUS, 2, y, x)));
  c.checkEquivalent(top3, c.run(top3));
}

/* (a * b) + (a * d) --> a * (b + d), including when the summed constants
   fold to zero */
TEST(Rewriting_Exhaustive, plus_of_shared_factor_mults)
{
  Context c;
  ASTNode a = c.bv(3), b = c.bv(3), d = c.bv(3);
  ASTNode m1 = c.hf->CreateTerm(BVMULT, 3, a, b);
  ASTNode m2 = c.hf->CreateTerm(BVMULT, 3, a, d);
  ASTNode plus = c.hf->CreateTerm(BVPLUS, 3, m1, m2);
  ASTNode top = c.hf->CreateNode(EQ, plus, c.bv(3));
  EXPECT_NE(c.run(top), top);
  c.checkEquivalent(top, c.run(top));

  // 3x + 5x at width 3 is 8x = 0.
  ASTNode x = c.bv(3);
  ASTNode k1 = c.hf->CreateTerm(BVMULT, 3, c.konst(3, 3), x);
  ASTNode k2 = c.hf->CreateTerm(BVMULT, 3, c.konst(5, 3), x);
  ASTNode plus2 = c.hf->CreateTerm(BVPLUS, 3, k1, k2);
  ASTNode top2 = c.hf->CreateNode(EQ, plus2, c.bv(3));
  EXPECT_NE(c.run(top2), top2);
  c.checkEquivalent(top2, c.run(top2));
}

// Distinct nodes of a kind reachable from n, so a shared node counts once.
static void countKind(const Kind k, const ASTNode& n, ASTNodeSet& seen,
                      unsigned& found)
{
  if (!seen.insert(n).second)
    return;
  if (n.GetKind() == k)
    found++;
  for (const auto& c : n)
    countKind(k, c, seen, found);
}

static unsigned countKind(const Kind k, const ASTNode& n)
{
  ASTNodeSet seen;
  unsigned found = 0;
  countKind(k, n, seen, found);
  return found;
}

/* ITE(p, x, ITE(q, x, y)) --> ITE(p OR q, x, y): the inner multiplexer is
   unshared, so it dies with the rewrite. */
TEST(Rewriting_Exhaustive, ite_chain_repeated_then)
{
  Context c;
  ASTNode p = c.boolean(), q = c.boolean();
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode inner = c.hf->CreateTerm(ITE, 3, q, x, y);
  ASTNode outer = c.hf->CreateTerm(ITE, 3, p, x, inner);
  ASTNode top = c.hf->CreateNode(EQ, outer, c.bv(3));

  ASTNode after = c.run(top);
  ASSERT_EQ(2u, countKind(ITE, top));
  ASSERT_EQ(1u, countKind(ITE, after));
  c.checkEquivalent(top, after);
}

/* ITE(p, x, ITE(q, y, x)) --> ITE(p OR NOT q, x, y). */
TEST(Rewriting_Exhaustive, ite_chain_repeated_else)
{
  Context c;
  ASTNode p = c.boolean(), q = c.boolean();
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode inner = c.hf->CreateTerm(ITE, 3, q, y, x);
  ASTNode outer = c.hf->CreateTerm(ITE, 3, p, x, inner);
  ASTNode top = c.hf->CreateNode(EQ, outer, c.bv(3));

  ASTNode after = c.run(top);
  ASSERT_EQ(2u, countKind(ITE, top));
  ASSERT_EQ(1u, countKind(ITE, after));
  c.checkEquivalent(top, after);
}

/* A chain of them collapses into one disjunction, one multiplexer at a time.
   */
TEST(Rewriting_Exhaustive, ite_chain_three_deep)
{
  Context c;
  ASTNode p = c.boolean(), q = c.boolean(), r = c.boolean();
  ASTNode x = c.bv(2), y = c.bv(2);
  ASTNode i2 = c.hf->CreateTerm(ITE, 2, r, x, y);
  ASTNode i1 = c.hf->CreateTerm(ITE, 2, q, x, i2);
  ASTNode i0 = c.hf->CreateTerm(ITE, 2, p, x, i1);
  ASTNode top = c.hf->CreateNode(EQ, i0, c.bv(2));

  ASTNode after = c.run(top);
  ASSERT_EQ(3u, countKind(ITE, top));
  ASSERT_EQ(1u, countKind(ITE, after));
  c.checkEquivalent(top, after);
}

/* With the inner multiplexer shared, merging would leave it in place and
   build the merged node beside it, so the rule declines. */
TEST(Rewriting_Exhaustive, ite_chain_inner_shared)
{
  Context c;
  ASTNode p = c.boolean(), q = c.boolean();
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode inner = c.hf->CreateTerm(ITE, 3, q, x, y);
  ASTNode outer = c.hf->CreateTerm(ITE, 3, p, x, inner);
  ASTNode top = c.hf->CreateNode(EQ, outer, inner);

  ASTNode after = c.run(top);
  ASSERT_EQ(2u, countKind(ITE, after));
  c.checkEquivalent(top, after);
}

/* The same shape over formulas rather than terms. */
TEST(Rewriting_Exhaustive, ite_chain_boolean)
{
  Context c;
  ASTNode p = c.boolean(), q = c.boolean();
  ASTNode x = c.boolean(), y = c.boolean();
  ASTNode inner = c.hf->CreateNode(ITE, q, x, y);
  ASTNode outer = c.hf->CreateNode(ITE, p, x, inner);
  ASTNode top = c.hf->CreateNode(NOT, outer);

  c.checkEquivalent(top, c.run(top));
}

/* ITE(p, ITE(q, x, y), y) --> ITE(p AND q, x, y): the inner multiplexer is
   the then branch this time, and the outer's else is what repeats. */
TEST(Rewriting_Exhaustive, ite_chain_then_side_repeated_else)
{
  Context c;
  ASTNode p = c.boolean(), q = c.boolean();
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode inner = c.hf->CreateTerm(ITE, 3, q, x, y);
  ASTNode outer = c.hf->CreateTerm(ITE, 3, p, inner, y);
  ASTNode top = c.hf->CreateNode(EQ, outer, c.bv(3));

  ASTNode after = c.run(top);
  ASSERT_EQ(2u, countKind(ITE, top));
  ASSERT_EQ(1u, countKind(ITE, after));
  c.checkEquivalent(top, after);
}

/* ITE(p, ITE(q, y, x), y) --> ITE(p AND NOT q, x, y). */
TEST(Rewriting_Exhaustive, ite_chain_then_side_repeated_then)
{
  Context c;
  ASTNode p = c.boolean(), q = c.boolean();
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode inner = c.hf->CreateTerm(ITE, 3, q, y, x);
  ASTNode outer = c.hf->CreateTerm(ITE, 3, p, inner, y);
  ASTNode top = c.hf->CreateNode(EQ, outer, c.bv(3));

  ASTNode after = c.run(top);
  ASSERT_EQ(2u, countKind(ITE, top));
  ASSERT_EQ(1u, countKind(ITE, after));
  c.checkEquivalent(top, after);
}

/* The then-side rule respects sharing too. */
TEST(Rewriting_Exhaustive, ite_chain_then_side_inner_shared)
{
  Context c;
  ASTNode p = c.boolean(), q = c.boolean();
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode inner = c.hf->CreateTerm(ITE, 3, q, x, y);
  ASTNode outer = c.hf->CreateTerm(ITE, 3, p, inner, y);
  ASTNode top = c.hf->CreateNode(EQ, outer, inner);

  ASTNode after = c.run(top);
  ASSERT_EQ(2u, countKind(ITE, after));
  c.checkEquivalent(top, after);
}

/* Both sides at once: an inner multiplexer on each branch, each repeating the
   value the other branch of the outer selects. */
TEST(Rewriting_Exhaustive, ite_chain_both_sides)
{
  Context c;
  ASTNode p = c.boolean(), q = c.boolean(), r = c.boolean();
  ASTNode x = c.bv(2), y = c.bv(2), z = c.bv(2);
  ASTNode thenSide = c.hf->CreateTerm(ITE, 2, q, x, y);
  ASTNode elseSide = c.hf->CreateTerm(ITE, 2, r, thenSide, z);
  ASTNode outer = c.hf->CreateTerm(ITE, 2, p, thenSide, elseSide);
  ASTNode top = c.hf->CreateNode(EQ, outer, c.bv(2));

  c.checkEquivalent(top, c.run(top));
}

} // namespace

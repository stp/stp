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
 * Exhaustive tests for SimplifyingNodeFactory rules, in particular the
 * sharing-independent rules moved here from the Rewriting pass.
 *
 * Each test builds the children with the hashing factory (so nothing is
 * pre-simplified), then creates the same node through both factories. The
 * two results must agree on every assignment of their free variables, and
 * where the rule is guaranteed to apply the simplifying factory's result
 * must differ structurally from the hashing factory's (i.e. the rule fired).
 */

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Parser/parser.h"
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
  NodeFactory* nf; // simplifying factory: under test.
  NodeFactory* hf; // hashing factory: builds inputs without simplifying.
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
          << "factory changed the meaning at assignment " << c << "\nbefore:"
          << before << "\nafter:" << after;
    }
  }

  // Create the node through both factories; the simplifying factory's result
  // must be equivalent, and (when expectFired) different.
  void checkTerm(Kind k, unsigned width, const ASTVec& children,
                 bool expectFired = true)
  {
    ASTNode plain = hf->CreateTerm(k, width, children);
    ASTNode simplified = nf->CreateTerm(k, width, children);
    if (expectFired)
    {
      EXPECT_NE(plain, simplified);
    }
    checkEquivalent(plain, simplified);
  }

  void checkNode(Kind k, const ASTVec& children, bool expectFired = true)
  {
    ASTNode plain = hf->CreateNode(k, children);
    ASTNode simplified = nf->CreateNode(k, children);
    if (expectFired)
    {
      EXPECT_NE(plain, simplified);
    }
    checkEquivalent(plain, simplified);
  }
};

/* constant = constant + t --> combined-constant = t */
TEST(SimplifyingNodeFactory_Exhaustive, eq_constant_plus)
{
  Context c;
  ASTNode t = c.bv(3);
  ASTNode plus = c.hf->CreateTerm(BVPLUS, 3, c.konst(5, 3), t);
  c.checkNode(EQ, {c.konst(3, 3), plus});
  c.checkNode(EQ, {plus, c.konst(3, 3)});
}

/* x << k (constant k) --> (extract of x) ++ 0^k, not a multiplication */
TEST(SimplifyingNodeFactory_Exhaustive, leftshift_by_constant)
{
  Context c;
  ASTNode x = c.bv(4);
  for (unsigned k = 1; k <= 3; k++)
  {
    ASTNode s = c.nf->CreateTerm(BVLEFTSHIFT, 4, x, c.konst(k, 4));
    EXPECT_EQ(s.GetKind(), BVCONCAT);
    c.checkTerm(BVLEFTSHIFT, 4, {x, c.konst(k, 4)});
  }
}

/* (~x) smod x, x smod (~x), (~x) smod (-x): the dividend becomes -1 */
TEST(SimplifyingNodeFactory_Exhaustive, smod_of_bvnot)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode nt = c.hf->CreateTerm(BVNOT, w, x);
    ASTNode neg = c.hf->CreateTerm(BVUMINUS, w, x);
    c.checkTerm(SBVMOD, w, {nt, x});
    c.checkTerm(SBVMOD, w, {x, nt});
    c.checkTerm(SBVMOD, w, {nt, neg});
  }
}

/* (~x) srem x and x srem (~x): rewrite to -(1 smod divisor) */
TEST(SimplifyingNodeFactory_Exhaustive, srem_of_bvnot)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode nt = c.hf->CreateTerm(BVNOT, w, x);
    c.checkTerm(SBVREM, w, {nt, x});
    c.checkTerm(SBVREM, w, {x, nt});
  }
}

/* (~x) mod x, x mod (~x): the dividend becomes max; (-x) mod (~x): 1 srem */
TEST(SimplifyingNodeFactory_Exhaustive, mod_of_bvnot)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode nt = c.hf->CreateTerm(BVNOT, w, x);
    ASTNode neg = c.hf->CreateTerm(BVUMINUS, w, x);
    c.checkTerm(BVMOD, w, {nt, x});
    c.checkTerm(BVMOD, w, {x, nt});
    c.checkTerm(BVMOD, w, {neg, nt});
  }
}

/* ((x ++ k1) ++ k2) and (k0 ++ (k1 ++ y)): adjacent constants merge */
TEST(SimplifyingNodeFactory_Exhaustive, concat_constant_merge)
{
  Context c;
  ASTNode x = c.bv(3);
  ASTNode inner1 = c.hf->CreateTerm(BVCONCAT, 5, x, c.konst(2, 2));
  c.checkTerm(BVCONCAT, 7, {inner1, c.konst(1, 2)});

  ASTNode y = c.bv(3);
  ASTNode inner2 = c.hf->CreateTerm(BVCONCAT, 5, c.konst(2, 2), y);
  c.checkTerm(BVCONCAT, 7, {c.konst(1, 2), inner2});
}

/* extract over bvnot --> bvnot over extract */
TEST(SimplifyingNodeFactory_Exhaustive, extract_over_bvnot)
{
  Context c;
  ASTNode x = c.bv(4);
  ASTNode nt = c.hf->CreateTerm(BVNOT, 4, x);
  c.checkTerm(BVEXTRACT, 2, {nt, c.mgr.CreateBVConst(32, 2),
                             c.mgr.CreateBVConst(32, 1)});
}

/* extract over multiplication-by-2^p (a shift), both operand orders */
TEST(SimplifyingNodeFactory_Exhaustive, extract_over_shift_mult)
{
  Context c;
  ASTNode y = c.bv(4);
  ASTNode multA = c.hf->CreateTerm(BVMULT, 4, c.konst(4, 4), y);
  c.checkTerm(BVEXTRACT, 2, {multA, c.mgr.CreateBVConst(32, 2),
                             c.mgr.CreateBVConst(32, 1)});
  ASTNode multB = c.hf->CreateTerm(BVMULT, 4, y, c.konst(4, 4));
  c.checkTerm(BVEXTRACT, 2, {multB, c.mgr.CreateBVConst(32, 2),
                             c.mgr.CreateBVConst(32, 1)});
}

/* constant > (constant-top ++ y), with the tops equal and not equal */
TEST(SimplifyingNodeFactory_Exhaustive, gt_constant_concat)
{
  Context c;
  ASTNode y = c.bv(2);
  ASTNode concat = c.hf->CreateTerm(BVCONCAT, 4, c.konst(1, 2), y);
  // 0b0110: top bits 01 match the concat's constant -> rule fires.
  c.checkNode(stp::BVGT, {c.konst(6, 4), concat});
  // 0b1010: top bits 10 don't match -> no fire, still equivalent.
  c.checkNode(stp::BVGT, {c.konst(10, 4), concat}, false);
}

/* a XOR (NOT a OR b) == NOT a OR NOT b, all orientations */
TEST(SimplifyingNodeFactory_Exhaustive, xor_or_not)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode na = c.hf->CreateNode(NOT, a);
  ASTNode or1 = c.hf->CreateNode(OR, na, b);
  c.checkNode(XOR, {a, or1});
  c.checkNode(XOR, {or1, a});
  ASTNode or2 = c.hf->CreateNode(OR, b, na);
  c.checkNode(XOR, {a, or2});
}

/* A OR NOT(A OR B) == A OR NOT B, all orientations */
TEST(SimplifyingNodeFactory_Exhaustive, or_not_or)
{
  Context c;
  ASTNode a = c.boolean(), b = c.boolean();
  ASTNode inner = c.hf->CreateNode(OR, a, b);
  ASTNode nt = c.hf->CreateNode(NOT, inner);
  c.checkNode(OR, {a, nt});
  c.checkNode(OR, {nt, a});
  ASTNode inner2 = c.hf->CreateNode(OR, b, a);
  ASTNode nt2 = c.hf->CreateNode(NOT, inner2);
  c.checkNode(OR, {a, nt2});
}

/* 2^p * (k ++ y) when p == width(k): the shift pushes k out entirely */
TEST(SimplifyingNodeFactory_Exhaustive, mult_of_concat)
{
  Context c;
  ASTNode y = c.bv(2);
  ASTNode concat = c.hf->CreateTerm(BVCONCAT, 4, c.konst(1, 2), y);
  c.checkTerm(BVMULT, 4, {c.konst(4, 4), concat});
  c.checkTerm(BVMULT, 4, {concat, c.konst(4, 4)});
}

/* BVOR with a zero operand: the factory's NOT/AND form drops the identity
   (this subsumes the rule deleted from the Rewriting pass, for any arity).
   The deleted rule's example:
     117334:(BVOR
       1434:0x0000
       2594:(BVCONCAT
         1402:0x00
         384:T1@362))  */
TEST(SimplifyingNodeFactory_Exhaustive, bvor_zero)
{
  Context c;
  ASTNode x = c.bv(3), y = c.bv(3);
  c.checkTerm(stp::BVOR, 3, {c.konst(0, 3), x});
  c.checkTerm(stp::BVOR, 3, {c.konst(0, 3), x, y});
}

/* ((s & t) mod t) / s and (t & (s mod t)) / s: both become
   ite(s = 0, max, ite((s & t) = s AND s < t, 1, 0)), removing the
   division and the modulus. The original expressions:
     873:(NOT 872:(EQ
       842:(BVDIV
         838:(BVMOD
           576:(BVAND 42:s 48:t)
           48:t)
         42:s)
       870:(BVDIV
         866:(BVAND
           48:t
           854:(BVMOD 42:s 48:t))
         42:s)))  */
TEST(SimplifyingNodeFactory_Exhaustive, div_of_mod_of_and)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode s = c.bv(w);
    ASTNode t = c.bv(w);

    ASTNode modOfAnd =
        c.hf->CreateTerm(BVMOD, w, c.hf->CreateTerm(stp::BVAND, w, s, t), t);
    c.checkTerm(BVDIV, w, {modOfAnd, s});

    ASTNode andOfMod =
        c.hf->CreateTerm(stp::BVAND, w, t, c.hf->CreateTerm(BVMOD, w, s, t));
    c.checkTerm(BVDIV, w, {andOfMod, s});

    // Both forms must produce the identical node, so an equality between
    // them folds to true.
    ASTNode lhs = c.nf->CreateTerm(BVDIV, w, modOfAnd, s);
    ASTNode rhs = c.nf->CreateTerm(BVDIV, w, andOfMod, s);
    EXPECT_EQ(lhs, rhs);
    EXPECT_EQ(lhs.GetKind(), ITE);
  }
}

/* (x[i:j] ++ x[j-1:k]) --> x[i:k]: adjacent extracts of the same term */
TEST(SimplifyingNodeFactory_Exhaustive, concat_adjacent_extracts)
{
  Context c;
  ASTNode x = c.bv(8);
  auto idx = [&c](unsigned v) { return c.mgr.CreateBVConst(32, v); };

  // Full width: collapses all the way back to x.
  ASTNode top = c.hf->CreateTerm(BVEXTRACT, 4, x, idx(7), idx(4));
  ASTNode bottom = c.hf->CreateTerm(BVEXTRACT, 4, x, idx(3), idx(0));
  c.checkTerm(BVCONCAT, 8, {top, bottom});
  EXPECT_EQ(c.nf->CreateTerm(BVCONCAT, 8, top, bottom), x);

  // Partial: x[6:4] ++ x[3:1] --> x[6:1].
  ASTNode top2 = c.hf->CreateTerm(BVEXTRACT, 3, x, idx(6), idx(4));
  ASTNode bottom2 = c.hf->CreateTerm(BVEXTRACT, 3, x, idx(3), idx(1));
  c.checkTerm(BVCONCAT, 6, {top2, bottom2});
  EXPECT_EQ(c.nf->CreateTerm(BVCONCAT, 6, top2, bottom2).GetKind(), BVEXTRACT);

  // Not adjacent: x[7:5] ++ x[3:0] must be left alone.
  ASTNode top3 = c.hf->CreateTerm(BVEXTRACT, 3, x, idx(7), idx(5));
  c.checkTerm(BVCONCAT, 7, {top3, bottom}, false);
}

/* BVSX(m, BVSX(n, a)) --> BVSX(m, a) */
TEST(SimplifyingNodeFactory_Exhaustive, sx_of_sx)
{
  Context c;
  ASTNode a = c.bv(3);
  ASTNode inner = c.hf->CreateTerm(BVSX, 5, a, c.mgr.CreateBVConst(32, 5));
  c.checkTerm(BVSX, 8, {inner, c.mgr.CreateBVConst(32, 8)});

  ASTNode collapsed =
      c.nf->CreateTerm(BVSX, 8, inner, c.mgr.CreateBVConst(32, 8));
  EXPECT_EQ(collapsed.GetKind(), BVSX);
  EXPECT_EQ(collapsed[0], a);
}

/* x / 2^n --> 0^n ++ x[w-1:n] */
TEST(SimplifyingNodeFactory_Exhaustive, div_by_power_of_two)
{
  Context c;
  ASTNode x = c.bv(4);
  for (unsigned d : {2u, 4u, 8u})
  {
    c.checkTerm(BVDIV, 4, {x, c.konst(d, 4)});
    EXPECT_EQ(c.nf->CreateTerm(BVDIV, 4, x, c.konst(d, 4)).GetKind(),
              BVCONCAT);
  }
}

/* x mod 2^n --> 0^(w-n) ++ x[n-1:0] */
TEST(SimplifyingNodeFactory_Exhaustive, mod_by_power_of_two)
{
  Context c;
  ASTNode x = c.bv(4);
  for (unsigned d : {2u, 4u, 8u})
  {
    c.checkTerm(BVMOD, 4, {x, c.konst(d, 4)});
    EXPECT_EQ(c.nf->CreateTerm(BVMOD, 4, x, c.konst(d, 4)).GetKind(),
              BVCONCAT);
  }
}

/* (a ++ b) = (a ++ c) --> b = c, and the shared-tail variant */
TEST(SimplifyingNodeFactory_Exhaustive, eq_concat_shared_half)
{
  Context c;
  ASTNode a = c.bv(2);
  ASTNode x = c.bv(3);
  ASTNode y = c.bv(3);

  ASTNode sharedHead1 = c.hf->CreateTerm(BVCONCAT, 5, a, x);
  ASTNode sharedHead2 = c.hf->CreateTerm(BVCONCAT, 5, a, y);
  c.checkNode(EQ, {sharedHead1, sharedHead2});
  EXPECT_EQ(c.nf->CreateNode(EQ, sharedHead1, sharedHead2),
            c.nf->CreateNode(EQ, x, y));

  ASTNode sharedTail1 = c.hf->CreateTerm(BVCONCAT, 5, x, a);
  ASTNode sharedTail2 = c.hf->CreateTerm(BVCONCAT, 5, y, a);
  c.checkNode(EQ, {sharedTail1, sharedTail2});
  EXPECT_EQ(c.nf->CreateNode(EQ, sharedTail1, sharedTail2),
            c.nf->CreateNode(EQ, x, y));
}

/* constant = high ++ low --> high = constant[high] && low = constant[low].
   This is the common one-level case, which does not need the nested-concat
   continuation stack. */
TEST(SimplifyingNodeFactory_Exhaustive, eq_constant_shallow_concat)
{
  Context c;
  const ASTNode high = c.bv(2);
  const ASTNode low = c.bv(3);
  const ASTNode concat = c.hf->CreateTerm(BVCONCAT, 5, high, low);
  const ASTNode constant = c.konst(0b10110, 5);
  const ASTNode plain = c.hf->CreateNode(EQ, constant, concat);
  const ASTNode simplified = c.nf->CreateNode(EQ, constant, concat);
  const ASTNode reversePlain = c.hf->CreateNode(EQ, concat, constant);
  const ASTNode reverseSimplified = c.nf->CreateNode(EQ, concat, constant);

  const ASTNode lowEquality =
      c.nf->CreateNode(EQ, low, c.konst(0b110, 3));
  const ASTNode highEquality =
      c.nf->CreateNode(EQ, high, c.konst(0b10, 2));
  const ASTNode expected = c.nf->CreateNode(AND, lowEquality, highEquality);

  EXPECT_NE(plain, simplified);
  EXPECT_EQ(expected, simplified);
  EXPECT_NE(reversePlain, reverseSimplified);
  EXPECT_EQ(expected, reverseSimplified);
  c.checkEquivalent(plain, simplified);
  c.checkEquivalent(reversePlain, reverseSimplified);
}

/* equality and signed comparison of two sign extensions from the same
   width reduce to the originals */
TEST(SimplifyingNodeFactory_Exhaustive, sx_pairs)
{
  Context c;
  ASTNode a = c.bv(3);
  ASTNode b = c.bv(3);
  ASTNode len = c.mgr.CreateBVConst(32, 6);
  ASTNode sxa = c.hf->CreateTerm(BVSX, 6, a, len);
  ASTNode sxb = c.hf->CreateTerm(BVSX, 6, b, len);

  c.checkNode(EQ, {sxa, sxb});
  EXPECT_EQ(c.nf->CreateNode(EQ, sxa, sxb), c.nf->CreateNode(EQ, a, b));

  c.checkNode(BVSGT, {sxa, sxb});
  EXPECT_EQ(c.nf->CreateNode(BVSGT, sxa, sxb),
            c.nf->CreateNode(BVSGT, a, b));

  // Different source widths: the wider side's extension goes away, and
  // the narrower side extends just up to the wider side's width.
  ASTNode n = c.bv(2);
  ASTNode sxn = c.hf->CreateTerm(BVSX, 6, n, len);
  ASTNode nTo3 = c.nf->CreateTerm(BVSX, 3, n, c.mgr.CreateBVConst(32, 3));

  c.checkNode(EQ, {sxn, sxb});
  EXPECT_EQ(c.nf->CreateNode(EQ, sxn, sxb), c.nf->CreateNode(EQ, nTo3, b));

  c.checkNode(BVSGT, {sxb, sxn});
  EXPECT_EQ(c.nf->CreateNode(BVSGT, sxb, sxn),
            c.nf->CreateNode(BVSGT, b, nTo3));
}

/* (a ++ b) sgt (a ++ c): the shared head decides the sign, so the tails
   compare unsigned */
TEST(SimplifyingNodeFactory_Exhaustive, sgt_concat_shared_head)
{
  Context c;
  ASTNode a = c.bv(2);
  ASTNode x = c.bv(3);
  ASTNode y = c.bv(3);
  ASTNode l = c.hf->CreateTerm(BVCONCAT, 5, a, x);
  ASTNode r = c.hf->CreateTerm(BVCONCAT, 5, a, y);
  c.checkNode(BVSGT, {l, r});
  EXPECT_EQ(c.nf->CreateNode(BVSGT, l, r), c.nf->CreateNode(BVGT, x, y));
}

/* x sgt smallest --> NOT(x == smallest) and largest sgt x --> NOT(largest == x):
   nothing is below the most-negative value or above the most-positive value */
TEST(SimplifyingNodeFactory_Exhaustive, sgt_signed_boundaries)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode smallest = c.konst(1u << (w - 1), w);       // 100...0
    ASTNode largest = c.konst((1u << (w - 1)) - 1, w);  // 011...1

    c.checkNode(BVSGT, {x, smallest});
    EXPECT_EQ(c.nf->CreateNode(BVSGT, x, smallest),
              c.nf->CreateNode(NOT, c.nf->CreateNode(EQ, x, smallest)));

    c.checkNode(BVSGT, {largest, x});
    EXPECT_EQ(c.nf->CreateNode(BVSGT, largest, x),
              c.nf->CreateNode(NOT, c.nf->CreateNode(EQ, largest, x)));
  }
}

/* a 1-bit ITE choosing between 0 and 1 on a 1-bit equality collapses to
   the tested term or its complement */
TEST(SimplifyingNodeFactory_Exhaustive, ite_width1_boolean_to_term)
{
  Context c;
  ASTNode t = c.bv(1);
  ASTNode one = c.konst(1, 1);
  ASTNode zero = c.konst(0, 1);

  for (int constFirst = 0; constFirst < 2; constFirst++)
  {
    ASTNode eqOne = constFirst ? c.hf->CreateNode(EQ, one, t)
                               : c.hf->CreateNode(EQ, t, one);
    ASTNode eqZero = constFirst ? c.hf->CreateNode(EQ, zero, t)
                                : c.hf->CreateNode(EQ, t, zero);

    c.checkTerm(ITE, 1, {eqOne, one, zero});
    EXPECT_EQ(c.nf->CreateTerm(ITE, 1, eqOne, one, zero), t);

    c.checkTerm(ITE, 1, {eqZero, zero, one});
    EXPECT_EQ(c.nf->CreateTerm(ITE, 1, eqZero, zero, one), t);

    c.checkTerm(ITE, 1, {eqOne, zero, one});
    c.checkTerm(ITE, 1, {eqZero, one, zero});
    EXPECT_EQ(c.nf->CreateTerm(ITE, 1, eqOne, zero, one),
              c.nf->CreateTerm(ITE, 1, eqZero, one, zero));
  }
}

/* 1-bit comparisons have a single satisfying assignment */
TEST(SimplifyingNodeFactory_Exhaustive, gt_sgt_width1)
{
  Context c;
  ASTNode a = c.bv(1);
  ASTNode b = c.bv(1);
  c.checkNode(BVGT, {a, b});
  c.checkNode(BVSGT, {a, b});
}

/* ~a > ~b --> b > a */
TEST(SimplifyingNodeFactory_Exhaustive, gt_of_bvnots)
{
  Context c;
  ASTNode a = c.bv(3);
  ASTNode b = c.bv(3);
  ASTNode na = c.hf->CreateTerm(BVNOT, 3, a);
  ASTNode nb = c.hf->CreateTerm(BVNOT, 3, b);
  c.checkNode(BVGT, {na, nb});
  EXPECT_EQ(c.nf->CreateNode(BVGT, na, nb), c.nf->CreateNode(BVGT, b, a));
}

/* x > (x + c) --> x > ~c, and (x + c) > x --> NOT(x > ~c) */
TEST(SimplifyingNodeFactory_Exhaustive, gt_vs_plus_constant)
{
  Context c;
  ASTNode x = c.bv(3);
  for (unsigned k = 1; k <= 7; k++)
  {
    for (int constFirst = 0; constFirst < 2; constFirst++)
    {
      ASTNode plus = constFirst
                         ? c.hf->CreateTerm(BVPLUS, 3, c.konst(k, 3), x)
                         : c.hf->CreateTerm(BVPLUS, 3, x, c.konst(k, 3));
      c.checkNode(BVGT, {x, plus});
      c.checkNode(BVGT, {plus, x});
    }
  }
}

/* 1-bit (x = 1) --> NOT(x = 0), for both operand orders */
TEST(SimplifyingNodeFactory_Exhaustive, eq_width1_normalised)
{
  Context c;
  ASTNode x = c.bv(1);
  ASTNode notZero =
      c.nf->CreateNode(NOT, c.nf->CreateNode(EQ, x, c.konst(0, 1)));
  c.checkNode(EQ, {x, c.konst(1, 1)});
  EXPECT_EQ(c.nf->CreateNode(EQ, x, c.konst(1, 1)), notZero);
  EXPECT_EQ(c.nf->CreateNode(EQ, c.konst(1, 1), x), notZero);
}

/* (c << s) with a negative constant c --> -((-c) << s); the most negative
   constant is left alone */
TEST(SimplifyingNodeFactory_Exhaustive, leftshift_negative_constant_base)
{
  Context c;
  ASTNode s = c.bv(4);
  for (unsigned k : {9u, 12u, 15u}) // negative 4-bit constants, not 8
    c.checkTerm(BVLEFTSHIFT, 4, {c.konst(k, 4), s});
  c.checkTerm(BVLEFTSHIFT, 4, {c.konst(8, 4), s}, false);
}

/* extracts entirely inside a sign-extension rebase onto the sign bit;
   extracts entirely inside the original term drop the extension;
   straddling extracts are left alone */
TEST(SimplifyingNodeFactory_Exhaustive, extract_over_sx)
{
  Context c;
  ASTNode x = c.bv(3);
  ASTNode sx = c.hf->CreateTerm(BVSX, 6, x, c.mgr.CreateBVConst(32, 6));

  // Inside the extension.
  c.checkTerm(BVEXTRACT, 3,
              {sx, c.mgr.CreateBVConst(32, 5), c.mgr.CreateBVConst(32, 3)});
  // Inside the original.
  c.checkTerm(BVEXTRACT, 2,
              {sx, c.mgr.CreateBVConst(32, 1), c.mgr.CreateBVConst(32, 0)});
  EXPECT_EQ(c.nf->CreateTerm(BVEXTRACT, 2, sx, c.mgr.CreateBVConst(32, 1),
                             c.mgr.CreateBVConst(32, 0)),
            c.nf->CreateTerm(BVEXTRACT, 2, x, c.mgr.CreateBVConst(32, 1),
                             c.mgr.CreateBVConst(32, 0)));
  // Straddling.
  c.checkTerm(BVEXTRACT, 3,
              {sx, c.mgr.CreateBVConst(32, 3), c.mgr.CreateBVConst(32, 1)},
              false);
}

/* repeating a 1-bit term, directly or against its own sign-extension,
   is a sign-extension */
TEST(SimplifyingNodeFactory_Exhaustive, concat_repeated_bit_to_sx)
{
  Context c;
  ASTNode t = c.bv(1);
  ASTNode sx = c.hf->CreateTerm(BVSX, 3, t, c.mgr.CreateBVConst(32, 3));

  c.checkTerm(BVCONCAT, 2, {t, t});
  EXPECT_EQ(c.nf->CreateTerm(BVCONCAT, 2, t, t),
            c.nf->CreateTerm(BVSX, 2, t, c.mgr.CreateBVConst(32, 2)));

  c.checkTerm(BVCONCAT, 4, {t, sx});
  c.checkTerm(BVCONCAT, 4, {sx, t});
  EXPECT_EQ(c.nf->CreateTerm(BVCONCAT, 4, t, sx),
            c.nf->CreateTerm(BVSX, 4, t, c.mgr.CreateBVConst(32, 4)));
  EXPECT_EQ(c.nf->CreateTerm(BVCONCAT, 4, sx, t),
            c.nf->CreateTerm(BVSX, 4, t, c.mgr.CreateBVConst(32, 4)));
}

/* x / x --> ite(x = 0, all-ones, 1) */
TEST(SimplifyingNodeFactory_Exhaustive, udiv_self)
{
  Context c;
  for (unsigned w : {1u, 3u})
  {
    ASTNode x = c.bv(w);
    c.checkTerm(BVDIV, w, {x, x});
  }
}

/* sdiv constant rules: by zero, of zero, and negative-constant
   normalisation on either side (the most negative constant excluded) */
TEST(SimplifyingNodeFactory_Exhaustive, sdiv_constant_rules)
{
  Context c;
  ASTNode x = c.bv(3);
  c.checkTerm(SBVDIV, 3, {x, c.konst(0, 3)});
  c.checkTerm(SBVDIV, 3, {c.konst(0, 3), x});
  c.checkTerm(SBVDIV, 3, {c.konst(6, 3), x}); // -2 / x
  c.checkTerm(SBVDIV, 3, {x, c.konst(6, 3)}); // x / -2
  c.checkTerm(SBVDIV, 3, {c.konst(4, 3), x}, false); // most negative
  c.checkTerm(SBVDIV, 3, {x, c.konst(4, 3)}, false);
}

/* srem negative-constant normalisation on either side */
TEST(SimplifyingNodeFactory_Exhaustive, srem_negative_constants)
{
  Context c;
  ASTNode x = c.bv(3);
  c.checkTerm(SBVREM, 3, {c.konst(6, 3), x}); // -2 rem x
  c.checkTerm(SBVREM, 3, {x, c.konst(6, 3)}); // x rem -2
  c.checkTerm(SBVREM, 3, {c.konst(4, 3), x}, false); // most negative
  c.checkTerm(SBVREM, 3, {x, c.konst(4, 3)}, false);
}

/* a literal and its negation one level down a same-kind child annihilate */
TEST(SimplifyingNodeFactory_Exhaustive, nested_complementary_literals)
{
  Context c;
  ASTNode p = c.boolean();
  ASTNode q = c.boolean();
  ASTNode r = c.boolean();
  ASTNode notP = c.hf->CreateNode(NOT, p);

  ASTNode innerAnd = c.hf->CreateNode(AND, q, notP);
  c.checkNode(AND, {p, innerAnd});
  EXPECT_EQ(c.nf->CreateNode(AND, p, innerAnd), c.mgr.ASTFalse);

  ASTNode innerOr = c.hf->CreateNode(OR, q, notP);
  c.checkNode(OR, {p, innerOr});
  EXPECT_EQ(c.nf->CreateNode(OR, p, innerOr), c.mgr.ASTTrue);

  // Complements split across two nested same-kind children.
  ASTNode andA = c.hf->CreateNode(AND, p, q);
  ASTNode andB = c.hf->CreateNode(AND, r, notP);
  c.checkNode(AND, {andA, andB});
  EXPECT_EQ(c.nf->CreateNode(AND, andA, andB), c.mgr.ASTFalse);

  // An AND nested inside an OR must NOT annihilate.
  c.checkNode(OR, {p, innerAnd}, false);
}

/* (x umod s) >u x --> false, so (x umod s) <=u x --> true. */
TEST(SimplifyingNodeFactory_Exhaustive, gt_urem_dividend)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode y = c.bv(w);
    ASTNode rem = c.hf->CreateTerm(BVMOD, w, x, y);
    c.checkNode(BVGT, {rem, x});
    c.checkNode(BVLE, {rem, x});
    ASTNode negRem =
        c.hf->CreateTerm(BVMOD, w, x, c.hf->CreateTerm(BVUMINUS, w, y));
    c.checkNode(BVLE, {negRem, x});
    // The divisor's remainder is NOT bounded by the divisor this way.
    c.checkNode(BVGT, {rem, y}, false);
  }
}

/* (x udiv ~x) >u x --> false. */
TEST(SimplifyingNodeFactory_Exhaustive, gt_udiv_by_not)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode div =
        c.hf->CreateTerm(BVDIV, w, x, c.hf->CreateTerm(BVNOT, w, x));
    c.checkNode(BVGT, {div, x});
  }
}

/* Shifts never exceed the complement of the shift amount:
   (t << s) >u ~s and (t >> s) >u ~s --> false, also with s = ~u. */
TEST(SimplifyingNodeFactory_Exhaustive, gt_shift_vs_not_amount)
{
  Context c;
  for (unsigned w : {2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode y = c.bv(w);
    ASTNode noty = c.hf->CreateTerm(BVNOT, w, y);
    for (Kind k : {BVLEFTSHIFT, BVRIGHTSHIFT})
    {
      c.checkNode(BVGT, {c.hf->CreateTerm(k, w, x, y), noty});
      c.checkNode(BVGT, {c.hf->CreateTerm(k, w, x, noty), y});
      // The shifted value is not bounded by an unrelated term.
      c.checkNode(BVGT, {c.hf->CreateTerm(k, w, x, y), x}, false);
    }
  }
}

/* x <=s (x umod ~x) --> true, both for the raw form and for the
   (ones umod ~x) shape the BVMOD rules normalise it to. */
TEST(SimplifyingNodeFactory_Exhaustive, sgt_urem_by_not)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode nt = c.hf->CreateTerm(BVNOT, w, x);
    c.checkNode(BVSLE, {x, c.hf->CreateTerm(BVMOD, w, x, nt)});
    c.checkNode(BVSLE, {x, c.nf->CreateTerm(BVMOD, w, x, nt)});
  }
}

/* x <=s (x srem ~x) --> true, raw form and the -(1 smod ~x) normal form. */
TEST(SimplifyingNodeFactory_Exhaustive, sgt_srem_by_not)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode nt = c.hf->CreateTerm(BVNOT, w, x);
    c.checkNode(BVSLE, {x, c.hf->CreateTerm(SBVREM, w, x, nt)});
    c.checkNode(BVSLE, {x, c.nf->CreateTerm(SBVREM, w, x, nt)});
  }
}

/* x = (~x << x) and x = (~x sdiv x) --> false, in both argument orders. */
TEST(SimplifyingNodeFactory_Exhaustive, eq_impossible_not_forms)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode nt = c.hf->CreateTerm(BVNOT, w, x);
    for (Kind k : {BVLEFTSHIFT, SBVDIV})
    {
      ASTNode t = c.hf->CreateTerm(k, w, nt, x);
      c.checkNode(EQ, {x, t});
      c.checkNode(EQ, {t, x});
    }
  }
}

/* (t >> s) --> 0 when t is structurally <=u s: an AND containing s, or
   s umod/lshr/ashr something. */
TEST(SimplifyingNodeFactory_Exhaustive, rightshift_dominated_numerator)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode y = c.bv(w);
    c.checkTerm(BVRIGHTSHIFT, w, {c.hf->CreateTerm(BVAND, w, x, y), x});
    c.checkTerm(BVRIGHTSHIFT, w, {c.hf->CreateTerm(BVMOD, w, x, y), x});
    c.checkTerm(BVRIGHTSHIFT, w, {c.hf->CreateTerm(BVRIGHTSHIFT, w, x, y), x});
    c.checkTerm(BVRIGHTSHIFT, w, {c.hf->CreateTerm(BVSRSHIFT, w, x, y), x});
    // Dominance runs the other way for the divisor: no rule.
    c.checkTerm(BVRIGHTSHIFT, w, {c.hf->CreateTerm(BVMOD, w, x, y), y}, false);
  }
}

/* (x >> (x | y)) --> 0. The OR arrives as ~(~x & ~y). */
TEST(SimplifyingNodeFactory_Exhaustive, rightshift_by_or_containing_numerator)
{
  Context c;
  for (unsigned w : {2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode y = c.bv(w);
    ASTNode amount = c.nf->CreateTerm(BVOR, w, x, y);
    c.checkTerm(BVRIGHTSHIFT, w, {x, amount});
    // An OR not containing the numerator must not fire.
    ASTNode z = c.bv(w);
    ASTNode other = c.nf->CreateTerm(BVOR, w, y, z);
    c.checkTerm(BVRIGHTSHIFT, w, {x, other}, false);
  }
}

/* ((x ashr x) << x) --> 0. The arithmetic shift arrives as the sign-spread
   sx(x[msb:msb]). */
TEST(SimplifyingNodeFactory_Exhaustive, leftshift_of_sign_spread)
{
  Context c;
  for (unsigned w : {2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode spread = c.nf->CreateTerm(BVSRSHIFT, w, x, x);
    c.checkTerm(BVLEFTSHIFT, w, {spread, x});
  }
}

/* x & (t << x) --> 0, in any operand order and with extra operands. */
TEST(SimplifyingNodeFactory_Exhaustive, and_with_shift_by_operand)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode y = c.bv(w);
    ASTNode shift = c.hf->CreateTerm(BVLEFTSHIFT, w, y, x);
    c.checkTerm(BVAND, w, {x, shift});
    c.checkTerm(BVAND, w, {shift, x});
    ASTNode z = c.bv(w);
    c.checkTerm(BVAND, w, {z, x, shift});
    // Shift by an amount that isn't an operand: no rule.
    c.checkTerm(BVAND, w, {z, shift}, false);
  }
}

/* a ^ (a ^ b) --> b, including through a negated nested xor. */
TEST(SimplifyingNodeFactory_Exhaustive, xor_nested_cancel)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode y = c.bv(w);
    ASTNode inner = c.hf->CreateTerm(BVXOR, w, x, y);
    EXPECT_EQ(c.nf->CreateTerm(BVXOR, w, x, inner), y);
    EXPECT_EQ(c.nf->CreateTerm(BVXOR, w, inner, x), y);
    c.checkTerm(BVXOR, w, {x, inner});
    ASTNode notInner = c.hf->CreateTerm(BVNOT, w, inner);
    c.checkTerm(BVXOR, w, {x, notInner});
  }
}

/* a + -(a + b) --> -b; b - (a + b) and a - (a - b) reach it through the
   plus/uminus rewrite of subtraction, and x - ~(-x) --> 1 falls out. */
TEST(SimplifyingNodeFactory_Exhaustive, plus_cancels_negated_sum)
{
  Context c;
  for (unsigned w : {1u, 2u, 4u})
  {
    ASTNode x = c.bv(w);
    ASTNode y = c.bv(w);
    ASTNode sum = c.hf->CreateTerm(BVPLUS, w, x, y);
    ASTNode negSum = c.hf->CreateTerm(BVUMINUS, w, sum);
    c.checkTerm(BVPLUS, w, {x, negSum});
    c.checkTerm(BVPLUS, w, {negSum, y});
    c.checkTerm(BVSUB, w, {x, sum});
    c.checkTerm(BVSUB, w, {x, c.hf->CreateTerm(BVSUB, w, x, y)});
    ASTNode notNeg =
        c.hf->CreateTerm(BVNOT, w, c.hf->CreateTerm(BVUMINUS, w, x));
    c.checkTerm(BVSUB, w, {x, notNeg});
    if (w >= 2)
    {
      // At width 1 BVPLUS routes through the xor handler and the chain to
      // these exact forms doesn't apply (the results are still equivalent).
      EXPECT_EQ(c.nf->CreateTerm(BVSUB, w, x,
                                 c.nf->CreateTerm(BVSUB, w, x, y)),
                y);
      EXPECT_EQ(c.nf->CreateTerm(BVSUB, w, x, notNeg), c.konst(1, w));
    }
  }
}

/* a + (-b) * (a sdiv b) --> a srem b, and the unsigned pair, for a symbolic
   divisor and for every constant one. */
TEST(SimplifyingNodeFactory_Exhaustive, plus_of_division_product)
{
  const unsigned w = 4;
  const struct
  {
    Kind div;
    Kind rem;
  } pairs[] = {{SBVDIV, SBVREM}, {BVDIV, BVMOD}};

  for (const auto& p : pairs)
  {
    {
      Context c;
      ASTNode a = c.bv(w);
      ASTNode b = c.bv(w);
      ASTNode quot = c.hf->CreateTerm(p.div, w, a, b);
      ASTNode negB = c.hf->CreateTerm(BVUMINUS, w, b);
      // The multiplier's operands, and the sum's, in both orders.
      for (const ASTVec& mulArgs :
           {ASTVec{negB, quot}, ASTVec{quot, negB}})
      {
        ASTNode mult = c.hf->CreateTerm(BVMULT, w, mulArgs);
        EXPECT_EQ(c.nf->CreateTerm(BVPLUS, w, a, mult),
                  c.nf->CreateTerm(p.rem, w, a, b));
        c.checkTerm(BVPLUS, w, {a, mult});
        c.checkTerm(BVPLUS, w, {mult, a});
      }
    }

    for (unsigned bv = 0; bv < (1u << w); bv++)
    {
      Context c;
      ASTNode a = c.bv(w);
      ASTNode b = c.konst(bv, w);
      ASTNode negB = c.konst(((1u << w) - bv) & ((1u << w) - 1), w);
      ASTNode quot = c.hf->CreateTerm(p.div, w, a, b);
      ASTNode mult = c.hf->CreateTerm(BVMULT, w, negB, quot);
      EXPECT_EQ(c.nf->CreateTerm(BVPLUS, w, a, mult),
                c.nf->CreateTerm(p.rem, w, a, b));
      c.checkTerm(BVPLUS, w, {a, mult});
    }
  }
}

/* The same sum written as a subtraction: a - b * (a sdiv b), which reaches
   the rule as a plus of a negated product. */
TEST(SimplifyingNodeFactory_Exhaustive, subtract_division_product)
{
  const unsigned w = 4;
  Context c;
  ASTNode a = c.bv(w);
  ASTNode b = c.bv(w);

  for (const auto& p : {std::make_pair(SBVDIV, SBVREM),
                        std::make_pair(BVDIV, BVMOD)})
  {
    ASTNode quot = c.hf->CreateTerm(p.first, w, a, b);
    for (const ASTVec& mulArgs : {ASTVec{b, quot}, ASTVec{quot, b}})
    {
      ASTNode mult = c.hf->CreateTerm(BVMULT, w, mulArgs);
      EXPECT_EQ(c.nf->CreateTerm(BVSUB, w, a, mult),
                c.nf->CreateTerm(p.second, w, a, b));
      c.checkTerm(BVSUB, w, {a, mult});
      c.checkTerm(BVPLUS, w, {a, c.hf->CreateTerm(BVUMINUS, w, mult)});
    }
  }
}

/* The pair is found wherever it sits in a wider sum. */
TEST(SimplifyingNodeFactory_Exhaustive, plus_of_division_product_nary)
{
  const unsigned w = 4;
  Context c;
  ASTNode a = c.bv(w);
  ASTNode b = c.bv(w);
  ASTNode other = c.bv(w);
  ASTNode quot = c.hf->CreateTerm(SBVDIV, w, a, b);
  ASTNode mult =
      c.hf->CreateTerm(BVMULT, w, c.hf->CreateTerm(BVUMINUS, w, b), quot);

  ASTNode expected =
      c.nf->CreateTerm(BVPLUS, w, c.nf->CreateTerm(SBVREM, w, a, b), other);
  EXPECT_EQ(c.nf->CreateTerm(BVPLUS, w, {a, mult, other}), expected);
  EXPECT_EQ(c.nf->CreateTerm(BVPLUS, w, {other, mult, a}), expected);
  c.checkTerm(BVPLUS, w, {a, mult, other});
  c.checkTerm(BVPLUS, w, {mult, other, a});
}

/* Near misses: the multiplier is not the negated divisor, the dividend is not
   the other operand, or the quotient is signed where the sum is not. */
TEST(SimplifyingNodeFactory_Exhaustive, plus_of_division_product_near_misses)
{
  const unsigned w = 4;
  Context c;
  ASTNode a = c.bv(w);
  ASTNode b = c.bv(w);
  ASTNode d = c.bv(w);
  ASTNode quot = c.hf->CreateTerm(SBVDIV, w, a, b);
  ASTNode negB = c.hf->CreateTerm(BVUMINUS, w, b);
  ASTNode negD = c.hf->CreateTerm(BVUMINUS, w, d);

  // Multiplied by the divisor rather than its negation.
  c.checkTerm(BVPLUS, w, {a, c.hf->CreateTerm(BVMULT, w, b, quot)}, false);
  // Multiplied by an unrelated negated term.
  c.checkTerm(BVPLUS, w, {a, c.hf->CreateTerm(BVMULT, w, negD, quot)}, false);
  // Added to something that is not the dividend.
  c.checkTerm(BVPLUS, w, {d, c.hf->CreateTerm(BVMULT, w, negB, quot)}, false);
  // Subtracted product, but of the negated divisor.
  c.checkTerm(BVSUB, w, {a, c.hf->CreateTerm(BVMULT, w, negB, quot)}, false);
}

/* (x srem y) / y, (x smod y) / y and (x umod y) / y are zero away from a zero
   divisor, where they take the total quotient of the dividend. */
TEST(SimplifyingNodeFactory_Exhaustive, division_of_remainder)
{
  const unsigned w = 4;
  const struct
  {
    Kind rem;
    Kind div;
  } pairs[] = {{SBVREM, SBVDIV}, {SBVMOD, SBVDIV}, {BVMOD, BVDIV}};

  for (const auto& p : pairs)
  {
    {
      Context c;
      ASTNode a = c.bv(w);
      ASTNode b = c.bv(w);
      ASTNode rem = c.hf->CreateTerm(p.rem, w, a, b);
      c.checkTerm(p.div, w, {rem, b});
    }

    for (unsigned bv = 0; bv < (1u << w); bv++)
    {
      Context c;
      ASTNode a = c.bv(w);
      ASTNode b = c.konst(bv, w);
      ASTNode rem = c.hf->CreateTerm(p.rem, w, a, b);
      c.checkTerm(p.div, w, {rem, b});
      if (bv != 0)
      {
        EXPECT_EQ(c.nf->CreateTerm(p.div, w, rem, b), c.konst(0, w));
      }
    }
  }
}

/* Near misses for the same: a remainder taken against a different divisor,
   and a remainder of the wrong signedness for the division. */
TEST(SimplifyingNodeFactory_Exhaustive, division_of_remainder_near_misses)
{
  const unsigned w = 4;
  Context c;
  ASTNode a = c.bv(w);
  ASTNode b = c.bv(w);
  ASTNode d = c.bv(w);

  c.checkTerm(SBVDIV, w, {c.hf->CreateTerm(SBVREM, w, a, d), b}, false);
  c.checkTerm(BVDIV, w, {c.hf->CreateTerm(BVMOD, w, a, d), b}, false);
  // An unsigned remainder can exceed a signed divisor's magnitude, and a
  // signed one can exceed an unsigned divisor's, so neither cross pair folds.
  c.checkTerm(SBVDIV, w, {c.hf->CreateTerm(BVMOD, w, a, b), b}, false);
  c.checkTerm(BVDIV, w, {c.hf->CreateTerm(SBVREM, w, a, b), b}, false);
}

/* An extract narrows through a whole stack of operators at once, not just the
   one immediately beneath it: every slice of a term built from concats, sign
   extensions, complements and nested extracts must mean what it meant before
   the pushes, at every assignment and for every slice. */
TEST(SimplifyingNodeFactory_Exhaustive, extract_narrows_through_a_stack)
{
  Context c;
  ASTNode x = c.bv(2);
  ASTNode y = c.bv(2);

  // (~(sx(x, 4) ++ y))[hi:lo], and the same under an outer extract, so the
  // walk crosses concat, bvnot, bvsx and extract in one go.
  ASTNode sx = c.hf->CreateTerm(BVSX, 4, x, c.konst(4, 32));
  ASTNode cat = c.hf->CreateTerm(BVCONCAT, 6, sx, y);
  ASTNode nt = c.hf->CreateTerm(BVNOT, 6, cat);
  ASTNode neg = c.hf->CreateTerm(BVUMINUS, 6, nt);

  for (const ASTNode& base : {cat, nt, neg})
  {
    for (unsigned hi = 0; hi < 6; hi++)
    {
      for (unsigned lo = 0; lo <= hi; lo++)
      {
        // Every slice, whichever side of the concat it falls on and whether
        // or not it straddles the split.
        c.checkTerm(BVEXTRACT, hi - lo + 1,
                    {base, c.konst(hi, 32), c.konst(lo, 32)}, false);

        // The same slice reached through an outer extract of an inner one.
        ASTNode inner = c.hf->CreateTerm(BVEXTRACT, hi + 1, base,
                                         c.konst(hi, 32), c.konst(0, 32));
        c.checkTerm(BVEXTRACT, hi - lo + 1,
                    {inner, c.konst(hi - lo, 32), c.konst(0, 32)}, false);
      }
    }
  }
}

/* The n-ary bvmul rules (multRules). */

/* a zero operand anywhere zeroes the whole product */
TEST(SimplifyingNodeFactory_Exhaustive, nary_mult_zero_child)
{
  Context c;
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTVec ch = {x, c.konst(0, 3), y};
  EXPECT_EQ(c.nf->CreateTerm(BVMULT, 3, ch), c.konst(0, 3));
  c.checkTerm(BVMULT, 3, ch);
}

/* a one operand drops out */
TEST(SimplifyingNodeFactory_Exhaustive, nary_mult_one_dropped)
{
  Context c;
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTVec ch = {x, c.konst(1, 3), y};
  ASTNode r = c.nf->CreateTerm(BVMULT, 3, ch);
  EXPECT_EQ(BVMULT, r.GetKind());
  EXPECT_EQ(2u, r.Degree());
  c.checkTerm(BVMULT, 3, ch);
}

/* constants fold together wherever they sit */
TEST(SimplifyingNodeFactory_Exhaustive, nary_mult_constants_fold)
{
  Context c;
  ASTNode x = c.bv(3);
  ASTVec ch = {c.konst(2, 3), x, c.konst(3, 3)};
  ASTNode r = c.nf->CreateTerm(BVMULT, 3, ch);
  EXPECT_EQ(BVMULT, r.GetKind());
  EXPECT_EQ(2u, r.Degree());
  EXPECT_TRUE(r[0] == c.konst(6, 3) || r[1] == c.konst(6, 3)) << r;
  c.checkTerm(BVMULT, 3, ch);
}

/* negations lift out of the product; an even number cancels entirely */
TEST(SimplifyingNodeFactory_Exhaustive, nary_mult_negation_parity_even)
{
  Context c;
  ASTNode x = c.bv(2), y = c.bv(2), z = c.bv(2);
  ASTNode nx = c.hf->CreateTerm(BVUMINUS, 2, x);
  ASTNode ny = c.hf->CreateTerm(BVUMINUS, 2, y);
  ASTVec ch = {nx, ny, z};
  ASTNode r = c.nf->CreateTerm(BVMULT, 2, ch);
  EXPECT_EQ(BVMULT, r.GetKind());
  EXPECT_EQ(3u, r.Degree());
  c.checkTerm(BVMULT, 2, ch);
}

/* an odd number of negations leaves one on top */
TEST(SimplifyingNodeFactory_Exhaustive, nary_mult_negation_parity_odd)
{
  Context c;
  ASTNode x = c.bv(2), y = c.bv(2), z = c.bv(2);
  ASTNode nx = c.hf->CreateTerm(BVUMINUS, 2, x);
  ASTVec ch = {nx, y, z};
  ASTNode r = c.nf->CreateTerm(BVMULT, 2, ch);
  EXPECT_EQ(BVUMINUS, r.GetKind());
  c.checkTerm(BVMULT, 2, ch);
}

/* a max constant is -1: it becomes the sign of the product */
TEST(SimplifyingNodeFactory_Exhaustive, nary_mult_max_becomes_negation)
{
  Context c;
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTVec ch = {c.konst(7, 3), x, y};
  ASTNode r = c.nf->CreateTerm(BVMULT, 3, ch);
  EXPECT_EQ(BVUMINUS, r.GetKind());
  c.checkTerm(BVMULT, 3, ch);
}

/* constants, ones and negations together */
TEST(SimplifyingNodeFactory_Exhaustive, nary_mult_mixed)
{
  Context c;
  ASTNode x = c.bv(3), y = c.bv(3);
  ASTNode nx = c.hf->CreateTerm(BVUMINUS, 3, x);
  ASTVec ch = {nx, c.konst(2, 3), y, c.konst(3, 3)};
  ASTNode r = c.nf->CreateTerm(BVMULT, 3, ch);
  EXPECT_EQ(BVUMINUS, r.GetKind());
  EXPECT_EQ(BVMULT, r[0].GetKind());
  EXPECT_EQ(3u, r[0].Degree());
  c.checkTerm(BVMULT, 3, ch);
}

/* no rule applies: the product must SURVIVE as one n-ary node -- the
   defining property of this representation change */
TEST(SimplifyingNodeFactory_Exhaustive, nary_mult_arity_survives)
{
  Context c;
  ASTNode x = c.bv(3), y = c.bv(3), z = c.bv(3);
  ASTVec ch = {x, y, z};
  ASTNode r = c.nf->CreateTerm(BVMULT, 3, ch);
  EXPECT_EQ(BVMULT, r.GetKind());
  EXPECT_EQ(3u, r.Degree());
  c.checkTerm(BVMULT, 3, ch, false);
}

} // namespace

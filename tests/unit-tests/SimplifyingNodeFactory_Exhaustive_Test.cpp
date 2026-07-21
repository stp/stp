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
      EXPECT_NE(plain, simplified);
    checkEquivalent(plain, simplified);
  }

  void checkNode(Kind k, const ASTVec& children, bool expectFired = true)
  {
    ASTNode plain = hf->CreateNode(k, children);
    ASTNode simplified = nf->CreateNode(k, children);
    if (expectFired)
      EXPECT_NE(plain, simplified);
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

/* equality decided by differing leading constant bits */
TEST(SimplifyingNodeFactory_Exhaustive, eq_differing_leading_constants)
{
  Context c;
  ASTNode x = c.bv(3);
  ASTNode y = c.bv(3);
  ASTNode oneTop = c.hf->CreateTerm(BVCONCAT, 5, c.konst(2, 2), x); // 10 ++ x
  ASTNode zeroTop = c.hf->CreateTerm(BVCONCAT, 5, c.konst(1, 2), y); // 01 ++ y

  c.checkNode(EQ, {oneTop, zeroTop});
  EXPECT_EQ(c.nf->CreateNode(EQ, oneTop, zeroTop), c.mgr.ASTFalse);

  // Same leading constants: must not fold to a constant.
  ASTNode oneTop2 = c.hf->CreateTerm(BVCONCAT, 5, c.konst(2, 2), y);
  c.checkNode(EQ, {oneTop, oneTop2}, false);
}

/* unsigned comparisons decided by differing leading constant bits */
TEST(SimplifyingNodeFactory_Exhaustive, gt_differing_leading_constants)
{
  Context c;
  ASTNode x = c.bv(3);
  ASTNode y = c.bv(3);
  ASTNode hi = c.hf->CreateTerm(BVCONCAT, 5, c.konst(2, 2), x); // 10 ++ x
  ASTNode lo = c.hf->CreateTerm(BVCONCAT, 5, c.konst(1, 2), y); // 01 ++ y

  c.checkNode(BVGT, {hi, lo});
  c.checkNode(BVGT, {lo, hi});
  c.checkNode(BVLT, {hi, lo});
  c.checkNode(BVGE, {lo, hi});
  EXPECT_EQ(c.nf->CreateNode(BVGT, hi, lo), c.mgr.ASTTrue);
  EXPECT_EQ(c.nf->CreateNode(BVGT, lo, hi), c.mgr.ASTFalse);
}

/* signed comparisons decided by leading constant bits, honouring the sign */
TEST(SimplifyingNodeFactory_Exhaustive, sgt_differing_leading_constants)
{
  Context c;
  ASTNode x = c.bv(3);
  ASTNode y = c.bv(3);
  ASTNode neg = c.hf->CreateTerm(BVCONCAT, 5, c.konst(3, 2), x); // 11 ++ x
  ASTNode pos = c.hf->CreateTerm(BVCONCAT, 5, c.konst(1, 2), y); // 01 ++ y
  ASTNode neg2 = c.hf->CreateTerm(BVCONCAT, 5, c.konst(2, 2), y); // 10 ++ y

  // Differing sign bits: the positive side is bigger.
  c.checkNode(BVSGT, {pos, neg});
  c.checkNode(BVSGT, {neg, pos});
  EXPECT_EQ(c.nf->CreateNode(BVSGT, pos, neg), c.mgr.ASTTrue);
  EXPECT_EQ(c.nf->CreateNode(BVSGT, neg, pos), c.mgr.ASTFalse);

  // Same sign bit: the unsigned order of the leading bits decides.
  c.checkNode(BVSGT, {neg, neg2});
  c.checkNode(BVSLT, {neg2, neg});
  EXPECT_EQ(c.nf->CreateNode(BVSGT, neg, neg2), c.mgr.ASTTrue);
}

} // namespace

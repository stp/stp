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
 * Exhaustive soundness test for the div/mod-by-power-of-two rewrite rules in
 * the SimplifyingNodeFactory:
 *
 *   (bvudiv x 2^k) --> 0^k       ++ x[w-1:k]     (k in [1, w-1])
 *   (bvurem x 2^k) --> 0^(w-k)   ++ x[k-1:0]     (k in [1, w-1])
 *   (bvsmod x 2^k) --> 0^(w-k)   ++ x[k-1:0]     (k in [1, w-2], 2^k positive)
 *
 * SBVDIV (bvsdiv) and SBVREM (bvsrem) by 2^k are deliberately NOT rewritten to
 * an extract/concat, because signed division rounds toward zero and the signed
 * remainder follows the dividend's sign -- both need a sign correction. This
 * test also asserts those two do NOT misfire.
 *
 * For every width w in 1..8, every k with 2^k < 2^w, and EVERY dividend value
 * x in [0, 2^w) we:
 *   1. brute-force the expected result,
 *   2. build the term with a CONSTANT dividend and assert it constant-folds to
 *      the expected value (validates consteval and our expectation), and
 *   3. build it with a SYMBOLIC dividend, assert the rewrite fired to the
 *      extract/concat form where the rule applies, then substitute every
 *      concrete x and evaluate to prove semantic equivalence.
 */

#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Parser/parser.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/cpp_interface.h"
#include <gtest/gtest.h>
#include <string>

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

  ASTNode konst(unsigned value, unsigned width)
  {
    return mgr.CreateBVConst(width, value);
  }

  // Evaluate a node with the given symbol assignment down to a constant.
  ASTNode eval(const ASTNode& n, ASTNodeMap assignment /*by value*/)
  {
    ASTNodeMap cache;
    ASTNode s = SubstitutionMap::replace(n, assignment, cache, &snf);
    if (s.isConstant())
      return s;
    return NonMemberBVConstEvaluator(&mgr, s);
  }
};

// Unsigned value of a width-w constant node.
unsigned toUnsigned(const ASTNode& n)
{
  unsigned v = 0;
  for (unsigned i = 0; i < n.GetValueWidth(); i++)
    if (CONSTANTBV::BitVector_bit_test(n.GetBVConst(), i))
      v |= (1u << i);
  return v;
}

// The primary exhaustive soundness check.
TEST(DivModPow2, exhaustive)
{
  Context c;

  for (unsigned w = 1; w <= 8; w++)
  {
    const unsigned domain = 1u << w;

    for (unsigned k = 0; k * 1u < w; k++) // 2^k must fit: k in [0, w-1]
    {
      const unsigned m = 1u << k; // the divisor, a power of two
      const ASTNode div = c.konst(m, w);

      // Whether each rewrite rule is expected to fire (produce a concat).
      const bool udivFires = (k >= 1);          // BVDIV: k in [1, w-1]
      const bool uremFires = (k >= 1);          // BVMOD: k in [1, w-1]
      const bool smodFires = (k >= 1 && k + 1 < w); // SBVMOD: k in [1, w-2]
      // 2^k is positive iff its top (sign) bit is clear, i.e. k != w-1. Only
      // then does bvsmod equal the low k bits; when 2^k is negative (k==w-1)
      // the low-bits identity does not hold, so we skip the SBVMOD check.
      const bool smodPositive = (k + 1 < w); // k <= w-2

      // --- Symbolic dividend: assert the rewrite form, then prove semantics.
      ASTNode x = c.bv(w);
      ASTNode udiv = c.nf->CreateTerm(BVDIV, w, x, div);
      ASTNode urem = c.nf->CreateTerm(BVMOD, w, x, div);
      ASTNode smod = c.nf->CreateTerm(SBVMOD, w, x, div);
      ASTNode sdiv = c.nf->CreateTerm(SBVDIV, w, x, div);
      ASTNode srem = c.nf->CreateTerm(SBVREM, w, x, div);

      if (udivFires)
        EXPECT_EQ(udiv.GetKind(), BVCONCAT)
            << "BVDIV by 2^" << k << " width " << w << " did not rewrite";
      if (uremFires)
        EXPECT_EQ(urem.GetKind(), BVCONCAT)
            << "BVMOD by 2^" << k << " width " << w << " did not rewrite";
      if (smodFires)
        EXPECT_EQ(smod.GetKind(), BVCONCAT)
            << "SBVMOD by 2^" << k << " width " << w << " did not rewrite";

      // SBVDIV / SBVREM must NOT be rewritten to an extract/concat form. For
      // a divisor that is neither 1 nor all-ones (true for k in [1, w-1] with
      // w > 1) no signed rule applies, so the node is left untouched.
      if (k >= 1)
      {
        EXPECT_NE(sdiv.GetKind(), BVCONCAT)
            << "SBVDIV by 2^" << k << " width " << w << " misfired to concat";
        EXPECT_NE(sdiv.GetKind(), BVEXTRACT);
        EXPECT_EQ(sdiv.GetKind(), SBVDIV)
            << "SBVDIV by 2^" << k << " width " << w << " changed unexpectedly";
        EXPECT_NE(srem.GetKind(), BVCONCAT)
            << "SBVREM by 2^" << k << " width " << w << " misfired to concat";
        EXPECT_NE(srem.GetKind(), BVEXTRACT);
        EXPECT_EQ(srem.GetKind(), SBVREM)
            << "SBVREM by 2^" << k << " width " << w << " changed unexpectedly";
      }

      for (unsigned xv = 0; xv < domain; xv++)
      {
        const unsigned expUdiv = xv >> k;              // bvudiv
        const unsigned expUrem = xv & (m - 1);         // bvurem: low k bits
        const unsigned expSmod = xv & (m - 1);         // bvsmod by +2^k

        // Symbolic rewrite, evaluated at x = xv.
        ASTNodeMap a;
        a.insert({x, c.konst(xv, w)});
        EXPECT_EQ(toUnsigned(c.eval(udiv, a)), expUdiv)
            << "BVDIV rewrite wrong: w=" << w << " k=" << k << " x=" << xv;
        ASTNodeMap a2;
        a2.insert({x, c.konst(xv, w)});
        EXPECT_EQ(toUnsigned(c.eval(urem, a2)), expUrem)
            << "BVMOD rewrite wrong: w=" << w << " k=" << k << " x=" << xv;
        if (smodFires)
        {
          ASTNodeMap a3;
          a3.insert({x, c.konst(xv, w)});
          EXPECT_EQ(toUnsigned(c.eval(smod, a3)), expSmod)
              << "SBVMOD rewrite wrong: w=" << w << " k=" << k << " x=" << xv;
        }

        // Constant dividend: must constant-fold to the expected value.
        ASTNode cUdiv = c.nf->CreateTerm(BVDIV, w, c.konst(xv, w), div);
        ASTNode cUrem = c.nf->CreateTerm(BVMOD, w, c.konst(xv, w), div);
        ASSERT_TRUE(cUdiv.isConstant());
        ASSERT_TRUE(cUrem.isConstant());
        EXPECT_EQ(toUnsigned(cUdiv), expUdiv)
            << "BVDIV const-fold wrong: w=" << w << " k=" << k << " x=" << xv;
        EXPECT_EQ(toUnsigned(cUrem), expUrem)
            << "BVMOD const-fold wrong: w=" << w << " k=" << k << " x=" << xv;
        if (smodPositive)
        {
          ASTNode cSmod = c.nf->CreateTerm(SBVMOD, w, c.konst(xv, w), div);
          ASSERT_TRUE(cSmod.isConstant());
          EXPECT_EQ(toUnsigned(cSmod), expSmod)
              << "SBVMOD const-fold wrong: w=" << w << " k=" << k
              << " x=" << xv;
        }
      }
    }
  }
}

} // namespace

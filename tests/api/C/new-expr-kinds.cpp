/***********
AUTHORS: Trevor Hansen

BEGIN DATE: July, 2026

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
 * Node kinds that STP has always parsed and bit-blasted but that had no
 * constructor in the C API: zero-extend, the six overflow predicates, the
 * bitwise nand/nor/xnor and the boolean nand/nor.
 *
 * Each operator is checked by asking STP to prove it equivalent, for every
 * input, to a reference expression built only from constructors that predate
 * it. A query over free variables covers the whole input space at that width
 * rather than a sample of it, and goes through bit-blasting rather than being
 * folded away by the simplifier.
 */

#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <string>

namespace
{

// Return codes of vc_query().
const int QUERY_VALID = 1;

// Width used for the equivalence proofs. Small enough that the doubled-width
// multiplies in the reference for the *mulo predicates stay quick, large
// enough to exercise carries.
const int W = 6;

class Fixture
{
public:
  Fixture() : vc(vc_createValidityChecker()) {}
  ~Fixture() { vc_Destroy(vc); }

  VC vc;

  Expr bv(const char* name, int width = W)
  {
    return vc_varExpr(vc, name, vc_bvType(vc, width));
  }

  Expr boolean(const char* name) { return vc_varExpr(vc, name, vc_boolType(vc)); }

  Expr zeroes(int width) { return vc_bvConstExprFromInt(vc, width, 0); }

  // Zero-extend 'e' to 'width' without using vc_bvZeroExtend, which is one of
  // the constructors under test.
  Expr zeroExtendByConcat(Expr e, int width)
  {
    const int have = vc_getBVLength(vc, e);
    EXPECT_LT(have, width);
    return vc_bvConcatExpr(vc, zeroes(width - have), e);
  }

  // The two's-complement constant for a negative value at the given width.
  Expr negativeConst(int width, unsigned long long magnitude)
  {
    return vc_bvConstExprFromLL(vc, width, (1ULL << width) - magnitude);
  }

  // Assert that the two boolean expressions agree on every input.
  void expectEquivalent(Expr actual, Expr reference, const std::string& what)
  {
    EXPECT_EQ(vc_query(vc, vc_iffExpr(vc, actual, reference)), QUERY_VALID)
        << what << " does not match its reference expression";
  }

  // Assert that the two terms are equal on every input.
  void expectEqual(Expr actual, Expr reference, const std::string& what)
  {
    EXPECT_EQ(vc_query(vc, vc_eqExpr(vc, actual, reference)), QUERY_VALID)
        << what << " does not match its reference expression";
  }
};

/*
 * "The exact result carried in 'wide' falls outside the signed 'w'-bit range",
 * i.e. the standard signed-overflow condition. 'wideWidth' is the width of
 * 'wide' itself, which is wider than 'w' so that the exact result fits.
 */
Expr outsideSignedRange(Fixture& f, Expr wide, int wideWidth, int w)
{
  Expr max = vc_bvConstExprFromLL(f.vc, wideWidth, (1ULL << (w - 1)) - 1);
  Expr min = f.negativeConst(wideWidth, 1ULL << (w - 1));

  return vc_orExpr(f.vc, vc_sbvLtExpr(f.vc, wide, min),
                   vc_sbvGtExpr(f.vc, wide, max));
}

// "The unsigned value of 'wide' does not fit in 'w' bits."
Expr aboveUnsignedRange(Fixture& f, Expr wide, int wideWidth, int w)
{
  return vc_bvGeExpr(f.vc, wide,
                     vc_bvConstExprFromLL(f.vc, wideWidth, 1ULL << w));
}

/*
 * Widths the overflow predicates are proved over. One is the interesting case:
 * the bit-blasted predicates index the top bit as l[w-1], so it is where an
 * off-by-one in that indexing would show up. At width one the only signed
 * values are 0 and -1.
 */
const int OVERFLOW_WIDTHS[] = {1, 2, W};

} // namespace

/////////////////////////////////////////////////////////////////////////////
/// ZERO EXTEND
/////////////////////////////////////////////////////////////////////////////

// Widening pads with zeroes, which is exactly a concat with a zero constant.
TEST(new_expr_kinds, zero_extend_widens_with_zeroes)
{
  Fixture f;
  Expr a = f.bv("a");

  for (int to = W + 1; to <= 2 * W; to++)
  {
    Expr extended = vc_bvZeroExtend(f.vc, a, to);
    ASSERT_EQ(vc_getBVLength(f.vc, extended), to);

    f.expectEqual(extended, f.zeroExtendByConcat(a, to),
                  "vc_bvZeroExtend to width " + std::to_string(to));
  }
}

// Extending to the width it already has is the identity.
TEST(new_expr_kinds, zero_extend_to_same_width_is_identity)
{
  Fixture f;
  Expr a = f.bv("a");

  Expr same = vc_bvZeroExtend(f.vc, a, W);
  ASSERT_EQ(vc_getBVLength(f.vc, same), W);
  f.expectEqual(same, a, "vc_bvZeroExtend to the same width");
}

/*
 * Asking for fewer bits truncates rather than failing, which is what
 * vc_bvSignExtend already does and so is what a caller reaching for the
 * matching function will expect.
 */
TEST(new_expr_kinds, zero_extend_to_narrower_width_truncates)
{
  Fixture f;
  Expr a = f.bv("a");

  Expr narrowed = vc_bvZeroExtend(f.vc, a, W - 2);
  ASSERT_EQ(vc_getBVLength(f.vc, narrowed), W - 2);

  f.expectEqual(narrowed, vc_bvExtract(f.vc, a, W - 3, 0),
                "vc_bvZeroExtend to a narrower width");
}

// Zero-extending differs from sign-extending exactly on negative inputs.
TEST(new_expr_kinds, zero_extend_differs_from_sign_extend_when_negative)
{
  Fixture f;
  Expr a = f.bv("a");
  const int wide = W + 2;

  Expr agree = vc_eqExpr(f.vc, vc_bvZeroExtend(f.vc, a, wide),
                         vc_bvSignExtend(f.vc, a, wide));

  // They agree iff the top bit of 'a' is clear.
  EXPECT_EQ(vc_query(f.vc, vc_iffExpr(f.vc, agree,
                                      vc_bvBoolExtract_Zero(f.vc, a, W - 1))),
            QUERY_VALID);
}

/////////////////////////////////////////////////////////////////////////////
/// OVERFLOW PREDICATES
/////////////////////////////////////////////////////////////////////////////

// Unsigned addition overflows iff the exact sum needs more than w bits.
TEST(new_expr_kinds, unsigned_add_overflow)
{
  for (const int w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    Expr a = f.bv("a", w);
    Expr b = f.bv("b", w);

    Expr exact = vc_bvPlusExpr(f.vc, w + 1, f.zeroExtendByConcat(a, w + 1),
                               f.zeroExtendByConcat(b, w + 1));

    f.expectEquivalent(vc_bvUnsignedAddOverflowExpr(f.vc, a, b),
                       aboveUnsignedRange(f, exact, w + 1, w),
                       "vc_bvUnsignedAddOverflowExpr");
  }
}

// Signed addition overflows iff the exact sum leaves the signed w-bit range.
TEST(new_expr_kinds, signed_add_overflow)
{
  for (const int w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    Expr a = f.bv("a", w);
    Expr b = f.bv("b", w);

    Expr exact = vc_bvPlusExpr(f.vc, w + 1, vc_bvSignExtend(f.vc, a, w + 1),
                               vc_bvSignExtend(f.vc, b, w + 1));

    f.expectEquivalent(vc_bvSignedAddOverflowExpr(f.vc, a, b),
                       outsideSignedRange(f, exact, w + 1, w),
                       "vc_bvSignedAddOverflowExpr");
  }
}

// Unsigned subtraction overflows (borrows) iff the left operand is smaller.
TEST(new_expr_kinds, unsigned_sub_overflow)
{
  for (const int w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    Expr a = f.bv("a", w);
    Expr b = f.bv("b", w);

    f.expectEquivalent(vc_bvUnsignedSubOverflowExpr(f.vc, a, b),
                       vc_bvLtExpr(f.vc, a, b),
                       "vc_bvUnsignedSubOverflowExpr");
  }
}

// Signed subtraction overflows iff the exact difference leaves the range.
TEST(new_expr_kinds, signed_sub_overflow)
{
  for (const int w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    Expr a = f.bv("a", w);
    Expr b = f.bv("b", w);

    Expr exact = vc_bvMinusExpr(f.vc, w + 1, vc_bvSignExtend(f.vc, a, w + 1),
                                vc_bvSignExtend(f.vc, b, w + 1));

    f.expectEquivalent(vc_bvSignedSubOverflowExpr(f.vc, a, b),
                       outsideSignedRange(f, exact, w + 1, w),
                       "vc_bvSignedSubOverflowExpr");
  }
}

// Unsigned multiplication overflows iff the exact 2w-bit product needs
// more than w bits.
TEST(new_expr_kinds, unsigned_mul_overflow)
{
  for (const int w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    Expr a = f.bv("a", w);
    Expr b = f.bv("b", w);

    Expr exact = vc_bvMultExpr(f.vc, 2 * w, f.zeroExtendByConcat(a, 2 * w),
                               f.zeroExtendByConcat(b, 2 * w));

    f.expectEquivalent(vc_bvUnsignedMulOverflowExpr(f.vc, a, b),
                       aboveUnsignedRange(f, exact, 2 * w, w),
                       "vc_bvUnsignedMulOverflowExpr");
  }
}

// Signed multiplication overflows iff the exact product leaves the range.
TEST(new_expr_kinds, signed_mul_overflow)
{
  for (const int w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    Expr a = f.bv("a", w);
    Expr b = f.bv("b", w);

    Expr exact = vc_bvMultExpr(f.vc, 2 * w, vc_bvSignExtend(f.vc, a, 2 * w),
                               vc_bvSignExtend(f.vc, b, 2 * w));

    f.expectEquivalent(vc_bvSignedMulOverflowExpr(f.vc, a, b),
                       outsideSignedRange(f, exact, 2 * w, w),
                       "vc_bvSignedMulOverflowExpr");
  }
}

/*
 * The signed and unsigned predicates are genuinely different: multiplying
 * -1 by -1 overflows unsigned (the operands read as large positives) but not
 * signed. A predicate wired to the wrong kind would not survive this.
 */
TEST(new_expr_kinds, signed_and_unsigned_mul_overflow_differ)
{
  Fixture f;
  Expr minusOne = f.negativeConst(W, 1);

  EXPECT_EQ(vc_query(f.vc, vc_bvUnsignedMulOverflowExpr(f.vc, minusOne, minusOne)),
            QUERY_VALID);
  EXPECT_EQ(vc_query(f.vc, vc_notExpr(f.vc, vc_bvSignedMulOverflowExpr(
                                               f.vc, minusOne, minusOne))),
            QUERY_VALID);
}

/////////////////////////////////////////////////////////////////////////////
/// BITWISE NAND / NOR / XNOR
/////////////////////////////////////////////////////////////////////////////

TEST(new_expr_kinds, bitwise_nand)
{
  Fixture f;
  Expr a = f.bv("a");
  Expr b = f.bv("b");

  f.expectEqual(vc_bvNandExpr(f.vc, a, b),
                vc_bvNotExpr(f.vc, vc_bvAndExpr(f.vc, a, b)),
                "vc_bvNandExpr");
}

TEST(new_expr_kinds, bitwise_nor)
{
  Fixture f;
  Expr a = f.bv("a");
  Expr b = f.bv("b");

  f.expectEqual(vc_bvNorExpr(f.vc, a, b),
                vc_bvNotExpr(f.vc, vc_bvOrExpr(f.vc, a, b)), "vc_bvNorExpr");
}

TEST(new_expr_kinds, bitwise_xnor)
{
  Fixture f;
  Expr a = f.bv("a");
  Expr b = f.bv("b");

  f.expectEqual(vc_bvXnorExpr(f.vc, a, b),
                vc_bvNotExpr(f.vc, vc_bvXorExpr(f.vc, a, b)), "vc_bvXnorExpr");
}

// The bitwise results keep the operands' width.
TEST(new_expr_kinds, bitwise_results_keep_their_width)
{
  Fixture f;
  Expr a = f.bv("a");
  Expr b = f.bv("b");

  EXPECT_EQ(vc_getBVLength(f.vc, vc_bvNandExpr(f.vc, a, b)), W);
  EXPECT_EQ(vc_getBVLength(f.vc, vc_bvNorExpr(f.vc, a, b)), W);
  EXPECT_EQ(vc_getBVLength(f.vc, vc_bvXnorExpr(f.vc, a, b)), W);
}

/////////////////////////////////////////////////////////////////////////////
/// BOOLEAN NAND / NOR
/////////////////////////////////////////////////////////////////////////////

TEST(new_expr_kinds, boolean_nand)
{
  Fixture f;
  Expr p = f.boolean("p");
  Expr q = f.boolean("q");

  f.expectEquivalent(vc_nandExpr(f.vc, p, q),
                     vc_notExpr(f.vc, vc_andExpr(f.vc, p, q)), "vc_nandExpr");
}

TEST(new_expr_kinds, boolean_nor)
{
  Fixture f;
  Expr p = f.boolean("p");
  Expr q = f.boolean("q");

  f.expectEquivalent(vc_norExpr(f.vc, p, q),
                     vc_notExpr(f.vc, vc_orExpr(f.vc, p, q)), "vc_norExpr");
}

/////////////////////////////////////////////////////////////////////////////
/// KIND REPORTING
/////////////////////////////////////////////////////////////////////////////

/*
 * The legacy Kind prefix is aligned with exprkind_t, while internal-only
 * kinds are explicitly mapped to their public representation by
 * getExprKind(). These kinds were listed in the public enum long before
 * anything could build them, so nothing had been holding that prefix
 * correspondence in place for them.
 *
 * Only the kinds that survive construction can be checked this way; see below
 * for the ones the node factory rewrites.
 */
TEST(new_expr_kinds, kinds_are_reported_correctly)
{
  Fixture f;
  Expr a = f.bv("a");
  Expr b = f.bv("b");

  EXPECT_EQ(getExprKind(vc_bvUnsignedAddOverflowExpr(f.vc, a, b)), BVUADDO);
  EXPECT_EQ(getExprKind(vc_bvSignedAddOverflowExpr(f.vc, a, b)), BVSADDO);
  EXPECT_EQ(getExprKind(vc_bvUnsignedSubOverflowExpr(f.vc, a, b)), BVUSUBO);
  EXPECT_EQ(getExprKind(vc_bvSignedSubOverflowExpr(f.vc, a, b)), BVSSUBO);
  EXPECT_EQ(getExprKind(vc_bvUnsignedMulOverflowExpr(f.vc, a, b)), BVUMULO);
  EXPECT_EQ(getExprKind(vc_bvSignedMulOverflowExpr(f.vc, a, b)), BVSMULO);
}

/*
 * The rest do not reach the caller as the kind its constructor is named for.
 *
 * BVNAND, BVNOR and BVXNOR are vestigial kinds: no parser produces them --
 * SMT-LIB2 expands bvnand/bvnor/bvxnor into a negated and/or/xor, see
 * lib/Parser/smt2.y -- so only the bit-blaster is complete for them, and
 * BVConstEvaluator would abort on one with a constant operand. The
 * constructors expand them the same way the parser does.
 *
 * The remaining three are canonicalised by SimplifyingNodeFactory, which is
 * the factory a validity checker builds through: a zero-extend becomes a
 * concat with a zero constant, and the boolean nand/nor a negated and/or.
 *
 * Either way the equivalence proofs above are what pin down what the
 * constructors mean; a caller inspecting getExprKind() should not expect to
 * see the kind it asked for.
 */
TEST(new_expr_kinds, some_kinds_are_rewritten_on_construction)
{
  Fixture f;
  Expr a = f.bv("a");
  Expr b = f.bv("b");
  Expr p = f.boolean("p");
  Expr q = f.boolean("q");

  // Which kind the negated form settles on is the simplifier's business -- it
  // pushes the negation through with De Morgan, for instance -- so what
  // matters is only that the vestigial kind is not what comes back.
  EXPECT_NE(getExprKind(vc_bvNandExpr(f.vc, a, b)), BVNAND);
  EXPECT_NE(getExprKind(vc_bvNorExpr(f.vc, a, b)), BVNOR);
  EXPECT_NE(getExprKind(vc_bvXnorExpr(f.vc, a, b)), BVXNOR);

  EXPECT_EQ(getExprKind(vc_bvZeroExtend(f.vc, a, W + 1)), BVCONCAT);
  EXPECT_EQ(getExprKind(vc_nandExpr(f.vc, p, q)), NOT);
  EXPECT_EQ(getExprKind(vc_norExpr(f.vc, p, q)), NOT);
}

/*
 * The point of expanding them: an operand that is constant sends the
 * expression through BVConstEvaluator, which has no case for the BVNAND,
 * BVNOR or BVXNOR kinds and calls FatalError on anything it does not know.
 */
TEST(new_expr_kinds, bitwise_negated_ops_fold_with_constant_operands)
{
  Fixture f;
  Expr a = f.bv("a");

  // Values chosen to fit in W bits.
  const unsigned int K = 0x2A, J = 0x35;
  const unsigned int MASK = (1u << W) - 1;
  Expr k = vc_bvConstExprFromInt(f.vc, W, K);

  f.expectEqual(vc_bvNandExpr(f.vc, a, k),
                vc_bvNotExpr(f.vc, vc_bvAndExpr(f.vc, a, k)),
                "vc_bvNandExpr with a constant operand");
  f.expectEqual(vc_bvNorExpr(f.vc, a, k),
                vc_bvNotExpr(f.vc, vc_bvOrExpr(f.vc, a, k)),
                "vc_bvNorExpr with a constant operand");
  f.expectEqual(vc_bvXnorExpr(f.vc, a, k),
                vc_bvNotExpr(f.vc, vc_bvXorExpr(f.vc, a, k)),
                "vc_bvXnorExpr with a constant operand");

  // Both operands constant: the whole expression has to fold to a value.
  Expr folded = vc_bvNandExpr(f.vc, vc_bvConstExprFromInt(f.vc, W, J), k);
  EXPECT_EQ(getExprKind(folded), BVCONST);
  EXPECT_EQ(getBVUnsigned(folded), (~(J & K)) & MASK);
}

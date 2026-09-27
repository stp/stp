/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// api3-new-expr-kinds.cpp -- node kinds that STP has always parsed and
// bit-blasted but that the 2.x C API was late to construct: zero-extend, the
// six overflow predicates, the bitwise nand/nor/xnor and the Boolean nand/nor.
// In 3.x the first ten are named constructors (zero_extend, bvuaddo ...
// bvsmulo, bvnand, bvnor, bvxnor); the public kinds have no Boolean nand or
// nor, which are spelled not_ over and_ and or_.
//
// Each operator is checked by asking STP to prove it equivalent, for every
// input, to a reference expression built only from other constructors. An
// entailment over free variables covers the whole input space at that width
// rather than a sample of it, and goes through bit-blasting rather than being
// folded away by the simplifier.

#include "api3_common.hpp"

#include <cstdint>
#include <string>

using namespace stp;

namespace
{

// Width used for the equivalence proofs. Small enough that the doubled-width
// multiplies in the reference for the *mulo predicates stay quick, large
// enough to exercise carries.
constexpr std::uint32_t W = 6;

// The options of a 2.x checker: vc_createValidityChecker set 'd', so every
// 2.x case ran with the counterexample self-check on, and every solver here
// runs with check-sanity.
Options checkerOptions()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

class Fixture
{
public:
  TermManager tm;
  Solver s{tm, checkerOptions()};

  Term bv(const char* name, std::uint32_t width = W)
  {
    return tm.declare(name, tm.mk_bv_sort(width));
  }

  Term boolean(const char* name) { return tm.declare(name, tm.mk_bool_sort()); }

  Term zeroes(std::uint32_t width) { return tm.mk_bv(width, 0); }

  // Zero-extend 'e' to 'width' without using zero_extend, which is one of the
  // constructors under test.
  Term zeroExtendByConcat(const Term& e, std::uint32_t width)
  {
    const std::uint32_t have = e.sort().bv_size();
    EXPECT_LT(have, width);
    return concat(zeroes(width - have), e);
  }

  // The two's-complement constant for a negative value at the given width.
  Term negativeConst(std::uint32_t width, std::uint64_t magnitude)
  {
    return tm.mk_bv(width, (std::uint64_t(1) << width) - magnitude);
  }

  // Assert that the two Boolean terms agree on every input (= on Bool is iff).
  void expectEquivalent(const Term& actual, const Term& reference, const std::string& what)
  {
    EXPECT_TRUE(s.entails(actual == reference).is_valid())
        << what << " does not match its reference expression";
  }

  // Assert that the two terms are equal on every input.
  void expectEqual(const Term& actual, const Term& reference, const std::string& what)
  {
    EXPECT_TRUE(s.entails(actual == reference).is_valid())
        << what << " does not match its reference expression";
  }
};

/*
 * "The exact result carried in 'wide' falls outside the signed 'w'-bit range",
 * i.e. the standard signed-overflow condition. 'wideWidth' is the width of
 * 'wide' itself, which is wider than 'w' so that the exact result fits.
 */
Term outsideSignedRange(Fixture& f, const Term& wide, std::uint32_t wideWidth, std::uint32_t w)
{
  const Term max = f.tm.mk_bv(wideWidth, (std::uint64_t(1) << (w - 1)) - 1);
  const Term min = f.negativeConst(wideWidth, std::uint64_t(1) << (w - 1));

  return bvslt(wide, min) || bvsgt(wide, max);
}

// "The unsigned value of 'wide' does not fit in 'w' bits."
Term aboveUnsignedRange(Fixture& f, const Term& wide, std::uint32_t wideWidth, std::uint32_t w)
{
  return bvuge(wide, f.tm.mk_bv(wideWidth, std::uint64_t(1) << w));
}

/*
 * Widths the overflow predicates are proved over. One is the interesting case:
 * the bit-blasted predicates index the top bit as l[w-1], so it is where an
 * off-by-one in that indexing would show up. At width one the only signed
 * values are 0 and -1.
 */
const std::uint32_t OVERFLOW_WIDTHS[] = {1, 2, W};

} // namespace

/////////////////////////////////////////////////////////////////////////////
/// ZERO EXTEND
/////////////////////////////////////////////////////////////////////////////

// Widening pads with zeroes, which is exactly a concat with a zero constant.
// (2.x's vc_bvZeroExtend extended to a width; 3.x's zero_extend(k, t) extends
// by k bits.)
TEST(new_expr_kinds, zero_extend_widens_with_zeroes)
{
  Fixture f;
  const Term a = f.bv("a");

  for (std::uint32_t to = W + 1; to <= 2 * W; to++)
  {
    const Term extended = zero_extend(to - W, a);
    ASSERT_EQ(extended.sort().bv_size(), to);

    f.expectEqual(extended, f.zeroExtendByConcat(a, to),
                  "zero_extend to width " + std::to_string(to));
  }
}

// Extending to the width it already has (by zero bits) is the identity.
TEST(new_expr_kinds, zero_extend_to_same_width_is_identity)
{
  Fixture f;
  const Term a = f.bv("a");

  const Term same = zero_extend(0, a);
  ASSERT_EQ(same.sort().bv_size(), W);
  f.expectEqual(same, a, "zero_extend by nothing");
}

/*
 * 2.x: asking vc_bvZeroExtend for fewer bits truncated rather than failing,
 * which is what vc_bvSignExtend already did. 3.x's zero_extend extends by a
 * count and never narrows: narrowing is extract, and the count a caller
 * computes for a narrower target (target - width, here -2 as an unsigned
 * 32-bit count) is not an extension and must be refused.
 */
TEST(new_expr_kinds, zero_extend_to_narrower_width_truncates)
{
  Fixture f;
  const Term a = f.bv("a");

  const Term narrowed = extract(W - 3, 0, a);
  ASSERT_EQ(narrowed.sort().bv_size(), W - 2);
  // the low W-2 bits: zero-extended back, a with its top two bits cleared
  f.expectEqual(zero_extend(2, narrowed), bvand(a, f.tm.mk_bv(W, (1u << (W - 2)) - 1)),
                "extract to a narrower width");

  // the count a narrower target computes wraps to an extension beyond the
  // largest width, and is refused rather than wrapped back (the manager stays
  // usable)
  const std::uint32_t wrapped = (W - 2) - W;
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, zero_extend(wrapped, a));
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE, sign_extend(wrapped, a));
  EXPECT_EQ(zero_extend(2, a).sort().bv_size(), W + 2);
}

// Zero-extending differs from sign-extending exactly on negative inputs.
TEST(new_expr_kinds, zero_extend_differs_from_sign_extend_when_negative)
{
  Fixture f;
  const Term a = f.bv("a");
  const std::uint32_t wide = W + 2;

  const Term agree = zero_extend(wide - W, a) == sign_extend(wide - W, a);

  // They agree iff the top bit of 'a' is clear. (2.x's vc_bvBoolExtract_Zero
  // was true for a clear bit; 3.x's bit(t, i) is true for a set one.)
  EXPECT_TRUE(f.s.entails(agree == !bit(a, W - 1)).is_valid());
}

/////////////////////////////////////////////////////////////////////////////
/// OVERFLOW PREDICATES
/////////////////////////////////////////////////////////////////////////////

// Unsigned addition overflows iff the exact sum needs more than w bits.
TEST(new_expr_kinds, unsigned_add_overflow)
{
  for (const std::uint32_t w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    const Term a = f.bv("a", w);
    const Term b = f.bv("b", w);

    const Term exact = bvadd(f.zeroExtendByConcat(a, w + 1), f.zeroExtendByConcat(b, w + 1));

    f.expectEquivalent(bvuaddo(a, b), aboveUnsignedRange(f, exact, w + 1, w), "bvuaddo");
  }
}

// Signed addition overflows iff the exact sum leaves the signed w-bit range.
TEST(new_expr_kinds, signed_add_overflow)
{
  for (const std::uint32_t w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    const Term a = f.bv("a", w);
    const Term b = f.bv("b", w);

    const Term exact = bvadd(sign_extend(1, a), sign_extend(1, b));

    f.expectEquivalent(bvsaddo(a, b), outsideSignedRange(f, exact, w + 1, w), "bvsaddo");
  }
}

// Unsigned subtraction overflows (borrows) iff the left operand is smaller.
TEST(new_expr_kinds, unsigned_sub_overflow)
{
  for (const std::uint32_t w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    const Term a = f.bv("a", w);
    const Term b = f.bv("b", w);

    f.expectEquivalent(bvusubo(a, b), bvult(a, b), "bvusubo");
  }
}

// Signed subtraction overflows iff the exact difference leaves the range.
TEST(new_expr_kinds, signed_sub_overflow)
{
  for (const std::uint32_t w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    const Term a = f.bv("a", w);
    const Term b = f.bv("b", w);

    const Term exact = bvsub(sign_extend(1, a), sign_extend(1, b));

    f.expectEquivalent(bvssubo(a, b), outsideSignedRange(f, exact, w + 1, w), "bvssubo");
  }
}

// Unsigned multiplication overflows iff the exact 2w-bit product needs
// more than w bits.
TEST(new_expr_kinds, unsigned_mul_overflow)
{
  for (const std::uint32_t w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    const Term a = f.bv("a", w);
    const Term b = f.bv("b", w);

    const Term exact = bvmul(f.zeroExtendByConcat(a, 2 * w), f.zeroExtendByConcat(b, 2 * w));

    f.expectEquivalent(bvumulo(a, b), aboveUnsignedRange(f, exact, 2 * w, w), "bvumulo");
  }
}

// Signed multiplication overflows iff the exact product leaves the range.
TEST(new_expr_kinds, signed_mul_overflow)
{
  for (const std::uint32_t w : OVERFLOW_WIDTHS)
  {
    SCOPED_TRACE("width " + std::to_string(w));
    Fixture f;
    const Term a = f.bv("a", w);
    const Term b = f.bv("b", w);

    const Term exact = bvmul(sign_extend(w, a), sign_extend(w, b));

    f.expectEquivalent(bvsmulo(a, b), outsideSignedRange(f, exact, 2 * w, w), "bvsmulo");
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
  const Term minusOne = f.negativeConst(W, 1);

  EXPECT_TRUE(f.s.entails(bvumulo(minusOne, minusOne)).is_valid());
  EXPECT_TRUE(f.s.entails(!bvsmulo(minusOne, minusOne)).is_valid());
}

/////////////////////////////////////////////////////////////////////////////
/// BITWISE NAND / NOR / XNOR
/////////////////////////////////////////////////////////////////////////////

TEST(new_expr_kinds, bitwise_nand)
{
  Fixture f;
  const Term a = f.bv("a");
  const Term b = f.bv("b");

  f.expectEqual(bvnand(a, b), bvnot(bvand(a, b)), "bvnand");
}

TEST(new_expr_kinds, bitwise_nor)
{
  Fixture f;
  const Term a = f.bv("a");
  const Term b = f.bv("b");

  f.expectEqual(bvnor(a, b), bvnot(bvor(a, b)), "bvnor");
}

TEST(new_expr_kinds, bitwise_xnor)
{
  Fixture f;
  const Term a = f.bv("a");
  const Term b = f.bv("b");

  f.expectEqual(bvxnor(a, b), bvnot(bvxor(a, b)), "bvxnor");
}

// The bitwise results keep the operands' width.
TEST(new_expr_kinds, bitwise_results_keep_their_width)
{
  Fixture f;
  const Term a = f.bv("a");
  const Term b = f.bv("b");

  EXPECT_EQ(bvnand(a, b).sort().bv_size(), W);
  EXPECT_EQ(bvnor(a, b).sort().bv_size(), W);
  EXPECT_EQ(bvxnor(a, b).sort().bv_size(), W);
}

/////////////////////////////////////////////////////////////////////////////
/// BOOLEAN NAND / NOR
/////////////////////////////////////////////////////////////////////////////

// 3.x has no Boolean nand constructor: not_(and_(p, q)) is its spelling, so
// the case proves that spelling against an if-then-else reference instead of
// against itself.
TEST(new_expr_kinds, boolean_nand)
{
  Fixture f;
  const Term p = f.boolean("p");
  const Term q = f.boolean("q");

  f.expectEquivalent(!(p && q), ite(p, !q, f.tm.mk_true()), "not_(and_(p, q))");
}

// Likewise nor: not_(or_(p, q)).
TEST(new_expr_kinds, boolean_nor)
{
  Fixture f;
  const Term p = f.boolean("p");
  const Term q = f.boolean("q");

  f.expectEquivalent(!(p || q), ite(p, f.tm.mk_false(), !q), "not_(or_(p, q))");
}

/////////////////////////////////////////////////////////////////////////////
/// KIND REPORTING
/////////////////////////////////////////////////////////////////////////////

/*
 * 2.x's legacy Kind prefix was aligned with exprkind_t, and these kinds were
 * listed in the public enum long before anything could build them, so
 * nothing had held that correspondence in place for them. In 3.x Term::kind()
 * reports the public kinds of kinds.toml.
 *
 * Only the kinds that survive construction can be checked this way; see below
 * for the ones the manager rewrites.
 */
TEST(new_expr_kinds, kinds_are_reported_correctly)
{
  Fixture f;
  const Term a = f.bv("a");
  const Term b = f.bv("b");

  EXPECT_EQ(bvuaddo(a, b).kind(), Kind::BV_UADDO);
  EXPECT_EQ(bvsaddo(a, b).kind(), Kind::BV_SADDO);
  EXPECT_EQ(bvusubo(a, b).kind(), Kind::BV_USUBO);
  EXPECT_EQ(bvssubo(a, b).kind(), Kind::BV_SSUBO);
  EXPECT_EQ(bvumulo(a, b).kind(), Kind::BV_UMULO);
  EXPECT_EQ(bvsmulo(a, b).kind(), Kind::BV_SMULO);
}

/*
 * The rest do not reach the caller as the kind their constructor is named for.
 *
 * BVNAND, BVNOR and BVXNOR are vestigial engine kinds: no parser produces them
 * -- SMT-LIB2 expands bvnand/bvnor/bvxnor into a negated and/or/xor, see
 * lib/Parser/smt2.y -- so only the bit-blaster is complete for them, and
 * BVConstEvaluator would abort on one with a constant operand. The
 * constructors expand them the same way the parser does.
 *
 * The remaining three are canonicalised by the manager's construction-time
 * folding (on by default): a zero-extend becomes a concat with a zero
 * constant, and the Boolean nand/nor a negated and/or.
 *
 * Either way the equivalence proofs above are what pin down what the
 * constructors mean; a caller inspecting kind() should not expect to see the
 * kind it asked for.
 */
TEST(new_expr_kinds, some_kinds_are_rewritten_on_construction)
{
  Fixture f;
  const Term a = f.bv("a");
  const Term b = f.bv("b");
  const Term p = f.boolean("p");
  const Term q = f.boolean("q");

  // Which kind the negated form settles on is the folding's business -- it
  // pushes the negation through with De Morgan, for instance -- so what
  // matters is only that the vestigial kind is not what comes back.
  EXPECT_NE(bvnand(a, b).kind(), Kind::BV_NAND);
  EXPECT_NE(bvnor(a, b).kind(), Kind::BV_NOR);
  EXPECT_NE(bvxnor(a, b).kind(), Kind::BV_XNOR);

  EXPECT_EQ(zero_extend(1, a).kind(), Kind::BV_CONCAT);
  EXPECT_EQ((!(p && q)).kind(), Kind::NOT);
  EXPECT_EQ((!(p || q)).kind(), Kind::NOT);

  // 3.x: without the folding (simplify = false) a zero-extend is kept as
  // written, while the negated bitwise operators still read as the negation
  // they are built as.
  TermManager raw = api3::raw_manager();
  const Term ra = raw.declare("a", raw.mk_bv_sort(W));
  const Term rb = raw.declare("b", raw.mk_bv_sort(W));
  EXPECT_EQ(zero_extend(1, ra).kind(), Kind::BV_ZERO_EXTEND);
  const Term rawNand = bvnand(ra, rb);
  EXPECT_EQ(rawNand.kind(), Kind::BV_NOT);
  EXPECT_EQ(rawNand.child(0).kind(), Kind::BV_AND);
}

/*
 * The point of expanding them: an operand that is constant sends the
 * expression through BVConstEvaluator, which has no case for the BVNAND,
 * BVNOR or BVXNOR kinds and ends in FatalError on anything it does not know.
 */
TEST(new_expr_kinds, bitwise_negated_ops_fold_with_constant_operands)
{
  Fixture f;
  const Term a = f.bv("a");

  // Values chosen to fit in W bits.
  const std::uint64_t K = 0x2A, J = 0x35;
  const std::uint64_t MASK = (std::uint64_t(1) << W) - 1;
  const Term k = f.tm.mk_bv(W, K);

  f.expectEqual(bvnand(a, k), bvnot(bvand(a, k)), "bvnand with a constant operand");
  f.expectEqual(bvnor(a, k), bvnot(bvor(a, k)), "bvnor with a constant operand");
  f.expectEqual(bvxnor(a, k), bvnot(bvxor(a, k)), "bvxnor with a constant operand");

  // Both operands constant: the whole expression has to fold to a value.
  const Term folded = bvnand(f.tm.mk_bv(W, J), k);
  EXPECT_EQ(folded.kind(), Kind::VALUE);
  EXPECT_EQ(folded.to_uint64(), (~(J & K)) & MASK);
}

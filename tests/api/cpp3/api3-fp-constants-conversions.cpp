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

// api3-fp-constants-conversions.cpp -- floating-point constants (from bits,
// from native numbers, the special values) and the conversions between
// floats, bit-vectors and other formats: their values through a model, every
// rounding mode end to end, SMT-LIB '=' against fp.eq, the partial
// operations under TermManager::simplify, and the sort checks that keep two
// formats with one packed width apart.

#include "api3_common.hpp"

#include <cstdint>
#include <string>
#include <type_traits>
#include <utility>

using namespace stp;

namespace
{

// A 2.x checker's configuration: the counterexample self-check on (3.x's
// default is off), so every satisfiable check constructs its model and checks
// each assertion against it.
Options self_checking()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

// The packed interchange bits of a float value (formats up to 64 bits).
std::uint64_t packed(const FloatValue& v)
{
  return std::stoull(v.bits(), nullptr, 2);
}

// Check (expecting sat) and read the packed bits of `v`'s value. ASSERT_*
// needs a void function, so guard by hand: a model read after a check that was
// not sat is a NO_MODEL error, which would only obscure the failure.
std::uint64_t solveRead(Solver& s, const Term& v)
{
  const Result r = s.check_sat();
  EXPECT_TRUE(r.is_sat()) << r;
  if (!r.is_sat())
    return ~std::uint64_t(0);
  return packed(s.model().fp_value(v));
}

// Whether TermManager::mk_fp(sort, mode, 1.0) accepts a mode of type Mode.
template <class Mode, class = void>
struct mk_fp_takes_mode : std::false_type
{
};
template <class Mode>
struct mk_fp_takes_mode<Mode, std::void_t<decltype(std::declval<TermManager&>().mk_fp(
                                  std::declval<const Sort&>(), std::declval<Mode>(), 1.0))>>
    : std::true_type
{
};

} // namespace

// 3.x: a format is a sort, and mk_fp_sort refuses one SMT-LIB does not allow
// with a RecoverableError (INVALID_ARGUMENT) where 2.x ended the process.
TEST(fp_constants, from_bits_rejects_invalid_smt_format)
{
  TermManager tm;
  const auto e = API3_ERROR_OF(tm.mk_fp_sort(1, 4));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::INVALID_ARGUMENT);
  EXPECT_NE(std::string(e->what()).find("at least 2 exponent and 2 significand bits"),
            std::string::npos)
      << e->what();
  // the generic constructor refuses the same format given as indices
  API3_EXPECT_ERROR(ErrorCode::INDEX_OUT_OF_RANGE,
                    tm.mk_term(Kind::FP_TO_FP_FROM_BV, {tm.mk_bv(5, 0)}, {1, 4}));
}

// The narrowest formats SMT-LIB allows used to be refused outright, because
// SymFPU's unpack aborted on them. They are fixed in STP's SymFPU fork instead
// (the commit cmake/FindSymFPU.cmake pins), so the API builds and solves at
// them like any other format. (2, 3) is the case that needs two of those
// fixes: the first makes it reachable at all, and doing so gives it an
// unpacked exponent width equal to its significand width, which is exactly
// the family the second one fixes.
TEST(fp_constants, from_bits_at_the_narrowest_formats)
{
  for (std::uint32_t sb = 2; sb <= 4; sb++)
    for (std::uint32_t eb = 2; eb <= 4; eb++)
    {
      TermManager tm;
      Solver s(tm, self_checking());
      // The all-ones exponent with a zero significand is an infinity at every
      // format, so the bits say what the value must classify as.
      const Term bits = tm.mk_bv(eb + sb, ((1ULL << eb) - 1) << (sb - 1));
      const Term x = tm.mk_fp_from_bits(tm.mk_fp_sort(eb, sb), bits);
      s.add(fp_is_inf(x));
      s.add(fp_is_pos(x));
      EXPECT_TRUE(s.check_sat().is_sat()) << "format (" << eb << ", " << sb << ")";
    }
}

// The special-value constructors produce values that classify as claimed.
TEST(fp_constants, special_values)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Sort f = tm.mk_fp_sort(5, 11);
  s.add(fp_is_nan(tm.mk_fp_nan(f)));
  s.add(fp_is_inf(tm.mk_fp_pos_inf(f)));
  s.add(fp_is_pos(tm.mk_fp_pos_inf(f)));
  s.add(fp_is_inf(tm.mk_fp_neg_inf(f)));
  s.add(fp_is_neg(tm.mk_fp_neg_inf(f)));
  s.add(fp_is_zero(tm.mk_fp_pos_zero(f)));
  s.add(fp_is_pos(tm.mk_fp_pos_zero(f)));
  s.add(fp_is_neg(tm.mk_fp_neg_zero(f)));
  EXPECT_TRUE(s.check_sat().is_sat()); // all consistent
}

TEST(fp_constants, plus_infinity_is_not_nan)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Sort f = tm.mk_fp_sort(5, 11);
  s.add(fp_is_nan(tm.mk_fp_pos_inf(f)));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

// Exact native-format conversions do not use the rounding mode numerically,
// but it is still a required, source-sorted operand.
TEST(fp_constants, native_exact_conversion_checks_rounding_mode_sort)
{
  TermManager tm;
  const Sort binary64 = tm.mk_fp_sort(11, 53);
  const Sort binary32 = tm.mk_fp_sort(8, 24);
  const Term bv5 = tm.mk_bv(5, 0);

  // 3.x: mk_fp(sort, mode, double) takes a RoundingMode enumerator, so a mode
  // of another sort cannot be written there at all.
  static_assert(mk_fp_takes_mode<RoundingMode>::value, "mk_fp takes a RoundingMode");
  static_assert(!mk_fp_takes_mode<Term>::value, "mk_fp takes no mode term");

  // The conversions that take the mode as a term refuse a bit-vector there,
  // although 1 converts exactly into either format.
  const auto e64 = API3_ERROR_OF(to_fp(binary64, bv5, tm.mk_real(1)));
  ASSERT_TRUE(e64.has_value());
  EXPECT_EQ(e64->code(), ErrorCode::SORT_MISMATCH);
  EXPECT_EQ(e64->argument_index(), std::optional<int>(0));
  EXPECT_NE(std::string(e64->what()).find("expected a rounding mode"), std::string::npos)
      << e64->what();
  const auto e32 = API3_ERROR_OF(to_fp(binary32, bv5, tm.mk_real(1)));
  ASSERT_TRUE(e32.has_value());
  EXPECT_EQ(e32->code(), ErrorCode::SORT_MISMATCH);
  EXPECT_EQ(e32->argument_index(), std::optional<int>(0));

  // A native double beside a float term is converted under the call's mode
  // term, which the operation checks: the bit-vector mode is refused the same
  // way, at argument 0, whatever its bits, and never read as a mode.
  const Term operand = tm.declare("mode_operand", binary32);
  for (const Term& mode : {bv5, tm.mk_bv(5, 0)})
  {
    const auto e = API3_ERROR_OF(fp_add(mode, operand, 1.0));
    ASSERT_TRUE(e.has_value());
    EXPECT_EQ(e->code(), ErrorCode::SORT_MISMATCH);
    EXPECT_EQ(e->argument_index(), std::optional<int>(0));
  }
}

// mk_fp(sort, mode, double) is exact when the target is binary64 (3.5 is
// 0x400C...), and rounds once under the mode otherwise (2.0 in half precision
// is 0x4000).
TEST(fp_constants, from_double_exact)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Sort dbl = tm.mk_fp_sort(11, 53);
  const Term x = tm.declare("x", dbl);
  s.add(fp_eq(x, tm.mk_fp(dbl, RoundingMode::RNE, 3.5)));
  EXPECT_EQ(solveRead(s, x), 0x400C000000000000ULL);
}

TEST(fp_constants, from_double_narrowed)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Sort half = tm.mk_fp_sort(5, 11);
  const Term x = tm.declare("x", half);
  s.add(fp_eq(x, tm.mk_fp(half, RoundingMode::RNE, 2.0)));
  EXPECT_EQ(solveRead(s, x), 0x4000u);
}

// float -> bit-vector: fp.to_ubv and fp.to_sbv.
TEST(fp_conversions, to_bitvector)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Sort half = tm.mk_fp_sort(5, 11);
  const Term two = tm.mk_fp_from_bits(half, tm.mk_bv(16, 0x4000));
  const Term negtwo = tm.mk_fp_from_bits(half, tm.mk_bv(16, 0xC000));

  const Term ubv = tm.declare("ubv", tm.mk_bv_sort(8));
  const Term sbv = tm.declare("sbv", tm.mk_bv_sort(8));
  s.add(ubv == fp_to_ubv(8, rne, two));
  s.add(sbv == fp_to_sbv(8, rne, negtwo));

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(m.uint64_value(ubv), 2u);
  EXPECT_EQ(m.uint64_value(sbv), 0xFEu); // -2, 8-bit
}

// bit-vector -> float: reinterpret, signed conversion, unsigned conversion.
TEST(fp_conversions, to_float)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Sort half = tm.mk_fp_sort(5, 11);
  const Term rne = tm.mk_rm(RoundingMode::RNE);

  const Term rein = tm.declare("rein", half);
  const Term fromS = tm.declare("fromS", half);
  const Term fromU = tm.declare("fromU", half);
  s.add(fp_eq(rein, to_fp_from_bits(half, tm.mk_bv(16, 0x4000))));
  s.add(fp_eq(fromS, to_fp(half, rne, tm.mk_bv(8, 3))));
  s.add(fp_eq(fromU, to_fp_unsigned(half, rne, tm.mk_bv(8, 5))));

  ASSERT_TRUE(s.check_sat().is_sat());
  const Model m = s.model();
  EXPECT_EQ(packed(m.fp_value(rein)), 0x4000u);  // 2.0
  EXPECT_EQ(packed(m.fp_value(fromS)), 0x4200u); // 3.0
  EXPECT_EQ(packed(m.fp_value(fromU)), 0x4500u); // 5.0
}

// A native float into the single format is exact (1.5f is 0x3FC00000). 3.x
// has one native overload, taking a double, which a float converts to
// exactly.
TEST(fp_constants, from_float)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term sv = tm.declare("sv", tm.mk_fp_sort(8, 24));
  s.add(fp_eq(sv, tm.mk_fp(tm.mk_fp_sort(8, 24), RoundingMode::RNE, 1.5f)));
  EXPECT_EQ(solveRead(s, sv), 0x3FC00000u);
}

// to_fp from a float: reformat a double to half precision (3.0 -> 0x4200).
TEST(fp_conversions, reformat_double_to_half)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term d = tm.declare("d", tm.mk_fp_sort(11, 53));
  s.add(fp_eq(d, tm.mk_fp(tm.mk_fp_sort(11, 53), RoundingMode::RNE, 3.0)));
  const Term h = tm.declare("h", tm.mk_fp_sort(5, 11));
  s.add(fp_eq(h, to_fp(tm.mk_fp_sort(5, 11), rne, d)));
  EXPECT_EQ(solveRead(s, h), 0x4200u);
}

// Every rounding mode end-to-end, distinguished pairwise: fp.to_sbv of 2.5,
// -2.5 and 1.5 gives each mode a unique signature --
//   RNE (2, -2, 2), RNA (3, -3, 2), RTP (3, -2, 2),
//   RTN (2, -3, 1), RTZ (2, -2, 1).
// A wrong encoding in mk_rm (or a mode falling through symfpu's dispatch)
// breaks at least one probe.
TEST(fp_conversions, every_rounding_mode)
{
  const struct
  {
    RoundingMode mode;
    std::uint64_t pos, neg, tie;
  } probes[] = {
      {RoundingMode::RNE, 2, 0xFE, 2}, {RoundingMode::RNA, 3, 0xFD, 2},
      {RoundingMode::RTP, 3, 0xFE, 2}, {RoundingMode::RTN, 2, 0xFD, 1},
      {RoundingMode::RTZ, 2, 0xFE, 1},
  };

  for (const auto& p : probes)
  {
    TermManager tm;
    Solver s(tm, self_checking());
    const Sort half = tm.mk_fp_sort(5, 11);
    const Term rm = tm.mk_rm(p.mode);
    const Term posHalf = tm.mk_fp_from_bits(half, tm.mk_bv(16, 0x4100));
    const Term negHalf = tm.mk_fp_from_bits(half, tm.mk_bv(16, 0xC100));
    const Term tieHalf = tm.mk_fp_from_bits(half, tm.mk_bv(16, 0x3E00));

    const Term a = tm.declare("a", tm.mk_bv_sort(8));
    const Term b = tm.declare("b", tm.mk_bv_sort(8));
    const Term c = tm.declare("c", tm.mk_bv_sort(8));
    s.add(a == fp_to_sbv(8, rm, posHalf));
    s.add(b == fp_to_sbv(8, rm, negHalf));
    s.add(c == fp_to_sbv(8, rm, tieHalf));

    ASSERT_TRUE(s.check_sat().is_sat()) << p.mode;
    const Model m = s.model();
    EXPECT_EQ(m.uint64_value(a), p.pos) << p.mode;
    EXPECT_EQ(m.uint64_value(b), p.neg) << p.mode;
    EXPECT_EQ(m.uint64_value(c), p.tie) << p.mode;
  }
}

// SMT '=' vs fp.eq: '=' keeps +0 and -0 distinct where fp.eq identifies
// them, and fp.eq(NaN, NaN) is false where '=' (which identifies every NaN
// with every NaN) holds.
TEST(fp_constants, eq_vs_smt_eq_semantics)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Sort half = tm.mk_fp_sort(5, 11);
  // fp.eq(+0, -0) holds.
  s.add(fp_eq(tm.mk_fp_pos_zero(half), tm.mk_fp_neg_zero(half)));
  // As SMT '=' they differ.
  s.add(!(tm.mk_fp_pos_zero(half) == tm.mk_fp_neg_zero(half)));
  // fp.eq(NaN, NaN) does not hold.
  s.add(!fp_eq(tm.mk_fp_nan(half), tm.mk_fp_nan(half)));
  EXPECT_TRUE(s.check_sat().is_sat()); // all consistent
}

// TermManager::simplify is another entrance to the source-level FP graph. The
// partial operations are built at their public arity and acquire their
// internal unspecified-value child only when they are totalised: at solve
// time, and when simplify or a model evaluates a closed one. In particular,
// neither the zero tie of min/max nor an undefined float-to-BV conversion may
// reach the constant evaluator at its raw arity.
TEST(fp_simplify, totalises_partial_operations)
{
  {
    TermManager tm;
    Solver s(tm, self_checking());
    const Sort half = tm.mk_fp_sort(5, 11);
    const Term plus_zero = tm.mk_fp_pos_zero(half);
    const Term minus_zero = tm.mk_fp_neg_zero(half);

    const Term minimum = tm.simplify(fp_min(plus_zero, minus_zero));
    const Term maximum = tm.simplify(fp_max(plus_zero, minus_zero));
    EXPECT_EQ(minimum.sort().kind(), SortKind::FP);
    EXPECT_EQ(maximum.sort().kind(), SortKind::FP);
    EXPECT_EQ(minimum.sort().fp_exp_size(), 5u);
    EXPECT_EQ(minimum.sort().fp_sig_size(), 11u);

    // Each result must be one of the two zero values, while SMT-LIB leaves the
    // choice between them unspecified.
    const Term min_is_zero = minimum == plus_zero || minimum == minus_zero;
    s.add(!min_is_zero);
    EXPECT_TRUE(s.check_sat().is_unsat());
  }

  // Use a fresh manager and solver for max: the previous solver is
  // intentionally inconsistent.
  TermManager tm;
  Solver s(tm, self_checking());
  const Sort half = tm.mk_fp_sort(5, 11);
  const Term plus_zero = tm.mk_fp_pos_zero(half);
  const Term minus_zero = tm.mk_fp_neg_zero(half);
  const Term maximum = tm.simplify(fp_max(plus_zero, minus_zero));
  const Term max_is_zero = maximum == plus_zero || maximum == minus_zero;
  s.add(!max_is_zero);
  EXPECT_TRUE(s.check_sat().is_unsat());

  // Both undefined conversion forms must also remain usable after simplify.
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term nan = tm.mk_fp_nan(half);
  const Term ubv = tm.simplify(fp_to_ubv(8, rne, nan));
  const Term sbv = tm.simplify(fp_to_sbv(8, rne, nan));
  EXPECT_EQ(ubv.sort().kind(), SortKind::BV);
  EXPECT_EQ(sbv.sort().kind(), SortKind::BV);
  EXPECT_EQ(ubv.sort().bv_size(), 8u);
  EXPECT_EQ(sbv.sort().bv_size(), 8u);
}

TEST(fp_simplify, preserves_defined_conversion_semantics)
{
  TermManager tm;
  Solver s(tm, self_checking());
  const Term rne = tm.mk_rm(RoundingMode::RNE);
  const Term two = tm.mk_fp_from_bits(tm.mk_fp_sort(5, 11), tm.mk_bv(16, 0x4000));
  const Term converted = tm.simplify(fp_to_ubv(8, rne, two));

  s.add(!(converted == tm.mk_bv(8, 2)));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

// These formats have the same 32-bit packed carrier. Width-only checks
// therefore cannot distinguish them; the public source sorts must. 3.x: each
// refusal is a RecoverableError (SORT_MISMATCH) naming the mismatched
// argument, where 2.x ended the process.
TEST(fp_sort_checks, release_api_rejects_mixed_formats)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_fp_sort(8, 24));
  const Term y = tm.declare("y", tm.mk_fp_sort(11, 21));
  const Term rne = tm.mk_rm(RoundingMode::RNE);

  const auto add = API3_ERROR_OF(fp_add(rne, x, y));
  ASSERT_TRUE(add.has_value());
  EXPECT_EQ(add->code(), ErrorCode::SORT_MISMATCH) << add->what();
  EXPECT_EQ(add->argument_index(), std::optional<int>(2));

  const auto lt = API3_ERROR_OF(fp_lt(x, y));
  ASSERT_TRUE(lt.has_value());
  EXPECT_EQ(lt->code(), ErrorCode::SORT_MISMATCH) << lt->what();
  EXPECT_EQ(lt->argument_index(), std::optional<int>(1));

  const auto feq = API3_ERROR_OF(fp_eq(x, y));
  ASSERT_TRUE(feq.has_value());
  EXPECT_EQ(feq->code(), ErrorCode::SORT_MISMATCH) << feq->what();
  EXPECT_EQ(feq->argument_index(), std::optional<int>(1));
}

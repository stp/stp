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

// values.cpp -- values and their readers: every mk_bv form, the string
// readers and their padding, fits/DOES_NOT_FIT, floating-point values in
// every class and format, rounding modes, Reals in lowest terms, and the
// literal operands that stand beside terms.

#include "api_common.hpp"

#include <chrono>
#include <cmath>
#include <limits>

using namespace stp;

namespace
{

class Values : public ::testing::Test
{
protected:
  TermManager tm;
  Sort bv8 = tm.mk_bv_sort(8), bv12 = tm.mk_bv_sort(12), bv16 = tm.mk_bv_sort(16);
  Sort f16 = tm.mk_fp16_sort(), f32 = tm.mk_fp32_sort(), f64 = tm.mk_fp64_sort();
  Sort f128 = tm.mk_fp128_sort(), R = tm.mk_real_sort();
};

// ---------------------------------------------------------------- bit-vectors

TEST_F(Values, mk_bv_unsigned_and_signed)
{
  EXPECT_EQ(tm.mk_bv(8, 255).to_uint64(), 255u);
  EXPECT_EQ(tm.mk_bv(8, 255).to_int64(), -1);
  EXPECT_EQ(tm.mk_bv(64, ~0ull).to_uint64(), ~0ull);
  EXPECT_EQ(tm.mk_bv(64, ~0ull).to_int64(), -1);
  EXPECT_EQ(tm.mk_bv(1, 1).to_uint64(), 1u);
  auto e = API_ERROR_OF(tm.mk_bv(8, 256));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::VALUE_OUT_OF_RANGE);
  EXPECT_EQ(e->argument_index(), std::optional<int>(1));
  ASSERT_EQ(e->sorts().size(), 1u);
  EXPECT_TRUE(e->sorts()[0] == bv8);
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(1, 2));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_bv(0, 0));
  EXPECT_EQ(tm.mk_bv_signed(8, -1).to_uint64(), 255u);
  EXPECT_EQ(tm.mk_bv_signed(8, -128).to_int64(), -128);
  EXPECT_EQ(tm.mk_bv_signed(8, 127).to_int64(), 127);
  EXPECT_EQ(tm.mk_bv_signed(64, -1).to_uint64(), ~0ull);
  EXPECT_EQ(tm.mk_bv_signed(100, -1).to_bv_string(16), std::string(25, 'f'));
  EXPECT_EQ(tm.mk_bv_signed(100, -2).to_int64(), -2);
  EXPECT_EQ(tm.mk_bv_signed(100, 5).to_uint64(), 5u);
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv_signed(8, 128));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv_signed(8, -129));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_bv_signed(0, 0));
  // the named values
  EXPECT_EQ(tm.mk_bv_zero(8).to_uint64(), 0u);
  EXPECT_EQ(tm.mk_bv_ones(8).to_uint64(), 255u);
  EXPECT_EQ(tm.mk_bv_min_signed(8).to_int64(), -128);
  EXPECT_EQ(tm.mk_bv_max_signed(8).to_int64(), 127);
  EXPECT_EQ(tm.mk_bv_ones(70).to_bv_string(2), std::string(70, '1'));
  EXPECT_TRUE(tm.mk_bv_zero(8).same_as(tm.mk_bv(8, 0)));
  EXPECT_TRUE(tm.mk_bv_ones(8).same_as(tm.mk_bv(8, 255)));
  EXPECT_TRUE(tm.mk_bv_min_signed(8).same_as(tm.mk_bv(8, 0x80)));
  EXPECT_TRUE(tm.mk_bv_max_signed(8).same_as(tm.mk_bv(8, 0x7f)));
  // wrapped
  EXPECT_EQ(tm.mk_bv_wrapped(8, 300).to_uint64(), 44u);
  EXPECT_EQ(tm.mk_bv_wrapped(8, 256).to_uint64(), 0u);
  EXPECT_EQ(tm.mk_bv_wrapped(64, ~0ull).to_uint64(), ~0ull);
  EXPECT_EQ(tm.mk_bv_wrapped(70, ~0ull).to_bv_string(16, false), "ffffffffffffffff");
  // values are interned: equal values are the same node
  EXPECT_TRUE(tm.mk_bv(8, 5).same_as(tm.mk_bv(8, 5)));
  EXPECT_TRUE(tm.mk_bv(8, 5).same_as(tm.mk_bv(8, "5", 10)));
  EXPECT_FALSE(tm.mk_bv(8, 5).same_as(tm.mk_bv(9, 5)));
}

TEST_F(Values, mk_bv_from_digits)
{
  EXPECT_EQ(tm.mk_bv(8, "255", 10).to_uint64(), 255u);
  EXPECT_EQ(tm.mk_bv(8, "-128", 10).to_int64(), -128);
  EXPECT_EQ(tm.mk_bv(8, "-1", 10).to_uint64(), 255u);
  EXPECT_EQ(tm.mk_bv(8, "+7", 10).to_uint64(), 7u);
  EXPECT_EQ(tm.mk_bv(8, "#xff", 16).to_uint64(), 255u);
  EXPECT_EQ(tm.mk_bv(8, "0xFF", 16).to_uint64(), 255u);
  EXPECT_EQ(tm.mk_bv(8, "0Xab", 16).to_uint64(), 0xabu);
  EXPECT_EQ(tm.mk_bv(8, "ff", 16).to_uint64(), 255u);
  EXPECT_EQ(tm.mk_bv(8, "#b1010", 2).to_uint64(), 10u);
  EXPECT_EQ(tm.mk_bv(8, "0b1010", 2).to_uint64(), 10u);
  EXPECT_EQ(tm.mk_bv(8, "1010", 2).to_uint64(), 10u);
  EXPECT_EQ(tm.mk_bv(8, "1_0", 2).to_uint64(), 2u); // separators are skipped
  EXPECT_EQ(tm.mk_bv(128, "0x0123456789abcdef0123456789abcdef", 16).to_bv_string(16),
            "0123456789abcdef0123456789abcdef");
  EXPECT_EQ(tm.mk_bv(96, "486579698794948075013401", 10).to_bv_string(10),
            "486579698794948075013401");
  auto e = API_ERROR_OF(tm.mk_bv(8, "256", 10));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::VALUE_OUT_OF_RANGE);
  EXPECT_EQ(e->argument_index(), std::optional<int>(1));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(8, "-129", 10));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(8, "100", 16));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(8, "111111111", 2));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(8, "-1", 16)); // sign: base 10 only
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(8, "", 10));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(8, "#x", 16));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(8, "1x", 10));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(8, "12", 2));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv(8, "g", 16));
  e = API_ERROR_OF(tm.mk_bv(8, "12", 3));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::INVALID_ARGUMENT);
  EXPECT_EQ(e->argument_index(), std::optional<int>(2));
}

TEST_F(Values, mk_bv_from_limbs_and_bytes)
{
  const Term two_limbs = tm.mk_bv_limbs(100, {1, 2});
  EXPECT_EQ(two_limbs.to_bv_string(16), "0000000020000000000000001");
  ASSERT_EQ(two_limbs.to_bv_limbs().size(), 2u);
  EXPECT_EQ(two_limbs.to_bv_limbs()[0], 1u);
  EXPECT_EQ(two_limbs.to_bv_limbs()[1], 2u);
  EXPECT_EQ(tm.mk_bv_limbs(8, {5}).to_uint64(), 5u);
  EXPECT_EQ(tm.mk_bv_limbs(8, {}).to_uint64(), 0u);
  EXPECT_EQ(tm.mk_bv_limbs(70, {0, 0, 0}).to_uint64(), 0u); // zero high limbs are fine
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv_limbs(100, {1, 1ull << 40}));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv_limbs(8, {256}));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_bv_limbs(0, {}));
  EXPECT_EQ(tm.mk_bv_bytes(16, {0x34, 0x12}, true).to_uint64(), 0x1234u);
  EXPECT_EQ(tm.mk_bv_bytes(16, {0x12, 0x34}, false).to_uint64(), 0x1234u);
  EXPECT_EQ(tm.mk_bv_bytes(16, {0x34, 0x12}).to_uint64(), 0x1234u); // little-endian default
  EXPECT_EQ(tm.mk_bv_bytes(12, {0x34, 0x02}, true).to_uint64(), 0x234u);
  EXPECT_EQ(tm.mk_bv_bytes(16, {0x34}, true).to_uint64(), 0x34u);
  EXPECT_EQ(tm.mk_bv_bytes(16, {}, true).to_uint64(), 0u);
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv_bytes(12, {0x34, 0x12}, true));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_bv_bytes(8, {0x34, 0x12}, false));
  // and back
  const Term v = tm.mk_bv(16, 0x1234);
  EXPECT_EQ(v.to_bv_bytes(true), (std::vector<std::uint8_t>{0x34, 0x12}));
  EXPECT_EQ(v.to_bv_bytes(false), (std::vector<std::uint8_t>{0x12, 0x34}));
  EXPECT_EQ(v.to_bv_bytes(), (std::vector<std::uint8_t>{0x34, 0x12}));
  EXPECT_EQ(tm.mk_bv(12, 0x123).to_bv_bytes(true), (std::vector<std::uint8_t>{0x23, 0x01}));
  EXPECT_EQ(tm.mk_bv(12, 0x123).to_bv_bytes(false), (std::vector<std::uint8_t>{0x01, 0x23}));
  EXPECT_EQ(tm.mk_bv(8, 0xab).to_bv_bytes(false), (std::vector<std::uint8_t>{0xab}));
  EXPECT_EQ(tm.mk_bv_bytes(128, tm.mk_bv(128, "0x0123456789abcdef0123456789abcdef", 16).to_bv_bytes())
                .to_bv_string(16),
            "0123456789abcdef0123456789abcdef");
}

TEST_F(Values, bv_string_padding)
{
  const Term v = tm.mk_bv(12, 0xabc);
  EXPECT_EQ(v.to_bv_string(), "101010111100");
  EXPECT_EQ(v.to_bv_string(2), "101010111100");
  EXPECT_EQ(v.to_bv_string(2, false), "101010111100");
  EXPECT_EQ(v.to_bv_string(16), "abc");
  EXPECT_EQ(v.to_bv_string(16, false), "abc");
  EXPECT_EQ(v.to_bv_string(10), "2748"); // unsigned; to_int64 is the signed reader
  EXPECT_EQ(v.to_int64(), -1348);
  const Term three = tm.mk_bv(12, 3);
  EXPECT_EQ(three.to_bv_string(2), "000000000011");
  EXPECT_EQ(three.to_bv_string(2, false), "11");
  EXPECT_EQ(three.to_bv_string(16), "003");
  EXPECT_EQ(three.to_bv_string(16, false), "3");
  EXPECT_EQ(three.to_bv_string(10), "3");
  EXPECT_EQ(tm.mk_bv(12, 0).to_bv_string(2, false), "0");
  EXPECT_EQ(tm.mk_bv(12, 0).to_bv_string(16, false), "0");
  EXPECT_EQ(tm.mk_bv(12, 0).to_bv_string(10), "0");
  // ceil(n/4) hex digits when the width is not a multiple of 4
  EXPECT_EQ(tm.mk_bv(9, 3).to_bv_string(16), "003");
  EXPECT_EQ(tm.mk_bv(9, 0x1ff).to_bv_string(16), "1ff");
  EXPECT_EQ(tm.mk_bv(1, 1).to_bv_string(16), "1");
  EXPECT_EQ(tm.mk_bv(8, 0xff).to_bv_string(10), "255");
  EXPECT_EQ(tm.mk_bv(64, ~0ull).to_bv_string(10), "18446744073709551615");
  EXPECT_EQ(tm.mk_bv_ones(70).to_bv_string(10), "1180591620717411303423");
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, v.to_bv_string(7));
  EXPECT_EQ(v.str(), "#xabc"); // lowercase hex, no leading space
  EXPECT_EQ(tm.mk_bv(9, 3).str(), "#b000000011");
}

TEST_F(Values, fits_and_does_not_fit)
{
  const Term small = tm.mk_bv(70, 1);
  EXPECT_TRUE(small.fits_uint64());
  EXPECT_TRUE(small.fits_int64());
  EXPECT_EQ(small.to_uint64(), 1u);
  const Term big = tm.mk_bv_limbs(70, {0, 1}); // 2^64
  EXPECT_FALSE(big.fits_uint64());
  EXPECT_FALSE(big.fits_int64());
  auto e = API_ERROR_OF(big.to_uint64());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::DOES_NOT_FIT);
  EXPECT_EQ(e->terms().size(), 1u);
  API_EXPECT_ERROR(ErrorCode::DOES_NOT_FIT, big.to_int64());
  EXPECT_EQ(big.to_bv_limbs()[1], 1u);
  EXPECT_EQ(big.to_bv_string(16, false), "10000000000000000");
  // a negative 100-bit value fits int64 but not uint64
  const Term neg = tm.mk_bv_signed(100, -5);
  EXPECT_TRUE(neg.fits_int64());
  EXPECT_FALSE(neg.fits_uint64());
  EXPECT_EQ(neg.to_int64(), -5);
  API_EXPECT_ERROR(ErrorCode::DOES_NOT_FIT, neg.to_uint64());
  // a 64-bit value with the top bit set fits uint64 (and int64 as negative)
  const Term top = tm.mk_bv(64, 1ull << 63);
  EXPECT_TRUE(top.fits_uint64());
  EXPECT_TRUE(top.fits_int64());
  EXPECT_EQ(top.to_int64(), std::numeric_limits<std::int64_t>::min());
  // a 65-bit positive value above int64 max
  const Term above = tm.mk_bv_limbs(65, {1ull << 63, 0});
  EXPECT_TRUE(above.fits_uint64());
  EXPECT_FALSE(above.fits_int64());
  EXPECT_EQ(above.to_uint64(), 1ull << 63);
  API_EXPECT_ERROR(ErrorCode::DOES_NOT_FIT, above.to_int64());
  // the readers refuse non-values and wrong sorts
  const Term x = tm.declare("x", bv8);
  e = API_ERROR_OF(x.to_uint64());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::NOT_A_VALUE);
  API_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, (x + 1).to_bv_string());
  API_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, x.fits_uint64());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_true().to_uint64());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_bv(8, 0).to_bool());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_fp_nan(f32).to_uint64());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_real(1).to_bv_limbs());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_bv(8, 1).to_fp());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_bv(8, 1).to_rm());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_bv(8, 1).to_rational());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_bv(8, 1).to_uninterpreted_index());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_rm(RoundingMode::RNA).to_fp());
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_fp_nan(f32).to_rm());
  EXPECT_TRUE(tm.mk_true().to_bool());
  EXPECT_FALSE(tm.mk_bool(false).to_bool());
  EXPECT_TRUE(tm.mk_bool(true).same_as(tm.mk_true()));
}

// ---------------------------------------------------------------- floating point

TEST_F(Values, fp_classes_and_fields)
{
  const Term one = tm.mk_fp(f32, RoundingMode::RNE, 1.0);
  const FloatValue v = one.to_fp();
  EXPECT_EQ(v.exp_size, 8u);
  EXPECT_EQ(v.sig_size, 24u);
  EXPECT_FALSE(v.sign);
  EXPECT_EQ(v.biased_exponent, 127u);
  ASSERT_EQ(v.significand.size(), 1u);
  EXPECT_EQ(v.significand[0], 0u);
  EXPECT_EQ(v.cls, FloatValue::Class::NORMAL);
  EXPECT_EQ(v.bits(), "00111111100000000000000000000000");
  EXPECT_EQ(v.to_double(), std::optional<double>(1.0));
  ASSERT_TRUE(v.to_rational().has_value());
  EXPECT_EQ(v.to_rational()->str(), "1");
  EXPECT_EQ(one.str(), "(fp #b0 #b01111111 #b00000000000000000000000)");

  const FloatValue neg = tm.mk_fp(f32, RoundingMode::RNE, -1.5).to_fp();
  EXPECT_TRUE(neg.sign);
  EXPECT_EQ(neg.significand[0], 1ull << 22);
  EXPECT_EQ(neg.to_double(), std::optional<double>(-1.5));
  EXPECT_EQ(neg.to_rational()->str(), "-3/2");

  const FloatValue tenth = tm.mk_fp(f32, RoundingMode::RNE, 0.1).to_fp();
  EXPECT_EQ(tenth.bits(), "00111101110011001100110011001101");
  EXPECT_EQ(tenth.to_rational()->str(), "13421773/134217728");
  EXPECT_EQ(static_cast<float>(*tenth.to_double()), 0.1f);
  EXPECT_NE(*tenth.to_double(), 0.1); // binary32's 0.1 is not binary64's

  const FloatValue sub = tm.mk_fp(f32, RoundingMode::RNE, 1e-45).to_fp();
  EXPECT_EQ(sub.cls, FloatValue::Class::SUBNORMAL);
  EXPECT_EQ(sub.biased_exponent, 0u);
  EXPECT_EQ(sub.significand[0], 1u);
  EXPECT_EQ(sub.to_rational()->numerator, "1"); // the smallest subnormal is 2^-149
  EXPECT_GT(*sub.to_double(), 0.0);
  EXPECT_LT(*sub.to_double(), 2e-45);

  const FloatValue pz = tm.mk_fp_pos_zero(f32).to_fp();
  EXPECT_EQ(pz.cls, FloatValue::Class::ZERO);
  EXPECT_FALSE(pz.sign);
  EXPECT_EQ(pz.to_double(), std::optional<double>(0.0));
  EXPECT_EQ(pz.to_rational()->str(), "0");
  const FloatValue nz = tm.mk_fp_neg_zero(f32).to_fp();
  EXPECT_EQ(nz.cls, FloatValue::Class::ZERO);
  EXPECT_TRUE(nz.sign);
  EXPECT_TRUE(std::signbit(*nz.to_double()));
  EXPECT_EQ(nz.bits(), "10000000000000000000000000000000");

  const FloatValue pinf = tm.mk_fp_pos_inf(f32).to_fp();
  EXPECT_EQ(pinf.cls, FloatValue::Class::INF);
  EXPECT_EQ(pinf.bits(), "01111111100000000000000000000000");
  EXPECT_TRUE(std::isinf(*pinf.to_double()));
  EXPECT_FALSE(pinf.to_rational().has_value());
  const FloatValue ninf = tm.mk_fp_neg_inf(f32).to_fp();
  EXPECT_TRUE(ninf.sign);
  EXPECT_LT(*ninf.to_double(), 0.0);

  const FloatValue nan = tm.mk_fp_nan(f32).to_fp();
  EXPECT_EQ(nan.cls, FloatValue::Class::NOT_A_NUMBER);
  EXPECT_EQ(nan.bits(), "01111111110000000000000000000000"); // the canonical quiet NaN
  EXPECT_TRUE(std::isnan(*nan.to_double()));
  EXPECT_FALSE(nan.to_rational().has_value());
}

TEST_F(Values, fp_formats)
{
  const Term h = tm.mk_fp(f16, RoundingMode::RNE, 1.0);
  EXPECT_EQ(h.to_fp().bits(), "0011110000000000");
  EXPECT_EQ(h.to_fp().biased_exponent, 15u);
  EXPECT_EQ(h.to_fp().to_double(), std::optional<double>(1.0));
  EXPECT_EQ(tm.mk_fp(f16, RoundingMode::RNE, 65504.0).to_fp().cls, FloatValue::Class::NORMAL);
  EXPECT_EQ(tm.mk_fp(f16, RoundingMode::RNE, 65520.0).to_fp().cls, FloatValue::Class::INF);
  EXPECT_EQ(tm.mk_fp(f16, RoundingMode::RTZ, 65520.0).to_fp().to_double(),
            std::optional<double>(65504.0));
  const Term d = tm.mk_fp(f64, RoundingMode::RNE, 0.1);
  EXPECT_EQ(d.to_fp().to_double(), std::optional<double>(0.1)); // exact for binary64
  EXPECT_EQ(d.to_fp().biased_exponent, 1019u);
  EXPECT_EQ(d.to_fp().bits().size(), 64u);
  const Term q = tm.mk_fp(f128, RoundingMode::RNE, 1.0);
  EXPECT_EQ(q.to_fp().exp_size, 15u);
  EXPECT_EQ(q.to_fp().sig_size, 113u);
  EXPECT_EQ(q.to_fp().biased_exponent, 16383u);
  EXPECT_EQ(q.to_fp().significand.size(), 2u);
  EXPECT_FALSE(q.to_fp().to_double().has_value()); // wider than binary64
  EXPECT_EQ(q.to_fp().to_rational()->str(), "1");
  EXPECT_EQ(q.to_fp().bits().size(), 128u);
  const Term q10 = tm.mk_fp(f128, RoundingMode::RNE, 0.1);
  // the exact rational of the double 0.1, carried exactly into binary128
  EXPECT_EQ(q10.to_fp().to_rational()->str(), "3602879701896397/36028797018963968");
  EXPECT_EQ(tm.mk_fp(f128, RoundingMode::RNE, "0.1").to_fp().to_rational()->numerator.size(), 34u);
  // a tiny format (the literal converters need at least 3 exponent bits)
  const Sort f5 = tm.mk_fp_sort(3, 2);
  EXPECT_EQ(tm.mk_fp(f5, RoundingMode::RNE, 1.0).to_fp().bits(), "00110");
  EXPECT_EQ(tm.mk_fp(f5, RoundingMode::RNE, 1.0).to_fp().to_double(), std::optional<double>(1.0));
  EXPECT_EQ(tm.mk_fp(f5, RoundingMode::RNE, "1.0").to_fp().bits(), "00110");
  const Sort f4 = tm.mk_fp_sort(2, 2);
  API_EXPECT_ERROR(ErrorCode::UNSUPPORTED, tm.mk_fp(f4, RoundingMode::RNE, 1.0));
  EXPECT_EQ(tm.mk_fp_from_bits(f4, "0010").to_fp().to_double(), std::optional<double>(1.0));
}

TEST_F(Values, fp_from_double_rounds_once_under_the_mode)
{
  const double rne = *tm.mk_fp(f32, RoundingMode::RNE, 0.1).to_fp().to_double();
  const double rna = *tm.mk_fp(f32, RoundingMode::RNA, 0.1).to_fp().to_double();
  const double rtp = *tm.mk_fp(f32, RoundingMode::RTP, 0.1).to_fp().to_double();
  const double rtn = *tm.mk_fp(f32, RoundingMode::RTN, 0.1).to_fp().to_double();
  const double rtz = *tm.mk_fp(f32, RoundingMode::RTZ, 0.1).to_fp().to_double();
  EXPECT_EQ(rne, rna);
  EXPECT_GT(rtp, 0.1);
  EXPECT_LT(rtn, 0.1);
  EXPECT_EQ(rtz, rtn);
  EXPECT_EQ(rne, rtp); // 0.1 rounds up to nearest in binary32
  EXPECT_EQ(*tm.mk_fp(f32, RoundingMode::RTN, -0.1).to_fp().to_double(), -rtp);
  EXPECT_EQ(*tm.mk_fp(f32, RoundingMode::RTZ, -0.1).to_fp().to_double(), -rtn);
  // overflow rounds to infinity or to the largest finite value
  EXPECT_EQ(tm.mk_fp(f32, RoundingMode::RNE, 1e39).to_fp().cls, FloatValue::Class::INF);
  EXPECT_EQ(tm.mk_fp(f32, RoundingMode::RTZ, 1e39).to_fp().cls, FloatValue::Class::NORMAL);
  EXPECT_EQ(tm.mk_fp(f32, RoundingMode::RTN, 1e39).to_fp().cls, FloatValue::Class::NORMAL);
  EXPECT_EQ(tm.mk_fp(f32, RoundingMode::RTP, 1e39).to_fp().cls, FloatValue::Class::INF);
  EXPECT_EQ(tm.mk_fp(f32, RoundingMode::RTP, -1e39).to_fp().cls, FloatValue::Class::NORMAL);
  // the specials and signed zero
  EXPECT_TRUE(tm.mk_fp(f32, RoundingMode::RNE, std::nan("")).same_as(tm.mk_fp_nan(f32)));
  EXPECT_TRUE(tm.mk_fp(f32, RoundingMode::RNE, INFINITY).same_as(tm.mk_fp_pos_inf(f32)));
  EXPECT_TRUE(tm.mk_fp(f32, RoundingMode::RNE, -INFINITY).same_as(tm.mk_fp_neg_inf(f32)));
  EXPECT_TRUE(tm.mk_fp(f32, RoundingMode::RNE, 0.0).same_as(tm.mk_fp_pos_zero(f32)));
  EXPECT_TRUE(tm.mk_fp(f32, RoundingMode::RNE, -0.0).same_as(tm.mk_fp_neg_zero(f32)));
  // an exact double is exact in binary64 and binary128
  EXPECT_EQ(tm.mk_fp(f64, RoundingMode::RTZ, 0.1).to_fp().to_double(), std::optional<double>(0.1));
  EXPECT_EQ(tm.mk_fp(f128, RoundingMode::RTZ, 0.1).to_fp().to_rational()->str(),
            tm.mk_fp(f128, RoundingMode::RTP, 0.1).to_fp().to_rational()->str());
}

TEST_F(Values, fp_from_decimal_and_rational_text)
{
  EXPECT_EQ(static_cast<float>(*tm.mk_fp(f32, RoundingMode::RNE, "0.1").to_fp().to_double()), 0.1f);
  EXPECT_TRUE(tm.mk_fp(f32, RoundingMode::RNE, "0.1").same_as(tm.mk_fp(f32, RoundingMode::RNE, 0.1)));
  EXPECT_EQ(tm.mk_fp(f32, RoundingMode::RNE, "1/3").to_fp().bits(),
            "00111110101010101010101010101011");
  EXPECT_EQ(tm.mk_fp(f32, RoundingMode::RTZ, "1/3").to_fp().bits(),
            "00111110101010101010101010101010");
  EXPECT_EQ(static_cast<float>(*tm.mk_fp(f32, RoundingMode::RNE, "-2.5e-3").to_fp().to_double()), -0.0025f);
  EXPECT_EQ(*tm.mk_fp(f64, RoundingMode::RNE, "-2.5e-3").to_fp().to_double(), -0.0025);
  EXPECT_EQ(*tm.mk_fp(f32, RoundingMode::RNE, "1E5").to_fp().to_double(), 100000.0);
  EXPECT_EQ(*tm.mk_fp(f32, RoundingMode::RNE, "12").to_fp().to_double(), 12.0);
  EXPECT_EQ(*tm.mk_fp(f32, RoundingMode::RNE, "+2.5").to_fp().to_double(), 2.5);
  EXPECT_EQ(*tm.mk_fp(f32, RoundingMode::RNE, "-3/2").to_fp().to_double(), -1.5);
  EXPECT_EQ(*tm.mk_fp(f64, RoundingMode::RNE, "1/3").to_fp().to_double(), 1.0 / 3.0);
  EXPECT_EQ(tm.mk_fp(f32, RoundingMode::RNE, "0").to_fp().cls, FloatValue::Class::ZERO);
  EXPECT_EQ(tm.mk_fp(f32, RoundingMode::RNE, "-0.0").to_fp().sign, true);
  EXPECT_EQ(tm.mk_fp(f32, RoundingMode::RNE, "1e39").to_fp().cls, FloatValue::Class::INF);
  // the rounding mode applies to text too
  EXPECT_LT(*tm.mk_fp(f32, RoundingMode::RTZ, "0.1").to_fp().to_double(),
            *tm.mk_fp(f32, RoundingMode::RTP, "0.1").to_fp().to_double());
  auto e = API_ERROR_OF(tm.mk_fp(f32, RoundingMode::RNE, "abc"));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::INVALID_ARGUMENT);
  EXPECT_EQ(e->argument_index(), std::optional<int>(2));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_fp(f32, RoundingMode::RNE, "1/0"));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_fp(f32, RoundingMode::RNE, "1/-2"));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_fp(f32, RoundingMode::RNE, "1.2.3"));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_fp(f32, RoundingMode::RNE, ""));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_fp(f32, RoundingMode::RNE, "1e"));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_fp(bv8, RoundingMode::RNE, 1.0));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_fp(bv8, RoundingMode::RNE, "1"));
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, tm.mk_fp(Sort(), RoundingMode::RNE, 1.0));
}

// A decimal literal's exponent is read as a bounded integer, and a literal far
// outside a format decides its value as the format's bound does, without
// expanding its digits: "12e2147483647" was +0 after a minute and 8 GB (an int
// overflowed), and "1e100000000" took seconds and hundreds of MB. A Real that
// far out is refused as past the number limits, with the start of the literal
// in the message rather than all of it.
TEST_F(Values, decimal_exponents_far_out)
{
  const auto started = std::chrono::steady_clock::now();
  for (RoundingMode rm : {RoundingMode::RNE, RoundingMode::RNA, RoundingMode::RTP, RoundingMode::RTN,
                          RoundingMode::RTZ})
  {
    // past the largest finite value, as a merely overflowing literal
    EXPECT_TRUE(tm.mk_fp(f16, rm, "12e2147483647").same_as(tm.mk_fp(f16, rm, "1e6")));
    EXPECT_TRUE(tm.mk_fp(f16, rm, "-1e100000000").same_as(tm.mk_fp(f16, rm, "-1e6")));
    EXPECT_TRUE(tm.mk_fp(f16, rm, "1e99999999999999999999999").same_as(tm.mk_fp(f16, rm, "1e6")));
    // under half the smallest subnormal, as a merely tiny literal
    EXPECT_TRUE(tm.mk_fp(f16, rm, "1e-100000000").same_as(tm.mk_fp(f16, rm, "1e-12")));
    EXPECT_TRUE(tm.mk_fp(f16, rm, "-7e-2147483648").same_as(tm.mk_fp(f16, rm, "-1e-12")));
  }
  EXPECT_EQ(tm.mk_fp(f16, RoundingMode::RNE, "12e2147483647").to_fp().cls, FloatValue::Class::INF);
  EXPECT_EQ(tm.mk_fp(f16, RoundingMode::RTZ, "12e2147483647").to_fp().cls, FloatValue::Class::NORMAL);
  EXPECT_EQ(tm.mk_fp(f16, RoundingMode::RNE, "1e-100000000").to_fp().cls, FloatValue::Class::ZERO);
  EXPECT_EQ(tm.mk_fp(f16, RoundingMode::RTP, "1e-100000000").to_fp().cls, FloatValue::Class::SUBNORMAL);
  // inside the format's range the bound changes nothing
  EXPECT_EQ(*tm.mk_fp(f64, RoundingMode::RNE, "1.5e300").to_fp().to_double(), 1.5e300);
  EXPECT_EQ(*tm.mk_fp(f64, RoundingMode::RNE, "4.9e-324").to_fp().to_double(), 4.9e-324);
  EXPECT_EQ(*tm.mk_fp(f32, RoundingMode::RNE, "0.00012e4").to_fp().to_double(), 1.2f);
  // zero, whatever its exponent
  EXPECT_EQ(tm.mk_fp(f16, RoundingMode::RNE, "0e999999999999").to_fp().cls, FloatValue::Class::ZERO);
  EXPECT_TRUE(tm.mk_fp(f16, RoundingMode::RNE, "-0.000e-99999999999").same_as(tm.mk_fp_neg_zero(f16)));
  // Reals
  EXPECT_EQ(tm.mk_real("1.5e3").to_rational().str(), "1500");
  EXPECT_EQ(tm.mk_real("0.00012e4").to_rational().str(), "6/5");
  EXPECT_EQ(tm.mk_real("0e999999999999").to_rational().str(), "0");
  auto e = API_ERROR_OF(tm.mk_real("1e10000000"));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::UNSUPPORTED);
  const std::string digits = "1" + std::string(30000, '0'); // no exponent, past the limits
  e = API_ERROR_OF(tm.mk_real(digits));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::UNSUPPORTED);
  EXPECT_LT(std::string(e->what()).size(), 400u) << e->what();
  // an exponent is its digits and nothing else
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_fp(f32, RoundingMode::RNE, "1e5x"));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_fp(f32, RoundingMode::RNE, "1e 5"));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_real("1e+"));
  EXPECT_LT(std::chrono::steady_clock::now() - started, std::chrono::seconds(5));
}

TEST_F(Values, fp_from_bits_canonicalises_nan)
{
  const Term one = tm.mk_fp(f32, RoundingMode::RNE, 1.0);
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, "0x3f800000").same_as(one));
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, "0b00111111100000000000000000000000").same_as(one));
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, "00111111100000000000000000000000").same_as(one));
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, tm.mk_bv(32, 0x3f800000)).same_as(one));
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, "0x1").same_as(tm.mk_fp(f32, RoundingMode::RNE, 1e-45)));
  // every NaN pattern is the canonical quiet NaN
  const Term nan = tm.mk_fp_nan(f32);
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, "0x7fc00000").same_as(nan));
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, "0x7f800001").same_as(nan));
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, "0xffc00000").same_as(nan));
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, "0xffffffff").same_as(nan));
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, tm.mk_bv(32, 0x7f800001)).same_as(nan));
  EXPECT_EQ(tm.mk_fp_from_bits(f32, "0x7f800001").to_fp().bits(), nan.to_fp().bits());
  EXPECT_TRUE(to_fp_from_bits(f32, tm.mk_bv(32, 0xffffffff)).same_as(nan));
  EXPECT_TRUE(tm.mk_fp_from_bits(f32, "0x7f800000").same_as(tm.mk_fp_pos_inf(f32)));
  EXPECT_TRUE(tm.mk_fp_from_bits(f16, "0x3c00").same_as(tm.mk_fp(f16, RoundingMode::RNE, 1.0)));
  EXPECT_TRUE(tm.mk_fp_from_bits(f64, "0x3ff0000000000000").same_as(tm.mk_fp(f64, RoundingMode::RNE, 1.0)));
  // (fp s e m) over values is a value; over symbols it is a term
  const Term triple = tm.mk_fp(tm.mk_bv(1, 0), tm.mk_bv(8, 127), tm.mk_bv(23, 0));
  EXPECT_TRUE(triple.is_value());
  EXPECT_TRUE(triple.same_as(one));
  const Term sym = tm.mk_fp(tm.declare("sg", tm.mk_bv_sort(1)), tm.mk_bv(8, 127), tm.mk_bv(23, 0));
  EXPECT_FALSE(sym.is_value());
  EXPECT_TRUE(sym.sort() == f32);
  // fp.to_ieee_bv is the inverse for every value, NaN canonical
  EXPECT_EQ(fp_to_ieee_bv(one).to_uint64(), 0x3f800000u);
  EXPECT_EQ(fp_to_ieee_bv(nan).to_uint64(), 0x7fc00000u);
  EXPECT_TRUE(to_fp_from_bits(f32, fp_to_ieee_bv(one)).same_as(one));
  // errors
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_fp_from_bits(f32, "0x1ffffffff"));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_fp_from_bits(f32, "0xzz"));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, tm.mk_fp_from_bits(f32, ""));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_fp_from_bits(f32, tm.mk_bv(16, 0)));
  API_EXPECT_ERROR(ErrorCode::NOT_A_VALUE, tm.mk_fp_from_bits(f32, tm.declare("b32", tm.mk_bv_sort(32))));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_fp_from_bits(bv8, "0x00"));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_fp_pos_zero(bv8));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, tm.mk_fp_nan(R));
}

TEST_F(Values, rounding_modes)
{
  for (RoundingMode rm : {RoundingMode::RNE, RoundingMode::RNA, RoundingMode::RTP, RoundingMode::RTN,
                          RoundingMode::RTZ})
  {
    const Term t = tm.mk_rm(rm);
    EXPECT_TRUE(t.is_value());
    EXPECT_TRUE(t.sort().is_rm());
    EXPECT_EQ(t.to_rm(), rm);
    EXPECT_EQ(t.str(), to_string(rm));
    EXPECT_TRUE(t.same_as(tm.mk_rm(rm)));
  }
  EXPECT_FALSE(tm.mk_rm(RoundingMode::RNE).same_as(tm.mk_rm(RoundingMode::RNA)));
  EXPECT_STREQ(to_string(RoundingMode::RTZ), "RTZ");
  std::ostringstream os;
  os << RoundingMode::RTP;
  EXPECT_EQ(os.str(), "RTP");
}

// ---------------------------------------------------------------- reals

TEST_F(Values, reals_in_lowest_terms)
{
  EXPECT_EQ(tm.mk_real(3).to_rational().str(), "3");
  EXPECT_EQ(tm.mk_real(-3).to_rational().str(), "-3");
  EXPECT_EQ(tm.mk_real(1, 2).to_rational().str(), "1/2");
  EXPECT_EQ(tm.mk_real(2, 4).to_rational().str(), "1/2");
  EXPECT_EQ(tm.mk_real(-6, -4).to_rational().str(), "3/2");
  EXPECT_EQ(tm.mk_real(6, -4).to_rational().str(), "-3/2");
  EXPECT_EQ(tm.mk_real(0, 5).to_rational().str(), "0");
  EXPECT_EQ(tm.mk_real("2/4").to_rational().str(), "1/2");
  EXPECT_EQ(tm.mk_real("-0.25").to_rational().str(), "-1/4");
  EXPECT_EQ(tm.mk_real("0.25").to_rational().str(), "1/4");
  EXPECT_EQ(tm.mk_real("12").to_rational().str(), "12");
  EXPECT_EQ(tm.mk_real("-3/7").to_rational().str(), "-3/7");
  EXPECT_EQ(tm.mk_real("2.5e-3").to_rational().str(), "1/400");
  EXPECT_EQ(tm.mk_real("1e3").to_rational().str(), "1000");
  const RationalValue r = tm.mk_real("-3/7").to_rational();
  EXPECT_EQ(r.numerator, "-3");
  EXPECT_EQ(r.denominator, "7");
  EXPECT_TRUE(r.fits_int64());
  EXPECT_EQ(r.num64(), -3);
  EXPECT_EQ(r.den64(), 7);
  EXPECT_NEAR(r.to_double(), -3.0 / 7.0, 1e-15);
  EXPECT_EQ(tm.mk_real(3).to_rational().denominator, "1");
  const RationalValue big = tm.mk_real("123456789012345678901234567890").to_rational();
  EXPECT_FALSE(big.fits_int64());
  API_EXPECT_ERROR(ErrorCode::DOES_NOT_FIT, big.num64());
  API_EXPECT_ERROR(ErrorCode::DOES_NOT_FIT, big.den64());
  EXPECT_GT(big.to_double(), 1e29);
  // values intern by value
  EXPECT_TRUE(tm.mk_real(1, 2).same_as(tm.mk_real("0.5")));
  EXPECT_TRUE(tm.mk_real(2, 4).same_as(tm.mk_real(1, 2)));
  EXPECT_TRUE(tm.mk_real(3).same_as(tm.mk_real(3, 1)));
  EXPECT_TRUE(tm.mk_real(3).sort().is_real());
  EXPECT_TRUE(tm.mk_real(3).is_value());
  EXPECT_EQ(tm.mk_real(3).str(), "3");
  EXPECT_EQ(tm.mk_real(1, 2).str(), "(/ 1 2)");
  EXPECT_EQ(tm.mk_real(-1, 2).str(), "(- (/ 1 2))");
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_real(1, 0));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_real("1/0"));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_real("abc"));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_real(""));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, tm.mk_real("1.2.3"));
}

// ---------------------------------------------------------------- literal operands

TEST_F(Values, integer_literals_take_the_terms_sort)
{
  const Term x = tm.declare("x", bv8);
  const Term r = tm.declare("r", R);
  const Term fx = tm.declare("fx", f32);
  EXPECT_EQ((x + 3).kind(), Kind::BV_ADD);
  EXPECT_TRUE((x + 3).same_as(bvadd(x, tm.mk_bv(8, 3))));
  EXPECT_TRUE((3 + x).same_as(bvadd(tm.mk_bv(8, 3), x)));
  EXPECT_TRUE(eq(x, 7).same_as(x == tm.mk_bv(8, 7)));
  EXPECT_TRUE((x == 7).same_as(eq(x, tm.mk_bv(8, 7))));
  EXPECT_TRUE((7 == x).same_as(eq(tm.mk_bv(8, 7), x)));
  EXPECT_TRUE((x != 7).same_as(distinct(x, tm.mk_bv(8, 7))));
  EXPECT_TRUE((x - 1).same_as(bvsub(x, tm.mk_bv(8, 1))));
  EXPECT_TRUE((1 - x).same_as(bvsub(tm.mk_bv(8, 1), x)));
  EXPECT_TRUE((x * 3).same_as(bvmul(x, tm.mk_bv(8, 3))));
  EXPECT_TRUE((x & 0x0f).same_as(bvand(x, tm.mk_bv(8, 0x0f))));
  EXPECT_TRUE((x | 0x0f).same_as(bvor(x, tm.mk_bv(8, 0x0f))));
  EXPECT_TRUE((x ^ 0x0f).same_as(bvxor(x, tm.mk_bv(8, 0x0f))));
  EXPECT_TRUE((x << 2).same_as(bvshl(x, tm.mk_bv(8, 2))));
  EXPECT_TRUE(bvult(x, 10).same_as(bvult(x, tm.mk_bv(8, 10))));
  EXPECT_TRUE(bvslt(x, -1).same_as(bvslt(x, tm.mk_bv_signed(8, -1))));
  EXPECT_TRUE(bvudiv(x, 2u).same_as(bvudiv(x, tm.mk_bv(8, 2))));
  EXPECT_TRUE(bvlshr(x, 1).same_as(bvlshr(x, tm.mk_bv(8, 1))));
  EXPECT_TRUE(bvuaddo(x, 200).same_as(bvuaddo(x, tm.mk_bv(8, 200))));
  // negative literals are two's complement of the width; every integral type works
  EXPECT_TRUE((x + -1).same_as(bvadd(x, tm.mk_bv(8, 255))));
  EXPECT_TRUE((x + -128).same_as(bvadd(x, tm.mk_bv(8, 128))));
  EXPECT_TRUE((x + 255u).same_as(bvadd(x, tm.mk_bv(8, 255))));
  EXPECT_TRUE((x + static_cast<short>(5)).same_as(x + 5));
  EXPECT_TRUE((x + static_cast<std::uint8_t>(5)).same_as(x + 5));
  EXPECT_TRUE((x + 5l).same_as(x + 5));
  EXPECT_TRUE((x + 5ull).same_as(x + 5));
  // Real literals
  EXPECT_TRUE((r + 3).same_as(real_add(r, tm.mk_real(3))));
  EXPECT_TRUE((3 * r).same_as(real_mul(tm.mk_real(3), r)));
  EXPECT_TRUE((r / 4).same_as(real_div(r, tm.mk_real(4))));
  EXPECT_TRUE(eq(r, 7).same_as(r == tm.mk_real(7)));
  EXPECT_TRUE(real_gt(r, 0).same_as(real_gt(r, tm.mk_real(0))));
  EXPECT_TRUE(real_lt(-2, r).same_as(real_lt(tm.mk_real(-2), r)));
  // an integer beside a float converts exactly under the manager's mode
  EXPECT_TRUE((fx + 2).same_as(fp_add(RoundingMode::RNE, fx, tm.mk_fp(f32, RoundingMode::RNE, 2.0))));
  EXPECT_TRUE((fx == 3).same_as(eq(fx, tm.mk_fp(f32, RoundingMode::RNE, 3.0))));
  EXPECT_TRUE((-3 * fx).same_as(fp_mul(RoundingMode::RNE, tm.mk_fp(f32, RoundingMode::RNE, -3.0), fx)));
}

TEST_F(Values, integer_literal_range_errors)
{
  const Term x = tm.declare("x", bv8);
  const Term b = tm.declare("b", tm.mk_bool_sort());
  auto e = API_ERROR_OF(x + 256);
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::VALUE_OUT_OF_RANGE);
  EXPECT_EQ(e->function(), "literal");
  ASSERT_EQ(e->sorts().size(), 1u);
  EXPECT_TRUE(e->sorts()[0] == bv8);
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, (void)(x + -129));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, (void)(x == 256u));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, (void)(x | 0x100));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, (void)(300 - x));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, bvult(x, 1000));
  API_EXPECT_ERROR(ErrorCode::VALUE_OUT_OF_RANGE, eq(x, ~0ull));
  EXPECT_TRUE((x + 255).sort() == bv8);
  // a literal beside a Bool or a declared sort has no meaning
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(b == 1));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(tm.mk_true() + 1));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(tm.declare("p", tm.declare_sort("S")) == 0));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(tm.declare("rm", tm.mk_rm_sort()) == 0));
  // operators that have no unambiguous meaning
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(x / x));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(x / 2));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(-b));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(b + b));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(b && x));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(x || b));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(!x));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(~b));
  API_EXPECT_ERROR(ErrorCode::NULL_HANDLE, (void)(Term() + 1));
}

TEST_F(Values, floating_literals)
{
  const Term fx = tm.declare("fx", f32);
  const Term x = tm.declare("x", bv8);
  const Term r = tm.declare("r", R);
  const Term rm = tm.declare("rm", tm.mk_rm_sort());
  // converted exactly and rounded once under the call's mode
  Term t = fp_add(RoundingMode::RTZ, fx, 0.1);
  ASSERT_EQ(t.kind(), Kind::FP_ADD);
  Term lit;
  for (const Term& c : t.children())
    if (c.is_value() && c.sort().is_fp())
      lit = c;
  ASSERT_FALSE(lit.is_null());
  EXPECT_TRUE(lit.same_as(tm.mk_fp(f32, RoundingMode::RTZ, 0.1)));
  EXPECT_EQ(lit.to_fp().bits(), "00111101110011001100110011001100");
  t = fp_add(RoundingMode::RNE, fx, 0.1);
  for (const Term& c : t.children())
    if (c.is_value() && c.sort().is_fp())
      lit = c;
  EXPECT_TRUE(lit.same_as(tm.mk_fp(f32, RoundingMode::RNE, 0.1)));
  EXPECT_TRUE(fp_add(tm.mk_rm(RoundingMode::RTP), fx, 1.5)
                  .same_as(fp_add(RoundingMode::RTP, fx, tm.mk_fp(f32, RoundingMode::RNE, 1.5))));
  EXPECT_TRUE(fp_mul(RoundingMode::RNE, 2.0, fx).same_as(fp_mul(RoundingMode::RNE, tm.mk_fp(f32, RoundingMode::RNE, 2.0), fx)));
  EXPECT_TRUE(fp_lt(fx, 0.0).same_as(fp_lt(fx, tm.mk_fp_pos_zero(f32))));
  EXPECT_TRUE(fp_eq(1.0, fx).same_as(fp_eq(tm.mk_fp(f32, RoundingMode::RNE, 1.0), fx)));
  EXPECT_TRUE(fp_min(fx, 1.5).same_as(fp_min(fx, tm.mk_fp(f32, RoundingMode::RNE, 1.5))));
  EXPECT_TRUE(fp_rem(fx, 2.0).same_as(fp_rem(fx, tm.mk_fp(f32, RoundingMode::RNE, 2.0))));
  EXPECT_TRUE((fx == 1.5).same_as(eq(fx, tm.mk_fp(f32, RoundingMode::RNE, 1.5))));
  EXPECT_TRUE((fx != 1.5).same_as(distinct(fx, tm.mk_fp(f32, RoundingMode::RNE, 1.5))));
  EXPECT_TRUE((fx + 1.5f).same_as(fx + 1.5));
  EXPECT_TRUE((fx * 2.0L).same_as(fx * 2.0));
  // the operators round under the manager's default mode
  EXPECT_TRUE((fx + 0.1).same_as(fp_add(RoundingMode::RNE, fx, tm.mk_fp(f32, RoundingMode::RNE, 0.1))));
  tm.set_default_rounding_mode(RoundingMode::RTZ);
  EXPECT_TRUE((fx + 0.1).same_as(fp_add(RoundingMode::RTZ, fx, tm.mk_fp(f32, RoundingMode::RTZ, 0.1))));
  tm.set_default_rounding_mode(RoundingMode::RNE);
  // a floating literal beside a Real is its exact rational
  EXPECT_TRUE((r + 0.5).same_as(real_add(r, tm.mk_real(1, 2))));
  EXPECT_TRUE(real_gt(r, 0.5).same_as(real_gt(r, tm.mk_real(1, 2))));
  EXPECT_TRUE((r * 0.1).same_as(real_mul(r, tm.mk_real("3602879701896397/36028797018963968"))));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, (void)(r + INFINITY));
  // and never beside a bit-vector, a Bool or under a symbolic mode
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(x + 1.5));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(x == 1.5));
  API_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, (void)(tm.mk_true() == 1.0));
  auto e = API_ERROR_OF(fp_add(rm, fx, 0.1));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::UNSUPPORTED);
  EXPECT_TRUE(fp_add(rm, fx, tm.mk_fp(f32, RoundingMode::RNE, 0.1)).kind() == Kind::FP_ADD);
  // NaN and the infinities as literals
  EXPECT_TRUE(fp_eq(fx, std::nan("")).same_as(fp_eq(fx, tm.mk_fp_nan(f32))));
  EXPECT_TRUE(fp_lt(fx, INFINITY).same_as(fp_lt(fx, tm.mk_fp_pos_inf(f32))));
  EXPECT_TRUE(fp_gt(fx, -INFINITY).same_as(fp_gt(fx, tm.mk_fp_neg_inf(f32))));
  EXPECT_TRUE(fp_eq(fx, -0.0).same_as(fp_eq(fx, tm.mk_fp_neg_zero(f32))));
}

} // namespace

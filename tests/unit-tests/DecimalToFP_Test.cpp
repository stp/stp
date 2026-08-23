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
 * Tests for decimalToPackedFPBits, the LibBF-backed conversion behind
 * ((_ to_fp e s) rm <decimal>).
 *
 * Two kinds of oracle: for Float32/Float64 under RNE, the host's strtof and
 * strtod (glibc converts exactly rounded); for the other formats and modes,
 * constants agreed by bitwuzla (MPFR), cvc5 (SymFPU) and z3 -- three
 * conversion implementations independent of LibBF.
 */

#include "stp/FloatBlaster/DecimalLiteral.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <gtest/gtest.h>
#include <string>

using namespace stp;
using namespace stp::symbolic_fp;

namespace
{

// Converts, asserting success; returns the packed bits.
std::string convert(const std::string& dec, unsigned eb, unsigned sb,
                    unsigned rm)
{
  std::string bits, err;
  const bool ok = decimalToPackedFPBits(dec, eb, sb, rm, bits, err);
  EXPECT_TRUE(ok) << dec << " (" << eb << "," << sb << "): " << err;
  if (!ok)
    return "";
  EXPECT_EQ(bits.size(), eb + sb) << dec;
  return bits;
}

std::string bitsOfU64(uint64_t v, unsigned width)
{
  std::string s(width, '0');
  for (unsigned i = 0; i < width; i++)
    if ((v >> (width - 1 - i)) & 1)
      s[i] = '1';
  return s;
}

std::string binary(const std::string& left, const std::string& right,
                   unsigned eb, unsigned sb, unsigned rm,
                   PackedFpBinaryOp operation)
{
  std::string bits, err;
  const bool ok = packedFPBinaryOp(left, right, eb, sb, rm, operation, bits,
                                   err);
  EXPECT_TRUE(ok) << "(" << eb << "," << sb << "): " << err;
  return ok ? bits : "";
}

std::string hostFloatBits(const std::string& dec)
{
  const float f = strtof(dec.c_str(), nullptr);
  uint32_t u;
  memcpy(&u, &f, 4);
  return bitsOfU64(u, 32);
}

std::string hostDoubleBits(const std::string& dec)
{
  const double d = strtod(dec.c_str(), nullptr);
  uint64_t u;
  memcpy(&u, &d, 8);
  return bitsOfU64(u, 64);
}

TEST(DecimalToFP, hostAgreementFloat32RNE)
{
  const char* cases[] = {
      "0.0",     "1.0",         "1.5",      "2.0",
      "0.5",     "0.1",         "0.2",      "123.456",
      "0.001",   "16777216.0",  "16777217.0", "16777218.0",
      "3.14159265358979323846", "65504.0",  "65520.0",
      "0.000000000000000000000000000000000000000000001",
      "340282346638528859811704183484516925440.0", // FLT_MAX, exactly
      "340282366920938463463374607431768211456.0", // 2^128: overflows
  };
  for (const char* c : cases)
    EXPECT_EQ(convert(c, 8, 24, ROUND_NEAREST_TIES_TO_EVEN),
              hostFloatBits(c))
        << c;
}

TEST(DecimalToFP, hostAgreementFloat64RNE)
{
  const char* cases[] = {
      "0.0", "1.0", "1.5", "2.0", "0.5", "0.1", "0.2", "123.456", "0.001",
      "16777217.0", "3.14159265358979323846",
      "9007199254740993.0", // 2^53 + 1: halfway, ties to even
      "2.2250738585072014", // ~DBL_MIN's digits, an ordinary hard case
  };
  for (const char* c : cases)
    EXPECT_EQ(convert(c, 11, 53, ROUND_NEAREST_TIES_TO_EVEN),
              hostDoubleBits(c))
        << c;
}

TEST(DecimalToFP, roundingModesFloat16)
{
  // 0.1 in Float16: only RTP rounds the significand up.
  EXPECT_EQ(convert("0.1", 5, 11, ROUND_NEAREST_TIES_TO_EVEN),
            bitsOfU64(0x2e66, 16));
  EXPECT_EQ(convert("0.1", 5, 11, ROUND_NEAREST_TIES_TO_AWAY),
            bitsOfU64(0x2e66, 16));
  EXPECT_EQ(convert("0.1", 5, 11, ROUND_TOWARD_POSITIVE),
            bitsOfU64(0x2e67, 16));
  EXPECT_EQ(convert("0.1", 5, 11, ROUND_TOWARD_NEGATIVE),
            bitsOfU64(0x2e66, 16));
  EXPECT_EQ(convert("0.1", 5, 11, ROUND_TOWARD_ZERO),
            bitsOfU64(0x2e66, 16));
}

TEST(DecimalToFP, tiesFloat32)
{
  // 2^24 + 1: exactly halfway between representable neighbours.
  EXPECT_EQ(convert("16777217.0", 8, 24, ROUND_NEAREST_TIES_TO_EVEN),
            bitsOfU64(0x4b800000, 32));
  EXPECT_EQ(convert("16777217.0", 8, 24, ROUND_NEAREST_TIES_TO_AWAY),
            bitsOfU64(0x4b800001, 32));
  EXPECT_EQ(convert("16777217.0", 8, 24, ROUND_TOWARD_POSITIVE),
            bitsOfU64(0x4b800001, 32));
  EXPECT_EQ(convert("16777217.0", 8, 24, ROUND_TOWARD_NEGATIVE),
            bitsOfU64(0x4b800000, 32));
  EXPECT_EQ(convert("16777217.0", 8, 24, ROUND_TOWARD_ZERO),
            bitsOfU64(0x4b800000, 32));
}

TEST(DecimalToFP, overflowIsModeSpecific)
{
  // 65520 > max Float16 (65504): nearest and away-side modes give +oo
  // (0x7c00), RTZ and RTN stop at the largest finite value (0x7bff).
  EXPECT_EQ(convert("65520.0", 5, 11, ROUND_NEAREST_TIES_TO_EVEN),
            bitsOfU64(0x7c00, 16));
  EXPECT_EQ(convert("65520.0", 5, 11, ROUND_NEAREST_TIES_TO_AWAY),
            bitsOfU64(0x7c00, 16));
  EXPECT_EQ(convert("65520.0", 5, 11, ROUND_TOWARD_POSITIVE),
            bitsOfU64(0x7c00, 16));
  EXPECT_EQ(convert("65520.0", 5, 11, ROUND_TOWARD_NEGATIVE),
            bitsOfU64(0x7bff, 16));
  EXPECT_EQ(convert("65520.0", 5, 11, ROUND_TOWARD_ZERO),
            bitsOfU64(0x7bff, 16));
}

TEST(DecimalToFP, subnormalsFloat16)
{
  const std::string minSub = "0.000000059604644775390625";      // 2^-24
  const std::string halfSub = "0.0000000298023223876953125";    // 2^-25
  EXPECT_EQ(convert(minSub, 5, 11, ROUND_NEAREST_TIES_TO_EVEN),
            bitsOfU64(0x0001, 16));
  // Half the smallest subnormal is a tie between it and zero.
  EXPECT_EQ(convert(halfSub, 5, 11, ROUND_NEAREST_TIES_TO_EVEN),
            bitsOfU64(0x0000, 16));
  EXPECT_EQ(convert(halfSub, 5, 11, ROUND_NEAREST_TIES_TO_AWAY),
            bitsOfU64(0x0001, 16));
  EXPECT_EQ(convert(halfSub, 5, 11, ROUND_TOWARD_POSITIVE),
            bitsOfU64(0x0001, 16));
  // Rounding a positive value down to nothing gives +zero, not -zero.
  EXPECT_EQ(convert(halfSub, 5, 11, ROUND_TOWARD_NEGATIVE),
            bitsOfU64(0x0000, 16));
  EXPECT_EQ(convert(halfSub, 5, 11, ROUND_TOWARD_ZERO),
            bitsOfU64(0x0000, 16));
}

TEST(DecimalToFP, spellingsOfTheSameValue)
{
  const std::string expected = convert("1.5", 8, 24,
                                       ROUND_NEAREST_TIES_TO_EVEN);
  EXPECT_EQ(convert("1.50", 8, 24, ROUND_NEAREST_TIES_TO_EVEN), expected);
  EXPECT_EQ(convert("1.5000000000000000000000000000000", 8, 24,
                    ROUND_NEAREST_TIES_TO_EVEN),
            expected);
  // Not legal SMT-LIB (numerals have no leading zeros), but STP's lexer is
  // historically lenient; the conversion must not care either.
  EXPECT_EQ(convert("0001.5", 8, 24, ROUND_NEAREST_TIES_TO_EVEN), expected);
}

TEST(DecimalToFP, wideFormat)
{
  // Float128: the packed pattern no longer fits a machine word, so build
  // the expectation from its fields: 1.5 = sign 0, biased exponent 16383,
  // significand 100...0.
  const std::string expected =
      "0" + bitsOfU64(16383, 15) + "1" + std::string(111, '0');
  EXPECT_EQ(convert("1.5", 15, 113, ROUND_NEAREST_TIES_TO_EVEN), expected);
  EXPECT_EQ(convert("0.5", 15, 113, ROUND_NEAREST_TIES_TO_EVEN),
            "0" + bitsOfU64(16382, 15) + std::string(112, '0'));
}

TEST(DecimalToFP, negativesAgreeWithHost)
{
  const char* cases[] = {
      "-1.5", "-0.1", "-123.456", "-16777217.0", "-65504.0",
      "-340282366920938463463374607431768211456.0", // -2^128: -oo under RNE
      "1", "2", "16777217", "-7",                   // bare numerals
  };
  for (const char* c : cases)
  {
    EXPECT_EQ(convert(c, 8, 24, ROUND_NEAREST_TIES_TO_EVEN), hostFloatBits(c))
        << c;
    EXPECT_EQ(convert(c, 11, 53, ROUND_NEAREST_TIES_TO_EVEN),
              hostDoubleBits(c))
        << c;
  }
}

TEST(DecimalToFP, negativeDirectedModesFlip)
{
  // 0.1 in Float16 rounds up only under RTP; negating the value swaps the
  // directed modes: -0.1 rounds "up" in magnitude only under RTN.
  EXPECT_EQ(convert("-0.1", 5, 11, ROUND_NEAREST_TIES_TO_EVEN),
            bitsOfU64(0xae66, 16));
  EXPECT_EQ(convert("-0.1", 5, 11, ROUND_NEAREST_TIES_TO_AWAY),
            bitsOfU64(0xae66, 16));
  EXPECT_EQ(convert("-0.1", 5, 11, ROUND_TOWARD_POSITIVE),
            bitsOfU64(0xae66, 16));
  EXPECT_EQ(convert("-0.1", 5, 11, ROUND_TOWARD_NEGATIVE),
            bitsOfU64(0xae67, 16));
  EXPECT_EQ(convert("-0.1", 5, 11, ROUND_TOWARD_ZERO),
            bitsOfU64(0xae66, 16));
  // And the negative side of the 2^-25 subnormal tie: the inexact
  // underflow keeps the sign, so the zeros here are -zero (0x8000).
  const std::string negHalfSub = "-0.0000000298023223876953125";
  EXPECT_EQ(convert(negHalfSub, 5, 11, ROUND_NEAREST_TIES_TO_EVEN),
            bitsOfU64(0x8000, 16));
  EXPECT_EQ(convert(negHalfSub, 5, 11, ROUND_NEAREST_TIES_TO_AWAY),
            bitsOfU64(0x8001, 16));
  EXPECT_EQ(convert(negHalfSub, 5, 11, ROUND_TOWARD_POSITIVE),
            bitsOfU64(0x8000, 16));
  EXPECT_EQ(convert(negHalfSub, 5, 11, ROUND_TOWARD_NEGATIVE),
            bitsOfU64(0x8001, 16));
  EXPECT_EQ(convert(negHalfSub, 5, 11, ROUND_TOWARD_ZERO),
            bitsOfU64(0x8000, 16));
}

TEST(DecimalToFP, exactZeroHasNoSign)
{
  // The real zero has no sign: "(- 0.0)" is the same real as "0.0", and
  // to_fp of it is +zero -- all-zero bits -- under every mode.
  EXPECT_EQ(convert("-0.0", 8, 24, ROUND_NEAREST_TIES_TO_EVEN),
            bitsOfU64(0, 32));
  EXPECT_EQ(convert("-0.000", 8, 24, ROUND_TOWARD_NEGATIVE),
            bitsOfU64(0, 32));
  EXPECT_EQ(convert("-0", 8, 24, ROUND_TOWARD_ZERO), bitsOfU64(0, 32));
  std::string bits, err;
  ASSERT_TRUE(rationalToPackedFPBits("0", "7", true, 8, 24,
                                     ROUND_TOWARD_NEGATIVE, bits, err))
      << err;
  EXPECT_EQ(bits, bitsOfU64(0, 32));
}

std::string convertRational(const std::string& p, const std::string& q,
                            bool neg, unsigned eb, unsigned sb, unsigned rm)
{
  std::string bits, err;
  const bool ok = rationalToPackedFPBits(p, q, neg, eb, sb, rm, bits, err);
  EXPECT_TRUE(ok) << "(/ " << p << " " << q << "): " << err;
  return ok ? bits : "";
}

TEST(DecimalToFP, rationalsAgreeWithHostDivision)
{
  // Hardware division is itself IEEE correctly rounded, so p/q computed
  // in float or double is the RNE oracle for the rational spelling.
  const std::pair<const char*, const char*> cases[] = {
      {"1", "3"},   {"2", "4"},     {"24", "65"},      {"355", "113"},
      {"10", "7"},  {"1", "10"},    {"7", "1"},        {"123456", "999"},
      {"1", "16777217"}, {"999999999", "7"},
  };
  for (const auto& c : cases)
  {
    const double pd = strtod(c.first, nullptr);
    const double qd = strtod(c.second, nullptr);
    // The float oracle is only an oracle when both components are exact
    // in float: casting 16777217 to float rounds the *operand* before
    // the division, and the engine (correctly) disagrees with that.
    if ((double)(float)pd == pd && (double)(float)qd == qd)
    {
      const float f = (float)pd / (float)qd;
      uint32_t fu;
      memcpy(&fu, &f, 4);
      EXPECT_EQ(convertRational(c.first, c.second, false, 8, 24,
                                ROUND_NEAREST_TIES_TO_EVEN),
                bitsOfU64(fu, 32))
          << c.first << "/" << c.second;
    }
    // Every pair here is double-exact, so the double leg always applies.
    const double d = pd / qd;
    uint64_t du;
    memcpy(&du, &d, 8);
    EXPECT_EQ(convertRational(c.first, c.second, false, 11, 53,
                              ROUND_NEAREST_TIES_TO_EVEN),
              bitsOfU64(du, 64))
        << c.first << "/" << c.second;
  }
}

TEST(DecimalToFP, rationalDirectedModes)
{
  // 1/3 = 0.0101...(01) binary: the nearest float32 is above the value,
  // so RNE and RTP land on ...ab, the downward modes on ...aa; negation
  // swaps the directed pair.
  EXPECT_EQ(convertRational("1", "3", false, 8, 24,
                            ROUND_NEAREST_TIES_TO_EVEN),
            bitsOfU64(0x3eaaaaab, 32));
  EXPECT_EQ(convertRational("1", "3", false, 8, 24, ROUND_TOWARD_POSITIVE),
            bitsOfU64(0x3eaaaaab, 32));
  EXPECT_EQ(convertRational("1", "3", false, 8, 24, ROUND_TOWARD_NEGATIVE),
            bitsOfU64(0x3eaaaaaa, 32));
  EXPECT_EQ(convertRational("1", "3", false, 8, 24, ROUND_TOWARD_ZERO),
            bitsOfU64(0x3eaaaaaa, 32));
  EXPECT_EQ(convertRational("1", "3", true, 8, 24,
                            ROUND_NEAREST_TIES_TO_EVEN),
            bitsOfU64(0xbeaaaaab, 32));
  EXPECT_EQ(convertRational("1", "3", true, 8, 24, ROUND_TOWARD_POSITIVE),
            bitsOfU64(0xbeaaaaaa, 32));
  EXPECT_EQ(convertRational("1", "3", true, 8, 24, ROUND_TOWARD_NEGATIVE),
            bitsOfU64(0xbeaaaaab, 32));
}

TEST(DecimalToFP, rationalDecimalComponentsScale)
{
  // (/ 1.2 3.25) is (/ 120 325) is (/ 24 65): decimal components only
  // shift powers of ten between numerator and denominator.
  for (unsigned rm : {ROUND_NEAREST_TIES_TO_EVEN, ROUND_TOWARD_POSITIVE,
                      ROUND_TOWARD_NEGATIVE, ROUND_TOWARD_ZERO,
                      ROUND_NEAREST_TIES_TO_AWAY})
  {
    EXPECT_EQ(convertRational("1.2", "3.25", false, 5, 11, rm),
              convertRational("120", "325", false, 5, 11, rm));
    EXPECT_EQ(convertRational("1.2", "3.25", false, 5, 11, rm),
              convertRational("24", "65", false, 5, 11, rm));
  }
}

TEST(DecimalToFP, rationalRefusals)
{
  std::string bits, err;
  EXPECT_FALSE(rationalToPackedFPBits("1", "0", false, 8, 24,
                                      ROUND_NEAREST_TIES_TO_EVEN, bits, err));
  EXPECT_NE(err.find("must not be zero"), std::string::npos) << err;
  err.clear();
  EXPECT_FALSE(rationalToPackedFPBits("1", "0.000", false, 8, 24,
                                      ROUND_NEAREST_TIES_TO_EVEN, bits, err));
  EXPECT_NE(err.find("must not be zero"), std::string::npos) << err;
  err.clear();
  EXPECT_FALSE(rationalToPackedFPBits("1.2.3", "5", false, 8, 24,
                                      ROUND_NEAREST_TIES_TO_EVEN, bits, err));
  EXPECT_NE(err.find("malformed"), std::string::npos) << err;
}

TEST(DecimalToFP, unsupportedExponentWidths)
{
  std::string bits, err;
  // SMT-LIB allows exponent width 2; LibBF's flag encoding starts at 3.
  EXPECT_FALSE(decimalToPackedFPBits("1.5", 2, 8,
                                     ROUND_NEAREST_TIES_TO_EVEN, bits, err));
  EXPECT_NE(err.find("exponent widths"), std::string::npos) << err;
  // And ends at LIMB_BITS - 3 (61 on 64-bit builds, 29 on 32-bit ones).
  err.clear();
  EXPECT_FALSE(decimalToPackedFPBits("1.5", 62, 8,
                                     ROUND_NEAREST_TIES_TO_EVEN, bits, err));
  EXPECT_NE(err.find("exponent widths"), std::string::npos) << err;
}

TEST(PackedFpBinaryOp, exactArithmeticAndCancellation)
{
  const std::string one = bitsOfU64(0x3c00, 16);
  const std::string onePointFive = bitsOfU64(0x3e00, 16);
  const std::string two = bitsOfU64(0x4000, 16);

  EXPECT_EQ(binary(onePointFive, two, 5, 11, ROUND_NEAREST_TIES_TO_EVEN,
                   PackedFpBinaryOp::Add),
            bitsOfU64(0x4300, 16)); // 3.5
  EXPECT_EQ(binary(two, onePointFive, 5, 11,
                   ROUND_NEAREST_TIES_TO_EVEN,
                   PackedFpBinaryOp::Subtract),
            bitsOfU64(0x3800, 16)); // 0.5
  EXPECT_EQ(binary(onePointFive, two, 5, 11,
                   ROUND_NEAREST_TIES_TO_EVEN,
                   PackedFpBinaryOp::Multiply),
            bitsOfU64(0x4200, 16)); // 3.0

  EXPECT_EQ(binary(one, one, 5, 11, ROUND_NEAREST_TIES_TO_EVEN,
                   PackedFpBinaryOp::Subtract),
            bitsOfU64(0x0000, 16));
  EXPECT_EQ(binary(one, one, 5, 11, ROUND_TOWARD_NEGATIVE,
                   PackedFpBinaryOp::Subtract),
            bitsOfU64(0x8000, 16));
}

TEST(PackedFpBinaryOp, underflowUsesTheRequestedRoundingMode)
{
  const std::string minSub = bitsOfU64(0x0001, 16);
  const std::string minusMinSub = bitsOfU64(0x8001, 16);
  const std::string half = bitsOfU64(0x3800, 16);

  EXPECT_EQ(binary(minSub, half, 5, 11, ROUND_NEAREST_TIES_TO_EVEN,
                   PackedFpBinaryOp::Multiply),
            bitsOfU64(0x0000, 16));
  EXPECT_EQ(binary(minSub, half, 5, 11, ROUND_NEAREST_TIES_TO_AWAY,
                   PackedFpBinaryOp::Multiply),
            minSub);
  EXPECT_EQ(binary(minSub, half, 5, 11, ROUND_TOWARD_POSITIVE,
                   PackedFpBinaryOp::Multiply),
            minSub);
  EXPECT_EQ(binary(minusMinSub, half, 5, 11, ROUND_TOWARD_POSITIVE,
                   PackedFpBinaryOp::Multiply),
            bitsOfU64(0x8000, 16));
  EXPECT_EQ(binary(minusMinSub, half, 5, 11, ROUND_TOWARD_NEGATIVE,
                   PackedFpBinaryOp::Multiply),
            minusMinSub);
}

TEST(PackedFpBinaryOp, overflowUsesTheRequestedRoundingMode)
{
  const std::string maxFinite = bitsOfU64(0x7bff, 16);
  const std::string two = bitsOfU64(0x4000, 16);
  EXPECT_EQ(binary(maxFinite, two, 5, 11, ROUND_NEAREST_TIES_TO_EVEN,
                   PackedFpBinaryOp::Multiply),
            bitsOfU64(0x7c00, 16));
  EXPECT_EQ(binary(maxFinite, two, 5, 11, ROUND_TOWARD_POSITIVE,
                   PackedFpBinaryOp::Multiply),
            bitsOfU64(0x7c00, 16));
  EXPECT_EQ(binary(maxFinite, two, 5, 11, ROUND_TOWARD_NEGATIVE,
                   PackedFpBinaryOp::Multiply),
            maxFinite);
  EXPECT_EQ(binary(maxFinite, two, 5, 11, ROUND_TOWARD_ZERO,
                   PackedFpBinaryOp::Multiply),
            maxFinite);
}

TEST(PackedFpBinaryOp, signedZerosArePreserved)
{
  const std::string minusZero = bitsOfU64(0x8000, 16);
  const std::string two = bitsOfU64(0x4000, 16);
  const std::string minusTwo = bitsOfU64(0xc000, 16);
  EXPECT_EQ(binary(minusZero, two, 5, 11, ROUND_NEAREST_TIES_TO_EVEN,
                   PackedFpBinaryOp::Multiply),
            minusZero);
  EXPECT_EQ(binary(minusZero, minusTwo, 5, 11,
                   ROUND_NEAREST_TIES_TO_EVEN,
                   PackedFpBinaryOp::Multiply),
            bitsOfU64(0x0000, 16));
}

TEST(PackedFpBinaryOp, rejectsMalformedAndNonfiniteInputs)
{
  const std::string one = bitsOfU64(0x3c00, 16);
  std::string bits, err;
  EXPECT_FALSE(packedFPBinaryOp(bitsOfU64(0x7c00, 16), one, 5, 11,
                                ROUND_NEAREST_TIES_TO_EVEN,
                                PackedFpBinaryOp::Add, bits, err));
  EXPECT_NE(err.find("finite operands"), std::string::npos) << err;
  err.clear();
  EXPECT_FALSE(packedFPBinaryOp("000000000000000x", one, 5, 11,
                                ROUND_NEAREST_TIES_TO_EVEN,
                                PackedFpBinaryOp::Add, bits, err));
  EXPECT_NE(err.find("non-bit"), std::string::npos) << err;
  err.clear();
  EXPECT_FALSE(packedFPBinaryOp("0", one, 5, 11,
                                ROUND_NEAREST_TIES_TO_EVEN,
                                PackedFpBinaryOp::Add, bits, err));
  EXPECT_NE(err.find("wrong width"), std::string::npos) << err;
}

} // namespace

/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August 2026
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

#include "stp/FloatBlaster/DecimalLiteral.h"

#include "stp/FloatBlaster/rounding_modes.h"

#include <cassert>
#include <sstream>

// Angle brackets on purpose: the header resolves through the SYSTEM
// include path the top-level LibBF block adds, which keeps its
// GNU-isms -- __int128 under -pedantic -- out of STP's -Werror.
extern "C"
{
#include <libbf.h>
}

#include <cstdlib>

namespace stp
{

namespace
{

// The context callback LibBF routes every allocation through; the same
// wrapper its own test programs use.
void* bfRealloc(void* opaque, void* ptr, size_t size)
{
  (void)opaque;
  return realloc(ptr, size);
}

// Bit i of the mantissa, i = 0 being the leading 1 LibBF normalises to the
// top of the highest limb. Bits past the stored limbs read as zero: LibBF
// keeps only as many limbs as the value needs, so an exact short value --
// "1.5" at 53 bits of precision -- stores one limb, not ceil(53/64).
int mantissaBit(const bf_t* v, int64_t i)
{
  const int64_t pos = (int64_t)v->len * LIMB_BITS - 1 - i;
  if (pos < 0)
    return 0;
  return (v->tab[pos / LIMB_BITS] >> (pos % LIMB_BITS)) & 1;
}

int bfRounding(unsigned rounding_mode)
{
  switch (rounding_mode)
  {
    case symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN: return BF_RNDN;
    case symbolic_fp::ROUND_NEAREST_TIES_TO_AWAY: return BF_RNDNA;
    case symbolic_fp::ROUND_TOWARD_POSITIVE: return BF_RNDU;
    case symbolic_fp::ROUND_TOWARD_NEGATIVE: return BF_RNDD;
    case symbolic_fp::ROUND_TOWARD_ZERO: return BF_RNDZ;
  }
  assert(false && "not a one-hot rounding mode");
  return BF_RNDN;
}

// LibBF encodes the exponent-field width in its operation flags, and the
// encodable range is [BF_EXP_BITS_MIN, BF_EXP_BITS_MAX] -- [3, 61] with
// 64-bit limbs, [3, 29] with 32-bit ones. SMT-LIB additionally allows
// exp_width 2, which therefore cannot be folded; every format anyone
// computes with is far inside the range.
bool checkFormat(unsigned exp_width, unsigned sig_width, std::string& err)
{
  if (exp_width < BF_EXP_BITS_MIN || exp_width > BF_EXP_BITS_MAX)
  {
    std::ostringstream os;
    os << "real literals are supported for floating-point exponent widths "
          "from "
       << BF_EXP_BITS_MIN << " to " << BF_EXP_BITS_MAX
       << " bits (this format has " << exp_width
       << "); write the value as its packed bits instead, e.g. "
          "((_ to_fp 8 24) #x3fc00000) for 1.5";
    err = os.str();
    return false;
  }
  if (sig_width < BF_PREC_MIN)
  {
    err = "a floating-point format needs at least 2 significand bits";
    return false;
  }
  return true;
}

// True iff the digits spell exactly zero ("0", "0.000", "000.0"): the one
// input whose float sign SMT-LIB pins (the real zero has no sign, and
// to_fp of it is +zero), so callers strip a minus when this holds.
bool magnitudeIsZero(const std::string& s)
{
  for (const char c : s)
    if (c != '0' && c != '.')
      return false;
  return true;
}

// Pack an already-rounded value -- bf_atof or bf_div left it exactly
// representable in (exp_width, sig_width) -- into the sign, biased
// exponent and stored significand fields. Pure bit extraction: no
// rounding happens here.
void packToBits(const bf_t* v, unsigned exp_width, unsigned sig_width,
                std::string& bits)
{
  const unsigned total = exp_width + sig_width;
  bits.assign(total, '0');
  bits[0] = v->sign ? '1' : '0';

  if (v->expn == BF_EXP_ZERO)
  {
    // Zero keeps only its sign: +zero from an exact zero (the callers
    // stripped the minus), either sign from an inexact underflow, where
    // IEEE keeps the sign of the exact value.
  }
  else if (v->expn == BF_EXP_INF)
  {
    // Overflow. LibBF already made the IEEE per-mode choice (its
    // bf_set_overflow): the nearest modes and the away-side directed mode
    // land here; round-toward-zero and the toward-side directed mode
    // instead produced the largest finite value and take the branch
    // below.
    for (unsigned j = 0; j < exp_width; j++)
      bits[1 + j] = '1';
  }
  else
  {
    // LibBF stores value = 0.1mmm... * 2^expn; IEEE stores
    // 1.mmm... * 2^e with a bias, so the biased exponent is
    // expn - 1 + bias. The same off-by-one bf_get_float64 applies for
    // float64; this is that packing for arbitrary widths.
    const int64_t bias = (int64_t)(((uint64_t)1 << (exp_width - 1)) - 1);
    int64_t e = (int64_t)v->expn + bias - 1;

    // e <= 0 is a subnormal: the field keeps exponent 0 and the
    // significand keeps the leading 1, pushed 1 - e places down.
    int64_t shift = 0;
    if (e <= 0)
    {
      shift = 1 - e;
      e = 0;
    }

    // Finite values never reach the all-ones field: LibBF's overflow
    // handling caps the exponent at the format maximum, which packs to
    // all-ones minus one.
    assert(e < (int64_t)(((uint64_t)1 << exp_width) - 1));

    for (unsigned j = 0; j < exp_width; j++)
      if ((((uint64_t)e) >> (exp_width - 1 - j)) & 1)
        bits[1 + j] = '1';

    // Stored significand: for a normal number the bits after the hidden
    // leading 1; for a subnormal, shift - 1 zeros and then the mantissa
    // from its leading 1 on. Bits the rounding already zeroed (LibBF
    // reduces a subnormal's effective precision) read back as zero.
    for (unsigned j = 0; j + 1 < sig_width; j++)
    {
      const int64_t i = (int64_t)j + 1 - shift;
      if (i >= 0 && mantissaBit(v, i))
        bits[1 + exp_width + j] = '1';
    }
  }
}

// Reconstruct a finite packed IEEE value as an exact LibBF dyadic. Parsing
// the significand as a base-two integer and applying its power-of-two scale
// avoids both host precision and a decimal round trip.
bool unpackFiniteBits(const std::string& bits, unsigned exp_width,
                      unsigned sig_width, bf_t* value, std::string& err)
{
  const unsigned width = exp_width + sig_width;
  if (bits.size() != width)
  {
    err = "a packed floating-point operand has the wrong width";
    return false;
  }
  for (const char c : bits)
    if (c != '0' && c != '1')
    {
      err = "a packed floating-point operand contains a non-bit character";
      return false;
    }

  uint64_t exponent = 0;
  for (unsigned i = 0; i < exp_width; i++)
    exponent = (exponent << 1) | static_cast<uint64_t>(bits[1 + i] - '0');
  const uint64_t max_exponent =
      (static_cast<uint64_t>(1) << exp_width) - 1;
  if (exponent == max_exponent)
  {
    err = "packedFPBinaryOp requires finite operands";
    return false;
  }

  const std::string fraction = bits.substr(1 + exp_width);
  bool fraction_nonzero = false;
  for (const char c : fraction)
    fraction_nonzero = fraction_nonzero || c == '1';
  if (exponent == 0 && !fraction_nonzero)
  {
    bf_set_zero(value, bits[0] == '1');
    return true;
  }

  std::string significand;
  if (bits[0] == '1')
    significand.push_back('-');
  significand.push_back(exponent == 0 ? '0' : '1');
  significand += fraction;

  const char* next = nullptr;
  int status = bf_atof(value, significand.c_str(), &next, 2, BF_PREC_INF,
                       BF_RNDZ | BF_ATOF_NO_NAN_INF);
  if ((status & (BF_ST_MEM_ERROR | BF_ST_INEXACT)) != 0 ||
      next != significand.c_str() + significand.size())
  {
    err = "failed to reconstruct a packed floating-point operand";
    return false;
  }

  const int64_t bias =
      (static_cast<int64_t>(1) << (exp_width - 1)) - 1;
  const int64_t unbiased = exponent == 0
                               ? 1 - bias
                               : static_cast<int64_t>(exponent) - bias;
  const int64_t scale = unbiased - static_cast<int64_t>(sig_width - 1);
  status = bf_mul_2exp(value, static_cast<slimb_t>(scale), BF_PREC_INF,
                       BF_RNDZ);
  if ((status & (BF_ST_MEM_ERROR | BF_ST_INEXACT)) != 0)
  {
    err = "failed to scale a packed floating-point operand";
    return false;
  }
  return true;
}

} // namespace

bool decimalToPackedFPBits(const std::string& decimal, unsigned exp_width,
                           unsigned sig_width, unsigned rounding_mode,
                           std::string& bits, std::string& err)
{
  if (!checkFormat(exp_width, sig_width, err))
    return false;

  // "(- 0.0)" is the real number zero, and SMT-LIB gives the real zero
  // +zero; strip the minus before LibBF can turn it into -zero. An
  // inexact underflow of a negative value still lands on -zero below,
  // which is IEEE: only the exact zero has its sign pinned.
  const std::string* input = &decimal;
  std::string stripped;
  if (!decimal.empty() && decimal[0] == '-' &&
      magnitudeIsZero(decimal.substr(1)))
  {
    stripped = decimal.substr(1);
    input = &stripped;
  }

  bf_context_t ctx;
  bf_context_init(&ctx, bfRealloc, nullptr);
  bf_t v;
  bf_init(&ctx, &v);

  // One call does the whole conversion: bf_atof reads the decimal exactly
  // and rounds once into (exp_width, sig_width) -- precision sig_width,
  // IEEE exponent range, subnormals on -- under the requested mode. What
  // remains is pure bit extraction; no rounding happens in STP.
  const bf_flags_t flags = (bf_flags_t)bfRounding(rounding_mode) |
                           bf_set_exp_bits((int)exp_width) |
                           BF_FLAG_SUBNORMAL;
  const char* next = nullptr;
  const int status =
      bf_atof(&v, input->c_str(), &next, 10, (limb_t)sig_width, flags);

  bool ok = false;
  if ((status & BF_ST_MEM_ERROR) != 0)
  {
    err = "out of memory while converting a real literal";
  }
  else if (next != input->c_str() + input->size() || bf_is_nan(&v))
  {
    // The parser only feeds digits, an optional single '.', and an
    // optional leading '-' through here, so anything bf_atof leaves
    // unconsumed is a bug, not user input.
    err = "malformed real literal: '" + decimal + "'";
  }
  else
  {
    packToBits(&v, exp_width, sig_width, bits);
    ok = true;
  }

  bf_delete(&v);
  bf_context_end(&ctx);
  return ok;
}

bool rationalToPackedFPBits(const std::string& numerator,
                            const std::string& denominator, bool negative,
                            unsigned exp_width, unsigned sig_width,
                            unsigned rounding_mode, std::string& bits,
                            std::string& err)
{
  if (!checkFormat(exp_width, sig_width, err))
    return false;

  // The components are numerals or decimals -- digits with at most one
  // '.' and no sign (the parser handles the sign). Split each into its
  // digits and count of fractional places.
  const auto split = [](const std::string& s, std::string& digits,
                        size_t& frac) {
    frac = 0;
    bool seen_dot = false;
    for (const char c : s)
    {
      if (c == '.')
      {
        if (seen_dot)
          return false;
        seen_dot = true;
      }
      else if (c >= '0' && c <= '9')
      {
        digits += c;
        if (seen_dot)
          frac++;
      }
      else
      {
        return false;
      }
    }
    return !digits.empty();
  };

  std::string num_digits, den_digits;
  size_t num_frac = 0, den_frac = 0;
  if (!split(numerator, num_digits, num_frac) ||
      !split(denominator, den_digits, den_frac))
  {
    err = "malformed rational constant: (/ " + numerator + " " + denominator +
          ")";
    return false;
  }

  if (magnitudeIsZero(den_digits))
  {
    err = "the denominator of a rational constant must not be zero: (/ " +
          numerator + " " + denominator + ")";
    return false;
  }
  // The real zero has no sign; see decimalToPackedFPBits.
  if (magnitudeIsZero(num_digits))
    negative = false;

  // p/q with p = P * 10^-a and q = Q * 10^-b is (P * 10^b) / (Q * 10^a):
  // shift each side's fractional places onto the other as trailing
  // zeros, leaving a ratio of exact integers.
  std::string n_str = (negative ? "-" : "") + num_digits +
                      std::string(den_frac, '0');
  const std::string d_str = den_digits + std::string(num_frac, '0');

  bf_context_t ctx;
  bf_context_init(&ctx, bfRealloc, nullptr);
  bf_t n, d, v;
  bf_init(&ctx, &n);
  bf_init(&ctx, &d);
  bf_init(&ctx, &v);

  // The integers parse exactly (BF_PREC_INF is only usable without the
  // exponent-width flags, which is fine: no rounding happens here), and
  // then one bf_div rounds once into the format under the requested
  // mode -- the same single-rounding guarantee the decimal path gets
  // from bf_atof.
  const char* next = nullptr;
  int status = bf_atof(&n, n_str.c_str(), &next, 10, BF_PREC_INF, BF_RNDZ);
  bool ok = false;
  if ((status & (BF_ST_MEM_ERROR | BF_ST_INEXACT)) != 0 ||
      next != n_str.c_str() + n_str.size())
  {
    err = "failed to read the numerator of (/ " + numerator + " " +
          denominator + ")";
  }
  else if (((status = bf_atof(&d, d_str.c_str(), &next, 10, BF_PREC_INF,
                              BF_RNDZ)) &
            (BF_ST_MEM_ERROR | BF_ST_INEXACT)) != 0 ||
           next != d_str.c_str() + d_str.size())
  {
    err = "failed to read the denominator of (/ " + numerator + " " +
          denominator + ")";
  }
  else
  {
    const bf_flags_t flags = (bf_flags_t)bfRounding(rounding_mode) |
                             bf_set_exp_bits((int)exp_width) |
                             BF_FLAG_SUBNORMAL;
    status = bf_div(&v, &n, &d, (limb_t)sig_width, flags);
    if ((status & BF_ST_MEM_ERROR) != 0)
    {
      err = "out of memory while converting a rational constant";
    }
    else if (bf_is_nan(&v))
    {
      // Unreachable: the denominator was checked nonzero above.
      err = "internal error converting (/ " + numerator + " " + denominator +
            ")";
    }
    else
    {
      packToBits(&v, exp_width, sig_width, bits);
      ok = true;
    }
  }

  bf_delete(&v);
  bf_delete(&d);
  bf_delete(&n);
  bf_context_end(&ctx);
  return ok;
}

bool packedFPBinaryOp(const std::string& left, const std::string& right,
                      unsigned exp_width, unsigned sig_width,
                      unsigned rounding_mode, PackedFpBinaryOp operation,
                      std::string& bits, std::string& err)
{
  if (!checkFormat(exp_width, sig_width, err))
    return false;

  bf_context_t ctx;
  bf_context_init(&ctx, bfRealloc, nullptr);
  bf_t a, b, result;
  bf_init(&ctx, &a);
  bf_init(&ctx, &b);
  bf_init(&ctx, &result);

  bool ok = unpackFiniteBits(left, exp_width, sig_width, &a, err) &&
            unpackFiniteBits(right, exp_width, sig_width, &b, err);
  if (ok)
  {
    const bf_flags_t flags = (bf_flags_t)bfRounding(rounding_mode) |
                             bf_set_exp_bits((int)exp_width) |
                             BF_FLAG_SUBNORMAL;
    int status = 0;
    switch (operation)
    {
      case PackedFpBinaryOp::Add:
        status = bf_add(&result, &a, &b, (limb_t)sig_width, flags);
        break;
      case PackedFpBinaryOp::Subtract:
        status = bf_sub(&result, &a, &b, (limb_t)sig_width, flags);
        break;
      case PackedFpBinaryOp::Multiply:
        status = bf_mul(&result, &a, &b, (limb_t)sig_width, flags);
        break;
    }

    if ((status & BF_ST_MEM_ERROR) != 0)
    {
      err = "out of memory while evaluating a packed floating-point operation";
      ok = false;
    }
    else if (bf_is_nan(&result))
    {
      err = "a finite packed floating-point operation produced NaN";
      ok = false;
    }
    else
      packToBits(&result, exp_width, sig_width, bits);
  }

  bf_delete(&result);
  bf_delete(&b);
  bf_delete(&a);
  bf_context_end(&ctx);
  return ok;
}

} // namespace stp

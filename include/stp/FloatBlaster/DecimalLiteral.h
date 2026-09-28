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

#ifndef STP_FP_DECIMAL_LITERAL_H
#define STP_FP_DECIMAL_LITERAL_H

#include <string>

namespace stp
{

// Convert an SMT-LIB real constant to the packed bit pattern of
// (_ FloatingPoint exp_width sig_width) under a rounding mode, for
// ((_ to_fp e s) rm <real>). sig_width counts the hidden bit, as the sort
// does.
//
// `decimal` is digits with an optional single '.' and an optional leading
// '-', no exponent part: "1.5", "-0.1", "7". rounding_mode is one of the
// five one-hot symbolic_fp::rounding_modes values. The conversion is
// exactly rounded in the target format under that mode -- IEEE-754
// semantics throughout: subnormals, underflow to zero, and per-mode
// overflow (round-to-nearest overflows to infinity, round-toward-zero to
// the largest finite value, the directed modes to whichever of the two
// their direction picks). The real zero has no sign, so "0.0" and "-0.0"
// both convert to +zero, as SMT-LIB requires; an inexact underflow of a
// negative value still gives -zero, which is IEEE. A real constant can
// never produce NaN.
//
// On success returns true and fills `bits` with exp_width + sig_width
// characters of '0'/'1', most significant first: sign, biased exponent,
// stored significand. On failure -- an exponent width outside what the
// conversion supports, a malformed literal, or out of memory -- returns
// false with a diagnostic in `err`.
bool decimalToPackedFPBits(const std::string& decimal, unsigned exp_width,
                           unsigned sig_width, unsigned rounding_mode,
                           std::string& bits, std::string& err);

// The rational spelling of a real constant, (/ numerator denominator) for
// ((_ to_fp e s) rm (/ p q)), possibly negated as a whole. The components
// are numerals or decimals -- digits with at most one '.', no sign of
// their own -- and the value is numerator/denominator, negated when
// `negative`. The two exact integers behind the ratio are divided with a
// single correctly-rounded bf_div, so the result carries the same
// exactly-rounded, IEEE-throughout guarantees as decimalToPackedFPBits,
// same output convention, same failure convention; a zero denominator is
// refused (that is not a rational constant), and a zero numerator gives
// +zero whatever `negative` says, the real zero having no sign.
bool rationalToPackedFPBits(const std::string& numerator,
                            const std::string& denominator, bool negative,
                            unsigned exp_width, unsigned sig_width,
                            unsigned rounding_mode, std::string& bits,
                            std::string& err);

enum class PackedFpBinaryOp
{
  Add,
  Subtract,
  Multiply
};

// Evaluate one binary operation on two finite packed values exactly in the
// target format. Inputs and output use the same MSB-first packed-bit spelling
// as decimalToPackedFPBits. LibBF first reconstructs each input as an exact
// dyadic value, then performs a single target-format rounding under
// `rounding_mode`; host floating-point arithmetic is never involved. An
// IEEE overflow result may be infinity. NaN/infinity inputs, malformed bit
// strings, unsupported formats, and allocation failures return false.
bool packedFPBinaryOp(const std::string& left, const std::string& right,
                      unsigned exp_width, unsigned sig_width,
                      unsigned rounding_mode, PackedFpBinaryOp operation,
                      std::string& bits, std::string& err);

} // namespace stp

#endif

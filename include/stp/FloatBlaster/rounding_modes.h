/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: January 2021
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

// The one-hot rounding-mode encoding, split out of symbolic_fp.h so the
// parser (which builds rounding-mode constants whether or not the SymFPU
// backend is compiled in) does not drag in the SymFPU headers.

#ifndef STP_FP_ROUNDING_MODES_H
#define STP_FP_ROUNDING_MODES_H

namespace stp
{
namespace symbolic_fp
{

// A rounding mode is a one-hot 5-bit bitvector: one bit per IEEE mode, so
// an invalid mode is representable (all-zero, or multiple bits) and
// roundingMode::valid() can constrain a symbolic one. The public C API's
// VCRoundingMode mirrors these values.
enum rounding_modes
{
  ROUND_NEAREST_TIES_TO_EVEN = 1,
  ROUND_TOWARD_POSITIVE = ROUND_NEAREST_TIES_TO_EVEN << 1,
  ROUND_TOWARD_NEGATIVE = ROUND_TOWARD_POSITIVE << 1,
  ROUND_TOWARD_ZERO = ROUND_TOWARD_NEGATIVE << 1,
  ROUND_NEAREST_TIES_TO_AWAY = ROUND_TOWARD_ZERO << 1,
};

// Whether a 5-bit carrier value denotes a rounding mode at all. Twenty-seven
// of the thirty-two patterns denote nothing, so anything that reads a mode
// back out of a carrier -- a model value, a checker candidate -- has to ask
// rather than assume.
inline bool isRoundingModeEncoding(unsigned encoding)
{
  return encoding == ROUND_NEAREST_TIES_TO_EVEN ||
         encoding == ROUND_TOWARD_POSITIVE ||
         encoding == ROUND_TOWARD_NEGATIVE ||
         encoding == ROUND_TOWARD_ZERO ||
         encoding == ROUND_NEAREST_TIES_TO_AWAY;
}

} // namespace symbolic_fp
} // namespace stp

#endif

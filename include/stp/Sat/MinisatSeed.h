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

#ifndef STP_SAT_MINISATSEED_H
#define STP_SAT_MINISATSEED_H

#include <cstdint>

namespace stp
{

// The seed MiniSat's random generator (Solver::drand) is given for a
// random-seed option value. drand keeps the seed in a double and truncates
// seed * 1389796 / (2^31 - 1) into an int, which overflows above about
// 3.3e12, and a multiple of 2^31 - 1 turns the seed into 0, which it must
// never be; its range is [1, 2^31 - 2].
inline double minisatSeed(std::uint64_t seed)
{
  return 1.0 + static_cast<double>(seed % 2147483646u);
}

} // namespace stp

#endif

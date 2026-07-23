/********************************************************************
 * AUTHORS: Trevor Hansen, Andrew Teylu
 *
 * BEGIN DATE: July, 2026
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

// Bit-counting on 64-bit words. GCC and Clang have builtins for these;
// MSVC does not, so it gets equivalents built from what it does have.

#ifndef BITOPS_H_
#define BITOPS_H_

#include <cassert>
#include <cstdint>

#ifdef _MSC_VER
#include <intrin.h>
#endif

namespace stp
{

// Number of zero bits below the lowest set bit. Undefined at zero, as the
// builtin is.
inline unsigned countTrailingZeroes64(uint64_t v)
{
  assert(v != 0);
#ifdef _MSC_VER
  unsigned long index;
  _BitScanForward64(&index, v);
  return static_cast<unsigned>(index);
#else
  return static_cast<unsigned>(__builtin_ctzll(v));
#endif
}

// Number of zero bits above the highest set bit. Undefined at zero, as the
// builtin is. MSVC's scan returns the position of that bit instead, hence
// the subtraction.
inline unsigned countLeadingZeroes64(uint64_t v)
{
  assert(v != 0);
#ifdef _MSC_VER
  unsigned long index;
  _BitScanReverse64(&index, v);
  return static_cast<unsigned>(63 - index);
#else
  return static_cast<unsigned>(__builtin_clzll(v));
#endif
}

// MSVC's __popcnt64 is not used: it is emitted unconditionally, so it
// faults on CPUs without POPCNT. Count in software instead.
inline unsigned popCount64(uint64_t v)
{
#ifdef _MSC_VER
  v = v - ((v >> 1) & 0x5555555555555555ULL);
  v = (v & 0x3333333333333333ULL) + ((v >> 2) & 0x3333333333333333ULL);
  v = (v + (v >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
  return static_cast<unsigned>((v * 0x0101010101010101ULL) >> 56);
#else
  return static_cast<unsigned>(__builtin_popcountll(v));
#endif
}

} // namespace stp

#endif

// EOF

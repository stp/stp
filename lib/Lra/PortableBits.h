#ifndef STP_LRA_PORTABLE_BITS_H
#define STP_LRA_PORTABLE_BITS_H

#include <cstdint>

#if !defined(__GNUC__) && !defined(__clang__) && defined(_MSC_VER) &&        \
    (defined(_M_X64) || defined(_M_ARM64))
#include <intrin.h>
#define STP_LRA_MSVC_BIT_SCAN 1
#endif

// Whether the arithmetic lanes may compute in a 128-bit integer type. GCC and
// Clang have __int128 wherever they define __SIZEOF_INT128__, and dividing in
// it calls helpers (__divti3, __udivti3, __umodti3) from their runtime
// library. clang-cl defines the macro too, but links against the MSVC runtime,
// which has none of those helpers, so it takes the 64-bit path cl.exe takes.
#if defined(__SIZEOF_INT128__) && !defined(_MSC_VER)
#define STP_LRA_HAVE_WIDE 1
#endif

namespace stp::lra {

// Bit scans for the machine-word lanes. GCC and Clang use their builtins;
// MSVC has none and uses its bit-scan intrinsics, and any other compiler the
// written-out forms below.

namespace detail {

// The written-out forms. Compiled on every target, so they are checked by
// the builds that use the builtins as well.

inline int portableCountLeadingZeros(std::uint64_t value) noexcept
{
  int count = 0;
  if ((value >> 32) == 0)
  {
    count += 32;
    value <<= 32;
  }
  if ((value >> 48) == 0)
  {
    count += 16;
    value <<= 16;
  }
  if ((value >> 56) == 0)
  {
    count += 8;
    value <<= 8;
  }
  if ((value >> 60) == 0)
  {
    count += 4;
    value <<= 4;
  }
  if ((value >> 62) == 0)
  {
    count += 2;
    value <<= 2;
  }
  if ((value >> 63) == 0)
    count += 1;
  return count;
}

inline int portableCountTrailingZeros(std::uint64_t value) noexcept
{
  int count = 0;
  if ((value & 0xFFFFFFFFU) == 0)
  {
    count += 32;
    value >>= 32;
  }
  if ((value & 0xFFFFU) == 0)
  {
    count += 16;
    value >>= 16;
  }
  if ((value & 0xFFU) == 0)
  {
    count += 8;
    value >>= 8;
  }
  if ((value & 0xFU) == 0)
  {
    count += 4;
    value >>= 4;
  }
  if ((value & 0x3U) == 0)
  {
    count += 2;
    value >>= 2;
  }
  if ((value & 0x1U) == 0)
    count += 1;
  return count;
}

}  // namespace detail

// The number of zero bits above the highest set bit. The value must not be
// zero.
inline int countLeadingZeros(std::uint64_t value) noexcept
{
#if defined(__GNUC__) || defined(__clang__)
  return __builtin_clzll(value);
#elif defined(STP_LRA_MSVC_BIT_SCAN)
  unsigned long index = 0;
  _BitScanReverse64(&index, value);
  return 63 - static_cast<int>(index);
#else
  return detail::portableCountLeadingZeros(value);
#endif
}

// The number of zero bits below the lowest set bit. The value must not be
// zero.
inline int countTrailingZeros(std::uint64_t value) noexcept
{
#if defined(__GNUC__) || defined(__clang__)
  return __builtin_ctzll(value);
#elif defined(STP_LRA_MSVC_BIT_SCAN)
  unsigned long index = 0;
  _BitScanForward64(&index, value);
  return static_cast<int>(index);
#else
  return detail::portableCountTrailingZeros(value);
#endif
}

}  // namespace stp::lra

#undef STP_LRA_MSVC_BIT_SCAN

#endif

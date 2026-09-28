#ifndef STP_LRA_STORAGE_CHECKED_CONVERSIONS_H
#define STP_LRA_STORAGE_CHECKED_CONVERSIONS_H

#include "Storage/StorageFailure.h"
#include "Storage/StorageMetrics.h"

#include <cstddef>
#include <cstdint>
#include <limits>
#include <vector>
#include <type_traits>

namespace stp::lra {

namespace detail {

// A template, so that the comparison below is never instantiated on a target
// where it cannot be true.  `if constexpr` in a non-template function still
// fully checks its discarded statement, and where From and To are the same
// width that check reads as a tautological comparison.
template <class To, class From>
inline To checkedNarrow(From value, char const* operation,
                        char const* message)
{
  if constexpr (sizeof(From) > sizeof(To))
  {
    if (value > static_cast<From>(std::numeric_limits<To>::max()))
    {
      throw StorageFailure(StorageFailureKind::ResourceLimit, operation,
                           message);
    }
  }
  return static_cast<To>(value);
}

}  // namespace detail

inline std::uint32_t checkedSizeToUint32(
    std::size_t value, char const* operation = "checkedSizeToUint32")
{
  if constexpr (sizeof(std::size_t) > sizeof(std::uint32_t))
  {
    if (value > static_cast<std::size_t>(
                    std::numeric_limits<std::uint32_t>::max()))
    {
      throw StorageFailure(StorageFailureKind::ResourceLimit, operation,
                           "size_t value is not representable as uint32_t");
    }
  }
  return static_cast<std::uint32_t>(value);
}

inline std::uint32_t checkedUint64ToUint32(
    std::uint64_t value, char const* operation = "checkedUint64ToUint32")
{
  if (value > std::numeric_limits<std::uint32_t>::max())
  {
    throw StorageFailure(StorageFailureKind::ResourceLimit, operation,
                         "uint64_t value is not representable as uint32_t");
  }
  return static_cast<std::uint32_t>(value);
}

inline std::uint64_t checkedSizeToUint64(
    std::size_t value, char const* operation = "checkedSizeToUint64")
{
  return detail::checkedNarrow<std::uint64_t>(
      value, operation, "size_t value is not representable as uint64_t");
}

inline std::size_t checkedUint64ToSize(
    std::uint64_t value, char const* operation = "checkedUint64ToSize")
{
  return detail::checkedNarrow<std::size_t>(
      value, operation, "uint64_t value is not representable as size_t");
}

template <class Difference>
std::size_t checkedDifferenceToSize(
    Difference value, char const* operation = "checkedDifferenceToSize")
{
  static_assert(std::is_integral_v<Difference>);
  if constexpr (std::is_signed_v<Difference>)
  {
    if (value < 0)
    {
      throw StorageFailure(StorageFailureKind::InvariantViolation, operation,
                           "negative container difference");
    }
  }
  using UnsignedDifference = std::make_unsigned_t<Difference>;
  UnsignedDifference const unsigned_value =
      static_cast<UnsignedDifference>(value);
  if constexpr (sizeof(UnsignedDifference) > sizeof(std::size_t))
  {
    if (unsigned_value > static_cast<UnsignedDifference>(
                             std::numeric_limits<std::size_t>::max()))
    {
      throw StorageFailure(StorageFailureKind::ResourceLimit, operation,
                           "container difference is not representable");
    }
  }
  return static_cast<std::size_t>(unsigned_value);
}

inline std::uint64_t checkedLogicalByteAdd(
    std::uint64_t lhs, std::uint64_t rhs,
    char const* operation = "checkedLogicalByteAdd")
{
  if (rhs > std::numeric_limits<std::uint64_t>::max() - lhs)
  {
    throw StorageFailure(StorageFailureKind::ResourceLimit, operation,
                         "logical byte addition overflow");
  }
  return lhs + rhs;
}

inline std::uint64_t checkedLogicalByteMultiply(
    std::uint64_t lhs, std::uint64_t rhs,
    char const* operation = "checkedLogicalByteMultiply")
{
  if (lhs != 0 && rhs > std::numeric_limits<std::uint64_t>::max() / lhs)
  {
    throw StorageFailure(StorageFailureKind::ResourceLimit, operation,
                         "logical byte multiplication overflow");
  }
  return lhs * rhs;
}

}  // namespace stp::lra

#endif

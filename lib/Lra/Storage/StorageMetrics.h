#ifndef STP_LRA_STORAGE_METRICS_H
#define STP_LRA_STORAGE_METRICS_H

#include <cstddef>
#include <cstdint>
#include <limits>
#include <type_traits>

namespace stp::lra {

struct StorageMetrics
{
  std::uint64_t generations_created;
  std::uint64_t generation_resets;
  std::uint64_t ids_allocated;
  std::uint64_t ordinal_exhaustions;
  std::uint64_t arena_values;
  std::uint64_t peak_arena_values;
  std::uint64_t logical_arena_bytes;
  std::uint64_t lookups;
  std::uint64_t stale_lookup_rejections;
  std::uint64_t invalid_ordinal_rejections;
  std::uint64_t checkpoints_created;
  std::uint64_t checkpoints_popped;
  std::uint64_t stale_checkpoint_rejections;
  std::uint64_t trail_appends;
  std::uint64_t vector_growths;
  std::uint64_t vector_resets;
  std::uint64_t dense_membership_resizes;
  std::uint64_t dense_membership_sets;
  std::uint64_t dense_membership_queries;
  std::uint64_t dense_membership_clears;
  std::uint64_t value_mutations;
  std::uint64_t presence_mutations;
  std::uint64_t trail_restorations;
  std::uint64_t sorts;
  std::uint64_t sort_attempts;
  std::uint64_t sort_successes;
  std::uint64_t sort_failures;
  std::uint64_t conversion_failures;
  std::uint64_t allocation_failures;
};

namespace detail {

inline void saturatingIncrement(std::uint64_t& value) noexcept
{
  if (value != std::numeric_limits<std::uint64_t>::max())
  {
    ++value;
  }
}

inline std::uint64_t saturatingAdd(std::uint64_t lhs,
                                   std::uint64_t rhs) noexcept
{
  std::uint64_t const maximum = std::numeric_limits<std::uint64_t>::max();
  return maximum - lhs < rhs ? maximum : lhs + rhs;
}

inline std::uint64_t saturatingMultiply(std::uint64_t lhs,
                                        std::uint64_t rhs) noexcept
{
  std::uint64_t const maximum = std::numeric_limits<std::uint64_t>::max();
  return lhs != 0 && rhs > maximum / lhs ? maximum : lhs * rhs;
}

template <class Size>
inline std::uint64_t saturatingIntegralSize(Size value) noexcept
{
  static_assert(std::is_unsigned_v<Size>);
  if constexpr (sizeof(Size) > sizeof(std::uint64_t))
  {
    if (value > static_cast<Size>(
                    std::numeric_limits<std::uint64_t>::max()))
    {
      return std::numeric_limits<std::uint64_t>::max();
    }
  }
  return static_cast<std::uint64_t>(value);
}

inline std::uint64_t saturatingSize(std::size_t value) noexcept
{
  return saturatingIntegralSize(value);
}

inline void observeMaximum(std::uint64_t& maximum,
                           std::uint64_t value) noexcept
{
  if (value > maximum)
  {
    maximum = value;
  }
}

}  // namespace detail
}  // namespace stp::lra

#endif

#ifndef STP_LRA_STORAGE_DENSE_MEMBERSHIP_H
#define STP_LRA_STORAGE_DENSE_MEMBERSHIP_H

#include "Storage/StorageMetrics.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

namespace stp::lra {

template <class Value>
class TrailedValueStorage;
namespace detail {
struct DenseMembershipTestAccess;
}

class DenseMembership final
{
 public:
  DenseMembership() = default;
  ~DenseMembership() noexcept = default;
  DenseMembership(DenseMembership const&) = default;
  DenseMembership& operator=(DenseMembership const&) = default;
  DenseMembership(DenseMembership&&) noexcept = default;
  DenseMembership& operator=(DenseMembership&&) noexcept = default;

  // Hold capacity for `count` so that a later ensureSize(count) cannot fail.
  void reserve(std::size_t count);
  void ensureSize(std::size_t count);
  void set(std::size_t index, bool value);
  bool test(std::size_t index) const;

  /* The trail-replay pair. Both assume the caller has already established
   * that the index or the size fits -- which the pop path does for the whole
   * journal slice before it undoes any of it -- so neither can fail, which is
   * what lets the replay run in place. */
  void setChecked(std::size_t index, bool value) noexcept;
  void shrinkToChecked(std::size_t count) noexcept;

  std::size_t size() const noexcept { return values_.size(); }
  std::size_t capacity() const noexcept { return values_.capacity(); }
  void clearValues() noexcept;
  void reset() noexcept;

  std::vector<std::uint8_t> const& bytes() const noexcept { return values_; }
  std::vector<std::size_t> activeIndices() const;
  StorageMetrics metrics() const noexcept { return metrics_; }
  void swap(DenseMembership& other) noexcept;

 private:

  std::vector<std::uint8_t> values_;
  mutable StorageMetrics metrics_{};

  template <class>
  friend class TrailedValueStorage;
  friend struct detail::DenseMembershipTestAccess;
};

std::string debugString(DenseMembership const& membership);

#if defined(STP_LRA_TEST_FAULT_INJECTION)
namespace detail {
struct DenseMembershipTestAccess
{
  static void corruptByte(DenseMembership& membership,
                          std::size_t index,
                          std::uint8_t value)
  {
    membership.values_.at(index) = value;
  }
};
}  // namespace detail
#endif

}  // namespace stp::lra

#endif

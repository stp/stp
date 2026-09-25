#include "Storage/DenseMembership.h"

#include "Storage/CheckedConversions.h"
#include "Storage/StorageFailure.h"

#include <algorithm>
#include <charconv>
#include <new>
#include <stdexcept>
#include <utility>

namespace stp::lra {

void DenseMembership::reserve(std::size_t count)
{
  try
  {
    values_.reserve(count);
  }
  catch (std::bad_alloc const&)
  {
    detail::saturatingIncrement(metrics_.allocation_failures);
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "DenseMembership::reserve",
                         "dense byte allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "DenseMembership::reserve",
                         "dense byte length limit");
  }
}

void DenseMembership::ensureSize(std::size_t count)
{
  if (count <= values_.size())
  {
    return;
  }
  if (count > values_.max_size())
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "DenseMembership::ensureSize",
                         "requested size exceeds vector maximum");
  }
  std::size_t const old_capacity = values_.capacity();
  try
  {
    values_.resize(count, std::uint8_t{0});
  }
  catch (std::bad_alloc const&)
  {
    detail::saturatingIncrement(metrics_.allocation_failures);
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "DenseMembership::ensureSize",
                         "dense byte allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "DenseMembership::ensureSize",
                         "dense byte length limit");
  }
  if (values_.capacity() != old_capacity)
  {
    detail::saturatingIncrement(metrics_.vector_growths);
  }
  detail::saturatingIncrement(metrics_.dense_membership_resizes);
}

void DenseMembership::set(std::size_t index, bool value)
{
  if (index >= values_.size())
  {
    throw StorageFailure(StorageFailureKind::OutOfRange,
                         "DenseMembership::set",
                         "dense membership index is out of range");
  }
  values_[index] = value ? std::uint8_t{1} : std::uint8_t{0};
  detail::saturatingIncrement(metrics_.dense_membership_sets);
}

bool DenseMembership::test(std::size_t index) const
{
  if (index >= values_.size())
  {
    throw StorageFailure(StorageFailureKind::OutOfRange,
                         "DenseMembership::test",
                         "dense membership index is out of range");
  }
  detail::saturatingIncrement(metrics_.dense_membership_queries);
  std::uint8_t const value = values_[index];
  if (value > 1U)
  {
    throw StorageFailure(StorageFailureKind::InvariantViolation,
                         "DenseMembership::test",
                         "dense membership byte is not zero or one");
  }
  return value != 0;
}

void DenseMembership::clearValues() noexcept
{
  std::fill(values_.begin(), values_.end(), std::uint8_t{0});
  detail::saturatingIncrement(metrics_.dense_membership_clears);
}

void DenseMembership::reset() noexcept
{
  std::vector<std::uint8_t>().swap(values_);
  detail::saturatingIncrement(metrics_.vector_resets);
}

void DenseMembership::swap(DenseMembership& other) noexcept
{
  values_.swap(other.values_);
  using std::swap;
  swap(metrics_, other.metrics_);
}

void DenseMembership::setChecked(std::size_t index, bool value) noexcept
{
  values_[index] = value ? std::uint8_t{1} : std::uint8_t{0};
  detail::saturatingIncrement(metrics_.dense_membership_sets);
}

void DenseMembership::shrinkToChecked(std::size_t count) noexcept
{
  values_.resize(count);
}


std::vector<std::size_t> DenseMembership::activeIndices() const
{
  std::vector<std::size_t> result;
  try
  {
    result.reserve(values_.size());
    for (std::size_t index = 0; index != values_.size(); ++index)
    {
      std::uint8_t const value = values_[index];
      if (value > 1U)
      {
        throw StorageFailure(StorageFailureKind::InvariantViolation,
                             "DenseMembership::activeIndices",
                             "dense membership byte is not zero or one");
      }
      if (value != 0)
      {
        result.push_back(index);
      }
    }
  }
  catch (std::bad_alloc const&)
  {
    detail::saturatingIncrement(metrics_.allocation_failures);
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "DenseMembership::activeIndices",
                         "canonical index allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "DenseMembership::activeIndices",
                         "canonical index length limit");
  }
  return result;
}

std::string debugString(DenseMembership const& membership)
{
  try
  {
    std::string result("membership[");
    bool first = true;
    for (std::size_t index : membership.activeIndices())
    {
      if (!first)
      {
        result.push_back(',');
      }
      first = false;
      char buffer[32];
      auto const converted = std::to_chars(
          buffer, buffer + sizeof(buffer), checkedSizeToUint64(index));
      if (converted.ec != std::errc{})
      {
        throw StorageFailure(StorageFailureKind::InternalError,
                             "debugString(DenseMembership)",
                             "integer formatting failed");
      }
      result.append(buffer, converted.ptr);
    }
    result.push_back(']');
    return result;
  }
  catch (std::bad_alloc const&)
  {
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "debugString(DenseMembership)",
                         "debug string allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "debugString(DenseMembership)",
                         "debug string length limit");
  }
}

}  // namespace stp::lra

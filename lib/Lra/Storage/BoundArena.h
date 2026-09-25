#ifndef STP_LRA_STORAGE_BOUND_ARENA_H
#define STP_LRA_STORAGE_BOUND_ARENA_H

#include "Storage/LraIds.h"
#include "Storage/StorageMetrics.h"

#include <cstddef>
#include <cstdint>
#include <deque>
#include <new>
#include <stdexcept>
#include <utility>

namespace stp::lra {

template <class Value>
class BoundArena final
{
 public:
  explicit BoundArena(CoreGeneration generation)
      : generation_(generation), ids_(generation), values_(), metrics_{}
  {
    metrics_.generations_created = 1;
  }
  ~BoundArena() noexcept = default;

  BoundArena(BoundArena const&) = delete;
  BoundArena& operator=(BoundArena const&) = delete;
  BoundArena(BoundArena&&) = delete;
  BoundArena& operator=(BoundArena&&) = delete;

  template <class... Args>
  BoundRef emplace(Args&&... args)
  {
    BoundRef prospective = preflightOrdinal();
    try
    {
      values_.emplace_back(std::forward<Args>(args)...);
    }
    catch (std::bad_alloc const&)
    {
      detail::saturatingIncrement(metrics_.allocation_failures);
      throw StorageFailure(StorageFailureKind::AllocationFailure,
                           "BoundArena::emplace", "deque allocation failed");
    }
    catch (std::length_error const&)
    {
      throw StorageFailure(StorageFailureKind::LengthError,
                           "BoundArena::emplace", "deque length limit");
    }

    ids_.commit(prospective);
    detail::saturatingIncrement(metrics_.ids_allocated);
    metrics_.arena_values = detail::saturatingSize(values_.size());
    detail::observeMaximum(metrics_.peak_arena_values, metrics_.arena_values);
    metrics_.logical_arena_bytes = logicalBytes();
    return prospective;
  }

  Value& at(BoundRef ref)
  {
    validateLookup(ref);
    return values_[ref.ordinal()];
  }

  Value const& at(BoundRef ref) const
  {
    validateLookup(ref);
    return values_[ref.ordinal()];
  }

  bool contains(BoundRef ref) const noexcept
  {
    detail::saturatingIncrement(metrics_.lookups);
    if (ref.generation() != generation_)
    {
      detail::saturatingIncrement(metrics_.stale_lookup_rejections);
      return false;
    }
    if (!ref.valid() || ref.ordinal() >= values_.size())
    {
      detail::saturatingIncrement(metrics_.invalid_ordinal_rejections);
      return false;
    }
    return true;
  }

  CoreGeneration generation() const noexcept { return generation_; }
  std::size_t size() const noexcept { return values_.size(); }
  bool empty() const noexcept { return values_.empty(); }
  std::uint64_t logicalBytes() const noexcept
  {
    return detail::saturatingMultiply(detail::saturatingSize(values_.size()),
                                      sizeof(Value));
  }
  StorageMetrics metrics() const noexcept { return metrics_; }

  void reset(CoreGeneration next_generation)
  {
    if (!isImmediateSuccessor(generation_, next_generation))
    {
      throw StorageFailure(StorageFailureKind::InvalidGeneration,
                           "BoundArena::reset",
                           "generation is not the immediate successor");
    }

    std::uint64_t const created = metrics_.generations_created;
    std::uint64_t const resets = metrics_.generation_resets;
    try
    {
      std::deque<Value> old_values;
      values_.swap(old_values);
    }
    catch (std::bad_alloc const&)
    {
      detail::saturatingIncrement(metrics_.allocation_failures);
      throw StorageFailure(StorageFailureKind::AllocationFailure,
                           "BoundArena::reset",
                           "replacement deque allocation failed");
    }
    catch (std::length_error const&)
    {
      throw StorageFailure(StorageFailureKind::LengthError,
                           "BoundArena::reset",
                           "replacement deque length limit");
    }
    ids_.reset(next_generation);
    generation_ = next_generation;
    metrics_ = {};
    metrics_.generations_created = created;
    detail::saturatingIncrement(metrics_.generations_created);
    metrics_.generation_resets = resets;
    detail::saturatingIncrement(metrics_.generation_resets);
  }

 private:
  BoundRef preflightOrdinal()
  {
    try
    {
      return ids_.preflight();
    }
    catch (StorageFailure const& failure)
    {
      if (failure.kind() == StorageFailureKind::ResourceLimit)
      {
        detail::saturatingIncrement(metrics_.ordinal_exhaustions);
      }
      throw;
    }
  }

  void validateLookup(BoundRef ref) const
  {
    detail::saturatingIncrement(metrics_.lookups);
    if (ref.generation() != generation_)
    {
      detail::saturatingIncrement(metrics_.stale_lookup_rejections);
      throw StorageFailure(StorageFailureKind::InvalidGeneration,
                           "BoundArena::at", "stale or foreign generation");
    }
    if (!ref.valid() || ref.ordinal() >= values_.size())
    {
      detail::saturatingIncrement(metrics_.invalid_ordinal_rejections);
      throw StorageFailure(StorageFailureKind::InvalidOrdinal,
                           "BoundArena::at", "ordinal is not allocated");
    }
  }

  CoreGeneration generation_;
  MonotonicIdAllocator<BoundRef> ids_;
  std::deque<Value> values_;
  mutable StorageMetrics metrics_;

  friend struct detail::StorageTestAccess;
};

#if defined(STP_LRA_TEST_FAULT_INJECTION)
template <class Value>
void detail::StorageTestAccess::setArenaNextOrdinal(
    BoundArena<Value>& arena, std::uint64_t value) noexcept
{
  arena.ids_.next_ordinal_ = value;
}
#endif

}  // namespace stp::lra

#endif

#ifndef STP_LRA_STORAGE_BOUND_ACTIVITY_TRAIL_H
#define STP_LRA_STORAGE_BOUND_ACTIVITY_TRAIL_H

#include "Storage/BoundArena.h"

#include <cstddef>
#include <cstdint>
#include <vector>

namespace stp::lra {

class BoundActivityTrail final
{
 public:
  explicit BoundActivityTrail(CoreGeneration generation);
  ~BoundActivityTrail() noexcept = default;
  BoundActivityTrail(BoundActivityTrail const&) = delete;
  BoundActivityTrail& operator=(BoundActivityTrail const&) = delete;
  BoundActivityTrail(BoundActivityTrail&&) = delete;
  BoundActivityTrail& operator=(BoundActivityTrail&&) = delete;

  Checkpoint push();
  void pop(Checkpoint checkpoint);

  template <class Value>
  void append(BoundRef ref, BoundArena<Value> const& arena)
  {
    if (ref.generation() != generation_ ||
        arena.generation() != generation_)
    {
      throw StorageFailure(StorageFailureKind::InvalidGeneration,
                           "BoundActivityTrail::append",
                           "trail, arena, and reference generations differ");
    }
    if (!arena.contains(ref))
    {
      throw StorageFailure(StorageFailureKind::InvalidOrdinal,
                           "BoundActivityTrail::append",
                           "reference is not allocated in the arena");
    }
    std::size_t const old_capacity = active_.capacity();
    try
    {
      active_.push_back(ref);
    }
    catch (std::bad_alloc const&)
    {
      detail::saturatingIncrement(metrics_.allocation_failures);
      throw StorageFailure(StorageFailureKind::AllocationFailure,
                           "BoundActivityTrail::append",
                           "active-reference allocation failed");
    }
    catch (std::length_error const&)
    {
      throw StorageFailure(StorageFailureKind::LengthError,
                           "BoundActivityTrail::append",
                           "active-reference length limit");
    }
    if (active_.capacity() != old_capacity)
    {
      detail::saturatingIncrement(metrics_.vector_growths);
    }
    detail::saturatingIncrement(metrics_.trail_appends);
  }

  std::vector<BoundRef> const& active() const noexcept { return active_; }
  std::size_t activeSize() const noexcept { return active_.size(); }
  std::size_t levelCount() const noexcept { return levels_.size(); }
  CoreGeneration generation() const noexcept { return generation_; }
  StorageMetrics metrics() const noexcept { return metrics_; }

  void clearToBase() noexcept;
  void reset(CoreGeneration next_generation);

 private:
  struct Level
  {
    std::uint32_t token;
    std::size_t active_size;
  };

  CoreGeneration generation_;
  std::uint64_t next_checkpoint_token_;
  std::vector<BoundRef> active_;
  std::vector<Level> levels_;
  StorageMetrics metrics_;

  friend struct detail::StorageTestAccess;
};

}  // namespace stp::lra

#endif

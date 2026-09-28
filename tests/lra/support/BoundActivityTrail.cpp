#include "BoundActivityTrail.h"

#include <algorithm>
#include <iterator>
#include <limits>
#include <new>
#include <stdexcept>
#include <utility>

namespace stp::lra {

BoundActivityTrail::BoundActivityTrail(CoreGeneration generation)
    : generation_(generation),
      next_checkpoint_token_(1),
      active_(),
      levels_(),
      metrics_{}
{
  if (!generation.valid())
  {
    throw StorageFailure(StorageFailureKind::InvalidGeneration,
                         "BoundActivityTrail", "invalid generation");
  }
  metrics_.generations_created = 1;
}

Checkpoint BoundActivityTrail::push()
{
  if (next_checkpoint_token_ >=
      std::numeric_limits<std::uint32_t>::max())
  {
    detail::saturatingIncrement(metrics_.ordinal_exhaustions);
    throw StorageFailure(StorageFailureKind::ResourceLimit,
                         "BoundActivityTrail::push",
                         "checkpoint token exhausted");
  }
  Level const level{static_cast<std::uint32_t>(next_checkpoint_token_),
                    active_.size()};
  std::size_t const old_capacity = levels_.capacity();
  try
  {
    levels_.push_back(level);
  }
  catch (std::bad_alloc const&)
  {
    detail::saturatingIncrement(metrics_.allocation_failures);
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "BoundActivityTrail::push",
                         "checkpoint allocation failed");
  }
  catch (std::length_error const&)
  {
    throw StorageFailure(StorageFailureKind::LengthError,
                         "BoundActivityTrail::push",
                         "checkpoint length limit");
  }
  ++next_checkpoint_token_;
  if (levels_.capacity() != old_capacity)
  {
    detail::saturatingIncrement(metrics_.vector_growths);
  }
  detail::saturatingIncrement(metrics_.checkpoints_created);
  return Checkpoint{generation_, level.token};
}

void BoundActivityTrail::pop(Checkpoint checkpoint)
{
  auto reject = [this](char const* detail_text) {
    detail::saturatingIncrement(metrics_.stale_checkpoint_rejections);
    throw StorageFailure(StorageFailureKind::InvalidCheckpoint,
                         "BoundActivityTrail::pop", detail_text);
  };
  if (checkpoint.generation != generation_ || checkpoint.depth == 0 ||
      checkpoint.depth >= next_checkpoint_token_ || levels_.empty())
  {
    reject("wrong generation, underflow, future, or stale token");
  }

  // From the top: a pop is almost always to the level just below it, and
  // the levels that stay were checked when they were pushed and by every
  // pop since. Only the levels being removed, and the join to the one
  // beneath them, are walked; a walk of the whole stack cost its depth on
  // every backtrack.
  auto const found_reverse = std::find_if(
      levels_.rbegin(), levels_.rend(),
      [checkpoint](Level const& level) { return level.token == checkpoint.depth; });
  if (found_reverse == levels_.rend())
  {
    reject("checkpoint token is not live");
  }
  auto const found = std::next(found_reverse).base();

  std::size_t previous_size = 0;
  std::uint32_t previous_token = 0;
  if (found != levels_.begin())
  {
    previous_token = std::prev(found)->token;
    previous_size = std::prev(found)->active_size;
  }
  for (auto level = found; level != levels_.end(); ++level)
  {
    if (level->token <= previous_token ||
        level->active_size < previous_size ||
        level->active_size > active_.size())
    {
      reject("corrupted live checkpoint stack");
    }
    previous_token = level->token;
    previous_size = level->active_size;
  }

  std::size_t const found_index =
      static_cast<std::size_t>(found - levels_.begin());
  while (active_.size() > found->active_size)
  {
    active_.pop_back();
  }
  while (levels_.size() > found_index)
  {
    levels_.pop_back();
  }
  detail::saturatingIncrement(metrics_.checkpoints_popped);
}

void BoundActivityTrail::clearToBase() noexcept
{
  active_.clear();
  levels_.clear();
}

void BoundActivityTrail::reset(CoreGeneration next_generation)
{
  if (!isImmediateSuccessor(generation_, next_generation))
  {
    throw StorageFailure(StorageFailureKind::InvalidGeneration,
                         "BoundActivityTrail::reset",
                         "generation is not the immediate successor");
  }
  std::uint64_t const created = metrics_.generations_created;
  std::uint64_t const resets = metrics_.generation_resets;
  std::vector<BoundRef>().swap(active_);
  std::vector<Level>().swap(levels_);
  generation_ = next_generation;
  next_checkpoint_token_ = 1;
  metrics_ = {};
  metrics_.generations_created = created;
  detail::saturatingIncrement(metrics_.generations_created);
  metrics_.generation_resets = resets;
  detail::saturatingIncrement(metrics_.generation_resets);
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
namespace detail {

void StorageTestAccess::setNextCheckpointToken(BoundActivityTrail& trail,
                                               std::uint64_t value) noexcept
{
  trail.next_checkpoint_token_ = value;
}

void StorageTestAccess::corruptTopLevelSize(BoundActivityTrail& trail,
                                            std::size_t value) noexcept
{
  if (!trail.levels_.empty())
  {
    trail.levels_.back().active_size = value;
  }
}

void StorageTestAccess::corruptTopLevelToken(BoundActivityTrail& trail,
                                             std::uint32_t value) noexcept
{
  if (!trail.levels_.empty())
  {
    trail.levels_.back().token = value;
  }
}

}  // namespace detail
#endif

}  // namespace stp::lra

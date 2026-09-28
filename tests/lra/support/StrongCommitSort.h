#ifndef STP_LRA_STORAGE_STRONG_COMMIT_SORT_H
#define STP_LRA_STORAGE_STRONG_COMMIT_SORT_H

#include "Storage/LraIds.h"
#include "Storage/StorageFailure.h"
#include "Storage/StorageMetrics.h"

#include <algorithm>
#include <cstdint>
#include <new>
#include <stdexcept>
#include <vector>

namespace stp::lra {

template <class T, class Compare>
void strongCommitSort(std::vector<T>& target, Compare compare,
                      StorageMetrics& metrics)
{
  detail::saturatingIncrement(metrics.sort_attempts);
  try
  {
    std::vector<T> temporary(target);
    std::sort(temporary.begin(), temporary.end(), compare);
    target.swap(temporary);
    detail::saturatingIncrement(metrics.sorts);
    detail::saturatingIncrement(metrics.sort_successes);
  }
  catch (std::bad_alloc const&)
  {
    detail::saturatingIncrement(metrics.allocation_failures);
    detail::saturatingIncrement(metrics.sort_failures);
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "strongCommitSort",
                         "temporary sequence or sort allocation failed");
  }
  catch (std::length_error const&)
  {
    detail::saturatingIncrement(metrics.sort_failures);
    throw StorageFailure(StorageFailureKind::LengthError,
                         "strongCommitSort",
                         "temporary sequence length limit");
  }
  catch (...)
  {
    detail::saturatingIncrement(metrics.sort_failures);
    throw;
  }
}

template <class T, class Compare>
void strongCommitSort(std::vector<T>& target, Compare compare)
{
  StorageMetrics discarded{};
  strongCommitSort(target, compare, discarded);
}

template <class ValueOf>
void sortBoundRefsStrongCommit(std::vector<BoundRef>& target,
                               ValueOf const& value_of,
                               StorageMetrics& metrics)
{
  detail::saturatingIncrement(metrics.sort_attempts);
  try
  {
    std::vector<BoundRef> temporary(target);
    std::vector<std::uint32_t> ordinals;
    ordinals.reserve(temporary.size());

    CoreGeneration generation{0};
    if (!temporary.empty())
    {
      generation = temporary.front().generation();
      if (!generation.valid())
      {
        throw StorageFailure(StorageFailureKind::InvalidGeneration,
                             "sortBoundRefsStrongCommit",
                             "invalid bound generation");
      }
    }

    for (BoundRef reference : temporary)
    {
      if (!reference.valid() || reference.generation() != generation)
      {
        throw StorageFailure(StorageFailureKind::InvalidGeneration,
                             "sortBoundRefsStrongCommit",
                             "bound references do not share one generation");
      }
      auto&& key = value_of(reference);
      int const self = key.compare(key);
      if (self != 0)
      {
        throw StorageFailure(StorageFailureKind::InvariantViolation,
                             "sortBoundRefsStrongCommit",
                             "projected exact comparator is not irreflexive");
      }
      ordinals.push_back(reference.ordinal());
    }

    std::sort(ordinals.begin(), ordinals.end());
    if (std::adjacent_find(ordinals.begin(), ordinals.end()) !=
        ordinals.end())
    {
      throw StorageFailure(StorageFailureKind::InvalidOrdinal,
                           "sortBoundRefsStrongCommit",
                           "duplicate bound reference is prohibited");
    }

    auto compare = [&value_of](BoundRef lhs, BoundRef rhs) {
      auto&& lhs_value = value_of(lhs);
      auto&& rhs_value = value_of(rhs);
      int const ordering = lhs_value.compare(rhs_value);
      if (ordering < -1 || ordering > 1)
      {
        throw StorageFailure(StorageFailureKind::InvariantViolation,
                             "sortBoundRefsStrongCommit",
                             "projected comparator returned a noncanonical value");
      }
      if (ordering != 0)
      {
        return ordering < 0;
      }
      return lhs.ordinal() > rhs.ordinal();
    };
    std::sort(temporary.begin(), temporary.end(), compare);
    target.swap(temporary);
    detail::saturatingIncrement(metrics.sorts);
    detail::saturatingIncrement(metrics.sort_successes);
  }
  catch (std::bad_alloc const&)
  {
    detail::saturatingIncrement(metrics.allocation_failures);
    detail::saturatingIncrement(metrics.sort_failures);
    throw StorageFailure(StorageFailureKind::AllocationFailure,
                         "sortBoundRefsStrongCommit",
                         "validation or temporary sort allocation failed");
  }
  catch (std::length_error const&)
  {
    detail::saturatingIncrement(metrics.sort_failures);
    throw StorageFailure(StorageFailureKind::LengthError,
                         "sortBoundRefsStrongCommit",
                         "validation or temporary sort length limit");
  }
  catch (...)
  {
    detail::saturatingIncrement(metrics.sort_failures);
    throw;
  }
}

template <class ValueOf>
void sortBoundRefsStrongCommit(std::vector<BoundRef>& target,
                               ValueOf const& value_of)
{
  StorageMetrics discarded{};
  sortBoundRefsStrongCommit(target, value_of, discarded);
}

}  // namespace stp::lra

#endif

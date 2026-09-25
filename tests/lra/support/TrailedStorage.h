#ifndef STP_LRA_STORAGE_TRAILED_STORAGE_H
#define STP_LRA_STORAGE_TRAILED_STORAGE_H

#include "BoundActivityTrail.h"
#include "Storage/Growth.h"
#include "Storage/CheckedConversions.h"
#include "Storage/DenseMembership.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <limits>
#include <new>
#include <stdexcept>
#include <utility>
#include <variant>
#include <vector>

namespace stp::lra {

namespace detail {
struct TrailedStorageTestAccess;
}

template <class Value>
class TrailedValueStorage final
{
 public:
  explicit TrailedValueStorage(CoreGeneration generation)
      : generation_(generation), active_bounds_(generation)
  {
    if (!generation.valid())
    {
      throw StorageFailure(StorageFailureKind::InvalidGeneration,
                           "TrailedValueStorage", "invalid generation");
    }
    metrics_.generations_created = 1;
  }

  ~TrailedValueStorage() noexcept = default;
  TrailedValueStorage(TrailedValueStorage const&) = delete;
  TrailedValueStorage& operator=(TrailedValueStorage const&) = delete;
  TrailedValueStorage(TrailedValueStorage&&) = delete;
  TrailedValueStorage& operator=(TrailedValueStorage&&) = delete;

  void ensureVariables(std::size_t count, Value const& initial)
  {
    if (count <= values_.size())
    {
      return;
    }
    constexpr std::uint64_t maximum_dense_count =
        static_cast<std::uint64_t>(VariableId::invalid_ordinal);
    if (checkedSizeToUint64(count, "TrailedValueStorage::ensureVariables") >
        maximum_dense_count)
    {
      throw StorageFailure(StorageFailureKind::ResourceLimit,
                           "TrailedValueStorage::ensureVariables",
                           "dense variable ordinal space exhausted");
    }

    try
    {
      // Reserve everything, then grow the values -- the one step whose
      // element copies can throw, and resize has the strong guarantee for a
      // copyable value -- and only then the membership and the trail, which
      // cannot fail within the capacity already held.
      std::size_t const old_capacity = values_.capacity();
      detail::reserveFor(values_, count);
      has_value_.reserve(count);
      detail::reserveForOneMore(changes_);
      std::size_t const previous_size = values_.size();
      values_.resize(count, initial);
      has_value_.ensureSize(count);
      if (!levels_.empty())
      {
        changes_.emplace_back(SizeChange{previous_size});
      }
      if (values_.capacity() != old_capacity)
      {
        detail::saturatingIncrement(metrics_.vector_growths);
      }
    }
    catch (StorageFailure const&)
    {
      throw;
    }
    catch (std::bad_alloc const&)
    {
      detail::saturatingIncrement(metrics_.allocation_failures);
      throw StorageFailure(StorageFailureKind::AllocationFailure,
                           "TrailedValueStorage::ensureVariables",
                           "value or trail allocation failed");
    }
    catch (std::length_error const&)
    {
      throw StorageFailure(StorageFailureKind::LengthError,
                           "TrailedValueStorage::ensureVariables",
                           "value or trail length limit");
    }
  }

  void ensureVariable(VariableId variable, Value const& initial)
  {
    validateGeneration(variable, "TrailedValueStorage::ensureVariable");
    std::uint64_t const count =
        static_cast<std::uint64_t>(variable.ordinal()) + 1U;
    ensureVariables(checkedUint64ToSize(
                        count, "TrailedValueStorage::ensureVariable"),
                    initial);
  }

  /* A write the trail does not journal: a pop leaves the value as it is.
   * For a store whose current values are valid at every checkpoint -- the
   * simplex assignment, which a pop only ever loosens the bounds on -- the
   * journal would cost a copy of the old value on every write and a replay
   * on every pop, and buy nothing. */
  void assignValue(VariableId variable, Value const& value)
  {
    std::size_t const index = validateVariable(
        variable, "TrailedValueStorage::assignValue");
    try
    {
      Value replacement(value);
      values_.at(index) = std::move(replacement);
      detail::saturatingIncrement(metrics_.value_mutations);
    }
    catch (StorageFailure const&)
    {
      throw;
    }
    catch (std::bad_alloc const&)
    {
      detail::saturatingIncrement(metrics_.allocation_failures);
      throw StorageFailure(StorageFailureKind::AllocationFailure,
                           "TrailedValueStorage::assignValue",
                           "value or mutation-log allocation failed");
    }
  }

  void setValue(VariableId variable, Value const& value)
  {
    std::size_t const index = validateVariable(
        variable, "TrailedValueStorage::setValue");
    try
    {
      /* Take the copy the caller asked for, and journal the value it is
       * about to replace, before touching the store.  Both of those can
       * throw and neither has changed anything when it does; the write
       * itself is a move-assignment, which cannot.  So this keeps the
       * all-or-nothing guarantee without copying the whole store to get it.
       *
       * That copy is not affordable here.  Every pivot writes a value, and
       * copying the values and the mutation log on each one makes a model
       * update cost the size of the model -- which is most of the solver's
       * time under any driver, and quadratic under one that keeps the core
       * alive across a search. */
      Value replacement(value);
      if (!levels_.empty())
      {
        changes_.emplace_back(ValueChange{index, values_.at(index)});
      }
      values_.at(index) = std::move(replacement);
      detail::saturatingIncrement(metrics_.value_mutations);
    }
    catch (StorageFailure const&)
    {
      throw;
    }
    catch (std::bad_alloc const&)
    {
      detail::saturatingIncrement(metrics_.allocation_failures);
      throw StorageFailure(StorageFailureKind::AllocationFailure,
                           "TrailedValueStorage::setValue",
                           "value or mutation-log allocation failed");
    }
    catch (std::length_error const&)
    {
      throw StorageFailure(StorageFailureKind::LengthError,
                           "TrailedValueStorage::setValue",
                           "value or mutation-log length limit");
    }
    catch (std::out_of_range const&)
    {
      throw StorageFailure(StorageFailureKind::InvariantViolation,
                           "TrailedValueStorage::setValue",
                           "validated value index became invalid");
    }
  }

  Value const& value(VariableId variable) const
  {
    std::size_t const index = validateVariable(
        variable, "TrailedValueStorage::value");
    try
    {
      return values_.at(index);
    }
    catch (std::out_of_range const&)
    {
      throw StorageFailure(StorageFailureKind::InvariantViolation,
                           "TrailedValueStorage::value",
                           "validated value index became invalid");
    }
  }

  void markPresent(VariableId variable, bool present)
  {
    std::size_t const index = validateVariable(
        variable, "TrailedValueStorage::markPresent");
    try
    {
      bool const previous = has_value_.test(index);
      detail::reserveForOneMore(changes_);
      if (!levels_.empty())
      {
        changes_.emplace_back(PresenceChange{index, previous});
      }
      has_value_.set(index, present);
      detail::saturatingIncrement(metrics_.presence_mutations);
    }
    catch (StorageFailure const&)
    {
      throw;
    }
    catch (std::bad_alloc const&)
    {
      detail::saturatingIncrement(metrics_.allocation_failures);
      throw StorageFailure(StorageFailureKind::AllocationFailure,
                           "TrailedValueStorage::markPresent",
                           "membership or mutation-log allocation failed");
    }
    catch (std::length_error const&)
    {
      throw StorageFailure(StorageFailureKind::LengthError,
                           "TrailedValueStorage::markPresent",
                           "membership or mutation-log length limit");
    }
  }

  bool hasValue(VariableId variable) const
  {
    return has_value_.test(validateVariable(
        variable, "TrailedValueStorage::hasValue"));
  }

  Checkpoint push()
  {
    try
    {
      if (levels_.size() == levels_.max_size())
      {
        throw StorageFailure(StorageFailureKind::LengthError,
                             "TrailedValueStorage::push",
                             "value checkpoint length limit");
      }
      detail::reserveForOneMore(levels_);
      Checkpoint const checkpoint = active_bounds_.push();
      levels_.push_back(Level{checkpoint.depth, changes_.size()});
      return checkpoint;
    }
    catch (StorageFailure const&)
    {
      throw;
    }
    catch (std::bad_alloc const&)
    {
      detail::saturatingIncrement(metrics_.allocation_failures);
      throw StorageFailure(StorageFailureKind::AllocationFailure,
                           "TrailedValueStorage::push",
                           "value checkpoint allocation failed");
    }
    catch (std::length_error const&)
    {
      throw StorageFailure(StorageFailureKind::LengthError,
                           "TrailedValueStorage::push",
                           "value checkpoint length limit");
    }
  }

  void pop(Checkpoint checkpoint)
  {
    auto const found = validateCheckpoint(checkpoint);
    std::size_t const found_index = checkedDifferenceToSize(
        found - levels_.begin(), "TrailedValueStorage::pop");
    std::size_t restored = changes_.size() - found->change_size;

    try
    {
      /* Check the whole slice before undoing any of it.  Replaying a journal
       * entry can only fail on a corrupted one -- an index or a size that
       * does not fit the store it claims to describe -- and that is decidable
       * without touching anything, by walking the slice backwards and
       * tracking what the size will be when each entry is reached.  Once the
       * slice is known good the replay cannot fail, so it runs in place.
       *
       * Copying the store to get that guarantee instead would cost the size
       * of the model and the whole trail on every backtrack, which is what a
       * driver that backtracks inside the search does constantly. */
      std::size_t reached_size = values_.size();
      for (std::size_t offset = changes_.size();
           offset != found->change_size; --offset)
      {
        checkReplayable(changes_[offset - 1U], reached_size);
      }

      for (std::size_t offset = changes_.size();
           offset != found->change_size; --offset)
      {
        Change& change = changes_[offset - 1U];
        std::visit(
            [&](auto& concrete) {
              replay(concrete, values_, has_value_);
            },
            change);
      }
      changes_.resize(found->change_size);
      levels_.resize(found_index);
      active_bounds_.pop(checkpoint);
      metrics_.trail_restorations = detail::saturatingAdd(
          metrics_.trail_restorations, detail::saturatingSize(restored));
    }
    catch (StorageFailure const&)
    {
      throw;
    }
    catch (std::bad_alloc const&)
    {
      detail::saturatingIncrement(metrics_.allocation_failures);
      throw StorageFailure(StorageFailureKind::AllocationFailure,
                           "TrailedValueStorage::pop",
                           "rollback copy or value allocation failed");
    }
    catch (std::length_error const&)
    {
      throw StorageFailure(StorageFailureKind::LengthError,
                           "TrailedValueStorage::pop",
                           "rollback copy length limit");
    }
    catch (std::out_of_range const&)
    {
      throw StorageFailure(StorageFailureKind::InvariantViolation,
                           "TrailedValueStorage::pop",
                           "corrupted rollback index");
    }
  }

  template <class BoundValue>
  void recordActive(BoundRef reference,
                    BoundArena<BoundValue> const& arena)
  {
    active_bounds_.append(reference, arena);
  }

  std::vector<BoundRef> const& activeBounds() const noexcept
  {
    return active_bounds_.active();
  }
  DenseMembership const& membership() const noexcept { return has_value_; }
  std::size_t variableCount() const noexcept { return values_.size(); }
  std::size_t levelCount() const noexcept { return levels_.size(); }
  std::size_t changeCount() const noexcept { return changes_.size(); }
  CoreGeneration generation() const noexcept { return generation_; }
  StorageMetrics metrics() const noexcept { return metrics_; }

  void clearCandidate() noexcept
  {
    active_bounds_.clearToBase();
    std::vector<Level>().swap(levels_);
    std::vector<Change>().swap(changes_);
    has_value_.clearValues();
  }

  void reset(CoreGeneration next_generation)
  {
    if (!isImmediateSuccessor(generation_, next_generation))
    {
      throw StorageFailure(StorageFailureKind::InvalidGeneration,
                           "TrailedValueStorage::reset",
                           "generation is not the immediate successor");
    }

    // Dependent active references and rollback witnesses die before values.
    active_bounds_.reset(next_generation);
    std::vector<Level>().swap(levels_);
    std::vector<Change>().swap(changes_);
    has_value_.reset();
    std::vector<Value>().swap(values_);
    generation_ = next_generation;
    std::uint64_t const created = metrics_.generations_created;
    std::uint64_t const resets = metrics_.generation_resets;
    metrics_ = {};
    metrics_.generations_created = created;
    detail::saturatingIncrement(metrics_.generations_created);
    metrics_.generation_resets = resets;
    detail::saturatingIncrement(metrics_.generation_resets);
  }

 private:
  struct ValueChange
  {
    std::size_t index;
    Value previous;
  };
  struct PresenceChange
  {
    std::size_t index;
    bool previous;
  };
  struct SizeChange
  {
    std::size_t previous_size;
  };
  using Change = std::variant<ValueChange, PresenceChange, SizeChange>;

  struct Level
  {
    std::uint32_t token;
    std::size_t change_size;
  };

  void validateGeneration(VariableId variable, char const* operation) const
  {
    if (variable.generation() != generation_)
    {
      throw StorageFailure(StorageFailureKind::InvalidGeneration, operation,
                           "stale or foreign variable generation");
    }
  }

  std::size_t validateVariable(VariableId variable,
                               char const* operation) const
  {
    validateGeneration(variable, operation);
    std::size_t const index = static_cast<std::size_t>(variable.ordinal());
    if (!variable.valid() || index >= values_.size() ||
        has_value_.size() != values_.size())
    {
      throw StorageFailure(StorageFailureKind::InvalidOrdinal, operation,
                           "variable ordinal is not registered");
    }
    return index;
  }

  typename std::vector<Level>::const_iterator validateCheckpoint(
      Checkpoint checkpoint) const
  {
    auto reject = [](char const* detail_text)
        -> typename std::vector<Level>::const_iterator {
      throw StorageFailure(StorageFailureKind::InvalidCheckpoint,
                           "TrailedValueStorage::pop", detail_text);
    };
    if (checkpoint.generation != generation_ || checkpoint.depth == 0 ||
        levels_.empty())
    {
      return reject("wrong generation, underflow, or stale token");
    }
    /* From the top: a pop is almost always to the level just below it,
     * and the levels that stay were checked when they were pushed and by
     * every pop since. Only the levels being removed, and the join to the
     * one beneath them, are walked. */
    auto const found_reverse = std::find_if(
        levels_.rbegin(), levels_.rend(), [checkpoint](Level const& level) {
          return level.token == checkpoint.depth;
        });
    if (found_reverse == levels_.rend())
    {
      return reject("checkpoint token is not live");
    }
    auto const found = std::next(found_reverse).base();
    std::uint32_t previous_token = 0;
    std::size_t previous_change_size = 0;
    if (found != levels_.begin())
    {
      previous_token = std::prev(found)->token;
      previous_change_size = std::prev(found)->change_size;
    }
    for (auto level = found; level != levels_.end(); ++level)
    {
      if (level->token <= previous_token ||
          level->change_size < previous_change_size ||
          level->change_size > changes_.size())
      {
        return reject("corrupted value checkpoint stack");
      }
      previous_token = level->token;
      previous_change_size = level->change_size;
    }
    return found;
  }

  /* Can this entry be replayed against a store that will be `size` values
   * long when the replay reaches it?  Walking the slice backwards, a growth
   * record is where the size shrinks again, so `size` is updated as it goes.
   * Anything that does not fit is a corrupted trail, not a runtime failure. */
  static void checkReplayable(Change const& change, std::size_t& size)
  {
    if (auto const* grown = std::get_if<SizeChange>(&change))
    {
      if (grown->previous_size > size)
      {
        throw StorageFailure(StorageFailureKind::InvariantViolation,
                             "TrailedValueStorage::pop",
                             "corrupted growth rollback record");
      }
      size = grown->previous_size;
      return;
    }
    std::size_t const index =
        std::holds_alternative<ValueChange>(change)
            ? std::get<ValueChange>(change).index
            : std::get<PresenceChange>(change).index;
    if (index >= size)
    {
      throw StorageFailure(StorageFailureKind::InvariantViolation,
                           "TrailedValueStorage::pop",
                           "corrupted rollback index");
    }
  }

  /* Undo one checked entry.  The journal is discarded immediately after, so
   * the recorded value is moved rather than copied, which is what makes this
   * unable to fail. */
  static void replay(ValueChange& change,
                     std::vector<Value>& values,
                     DenseMembership&) noexcept
  {
    values[change.index] = std::move(change.previous);
  }
  static void replay(PresenceChange& change,
                     std::vector<Value>&,
                     DenseMembership& membership) noexcept
  {
    membership.setChecked(change.index, change.previous);
  }
  static void replay(SizeChange& change,
                     std::vector<Value>& values,
                     DenseMembership& membership) noexcept
  {
    values.resize(change.previous_size);
    membership.shrinkToChecked(change.previous_size);
  }


  CoreGeneration generation_;
  std::vector<Value> values_;
  DenseMembership has_value_;
  BoundActivityTrail active_bounds_;
  std::vector<Change> changes_;
  std::vector<Level> levels_;
  StorageMetrics metrics_{};

  friend struct detail::TrailedStorageTestAccess;
};

#if defined(STP_LRA_TEST_FAULT_INJECTION)
namespace detail {
struct TrailedStorageTestAccess
{
  template <class Value>
  static void corruptTopLevelToken(TrailedValueStorage<Value>& storage,
                                   std::uint32_t value) noexcept
  {
    if (!storage.levels_.empty())
    {
      storage.levels_.back().token = value;
    }
  }

  template <class Value>
  static void corruptTopLevelChangeSize(
      TrailedValueStorage<Value>& storage, std::size_t value) noexcept
  {
    if (!storage.levels_.empty())
    {
      storage.levels_.back().change_size = value;
    }
  }
};
}  // namespace detail
#endif

}  // namespace stp::lra

#endif

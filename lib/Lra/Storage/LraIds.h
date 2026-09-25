#ifndef STP_LRA_STORAGE_LRA_IDS_H
#define STP_LRA_STORAGE_LRA_IDS_H

#include "Storage/StorageFailure.h"

#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>
#include <type_traits>

namespace stp::lra {

template <class Value>
class BoundArena;
class BoundActivityTrail;

struct CoreGeneration final
{
  std::uint64_t value;

  bool valid() const noexcept;
  std::uint32_t domainOrdinal() const noexcept;
  std::uint32_t epoch() const noexcept;

  friend bool operator==(CoreGeneration lhs, CoreGeneration rhs) noexcept
  {
    return lhs.value == rhs.value;
  }
  friend bool operator!=(CoreGeneration lhs, CoreGeneration rhs) noexcept
  {
    return !(lhs == rhs);
  }
  friend bool operator<(CoreGeneration lhs, CoreGeneration rhs) noexcept
  {
    return lhs.value < rhs.value;
  }
};

namespace detail {
struct StorageTestAccess;
}

class GenerationDomain final
{
 public:
  GenerationDomain();
  ~GenerationDomain() noexcept = default;
  GenerationDomain(GenerationDomain const&) = delete;
  GenerationDomain& operator=(GenerationDomain const&) = delete;
  GenerationDomain(GenerationDomain&&) = delete;
  GenerationDomain& operator=(GenerationDomain&&) = delete;

  CoreGeneration current() const noexcept;
  CoreGeneration advance();

 private:
  std::uint32_t domain_;
  std::uint32_t epoch_;

  friend struct detail::StorageTestAccess;
};

bool isImmediateSuccessor(CoreGeneration current,
                          CoreGeneration proposed) noexcept;

namespace detail {
struct VariableIdTag;
struct RowIdTag;
struct AtomIdTag;
struct BoundRefTag;
}  // namespace detail

template <class Tag>
class GenerationId final
{
 public:
  static constexpr std::uint32_t invalid_ordinal =
      std::numeric_limits<std::uint32_t>::max();
  static constexpr std::uint32_t maximum_usable_ordinal =
      invalid_ordinal - 1U;

  GenerationId(CoreGeneration generation, std::uint32_t ordinal)
      : generation_(generation), ordinal_(ordinal)
  {
    if (!generation.valid())
    {
      throw StorageFailure(StorageFailureKind::InvalidGeneration,
                           "GenerationId", "invalid generation");
    }
    if (ordinal == invalid_ordinal)
    {
      throw StorageFailure(StorageFailureKind::InvalidOrdinal,
                           "GenerationId", "reserved ordinal");
    }
  }

  CoreGeneration generation() const noexcept { return generation_; }
  std::uint32_t ordinal() const noexcept { return ordinal_; }
  bool valid() const noexcept
  {
    return generation_.valid() && ordinal_ != invalid_ordinal;
  }

  friend bool operator==(GenerationId lhs, GenerationId rhs) noexcept
  {
    return lhs.generation_ == rhs.generation_ && lhs.ordinal_ == rhs.ordinal_;
  }
  friend bool operator!=(GenerationId lhs, GenerationId rhs) noexcept
  {
    return !(lhs == rhs);
  }
  friend bool operator<(GenerationId lhs, GenerationId rhs) noexcept
  {
    return lhs.generation_ < rhs.generation_ ||
           (lhs.generation_ == rhs.generation_ &&
            lhs.ordinal_ < rhs.ordinal_);
  }

 private:
  CoreGeneration generation_;
  std::uint32_t ordinal_;
};

using VariableId = GenerationId<detail::VariableIdTag>;
using RowId = GenerationId<detail::RowIdTag>;
using AtomId = GenerationId<detail::AtomIdTag>;
using BoundRef = GenerationId<detail::BoundRefTag>;

struct OriginId final
{
  std::uint64_t solve_epoch;
  std::uint64_t serial;

  friend bool operator==(OriginId lhs, OriginId rhs) noexcept
  {
    return lhs.solve_epoch == rhs.solve_epoch && lhs.serial == rhs.serial;
  }
  friend bool operator<(OriginId lhs, OriginId rhs) noexcept
  {
    return lhs.solve_epoch < rhs.solve_epoch ||
           (lhs.solve_epoch == rhs.solve_epoch && lhs.serial < rhs.serial);
  }
};

struct Checkpoint final
{
  CoreGeneration generation;
  std::uint32_t depth;

  friend bool operator==(Checkpoint lhs, Checkpoint rhs) noexcept
  {
    return lhs.generation == rhs.generation && lhs.depth == rhs.depth;
  }
};

template <class Id>
struct GenerationIdHash final
{
  std::size_t operator()(Id id) const noexcept
  {
    constexpr std::uint64_t offset = UINT64_C(14695981039346656037);
    constexpr std::uint64_t prime = UINT64_C(1099511628211);
    std::uint64_t hash = offset;
    auto append = [&hash](std::uint64_t value, unsigned bytes) noexcept {
      for (unsigned index = 0; index != bytes; ++index)
      {
        unsigned const shift = (bytes - index - 1U) * 8U;
        hash ^= static_cast<std::uint8_t>(value >> shift);
        hash *= prime;
      }
    };
    append(id.generation().value, 8U);
    append(id.ordinal(), 4U);
    if constexpr (sizeof(std::size_t) >= sizeof(std::uint64_t))
    {
      return static_cast<std::size_t>(hash);
    }
    return static_cast<std::size_t>(
        static_cast<std::uint32_t>(hash) ^
        static_cast<std::uint32_t>(hash >> 32U));
  }
};

template <class Id>
class MonotonicIdAllocator final
{
 public:
  explicit MonotonicIdAllocator(CoreGeneration generation)
      : generation_(generation), next_ordinal_(0)
  {
    if (!generation.valid())
    {
      throw StorageFailure(StorageFailureKind::InvalidGeneration,
                           "MonotonicIdAllocator", "invalid generation");
    }
  }

  Id allocate()
  {
    Id const result = preflight();
    commit(result);
    return result;
  }

  CoreGeneration generation() const noexcept { return generation_; }
  std::uint64_t allocatedCount() const noexcept { return next_ordinal_; }

  void reset(CoreGeneration next_generation)
  {
    if (!isImmediateSuccessor(generation_, next_generation))
    {
      throw StorageFailure(StorageFailureKind::InvalidGeneration,
                           "MonotonicIdAllocator::reset",
                           "generation is not the immediate successor");
    }
    generation_ = next_generation;
    next_ordinal_ = 0;
  }

 private:
  Id preflight() const
  {
    if (next_ordinal_ > Id::maximum_usable_ordinal)
    {
      throw StorageFailure(StorageFailureKind::ResourceLimit,
                           "MonotonicIdAllocator::allocate",
                           "typed ordinal exhausted");
    }
    return Id(generation_, static_cast<std::uint32_t>(next_ordinal_));
  }

  void commit(Id expected) noexcept
  {
    if (expected.generation() != generation_ ||
        expected.ordinal() != next_ordinal_)
    {
      std::terminate();
    }
    ++next_ordinal_;
  }

  CoreGeneration generation_;
  std::uint64_t next_ordinal_;

  template <class>
  friend class BoundArena;
  friend struct detail::StorageTestAccess;
};

std::string debugString(CoreGeneration generation);
std::string debugString(VariableId id);
std::string debugString(RowId id);
std::string debugString(AtomId id);
std::string debugString(BoundRef id);
std::string debugString(OriginId id);
std::string debugString(Checkpoint checkpoint);

static_assert(sizeof(CoreGeneration) == sizeof(std::uint64_t));
static_assert(std::is_standard_layout_v<CoreGeneration>);
static_assert(std::is_trivially_copyable_v<CoreGeneration>);
static_assert(std::is_standard_layout_v<VariableId>);
static_assert(std::is_trivially_copyable_v<VariableId>);
static_assert(std::is_standard_layout_v<RowId>);
static_assert(std::is_trivially_copyable_v<RowId>);
static_assert(std::is_standard_layout_v<AtomId>);
static_assert(std::is_trivially_copyable_v<AtomId>);
static_assert(std::is_standard_layout_v<BoundRef>);
static_assert(std::is_trivially_copyable_v<BoundRef>);
static_assert(sizeof(VariableId) == sizeof(RowId));
static_assert(sizeof(RowId) == sizeof(AtomId));
static_assert(sizeof(AtomId) == sizeof(BoundRef));
static_assert(std::is_standard_layout_v<OriginId>);
static_assert(std::is_trivially_copyable_v<OriginId>);
static_assert(std::is_standard_layout_v<Checkpoint>);
static_assert(std::is_trivially_copyable_v<Checkpoint>);

#if defined(STP_LRA_TEST_FAULT_INJECTION)
namespace detail {
struct StorageTestAccess
{
  static std::uint64_t exchangeNextDomainOrdinal(std::uint64_t) noexcept;
  static void setEpoch(GenerationDomain& domain, std::uint32_t epoch) noexcept
  {
    domain.epoch_ = epoch;
  }

  template <class Id>
  static void setNextOrdinal(MonotonicIdAllocator<Id>& allocator,
                             std::uint64_t value) noexcept
  {
    allocator.next_ordinal_ = value;
  }

  template <class Value>
  static void setArenaNextOrdinal(BoundArena<Value>&,
                                  std::uint64_t) noexcept;
  static void setNextCheckpointToken(BoundActivityTrail&,
                                     std::uint64_t) noexcept;
  static void corruptTopLevelSize(BoundActivityTrail&,
                                  std::size_t) noexcept;
  static void corruptTopLevelToken(BoundActivityTrail&,
                                   std::uint32_t) noexcept;
};
}  // namespace detail
#endif

}  // namespace stp::lra

#endif

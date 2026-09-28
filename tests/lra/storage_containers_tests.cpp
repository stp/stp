#include "ExactLraCore.h"
#include "ExactRational.h"
#include "ImathAllocHooks.h"
#include "NumberBudget.h"
#include "Storage/CheckedConversions.h"
#include "Storage/DenseMembership.h"
#include "support/NoInline.h"
#include "support/StrongCommitSort.h"
#include "support/TrailedStorage.h"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <limits>
#include <new>
#include <random>
#include <stdexcept>
#include <string>
#include <thread>
#include <type_traits>
#include <utility>
#include <vector>

namespace allocation_fault {
thread_local std::int64_t fail_after = -1;
thread_local bool count_enabled = false;
thread_local std::uint64_t allocation_count = 0;
thread_local std::uint64_t allocation_bytes = 0;

void beforeAllocation(std::size_t size)
{
  if (count_enabled)
  {
    ++allocation_count;
    allocation_bytes += static_cast<std::uint64_t>(size);
  }
  if (fail_after == 0)
  {
    fail_after = -1;
    throw std::bad_alloc();
  }
  if (fail_after > 0)
  {
    --fail_after;
  }
}

void arm(std::uint64_t index) noexcept
{
  fail_after = static_cast<std::int64_t>(index);
}
void disarm() noexcept { fail_after = -1; }
void beginCount() noexcept
{
  allocation_count = 0;
  allocation_bytes = 0;
  count_enabled = true;
}
std::pair<std::uint64_t, std::uint64_t> endCount() noexcept
{
  count_enabled = false;
  return {allocation_count, allocation_bytes};
}
}  // namespace allocation_fault

STP_LRA_TEST_NOINLINE void* operator new(std::size_t size)
{
  allocation_fault::beforeAllocation(size);
  if (void* memory = std::malloc(size == 0 ? 1 : size))
  {
    return memory;
  }
  throw std::bad_alloc();
}
STP_LRA_TEST_NOINLINE void* operator new[](std::size_t size)
{
  return ::operator new(size);
}
STP_LRA_TEST_NOINLINE void operator delete(void* memory) noexcept
{
  std::free(memory);
}
STP_LRA_TEST_NOINLINE void operator delete[](void* memory) noexcept
{
  std::free(memory);
}
STP_LRA_TEST_NOINLINE void operator delete(void* memory, std::size_t) noexcept
{
  std::free(memory);
}
STP_LRA_TEST_NOINLINE void operator delete[](void* memory, std::size_t) noexcept
{
  std::free(memory);
}

namespace {

using stp::lra::BoundArena;
using stp::lra::BoundRef;
using stp::lra::Checkpoint;
using stp::lra::CoreGeneration;
using stp::lra::DenseMembership;
using stp::lra::ExactRational;
using stp::lra::GenerationDomain;
using stp::lra::MonotonicIdAllocator;
using stp::lra::NumberBudget;
using stp::lra::NumberFailure;
using stp::lra::NumberFailureKind;
using stp::lra::NumberLimits;
using stp::lra::NumberOperationScope;
using stp::lra::StorageFailure;
using stp::lra::StorageFailureKind;
using stp::lra::StorageMetrics;
using stp::lra::TrailedValueStorage;
using stp::lra::VariableId;

constexpr std::uint64_t unlimited =
    std::numeric_limits<std::uint64_t>::max();

NumberLimits generousLimits()
{
  return NumberLimits{UINT64_C(65536), UINT64_C(65536),
                      UINT64_C(268435456), UINT64_C(16777216)};
}

[[noreturn]] void fail(std::string const& message)
{
  allocation_fault::disarm();
  stp_lra_imath_test_disable_failures();
  throw std::runtime_error(message);
}

void require(bool condition, char const* message)
{
  if (!condition)
  {
    fail(message);
  }
}

void require(bool condition, std::string const& message)
{
  if (!condition)
  {
    fail(message);
  }
}

template <class Function>
void expectStorageFailure(StorageFailureKind expected,
                          char const* label,
                          Function&& function)
{
  try
  {
    function();
  }
  catch (StorageFailure const& failure)
  {
    allocation_fault::disarm();
    require(failure.kind() == expected,
            std::string(label) + ": wrong StorageFailureKind");
    require(failure.operation() != nullptr &&
                std::strlen(failure.operation()) != 0,
            std::string(label) + ": missing operation");
    return;
  }
  catch (std::bad_alloc const&)
  {
    allocation_fault::disarm();
    fail(std::string(label) + ": raw bad_alloc escaped");
  }
  allocation_fault::disarm();
  fail(std::string(label) + ": expected StorageFailure");
}

struct SyntheticFailure final : std::runtime_error
{
  SyntheticFailure() : std::runtime_error("synthetic value failure") {}
};

class ThrowingValue final
{
 public:
  ThrowingValue() : text_("initial") { ++live_; }
  explicit ThrowingValue(std::string text) : text_(std::move(text)) { ++live_; }
  ThrowingValue(ThrowingValue const& other)
  {
    beforeCopy();
    text_ = other.text_;
    ++live_;
  }
  ThrowingValue(ThrowingValue&& other) noexcept
      : text_(std::move(other.text_))
  {
    ++live_;
  }
  ThrowingValue& operator=(ThrowingValue const& other)
  {
    text_ = "assignment-mutated-temporary";
    beforeCopy();
    text_ = other.text_;
    return *this;
  }
  ThrowingValue& operator=(ThrowingValue&& other) noexcept
  {
    text_ = std::move(other.text_);
    return *this;
  }
  ~ThrowingValue() noexcept
  {
    --live_;
    ++destroyed_;
  }

  std::string const& text() const noexcept { return text_; }
  friend bool operator==(ThrowingValue const& lhs,
                         ThrowingValue const& rhs) noexcept
  {
    return lhs.text_ == rhs.text_;
  }

  static void failCopyAfter(std::int64_t count) noexcept
  {
    fail_copy_after_ = count;
  }
  static void disableFailures() noexcept { fail_copy_after_ = -1; }
  static std::int64_t live() noexcept { return live_; }
  static std::uint64_t destroyed() noexcept { return destroyed_; }

 private:
  static void beforeCopy()
  {
    if (fail_copy_after_ == 0)
    {
      fail_copy_after_ = -1;
      throw SyntheticFailure();
    }
    if (fail_copy_after_ > 0)
    {
      --fail_copy_after_;
    }
  }

  std::string text_;
  static thread_local std::int64_t fail_copy_after_;
  static std::atomic<std::int64_t> live_;
  static std::atomic<std::uint64_t> destroyed_;
};

thread_local std::int64_t ThrowingValue::fail_copy_after_ = -1;
std::atomic<std::int64_t> ThrowingValue::live_{0};
std::atomic<std::uint64_t> ThrowingValue::destroyed_{0};

class ExactKey final
{
 public:
  ExactKey(ExactRational rational, std::int64_t infinitesimal)
      : rational_(std::move(rational)), infinitesimal_(infinitesimal)
  {}

  int compare(ExactKey const& other) const
  {
    if (count_comparisons_)
    {
      ++comparison_count_;
    }
    if (fail_compare_after_ == 0)
    {
      fail_compare_after_ = -1;
      throw SyntheticFailure();
    }
    if (fail_compare_after_ > 0)
    {
      --fail_compare_after_;
    }
    if (corrupt_result_)
    {
      return 2;
    }
    int const rational_order = rational_.compare(other.rational_);
    if (rational_order != 0)
    {
      return rational_order;
    }
    return infinitesimal_ < other.infinitesimal_
               ? -1
               : (infinitesimal_ > other.infinitesimal_ ? 1 : 0);
  }

  static void failCompareAfter(std::int64_t value) noexcept
  {
    fail_compare_after_ = value;
  }
  static void corruptResult(bool value) noexcept { corrupt_result_ = value; }
  static void beginComparisonCount() noexcept
  {
    comparison_count_ = 0;
    count_comparisons_ = true;
  }
  static std::uint64_t endComparisonCount() noexcept
  {
    count_comparisons_ = false;
    return comparison_count_;
  }

 private:
  ExactRational rational_;
  std::int64_t infinitesimal_;
  static thread_local std::int64_t fail_compare_after_;
  static thread_local bool corrupt_result_;
  static thread_local bool count_comparisons_;
  static thread_local std::uint64_t comparison_count_;
};

thread_local std::int64_t ExactKey::fail_compare_after_ = -1;
thread_local bool ExactKey::corrupt_result_ = false;
thread_local bool ExactKey::count_comparisons_ = false;
thread_local std::uint64_t ExactKey::comparison_count_ = 0;

void testDirectVectorsAndConversions()
{
  static_assert(std::is_same_v<
                typename std::vector<std::uint8_t>::value_type,
                std::uint8_t>);
  static_assert(!std::is_same_v<
                typename std::vector<std::uint8_t>::reference, bool>);

  std::vector<ThrowingValue> sequence;
  sequence.emplace_back("a");
  sequence.push_back(ThrowingValue("b"));
  require(sequence.front().text() == "a" &&
              sequence.back().text() == "b",
          "direct vector append/front/back");
  sequence.resize(5, ThrowingValue("zero"));
  require(sequence.at(2).text() == "zero" &&
              sequence.at(4).text() == "zero",
          "vector growth deterministic initialization");
  sequence.resize(2);
  require(sequence.size() == 2 && sequence.back().text() == "b",
          "vector suffix shrink");
  std::vector<ThrowingValue> copy(sequence);
  require(copy == sequence, "vector exact copy");
  std::vector<ThrowingValue> moved(std::move(copy));
  require(moved == sequence, "vector move content");
  std::size_t const retained_capacity = moved.capacity();
  moved.clear();
  require(moved.empty() && moved.capacity() == retained_capacity,
          "logical clear retains ordinary capacity");
  std::vector<ThrowingValue>().swap(moved);
  require(moved.empty() && moved.capacity() == 0,
          "destructive reset releases vector storage");

  std::vector<ThrowingValue> protected_sequence{ThrowingValue("old")};
  ThrowingValue::failCopyAfter(0);
  try
  {
    std::vector<ThrowingValue> proposed(protected_sequence);
    proposed.at(0) = ThrowingValue("new");
    protected_sequence.swap(proposed);
    fail("throwing vector copy was expected");
  }
  catch (SyntheticFailure const&)
  {
    ThrowingValue::disableFailures();
  }
  require(protected_sequence.at(0).text() == "old",
          "temporary/swap protects vector content");

  std::vector<ThrowingValue> sort_copy_failure{
      ThrowingValue("c"), ThrowingValue("a"), ThrowingValue("b")};
  auto const sort_copy_before = sort_copy_failure;
  StorageMetrics sort_metrics{};
  ThrowingValue::failCopyAfter(0);
  try
  {
    stp::lra::strongCommitSort(
        sort_copy_failure,
        [](ThrowingValue const& lhs, ThrowingValue const& rhs) {
          return lhs.text() < rhs.text();
        },
        sort_metrics);
    fail("strong sort element copy failure expected");
  }
  catch (SyntheticFailure const&)
  {
    ThrowingValue::disableFailures();
  }
  require(sort_copy_failure == sort_copy_before &&
              sort_metrics.sort_attempts == 1 &&
              sort_metrics.sort_failures == 1,
          "strong sort protects input from element copy failure");

  require(stp::lra::checkedSizeToUint32(0) == 0,
          "size to uint32 zero");
  require(stp::lra::checkedSizeToUint32(
              std::numeric_limits<std::uint32_t>::max()) ==
              std::numeric_limits<std::uint32_t>::max(),
          "size to uint32 exact maximum");
  expectStorageFailure(StorageFailureKind::ResourceLimit,
                       "uint64 to uint32 above maximum", [] {
                         (void)stp::lra::checkedUint64ToUint32(
                             static_cast<std::uint64_t>(
                                 std::numeric_limits<std::uint32_t>::max()) +
                             1U);
                       });
  require(stp::lra::checkedDifferenceToSize<std::ptrdiff_t>(0) == 0,
          "difference zero");
  expectStorageFailure(StorageFailureKind::InvariantViolation,
                       "negative difference", [] {
                         (void)stp::lra::checkedDifferenceToSize<
                             std::ptrdiff_t>(-1);
                       });
  require(stp::lra::checkedLogicalByteAdd(unlimited - 1U, 1U) ==
              unlimited,
          "logical add exact maximum");
  expectStorageFailure(StorageFailureKind::ResourceLimit,
                       "logical add overflow", [] {
                         (void)stp::lra::checkedLogicalByteAdd(unlimited, 1U);
                       });
  require(stp::lra::checkedLogicalByteMultiply(unlimited, 1U) ==
              unlimited,
          "logical multiply exact maximum");
  expectStorageFailure(StorageFailureKind::ResourceLimit,
                       "logical multiply overflow", [] {
                         (void)stp::lra::checkedLogicalByteMultiply(
                             unlimited, 2U);
                       });
  std::cout << "{\"mode\":\"vector-conversion\",\"passed\":true,"
               "\"direct_std_vector\":true,\"conversion_boundaries\":12}"
            << std::endl;
}

void testDenseMembership()
{
  DenseMembership membership;
  membership.ensureSize(3);
  membership.ensureSize(257);
  membership.ensureSize(1000000);
  require(membership.size() == 1000000,
          "million-position dense membership");
  require(std::all_of(membership.bytes().begin(), membership.bytes().end(),
                      [](std::uint8_t value) { return value == 0; }),
          "dense growth zero initializes every byte");

  std::vector<std::uint8_t> oracle(membership.size(), 0);
  std::uint64_t state = UINT64_C(0x4d3142303244454e);
  for (std::size_t step = 0; step != 200000; ++step)
  {
    state = state * UINT64_C(6364136223846793005) + 1U;
    std::size_t const index = static_cast<std::size_t>(state % oracle.size());
    bool const value = ((state >> 41U) & 1U) != 0;
    membership.set(index, value);
    oracle[index] = value ? 1U : 0U;
    require(membership.test(index) == value,
            "random dense membership agrees with reference");
  }
  require(membership.bytes() == oracle,
          "full randomized dense state agrees");
  auto const active = membership.activeIndices();
  require(std::is_sorted(active.begin(), active.end()),
          "membership export is increasing");

  expectStorageFailure(StorageFailureKind::OutOfRange,
                       "dense set out of range", [&] {
                         membership.set(membership.size(), true);
                       });
  expectStorageFailure(StorageFailureKind::OutOfRange,
                       "dense test out of range", [&] {
                         (void)membership.test(membership.size());
                       });
  std::size_t const old_size = membership.size();
  std::size_t const old_capacity = membership.capacity();
  membership.clearValues();
  require(membership.size() == old_size &&
              membership.capacity() == old_capacity &&
              membership.activeIndices().empty(),
          "dense logical clear retains allocation and zeros values");
  membership.set(999999, true);
  DenseMembership moved(std::move(membership));
  require(moved.test(999999), "dense move preserves deterministic state");
  require(stp::lra::debugString(moved) == "membership[999999]",
          "dense debug output canonical");
  stp::lra::detail::DenseMembershipTestAccess::corruptByte(
      moved, 999999, std::uint8_t{2});
  expectStorageFailure(StorageFailureKind::InvariantViolation,
                       "corrupted dense byte", [&] {
                         (void)moved.test(999999);
                       });
  stp::lra::detail::DenseMembershipTestAccess::corruptByte(
      moved, 999999, std::uint8_t{1});
  require(moved.test(999999), "dense corruption recovery");
  moved.reset();
  require(moved.size() == 0 && moved.capacity() == 0,
          "dense destructive reset releases storage");
  std::cout << "{\"mode\":\"dense\",\"passed\":true,"
               "\"positions\":1000000,\"random_operations\":200000,"
               "\"reference_agreement\":true}"
            << std::endl;
}

void testTrailedStorage()
{
  GenerationDomain domain;
  CoreGeneration const generation = domain.current();
  MonotonicIdAllocator<VariableId> ids(generation);
  VariableId const v0 = ids.allocate();
  VariableId const v1 = ids.allocate();
  VariableId const v2 = ids.allocate();
  ThrowingValue initial("zero");
  TrailedValueStorage<ThrowingValue> storage(generation);
  storage.ensureVariable(v1, initial);
  require(storage.variableCount() == 2 &&
              storage.value(v0).text() == "zero" &&
              !storage.hasValue(v1),
          "dense typed variable registration");

  storage.setValue(v0, ThrowingValue("base"));
  storage.markPresent(v0, true);
  BoundArena<int> arena(generation);
  BoundRef const b0 = arena.emplace(7);
  Checkpoint const outer = storage.push();
  storage.recordActive(b0, arena);
  storage.setValue(v0, ThrowingValue("outer-one"));
  storage.setValue(v0, ThrowingValue("outer-two"));
  storage.markPresent(v1, true);
  Checkpoint const inner = storage.push();
  storage.setValue(v0, ThrowingValue("inner"));
  storage.markPresent(v0, false);
  storage.ensureVariable(v2, initial);
  storage.setValue(v2, ThrowingValue("grown"));
  storage.markPresent(v2, true);
  require(storage.variableCount() == 3 && storage.hasValue(v2),
          "growth and mutation inside checkpoint");

  storage.pop(inner);
  require(storage.variableCount() == 2 &&
              storage.value(v0).text() == "outer-two" &&
              storage.hasValue(v0) && storage.hasValue(v1) &&
              storage.activeBounds().size() == 1,
          "nested pop restores value presence size and active suffix");
  expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                       "checkpoint replay", [&] { storage.pop(inner); });
  storage.pop(outer);
  require(storage.value(v0).text() == "base" && storage.hasValue(v0) &&
              !storage.hasValue(v1) && storage.activeBounds().empty() &&
              arena.at(b0) == 7,
          "outer rollback restores values without destroying arena objects");

  GenerationDomain foreign_domain;
  VariableId foreign(foreign_domain.current(), 0);
  expectStorageFailure(StorageFailureKind::InvalidGeneration,
                       "foreign dense variable", [&] {
                         storage.setValue(foreign, initial);
                       });
  expectStorageFailure(StorageFailureKind::InvalidOrdinal,
                       "unregistered dense variable", [&] {
                         storage.setValue(v2, initial);
                       });
  expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                       "foreign checkpoint", [&] {
                         storage.pop(Checkpoint{foreign_domain.current(), 1});
                       });

  std::string const before = storage.value(v0).text();
  ThrowingValue::failCopyAfter(0);
  try
  {
    storage.setValue(v0, ThrowingValue("must-not-commit"));
    fail("throwing storage value copy expected");
  }
  catch (SyntheticFailure const&)
  {
    ThrowingValue::disableFailures();
  }
  require(storage.value(v0).text() == before,
          "throwing value mutation has strong commit");

  /* The same guarantee one copy later.  A mutation inside a checkpoint takes
   * the caller's value and then journals the value it displaces, so there is
   * a second copy, and it is the one that records the old value for a later
   * pop.  It has to be as recoverable as the first: nothing written, nothing
   * logged, and the level still poppable afterwards. */
  Checkpoint const logging = storage.push();
  std::size_t const logged = storage.changeCount();
  ThrowingValue::failCopyAfter(1);
  try
  {
    storage.setValue(v0, ThrowingValue("must-not-log"));
    fail("throwing storage trail copy expected");
  }
  catch (SyntheticFailure const&)
  {
    ThrowingValue::disableFailures();
  }
  require(storage.value(v0).text() == before &&
              storage.changeCount() == logged,
          "throwing trail record has strong commit");
  storage.pop(logging);
  require(storage.value(v0).text() == before,
          "level survived a failed mutation inside it");

  Checkpoint const corrupt = storage.push();
  storage.setValue(v0, ThrowingValue("corrupt-level-value"));
  stp::lra::detail::TrailedStorageTestAccess::corruptTopLevelChangeSize(
      storage, storage.changeCount() + 1U);
  expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                       "corrupted value trail size", [&] {
                         storage.pop(corrupt);
                       });
  storage.clearCandidate();
  require(storage.variableCount() == 2 && storage.levelCount() == 0 &&
              storage.changeCount() == 0 &&
              storage.membership().activeIndices().empty(),
          "logical candidate clear retains registered values only");
  expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                       "cleared checkpoint stale", [&] {
                         storage.pop(corrupt);
                       });

  VariableId const stale = v0;
  CoreGeneration const successor = domain.advance();
  storage.reset(successor);
  require(storage.generation() == successor && storage.variableCount() == 0 &&
              storage.membership().capacity() == 0,
          "destructive trailed reset releases storage");
  expectStorageFailure(StorageFailureKind::InvalidGeneration,
                       "stale variable after reset", [&] {
                         (void)storage.value(stale);
                       });
  expectStorageFailure(StorageFailureKind::InvalidGeneration,
                       "non-successor reset", [&] {
                         storage.reset(foreign_domain.current());
                       });

  std::cout << "{\"mode\":\"trail\",\"passed\":true,"
               "\"nested_levels\":2,\"repeated_mutations\":2,"
               "\"growth_rollback\":true,\"corruption_rejected\":true}"
            << std::endl;
}

ExactRational rational(char const* text)
{
  return ExactRational::parseDecimalOrFraction(text);
}

void requireDescending(std::vector<BoundRef> const& refs)
{
  for (std::size_t index = 1; index != refs.size(); ++index)
  {
    require(refs[index - 1U].ordinal() > refs[index].ordinal(),
            "equal exact values ordered by descending ordinal");
  }
}

void testStrongOrdering()
{
  NumberBudget budget(generousLimits());
  NumberOperationScope scope(budget);
  GenerationDomain domain;
  BoundArena<ExactKey> arena(domain.current());
  std::vector<BoundRef> ties;
  ties.reserve(8000);
  ExactRational equal = rational("123456789012345678901234567890/7");
  for (std::size_t index = 0; index != 8000; ++index)
  {
    ties.push_back(arena.emplace(equal, -3));
  }
  std::mt19937_64 generator(UINT64_C(0x4d31423032534f52));
  std::shuffle(ties.begin(), ties.end(), generator);
  std::vector<BoundRef> adversarial(ties.rbegin(), ties.rend());
  StorageMetrics metrics{};
  auto value_of = [&arena](BoundRef ref) -> ExactKey const& {
    return arena.at(ref);
  };
  stp::lra::sortBoundRefsStrongCommit(ties, value_of, metrics);
  requireDescending(ties);
  stp::lra::sortBoundRefsStrongCommit(adversarial, value_of, metrics);
  require(adversarial == ties, "repeated adversarial tie sort deterministic");

  BoundArena<ExactKey> mixed_arena(domain.current());
  std::vector<BoundRef> mixed;
  mixed.push_back(mixed_arena.emplace(rational("0"), 1));
  mixed.push_back(mixed_arena.emplace(rational("-999999999999999999/3"), 0));
  mixed.push_back(mixed_arena.emplace(rational("0"), -1));
  mixed.push_back(mixed_arena.emplace(
      rational("999999999999999999999999999999999/11"), 0));
  mixed.push_back(mixed_arena.emplace(rational("0"), 0));
  std::reverse(mixed.begin(), mixed.end());
  stp::lra::sortBoundRefsStrongCommit(
      mixed,
      [&mixed_arena](BoundRef ref) -> ExactKey const& {
        return mixed_arena.at(ref);
      },
      metrics);
  require(mixed[0].ordinal() == 1 && mixed[1].ordinal() == 2 &&
              mixed[2].ordinal() == 4 && mixed[3].ordinal() == 0 &&
              mixed[4].ordinal() == 3,
          "mixed rational infinitesimal and ordinal order");

  std::vector<BoundRef> duplicate{ties[0], ties[1], ties[0]};
  auto const duplicate_before = duplicate;
  expectStorageFailure(StorageFailureKind::InvalidOrdinal,
                       "duplicate bound sort", [&] {
                         stp::lra::sortBoundRefsStrongCommit(
                             duplicate, value_of, metrics);
                       });
  require(duplicate == duplicate_before,
          "duplicate rejection preserves original sequence");
  GenerationDomain foreign;
  BoundArena<ExactKey> foreign_arena(foreign.current());
  BoundRef const foreign_ref = foreign_arena.emplace(rational("0"), 0);
  std::vector<BoundRef> cross{ties[0], foreign_ref};
  auto const cross_before = cross;
  expectStorageFailure(StorageFailureKind::InvalidGeneration,
                       "cross-generation sort", [&] {
                         stp::lra::sortBoundRefsStrongCommit(
                             cross, value_of, metrics);
                       });
  require(cross == cross_before,
          "cross-generation rejection preserves original");

  BoundRef const unallocated(domain.current(),
                             static_cast<std::uint32_t>(arena.size()));
  std::vector<BoundRef> out_of_range{ties[0], unallocated};
  auto const out_of_range_before = out_of_range;
  expectStorageFailure(StorageFailureKind::InvalidOrdinal,
                       "unallocated bound sort", [&] {
                         stp::lra::sortBoundRefsStrongCommit(
                             out_of_range, value_of, metrics);
                       });
  require(out_of_range == out_of_range_before,
          "out-of-range rejection preserves original");

  ExactKey::corruptResult(true);
  std::vector<BoundRef> corrupt{ties[0], ties[1]};
  auto const corrupt_before = corrupt;
  expectStorageFailure(StorageFailureKind::InvariantViolation,
                       "corrupt comparator", [&] {
                         stp::lra::sortBoundRefsStrongCommit(
                             corrupt, value_of, metrics);
                       });
  ExactKey::corruptResult(false);
  require(corrupt == corrupt_before,
          "comparator corruption preserves sequence");
  require(metrics.sort_attempts == metrics.sort_successes +
                                      metrics.sort_failures &&
              metrics.sort_successes == 3 && metrics.sorts == 3 &&
              metrics.sort_failures == 4,
          "sort metrics classify every attempt");

  std::cout << "{\"mode\":\"sort\",\"passed\":true,"
               "\"equal_value_ties\":8000,\"repeat_orders\":2,"
               "\"duplicate_policy\":\"reject\","
               "\"sort_attempts\":"
            << metrics.sort_attempts << ",\"sort_failures\":"
            << metrics.sort_failures << "}" << std::endl;
}

void testMissingAndLimitedNumberScopes()
{
  GenerationDomain domain;
  NumberBudget owner(generousLimits());
  BoundArena<ExactKey> arena(domain.current());
  std::vector<BoundRef> refs;
  {
    NumberOperationScope scope(owner);
    refs.push_back(arena.emplace(rational("2/3"), 0));
    refs.push_back(arena.emplace(rational("1/3"), 0));
  }
  auto value_of = [&arena](BoundRef ref) -> ExactKey const& {
    return arena.at(ref);
  };
  auto const before = refs;
  try
  {
    stp::lra::sortBoundRefsStrongCommit(refs, value_of);
    fail("missing number scope must fail");
  }
  catch (NumberFailure const& failure)
  {
    require(failure.kind() == NumberFailureKind::InternalError,
            "missing number scope typed failure");
  }
  require(refs == before, "missing scope preserves sort input");
  {
    NumberOperationScope scope(owner);
    stp::lra::sortBoundRefsStrongCommit(refs, value_of);
  }
  require(refs.front().ordinal() == 1,
          "retry under owner scope succeeds");

  NumberBudget limited(NumberLimits{64, 8, UINT64_C(1048576),
                                    UINT64_C(4096)});
  BoundArena<ExactKey> limited_arena(domain.current());
  std::vector<BoundRef> limited_refs;
  {
    NumberOperationScope scope(limited);
    limited_refs.push_back(limited_arena.emplace(
        ExactRational(std::int64_t{61}, std::uint64_t{59}), 0));
    limited_refs.push_back(limited_arena.emplace(
        ExactRational(std::int64_t{53}, std::uint64_t{47}), 0));
    auto const limited_before = limited_refs;
    try
    {
      stp::lra::sortBoundRefsStrongCommit(
          limited_refs,
          [&limited_arena](BoundRef ref) -> ExactKey const& {
            return limited_arena.at(ref);
          });
      fail("comparison budget preflight must fail");
    }
    catch (NumberFailure const& failure)
    {
      require(failure.kind() == NumberFailureKind::ResourceLimit,
              "comparison resource failure classification");
    }
    require(limited_refs == limited_before,
            "comparison resource failure preserves sort input");
  }
  std::cout << "{\"mode\":\"scope\",\"passed\":true,"
               "\"missing_scope_rejected\":true,"
               "\"comparison_budget_rejected\":true,"
               "\"retry\":true}"
            << std::endl;
}

void runAllocationWorkload(DenseMembership& dense,
                           TrailedValueStorage<ThrowingValue>& trail,
                           VariableId variable,
                           std::vector<int>& sortable)
{
  dense.ensureSize(8192);
  dense.set(4096, true);
  (void)dense.activeIndices();
  (void)stp::lra::debugString(dense);
  trail.ensureVariable(variable, ThrowingValue("initial"));
  Checkpoint const checkpoint = trail.push();
  trail.setValue(variable, ThrowingValue("changed"));
  trail.markPresent(variable, true);
  trail.pop(checkpoint);
  StorageMetrics metrics{};
  stp::lra::strongCommitSort(sortable, std::less<int>{}, metrics);
}

std::pair<std::uint64_t, std::uint64_t> measureAllocationWorkload()
{
  GenerationDomain domain;
  VariableId variable(domain.current(), 0);
  DenseMembership dense;
  TrailedValueStorage<ThrowingValue> trail(domain.current());
  std::vector<int> sortable{9, 1, 7, 3, 5};
  allocation_fault::beginCount();
  runAllocationWorkload(dense, trail, variable, sortable);
  return allocation_fault::endCount();
}

// Growing the core one variable at a time must cost a bounded number of
// allocations per variable. Every container used to grow by copying itself
// and swapping the copy in, so the n-th variable copied the n-1 before it --
// quadratic allocations over the build, and the reason a few thousand
// variables took seconds before the first pivot. The bound here is loose on
// purpose: a dozen or so containers each reserving geometrically stays far
// under it, and the copying idiom is thousands of times over it at this size.
void testGrowthIsAmortised()
{
  constexpr std::size_t variables = 2048;
  NumberLimits const limits{50000, 50000, UINT64_C(128) * 1024U * 1024U,
                            UINT64_C(4) * 1024U * 1024U};
  // The core scopes its own budget around every call; an outer scope on
  // another budget would be refused as a conflict.
  stp::lra::ExactLraCore core(limits);
  allocation_fault::beginCount();
  for (std::size_t i = 0; i < variables; ++i)
  {
    auto const added = core.addVariable();
    require(added.status == stp::lra::InputStatus::Accepted &&
                added.value.has_value(),
            "addVariable failed while measuring growth (status " +
                std::to_string(static_cast<int>(added.status)) + ")");
  }
  auto const counted = allocation_fault::endCount();
  require(counted.first < 32U * variables,
          "adding " + std::to_string(variables) + " variables took " +
              std::to_string(counted.first) +
              " allocations: growth is not amortised");
  std::cout << "growth: " << variables << " variables, " << counted.first
            << " allocations" << std::endl;
}

void runFaultSweep()
{
  auto const measured = measureAllocationWorkload();
  require(measured.first != 0, "allocation workload exposes fault points");
  std::uint64_t injected_allocations = 0;
  for (std::uint64_t index = 0; index != measured.first; ++index)
  {
    GenerationDomain domain;
    VariableId variable(domain.current(), 0);
    DenseMembership dense;
    TrailedValueStorage<ThrowingValue> trail(domain.current());
    std::vector<int> sortable{9, 1, 7, 3, 5};
    allocation_fault::arm(index);
    try
    {
      runAllocationWorkload(dense, trail, variable, sortable);
      fail("injected C++ allocation point did not fail");
    }
    catch (StorageFailure const& failure)
    {
      allocation_fault::disarm();
      require(failure.kind() == StorageFailureKind::AllocationFailure,
              "C++ allocation failure translated");
      ++injected_allocations;
    }
    allocation_fault::disarm();
    for (std::uint8_t byte : dense.bytes())
    {
      require(byte <= 1U, "fault leaves dense bytes valid");
    }
    DenseMembership recovery_dense;
    TrailedValueStorage<ThrowingValue> recovery_trail(domain.current());
    std::vector<int> recovery_sort{9, 1, 7, 3, 5};
    runAllocationWorkload(recovery_dense, recovery_trail, variable,
                          recovery_sort);
    require(recovery_sort == std::vector<int>({1, 3, 5, 7, 9}),
            "recovery after every C++ allocation failure");
  }

  NumberBudget budget(generousLimits());
  NumberOperationScope scope(budget);
  GenerationDomain domain;
  BoundArena<ExactKey> arena(domain.current());
  std::vector<BoundRef> refs;
  /* Wider than the word representation on purpose. The check below wants a
   * native allocation point to inject at, and a value that fits a word is
   * compared without ever reaching IMath -- so a small fraction here leaves
   * that check with nothing to find and nothing to test. Both terms are odd
   * and differ by two, so they are coprime and survive canonicalisation at
   * this width; 26 digits clears the 2^62 word limit and the 2^31 one used
   * where there is no 128-bit type. */
  for (std::size_t index = 0; index != 32; ++index)
  {
    refs.push_back(arena.emplace(
        rational("10000000000000000000000001/10000000000000000000000003"), 0));
  }
  std::shuffle(refs.begin(), refs.end(),
               std::mt19937_64(UINT64_C(0x4641554c54534f52)));
  auto value_of = [&arena](BoundRef ref) -> ExactKey const& {
    return arena.at(ref);
  };

  ExactKey::beginComparisonCount();
  std::vector<BoundRef> counted(refs);
  stp::lra::sortBoundRefsStrongCommit(counted, value_of);
  std::uint64_t const comparison_points = ExactKey::endComparisonCount();
  require(comparison_points > refs.size(),
          "sort exposes complete comparison surface");
  std::uint64_t injected_comparisons = 0;
  for (std::uint64_t index = 0; index != comparison_points; ++index)
  {
    std::vector<BoundRef> candidate(refs);
    ExactKey::failCompareAfter(static_cast<std::int64_t>(index));
    try
    {
      stp::lra::sortBoundRefsStrongCommit(candidate, value_of);
      fail("injected comparison point did not fail");
    }
    catch (SyntheticFailure const&)
    {
      ExactKey::failCompareAfter(-1);
      ++injected_comparisons;
    }
    require(candidate == refs,
            "every comparison failure preserves original sequence");
    stp::lra::sortBoundRefsStrongCommit(candidate, value_of);
    requireDescending(candidate);
  }

  stp_lra_imath_test_fail_nth(unlimited);
  std::vector<BoundRef> native_counted(refs);
  stp::lra::sortBoundRefsStrongCommit(native_counted, value_of);
  std::uint64_t const native_points =
      stp_lra_imath_test_allocation_attempts();
  stp_lra_imath_test_disable_failures();
  require(native_points != 0, "exact comparisons expose native allocations");
  std::uint64_t injected_native = 0;
  for (std::uint64_t index = 0; index != native_points; ++index)
  {
    std::vector<BoundRef> candidate(refs);
    stp_lra_imath_test_fail_nth(index);
    try
    {
      stp::lra::sortBoundRefsStrongCommit(candidate, value_of);
      fail("injected exact comparison allocation did not fail");
    }
    catch (NumberFailure const& failure)
    {
      stp_lra_imath_test_disable_failures();
      require(failure.kind() == NumberFailureKind::AllocationFailure,
              "exact comparison allocation classification");
      ++injected_native;
    }
    require(candidate == refs,
            "native comparison allocation failure preserves sequence");
    stp_lra_imath_test_disable_failures();
    stp::lra::sortBoundRefsStrongCommit(candidate, value_of);
    requireDescending(candidate);
  }
  stp_lra_imath_test_disable_failures();

  std::cout << "{\"mode\":\"fault\",\"passed\":true,"
               "\"cpp_allocation_points\":"
            << measured.first << ",\"cpp_allocation_bytes\":"
            << measured.second << ",\"cpp_injected\":"
            << injected_allocations << ",\"comparison_points\":"
            << comparison_points << ",\"comparison_injected\":"
            << injected_comparisons << ",\"native_allocation_points\":"
            << native_points << ",\"native_injected\":" << injected_native
            << ",\"recovery\":true}" << std::endl;
}

void independentWorkload(unsigned worker)
{
  for (unsigned round = 0; round != 100; ++round)
  {
    NumberBudget budget(generousLimits());
    NumberOperationScope scope(budget);
    GenerationDomain domain;
    CoreGeneration generation = domain.current();
    MonotonicIdAllocator<VariableId> ids(generation);
    VariableId variable = ids.allocate();
    TrailedValueStorage<ThrowingValue> trail(generation);
    trail.ensureVariable(variable, ThrowingValue("zero"));
    Checkpoint checkpoint = trail.push();
    trail.setValue(variable, ThrowingValue(std::to_string(worker)));
    trail.markPresent(variable, true);
    trail.pop(checkpoint);
    require(!trail.hasValue(variable),
            "concurrent independent trail rollback");

    DenseMembership dense;
    dense.ensureSize(1024);
    std::size_t index = (worker * 131U + round * 17U) % dense.size();
    dense.set(index, true);
    require(dense.test(index), "concurrent independent dense state");

    BoundArena<ExactKey> arena(generation);
    std::vector<BoundRef> refs;
    ExactRational equal(static_cast<std::int64_t>(worker + 1U));
    for (std::size_t ordinal = 0; ordinal != 64; ++ordinal)
    {
      refs.push_back(arena.emplace(equal, 0));
    }
    std::reverse(refs.begin(), refs.end());
    stp::lra::sortBoundRefsStrongCommit(
        refs, [&arena](BoundRef ref) -> ExactKey const& {
          return arena.at(ref);
        });
    requireDescending(refs);
  }
}

void runConcurrency()
{
  std::atomic<unsigned> completed{0};
  std::atomic<bool> failed{false};
  std::vector<std::thread> threads;
  for (unsigned worker = 0; worker != 8; ++worker)
  {
    threads.emplace_back([worker, &completed, &failed] {
      try
      {
        independentWorkload(worker);
        ++completed;
      }
      catch (...)
      {
        failed = true;
      }
    });
  }
  for (auto& thread : threads)
  {
    thread.join();
  }
  require(!failed && completed == 8,
          "eight independent concurrent storage workers");
  std::cout << "{\"mode\":\"concurrency\",\"passed\":true,"
               "\"threads\":8,\"workloads_per_thread\":100,"
               "\"shared_instances\":false}"
            << std::endl;
}

void testDebugAllocationTranslation()
{
  GenerationDomain domain;
  BoundRef reference(domain.current(), 4294967294U);
  allocation_fault::beginCount();
  std::string expected = stp::lra::debugString(reference);
  auto const measured = allocation_fault::endCount();
  require(expected == "bound@1:1#4294967294" && measured.first != 0,
          "huge ID deterministic debug string");
  std::uint64_t translated = 0;
  for (std::uint64_t index = 0; index != measured.first; ++index)
  {
    allocation_fault::arm(index);
    expectStorageFailure(StorageFailureKind::AllocationFailure,
                         "debug allocation", [&] {
                           (void)stp::lra::debugString(reference);
                         });
    ++translated;
  }
  std::cout << "{\"mode\":\"debug\",\"passed\":true,"
               "\"allocation_points\":"
            << measured.first << ",\"translated\":" << translated
            << ",\"deterministic\":true}" << std::endl;
}

}  // namespace

int main(int argc, char** argv)
{
  try
  {
    if (argc != 2)
    {
      fail("expected one test mode");
    }
    std::string const mode(argv[1]);
    if (mode == "vector")
    {
      testDirectVectorsAndConversions();
    }
    else if (mode == "dense")
    {
      testDenseMembership();
    }
    else if (mode == "trail")
    {
      testTrailedStorage();
    }
    else if (mode == "sort")
    {
      testStrongOrdering();
    }
    else if (mode == "scope")
    {
      testMissingAndLimitedNumberScopes();
    }
    else if (mode == "growth")
    {
      testGrowthIsAmortised();
    }
    else if (mode == "fault")
    {
      runFaultSweep();
    }
    else if (mode == "concurrency")
    {
      runConcurrency();
    }
    else if (mode == "debug")
    {
      testDebugAllocationTranslation();
    }
    else
    {
      fail("unknown test mode: " + mode);
    }
    require(ThrowingValue::live() == 0,
            "all throwing storage values destroyed");
    return 0;
  }
  catch (std::exception const& exception)
  {
    allocation_fault::disarm();
    stp_lra_imath_test_disable_failures();
    std::cerr << "FAIL: " << exception.what() << std::endl;
    return 1;
  }
}

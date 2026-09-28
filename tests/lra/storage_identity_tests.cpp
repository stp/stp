#include "support/BoundActivityTrail.h"
#include "support/NoInline.h"
#include "Storage/LraIds.h"
#include "Storage/StorageFailure.h"
#include "Storage/StorageMetrics.h"

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
#include <optional>
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

void beforeAllocation()
{
  if (count_enabled)
  {
    ++allocation_count;
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
  count_enabled = true;
}

std::uint64_t endCount() noexcept
{
  count_enabled = false;
  return allocation_count;
}
}  // namespace allocation_fault

STP_LRA_TEST_NOINLINE void* operator new(std::size_t size)
{
  allocation_fault::beforeAllocation();
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

using stp::lra::AtomId;
using stp::lra::BoundActivityTrail;
using stp::lra::BoundArena;
using stp::lra::BoundRef;
using stp::lra::Checkpoint;
using stp::lra::CoreGeneration;
using stp::lra::GenerationDomain;
using stp::lra::GenerationIdHash;
using stp::lra::MonotonicIdAllocator;
using stp::lra::OriginId;
using stp::lra::RowId;
using stp::lra::StorageFailure;
using stp::lra::StorageFailureKind;
using stp::lra::VariableId;

[[noreturn]] void fail(std::string const& message)
{
  throw std::runtime_error(message);
}

void require(bool condition, std::string const& message)
{
  if (!condition)
  {
    fail(message);
  }
}

void require(bool condition, char const* message)
{
  if (!condition)
  {
    allocation_fault::disarm();
    fail(message);
  }
}

template <class Function>
void expectStorageFailure(StorageFailureKind expected,
                          char const* label,
                          Function&& operation)
{
  try
  {
    operation();
  }
  catch (StorageFailure const& failure)
  {
    allocation_fault::disarm();
    require(failure.kind() == expected,
            std::string(label) + ": wrong failure kind");
    require(failure.operation() != nullptr &&
                std::strlen(failure.operation()) != 0,
            std::string(label) + ": empty operation");
    return;
  }
  catch (std::bad_alloc const&)
  {
    allocation_fault::disarm();
    fail(std::string(label) +
         ": raw bad_alloc escaped typed storage translation");
  }
  allocation_fault::disarm();
  fail(std::string(label) + ": expected StorageFailure");
}

std::uint64_t independentIdHash(CoreGeneration generation,
                                std::uint32_t ordinal)
{
  std::uint64_t result = UINT64_C(14695981039346656037);
  auto byte = [&result](std::uint8_t value) {
    result ^= value;
    result *= UINT64_C(1099511628211);
  };
  for (unsigned shift = 64U; shift != 0; shift -= 8U)
  {
    byte(static_cast<std::uint8_t>(generation.value >> (shift - 8U)));
  }
  for (unsigned shift = 32U; shift != 0; shift -= 8U)
  {
    byte(static_cast<std::uint8_t>(ordinal >> (shift - 8U)));
  }
  return result;
}

void testIdsAndGenerations()
{
  static_assert(!std::is_constructible_v<RowId, VariableId>);
  static_assert(!std::is_convertible_v<RowId, VariableId>);
  static_assert(!std::is_constructible_v<BoundRef, AtomId>);
  static_assert(!std::is_copy_constructible_v<GenerationDomain>);
  static_assert(!std::is_move_constructible_v<GenerationDomain>);
  static_assert(std::is_standard_layout_v<VariableId>);
  static_assert(std::is_trivially_copyable_v<VariableId>);
  static_assert(std::is_same_v<
                decltype(std::optional<BoundRef>{}), std::optional<BoundRef>>);

  GenerationDomain first;
  require(first.current().valid(), "first generation valid");
  require(first.current().domainOrdinal() == 1, "first domain ordinal is one");
  require(first.current().epoch() == 1, "first epoch is one");
  GenerationDomain second;
  require(second.current().domainOrdinal() != first.current().domainOrdinal(),
          "independent domains differ");

  CoreGeneration const first_generation = first.current();
  CoreGeneration const advanced = first.advance();
  require(advanced.domainOrdinal() == first_generation.domainOrdinal(),
          "advance preserves domain");
  require(advanced.epoch() == 2, "advance increments epoch");
  require(stp::lra::isImmediateSuccessor(first_generation, advanced),
          "immediate successor accepted");
  require(!stp::lra::isImmediateSuccessor(advanced, first_generation),
          "reverse successor rejected");
  require(!stp::lra::isImmediateSuccessor(first_generation,
                                           second.current()),
          "cross-domain successor rejected");

  VariableId variable(first_generation, 7);
  VariableId variable_copy(first_generation, 7);
  VariableId variable_next(first_generation, 8);
  require(variable == variable_copy && variable != variable_next,
          "ID equality includes ordinal");
  require(variable < variable_next, "ID ordinal ordering");
  require(variable_next < VariableId(advanced, 0), "ID generation ordering");
  GenerationIdHash<VariableId> hash;
  std::uint64_t const expected_hash =
      independentIdHash(first_generation, variable.ordinal());
  // A 32-bit size_t gets the two halves folded together, not the low half.
  std::size_t const expected_size_hash =
      sizeof(std::size_t) >= sizeof(std::uint64_t)
          ? static_cast<std::size_t>(expected_hash)
          : static_cast<std::size_t>(
                static_cast<std::uint32_t>(expected_hash) ^
                static_cast<std::uint32_t>(expected_hash >> 32U));
  require(hash(variable) == expected_size_hash, "fixed-byte FNV-1a hash");
  require(stp::lra::debugString(variable) == "variable@1:1#7",
          "deterministic variable formatting");
  require(stp::lra::debugString(OriginId{9, 11}) == "origin(9:11)",
          "deterministic origin formatting");
  require(stp::lra::debugString(Checkpoint{first_generation, 4}) ==
              "checkpoint(1:1#4)",
          "deterministic checkpoint formatting");
  require(stp::lra::debugString(CoreGeneration{0}) == "generation(invalid)",
          "invalid generation formatting");
  std::uint64_t saturated = std::numeric_limits<std::uint64_t>::max();
  stp::lra::detail::saturatingIncrement(saturated);
  require(saturated == std::numeric_limits<std::uint64_t>::max(),
          "metric increment saturates");
  require(stp::lra::detail::saturatingAdd(
              saturated - 3U, 9U) == saturated,
          "metric addition saturates");
  require(stp::lra::detail::saturatingMultiply(saturated, 2U) == saturated,
          "logical byte multiplication saturates");

  expectStorageFailure(StorageFailureKind::InvalidGeneration,
                       "zero generation ID",
                       [] { (void)VariableId(CoreGeneration{0}, 0); });
  CoreGeneration const reserved_domain{
      (UINT64_C(0xffffffff) << 32U) | UINT64_C(1)};
  CoreGeneration const reserved_epoch{
      (UINT64_C(1) << 32U) | UINT64_C(0xffffffff)};
  require(!reserved_domain.valid() && !reserved_epoch.valid(),
          "reserved generation fields invalid");
  expectStorageFailure(StorageFailureKind::InvalidOrdinal,
                       "reserved ordinal ID", [&] {
                         (void)VariableId(
                             first_generation, VariableId::invalid_ordinal);
                       });
  VariableId maximum(first_generation,
                     VariableId::maximum_usable_ordinal);
  require(maximum.valid(), "maximum usable ordinal accepted");

  MonotonicIdAllocator<RowId> row_ids(first_generation);
  require(row_ids.allocate().ordinal() == 0, "allocator starts at zero");
  require(row_ids.allocate().ordinal() == 1, "allocator monotonic");
  stp::lra::detail::StorageTestAccess::setNextOrdinal(
      row_ids, RowId::maximum_usable_ordinal);
  require(row_ids.allocate().ordinal() == RowId::maximum_usable_ordinal,
          "allocator emits maximum usable ordinal");
  std::uint64_t const stopped_count = row_ids.allocatedCount();
  expectStorageFailure(StorageFailureKind::ResourceLimit,
                       "ordinal exhaustion", [&] { (void)row_ids.allocate(); });
  require(row_ids.allocatedCount() == stopped_count,
          "ordinal exhaustion preserves counter");

  GenerationDomain epoch_domain;
  stp::lra::detail::StorageTestAccess::setEpoch(
      epoch_domain, std::numeric_limits<std::uint32_t>::max() - 2U);
  CoreGeneration const final_epoch = epoch_domain.advance();
  require(final_epoch.epoch() ==
              std::numeric_limits<std::uint32_t>::max() - 1U,
          "maximum usable epoch emitted");
  expectStorageFailure(StorageFailureKind::Exhausted,
                       "epoch exhaustion",
                       [&] { (void)epoch_domain.advance(); });
  require(epoch_domain.current() == final_epoch,
          "epoch exhaustion preserves generation");

  std::uint64_t const old_domain =
      stp::lra::detail::StorageTestAccess::exchangeNextDomainOrdinal(
          std::numeric_limits<std::uint32_t>::max());
  expectStorageFailure(StorageFailureKind::Exhausted,
                       "domain exhaustion", [] { GenerationDomain exhausted; });
  std::uint64_t const exhausted_value =
      stp::lra::detail::StorageTestAccess::exchangeNextDomainOrdinal(old_domain);
  require(exhausted_value == std::numeric_limits<std::uint32_t>::max(),
          "domain exhaustion does not wrap or mutate");

  std::cout << "{\"domain_exhaustion\":true,\"epoch_exhaustion\":true,"
               "\"hash\":"
            << expected_hash
            << ",\"maximum_ordinal\":"
            << VariableId::maximum_usable_ordinal
            << ",\"mode\":\"ids\",\"passed\":true}\n";
}

struct StressValue
{
  static std::atomic<std::uint64_t> constructed;
  static std::atomic<std::uint64_t> destroyed;

  explicit StressValue(std::uint32_t value)
      : ordinal(value), text("arena-value-" + std::to_string(value))
  {
    constructed.fetch_add(1, std::memory_order_relaxed);
  }
  ~StressValue() noexcept
  {
    destroyed.fetch_add(1, std::memory_order_relaxed);
  }
  StressValue(StressValue const&) = delete;
  StressValue& operator=(StressValue const&) = delete;

  std::uint32_t ordinal;
  std::string text;
};

std::atomic<std::uint64_t> StressValue::constructed{0};
std::atomic<std::uint64_t> StressValue::destroyed{0};

struct ResetObserver
{
  static BoundArena<ResetObserver>* owner;
  static CoreGeneration destruction_generation;
  static std::uint64_t ordering_violations;

  ResetObserver() = default;
  ~ResetObserver() noexcept
  {
    if (owner != nullptr && owner->generation() != destruction_generation)
    {
      ++ordering_violations;
    }
  }
};

BoundArena<ResetObserver>* ResetObserver::owner = nullptr;
CoreGeneration ResetObserver::destruction_generation{0};
std::uint64_t ResetObserver::ordering_violations = 0;

void testArenaStress()
{
  constexpr std::uint32_t value_count = 250000;
  constexpr std::size_t sample_count = 1032;
  StressValue::constructed.store(0, std::memory_order_relaxed);
  StressValue::destroyed.store(0, std::memory_order_relaxed);
  GenerationDomain domain;
  BoundArena<StressValue> arena(domain.current());
  static_assert(!std::is_copy_constructible_v<decltype(arena)>);
  static_assert(!std::is_move_constructible_v<decltype(arena)>);

  std::vector<std::uint32_t> sample_indices;
  sample_indices.reserve(sample_count);
  for (std::size_t index = 0; index != sample_count; ++index)
  {
    sample_indices.push_back(static_cast<std::uint32_t>(
        (index * (value_count - 1ULL)) / (sample_count - 1ULL)));
  }
  require(std::adjacent_find(sample_indices.begin(), sample_indices.end()) ==
              sample_indices.end(),
          "arena sample indices are unique");

  struct Sample
  {
    BoundRef ref;
    StressValue* address;
  };
  std::vector<Sample> samples;
  samples.reserve(sample_count);
  auto const started = std::chrono::steady_clock::now();
  std::size_t next_sample = 0;
  BoundRef first(domain.current(), 0);
  BoundRef middle(domain.current(), 0);
  BoundRef final(domain.current(), 0);
  for (std::uint32_t index = 0; index != value_count; ++index)
  {
    BoundRef const ref = arena.emplace(index);
    require(ref.ordinal() == index, "arena ordinal matches insertion");
    if (index == 0)
    {
      first = ref;
    }
    if (index == value_count / 2U)
    {
      middle = ref;
    }
    if (index == value_count - 1U)
    {
      final = ref;
    }
    if (next_sample != sample_indices.size() &&
        index == sample_indices[next_sample])
    {
      samples.push_back(Sample{ref, &arena.at(ref)});
      ++next_sample;
    }
    if ((index & 1023U) == 1023U || index == value_count - 1U)
    {
      for (Sample const& sample : samples)
      {
        require(&arena.at(sample.ref) == sample.address,
                "deque address remains stable");
        require(sample.address->ordinal == sample.ref.ordinal(),
                "retained value remains stable");
      }
    }
  }
  auto const elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
      std::chrono::steady_clock::now() - started);
  require(samples.size() == sample_count, "all retained samples collected");
  require(arena.size() == value_count, "arena stress size");
  require(arena.at(first).ordinal == 0, "first lookup after growth");
  require(arena.at(middle).ordinal == value_count / 2U,
          "middle lookup after growth");
  require(arena.at(final).ordinal == value_count - 1U,
          "final lookup after growth");
  require(arena.logicalBytes() ==
              static_cast<std::uint64_t>(value_count) * sizeof(StressValue),
          "logical arena bytes");
  require(arena.metrics().arena_values == value_count &&
              arena.metrics().peak_arena_values == value_count,
          "arena metrics");

  GenerationDomain foreign_domain;
  BoundRef const foreign(foreign_domain.current(), 0);
  expectStorageFailure(StorageFailureKind::InvalidGeneration,
                       "cross-domain arena lookup",
                       [&] { (void)arena.at(foreign); });
  require(!arena.contains(foreign), "foreign ref not contained");
  BoundRef const at_size(domain.current(), value_count);
  expectStorageFailure(StorageFailureKind::InvalidOrdinal,
                       "ordinal at size", [&] { (void)arena.at(at_size); });
  BoundRef const maximum(domain.current(), BoundRef::maximum_usable_ordinal);
  expectStorageFailure(StorageFailureKind::InvalidOrdinal,
                       "maximum unallocated ordinal",
                       [&] { (void)arena.at(maximum); });
  CoreGeneration const future_generation{
      (static_cast<std::uint64_t>(domain.current().domainOrdinal()) << 32U) |
      static_cast<std::uint64_t>(domain.current().epoch() + 1U)};
  BoundRef const future(future_generation, 0);
  expectStorageFailure(StorageFailureKind::InvalidGeneration,
                       "future generation lookup",
                       [&] { (void)arena.at(future); });
  CoreGeneration const bit_flipped_generation{
      domain.current().value ^ UINT64_C(2)};
  BoundRef const generation_corrupt(bit_flipped_generation, 0);
  expectStorageFailure(StorageFailureKind::InvalidGeneration,
                       "bit-flipped generation",
                       [&] { (void)arena.at(generation_corrupt); });
  BoundRef const ordinal_corrupt(domain.current(),
                                 first.ordinal() ^ UINT32_C(0x40000000));
  expectStorageFailure(StorageFailureKind::InvalidOrdinal,
                       "bit-flipped ordinal",
                       [&] { (void)arena.at(ordinal_corrupt); });

  CoreGeneration const old_generation = domain.current();
  CoreGeneration const next_generation = domain.advance();
  arena.reset(next_generation);
  require(arena.empty(), "destructive reset empties arena");
  require(StressValue::destroyed.load(std::memory_order_relaxed) == value_count,
          "reset destroys each arena value exactly once");
  expectStorageFailure(StorageFailureKind::InvalidGeneration,
                       "stale ref after reset",
                       [&] { (void)arena.at(final); });
  require(!arena.contains(BoundRef(old_generation, 0)),
          "old generation absent after reset");
  BoundRef const new_zero = arena.emplace(900001U);
  require(new_zero.ordinal() == 0, "new generation restarts ordinal zero");
  require(arena.metrics().generation_resets == 1 &&
              arena.metrics().generations_created == 2,
          "reset lifetime metrics");

  {
    GenerationDomain ordering_domain;
    BoundArena<ResetObserver> ordering_arena(ordering_domain.current());
    (void)ordering_arena.emplace();
    ResetObserver::owner = &ordering_arena;
    ResetObserver::destruction_generation = ordering_domain.current();
    ResetObserver::ordering_violations = 0;
    ordering_arena.reset(ordering_domain.advance());
    ResetObserver::owner = nullptr;
    require(ResetObserver::ordering_violations == 0,
            "old arena values destroyed before generation publication");
  }

  std::cout << "{\"elapsed_us\":" << elapsed.count()
            << ",\"insertions\":" << value_count
            << ",\"logical_bytes\":"
            << static_cast<std::uint64_t>(value_count) * sizeof(StressValue)
            << ",\"mode\":\"arena\",\"passed\":true,"
               "\"retained_addresses\":"
            << samples.size()
            << ",\"reset_destruction_order\":true}\n";
}

void verifyActive(BoundActivityTrail const& trail,
                  std::vector<std::uint32_t> const& expected,
                  std::string const& label)
{
  require(trail.activeSize() == expected.size(), label + ": active size");
  for (std::size_t index = 0; index != expected.size(); ++index)
  {
    require(trail.active()[index].ordinal() == expected[index],
            label + ": active sequence");
  }
}

std::uint64_t nextRandom(std::uint64_t& state) noexcept
{
  state ^= state << 13U;
  state ^= state >> 7U;
  state ^= state << 17U;
  return state;
}

void testTrail()
{
  GenerationDomain domain;
  BoundArena<std::uint32_t> arena(domain.current());
  std::vector<BoundRef> refs;
  for (std::uint32_t index = 0; index != 32; ++index)
  {
    refs.push_back(arena.emplace(index));
  }
  BoundActivityTrail trail(domain.current());
  static_assert(!std::is_copy_constructible_v<BoundActivityTrail>);
  static_assert(!std::is_move_constructible_v<BoundActivityTrail>);

  Checkpoint const a = trail.push();
  trail.append(refs[0], arena);
  Checkpoint const b = trail.push();
  trail.append(refs[1], arena);
  trail.append(refs[2], arena);
  Checkpoint const c = trail.push();
  trail.append(refs[3], arena);
  verifyActive(trail, {0, 1, 2, 3}, "nested before pop B");
  trail.pop(b);
  verifyActive(trail, {0}, "pop B restores suffix");
  Checkpoint const d = trail.push();
  require(d.depth > c.depth, "checkpoint token not reused");
  trail.append(refs[4], arena);
  trail.pop(d);
  verifyActive(trail, {0}, "pop D");
  trail.pop(a);
  verifyActive(trail, {}, "pop A");
  require(arena.size() == refs.size(), "trail rollback keeps arena values");
  for (Checkpoint stale : {b, c, d, a})
  {
    expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                         "popped checkpoint replay",
                         [&] { trail.pop(stale); });
  }
  expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                       "checkpoint underflow",
                       [&] { trail.pop(Checkpoint{domain.current(), 0}); });
  expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                       "future checkpoint",
                       [&] { trail.pop(Checkpoint{domain.current(), 999999}); });
  GenerationDomain foreign;
  expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                       "cross-core checkpoint", [&] {
                         trail.pop(Checkpoint{foreign.current(), 1});
                       });

  Checkpoint corrupt_size = trail.push();
  trail.append(refs[5], arena);
  stp::lra::detail::StorageTestAccess::corruptTopLevelSize(
      trail, trail.activeSize() + 7U);
  expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                       "corrupt checkpoint size",
                       [&] { trail.pop(corrupt_size); });
  stp::lra::detail::StorageTestAccess::corruptTopLevelSize(trail, 0);
  trail.pop(corrupt_size);
  Checkpoint corrupt_token = trail.push();
  stp::lra::detail::StorageTestAccess::corruptTopLevelToken(
      trail, corrupt_token.depth + 1U);
  expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                       "corrupt checkpoint token",
                       [&] { trail.pop(corrupt_token); });
  stp::lra::detail::StorageTestAccess::corruptTopLevelToken(
      trail, corrupt_token.depth);
  trail.pop(corrupt_token);

  BoundActivityTrail token_limit(domain.current());
  stp::lra::detail::StorageTestAccess::setNextCheckpointToken(
      token_limit, std::numeric_limits<std::uint32_t>::max() - 1ULL);
  Checkpoint const final_token = token_limit.push();
  require(final_token.depth ==
              std::numeric_limits<std::uint32_t>::max() - 1U,
          "maximum checkpoint token accepted");
  expectStorageFailure(StorageFailureKind::ResourceLimit,
                       "checkpoint exhaustion",
                       [&] { (void)token_limit.push(); });
  require(token_limit.levelCount() == 1,
          "checkpoint exhaustion preserves levels");

  trail.clearToBase();
  std::size_t const retained_capacity = trail.active().capacity();
  require(trail.activeSize() == 0 && trail.levelCount() == 0,
          "logical clear");
  require(trail.active().capacity() == retained_capacity,
          "logical clear retains active capacity");

  struct ModelLevel
  {
    std::uint32_t token;
    std::size_t size;
  };
  std::vector<std::uint32_t> model_active;
  std::vector<ModelLevel> model_levels;
  std::vector<Checkpoint> stale;
  std::uint32_t model_next_token = corrupt_token.depth + 1U;
  std::uint64_t random_state = UINT64_C(0x5354504d31423031);
  constexpr std::size_t operation_count = 10000;
  for (std::size_t operation = 0; operation != operation_count; ++operation)
  {
    std::uint64_t const choice = nextRandom(random_state) % 100U;
    if (choice < 38U)
    {
      std::size_t const selected =
          static_cast<std::size_t>(nextRandom(random_state) % refs.size());
      trail.append(refs[selected], arena);
      model_active.push_back(refs[selected].ordinal());
    }
    else if (choice < 58U)
    {
      Checkpoint const checkpoint = trail.push();
      require(checkpoint.depth == model_next_token,
              "random oracle checkpoint token");
      model_levels.push_back(ModelLevel{model_next_token,
                                        model_active.size()});
      ++model_next_token;
    }
    else if (choice < 75U && !model_levels.empty())
    {
      std::size_t const selected = static_cast<std::size_t>(
          nextRandom(random_state) % model_levels.size());
      Checkpoint checkpoint{domain.current(), model_levels[selected].token};
      for (std::size_t index = selected; index != model_levels.size(); ++index)
      {
        stale.push_back(Checkpoint{domain.current(), model_levels[index].token});
      }
      trail.pop(checkpoint);
      model_active.resize(model_levels[selected].size);
      model_levels.resize(selected);
    }
    else if (choice < 88U && !stale.empty())
    {
      Checkpoint const checkpoint = stale[static_cast<std::size_t>(
          nextRandom(random_state) % stale.size())];
      expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                           "random stale checkpoint",
                           [&] { trail.pop(checkpoint); });
    }
    else
    {
      for (ModelLevel const& level : model_levels)
      {
        stale.push_back(Checkpoint{domain.current(), level.token});
      }
      trail.clearToBase();
      model_active.clear();
      model_levels.clear();
    }
    verifyActive(trail, model_active, "random trail oracle");
    require(trail.levelCount() == model_levels.size(),
            "random level count");
  }

  CoreGeneration const old_generation = domain.current();
  CoreGeneration const next_generation = domain.advance();
  expectStorageFailure(StorageFailureKind::InvalidGeneration,
                       "trail skipped reset generation", [&] {
                         CoreGeneration skipped{
                             (static_cast<std::uint64_t>(
                                  old_generation.domainOrdinal())
                              << 32U) |
                             static_cast<std::uint64_t>(
                                 old_generation.epoch() + 2U)};
                         trail.reset(skipped);
                       });
  trail.reset(next_generation);
  arena.reset(next_generation);
  require(trail.active().capacity() == 0 && trail.levelCount() == 0,
          "destructive trail reset releases storage");
  expectStorageFailure(StorageFailureKind::InvalidCheckpoint,
                       "stale checkpoint generation after reset",
                       [&] { trail.pop(Checkpoint{old_generation, 1}); });

  struct LifetimeValue
  {
    static std::atomic<std::uint64_t>& destroyedCount()
    {
      static std::atomic<std::uint64_t> count{0};
      return count;
    }
    ~LifetimeValue() noexcept
    {
      destroyedCount().fetch_add(1, std::memory_order_relaxed);
    }
  };
  LifetimeValue::destroyedCount().store(0, std::memory_order_relaxed);
  GenerationDomain lifetime_domain;
  BoundArena<LifetimeValue> lifetime_arena(lifetime_domain.current());
  BoundActivityTrail lifetime_trail(lifetime_domain.current());
  BoundRef const lifetime_ref = lifetime_arena.emplace();
  Checkpoint const lifetime_checkpoint = lifetime_trail.push();
  lifetime_trail.append(lifetime_ref, lifetime_arena);
  lifetime_trail.pop(lifetime_checkpoint);
  require(LifetimeValue::destroyedCount().load(std::memory_order_relaxed) == 0,
          "rollback does not destroy arena object");
  CoreGeneration const lifetime_next = lifetime_domain.advance();
  lifetime_trail.reset(lifetime_next);
  require(LifetimeValue::destroyedCount().load(std::memory_order_relaxed) == 0,
          "dependent trail reset precedes arena destruction");
  lifetime_arena.reset(lifetime_next);
  require(LifetimeValue::destroyedCount().load(std::memory_order_relaxed) == 1,
          "destructive arena reset destroys object once");

  std::cout << "{\"checkpoint_exhaustion\":true,"
               "\"mode\":\"trail\",\"operations\":"
            << operation_count
            << ",\"passed\":true,\"rollback_kept_arena\":true}\n";
}

struct ThrowingValue
{
  static int throw_after;
  explicit ThrowingValue(int value) : number(value)
  {
    if (throw_after == 0)
    {
      throw_after = -1;
      throw std::runtime_error("injected value construction failure");
    }
    if (throw_after > 0)
    {
      --throw_after;
    }
  }
  int number;
};
int ThrowingValue::throw_after = -1;

struct AllocatingValue
{
  explicit AllocatingValue(std::uint32_t value)
      : number(value), allocation(4096U, static_cast<char>('a' + value % 26U))
  {
  }
  std::uint32_t number;
  std::string allocation;
};

void testFaults()
{
  GenerationDomain domain;
  BoundArena<ThrowingValue> throwing(domain.current());
  BoundRef const baseline = throwing.emplace(7);
  ThrowingValue* const baseline_address = &throwing.at(baseline);
  ThrowingValue::throw_after = 0;
  try
  {
    (void)throwing.emplace(8);
    fail("throwing constructor was not injected");
  }
  catch (std::runtime_error const&)
  {
  }
  require(throwing.size() == 1 && &throwing.at(baseline) == baseline_address,
          "constructor failure preserves arena");
  BoundRef const after_constructor_failure = throwing.emplace(9);
  require(after_constructor_failure.ordinal() == 1,
          "constructor failure consumes no ordinal");

  constexpr std::uint32_t arena_fault_values = 256;
  std::uint64_t arena_points = 0;
  {
    BoundArena<AllocatingValue> probe(domain.current());
    allocation_fault::beginCount();
    for (std::uint32_t index = 0; index != arena_fault_values; ++index)
    {
      (void)probe.emplace(index);
    }
    arena_points = allocation_fault::endCount();
  }
  require(arena_points >= arena_fault_values,
          "arena allocation/growth surface observed");
  for (std::uint64_t point = 0; point != arena_points; ++point)
  {
    BoundArena<AllocatingValue> candidate(domain.current());
    allocation_fault::arm(point);
    AllocatingValue* first_address = nullptr;
    bool injected = false;
    for (std::uint32_t index = 0; index != arena_fault_values; ++index)
    {
      std::size_t const prior_size = candidate.size();
      try
      {
        BoundRef const ref = candidate.emplace(index);
        require(ref.ordinal() == index, "fault replay successful ordinal");
        if (index == 0)
        {
          first_address = &candidate.at(ref);
        }
      }
      catch (StorageFailure const& failure)
      {
        allocation_fault::disarm();
        require(!injected, "exactly one arena fault per replay");
        require(failure.kind() == StorageFailureKind::AllocationFailure,
                "arena fault typed translation");
        injected = true;
        require(candidate.size() == prior_size,
                "arena allocation failure preserves size");
        if (first_address != nullptr)
        {
          BoundRef const first_ref(domain.current(), 0);
          require(&candidate.at(first_ref) == first_address &&
                      first_address->number == 0,
                  "arena allocation failure preserves prior address/value");
        }
        BoundRef const retry = candidate.emplace(index);
        require(retry.ordinal() == index,
                "arena allocation failure consumes no ordinal");
        if (index == 0)
        {
          first_address = &candidate.at(retry);
        }
      }
      catch (std::bad_alloc const&)
      {
        allocation_fault::disarm();
        fail("raw bad_alloc escaped BoundArena::emplace");
      }
    }
    allocation_fault::disarm();
    require(injected && candidate.size() == arena_fault_values,
            "every observed arena point fails once and recovers");
  }

  std::uint64_t push_points = 0;
  {
    BoundActivityTrail probe(domain.current());
    allocation_fault::beginCount();
    (void)probe.push();
    push_points = allocation_fault::endCount();
  }
  require(push_points != 0, "checkpoint allocation surface observed");
  for (std::uint64_t point = 0; point != push_points; ++point)
  {
    BoundActivityTrail candidate(domain.current());
    allocation_fault::arm(point);
    expectStorageFailure(StorageFailureKind::AllocationFailure,
                         "checkpoint allocation injection",
                         [&] { (void)candidate.push(); });
    allocation_fault::disarm();
    require(candidate.levelCount() == 0, "failed push strong commit");
    require(candidate.push().depth == 1, "failed push token not consumed");
  }

  BoundArena<std::uint32_t> ref_arena(domain.current());
  BoundRef const ref = ref_arena.emplace(1);
  std::uint64_t append_points = 0;
  {
    BoundActivityTrail probe(domain.current());
    allocation_fault::beginCount();
    probe.append(ref, ref_arena);
    append_points = allocation_fault::endCount();
  }
  require(append_points != 0, "trail allocation surface observed");
  for (std::uint64_t point = 0; point != append_points; ++point)
  {
    BoundActivityTrail candidate(domain.current());
    allocation_fault::arm(point);
    expectStorageFailure(StorageFailureKind::AllocationFailure,
                         "trail append allocation injection",
                         [&] { candidate.append(ref, ref_arena); });
    allocation_fault::disarm();
    require(candidate.activeSize() == 0, "failed append strong commit");
    candidate.append(ref, ref_arena);
    require(candidate.activeSize() == 1, "failed append recovery");
  }

  std::uint64_t reset_points = 0;
  {
    GenerationDomain reset_domain;
    BoundArena<AllocatingValue> probe(reset_domain.current());
    (void)probe.emplace(0);
    CoreGeneration const successor = reset_domain.advance();
    allocation_fault::beginCount();
    probe.reset(successor);
    reset_points = allocation_fault::endCount();
  }
  require(reset_points != 0, "arena reset allocation surface observed");
  for (std::uint64_t point = 0; point != reset_points; ++point)
  {
    GenerationDomain reset_domain;
    BoundArena<AllocatingValue> candidate(reset_domain.current());
    BoundRef const existing = candidate.emplace(0);
    AllocatingValue* const address = &candidate.at(existing);
    CoreGeneration const old_generation = reset_domain.current();
    CoreGeneration const successor = reset_domain.advance();
    allocation_fault::arm(point);
    expectStorageFailure(StorageFailureKind::AllocationFailure,
                         "arena reset allocation injection",
                         [&] { candidate.reset(successor); });
    require(candidate.generation() == old_generation &&
                candidate.size() == 1 &&
                &candidate.at(existing) == address,
            "arena reset failure strong commit");
    candidate.reset(successor);
    require(candidate.generation() == successor && candidate.empty(),
            "arena reset allocation recovery");
  }

  BoundArena<std::uint32_t> exhausted(domain.current());
  stp::lra::detail::StorageTestAccess::setArenaNextOrdinal(
      exhausted, static_cast<std::uint64_t>(BoundRef::maximum_usable_ordinal) +
                     1U);
  expectStorageFailure(StorageFailureKind::ResourceLimit,
                       "arena ordinal preflight exhaustion",
                       [&] { (void)exhausted.emplace(3); });
  require(exhausted.empty() && exhausted.metrics().ordinal_exhaustions == 1,
          "arena exhaustion strong commit and metric");

  std::cout << "{\"allocation_fault_points\":"
            << arena_points + push_points + append_points + reset_points
            << ",\"arena_points\":" << arena_points
            << ",\"constructor_fault_points\":1,\"mode\":\"fault\","
               "\"passed\":true,\"recovery\":true,\"reset_points\":"
            << reset_points << "}\n";
}

std::uint64_t independentWorkload()
{
  GenerationDomain domain;
  std::uint64_t checksum = 0;
  for (unsigned workload = 0; workload != 100; ++workload)
  {
    BoundArena<std::uint64_t> arena(domain.current());
    BoundActivityTrail trail(domain.current());
    std::vector<BoundRef> refs;
    refs.reserve(64);
    for (std::uint32_t index = 0; index != 64; ++index)
    {
      refs.push_back(arena.emplace(index));
    }
    Checkpoint outer = trail.push();
    for (std::size_t index = 0; index != refs.size(); ++index)
    {
      trail.append(refs[index], arena);
      checksum += arena.at(refs[index]);
      if ((index % 8U) == 7U)
      {
        Checkpoint inner = trail.push();
        trail.append(refs[index], arena);
        trail.pop(inner);
      }
    }
    trail.pop(outer);
    require(trail.activeSize() == 0 && arena.size() == refs.size(),
            "concurrent independent workload state");
  }
  return checksum;
}

void testConcurrency()
{
  constexpr std::size_t thread_count = 8;
  std::vector<std::thread> threads;
  std::vector<std::uint64_t> results(thread_count, 0);
  std::atomic<std::size_t> ready{0};
  std::atomic<bool> start{false};
  for (std::size_t thread = 0; thread != thread_count; ++thread)
  {
    threads.emplace_back([thread, &ready, &start, &results] {
      ready.fetch_add(1, std::memory_order_release);
      while (!start.load(std::memory_order_acquire))
      {
        std::this_thread::yield();
      }
      results[thread] = independentWorkload();
    });
  }
  while (ready.load(std::memory_order_acquire) != thread_count)
  {
    std::this_thread::yield();
  }
  start.store(true, std::memory_order_release);
  for (std::thread& thread : threads)
  {
    thread.join();
  }
  require(std::all_of(results.begin(), results.end(),
                      [results](std::uint64_t value) {
                        return value == results.front();
                      }),
          "independent concurrent results deterministic");
  std::cout << "{\"mode\":\"concurrency\",\"passed\":true,"
               "\"threads\":"
            << thread_count << ",\"workloads_per_thread\":100}\n";
}

}  // namespace

int main(int argc, char** argv)
{
  try
  {
    if (argc != 2)
    {
      fail("usage: stp_lra_storage_m1b01_tests MODE");
    }
    std::string const mode(argv[1]);
    if (mode == "ids")
    {
      testIdsAndGenerations();
    }
    else if (mode == "arena")
    {
      testArenaStress();
    }
    else if (mode == "trail")
    {
      testTrail();
    }
    else if (mode == "fault")
    {
      testFaults();
    }
    else if (mode == "concurrency")
    {
      testConcurrency();
    }
    else
    {
      fail("unknown test mode: " + mode);
    }
    return 0;
  }
  catch (std::exception const& exception)
  {
    allocation_fault::disarm();
    std::cerr << "FAIL: " << exception.what() << '\n';
    return 1;
  }
}

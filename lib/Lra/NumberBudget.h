#ifndef STP_LRA_NUMBER_BUDGET_H
#define STP_LRA_NUMBER_BUDGET_H

#include "ImathAllocHooks.h"

#include <array>
#include <cstdint>
#include <limits>
#include <algorithm>
#include <memory>
#include <stdexcept>
#include <string>

namespace stp::lra {

enum class NumberFailureKind : std::uint8_t
{
  InvalidText,
  ZeroDenominator,
  DivisionByZero,
  NonIntegerOperand,
  ResourceLimit,
  AllocationFailure,
  RangeError,
  InternalError
};

class NumberFailure final : public std::runtime_error
{
 public:
  NumberFailure(NumberFailureKind,
                char const* operation,
                std::string detail = {});
  NumberFailureKind kind() const noexcept;
  char const* operation() const noexcept;

 private:
  NumberFailureKind kind_;
  char const* operation_;
};

struct NumberLimits
{
  std::uint64_t maximum_operand_bits;
  std::uint64_t maximum_result_bits;
  std::uint64_t maximum_allocation_bytes;
  std::uint64_t maximum_string_bytes;
};

struct NumberMetrics
{
  std::uint64_t constructs, copies, moves, destroys;
  std::uint64_t parses, canonicalizations, comparisons;
  std::uint64_t additions, subtractions, multiplications, divisions;
  std::uint64_t gcds, floor_divisions;
  std::uint64_t allocation_calls, allocated_bytes, peak_live_bytes;
  std::uint64_t current_values, peak_values;
  std::uint64_t maximum_numerator_bits, maximum_denominator_bits;
  std::uint64_t preflight_stops, allocation_stops;
  std::uint64_t native_materializations, native_demotions;
  std::uint64_t native_additions, native_subtractions;
  std::uint64_t native_multiplications, native_divisions;
  /* Arithmetic that took the arbitrary-precision route, one per
   * operation: the cost a representation-neutral guard can read. */
  std::uint64_t big_operations;

  struct AllocationSite
  {
    std::uint64_t calls;
    std::uint64_t bytes;
  };
  std::array<AllocationSite, STP_LRA_IMATH_ALLOCATION_SITE_COUNT>
      allocation_sites;
};

namespace detail {

enum class NumberMetricEvent : std::uint8_t
{
  Construct,
  Copy,
  Move,
  Destroy,
  Parse,
  Canonicalize,
  Compare,
  Add,
  Subtract,
  Multiply,
  Divide,
  Gcd,
  FloorDivide,
  NativeMaterialize,
  NativeDemote,
  NativeAdd,
  NativeSubtract,
  NativeMultiply,
  NativeDivide,
  BigOperation
};

/* The part of a budget's state that every number operation reads or writes:
 * the limits, the metrics, and two flags. It is a plain struct visible here
 * so that recording an event is an inline increment rather than a call, and
 * the opaque state pointer the values carry points at it. The allocation
 * state and the scope count stay private to the budget. */
struct NumberHotState
{
  NumberLimits limits;
  NumberMetrics metrics{};
  bool verify_canonical = true;
  /* The configured limits are wide enough that no word-sized value or
   * word-sized result can exceed them, so an operation on words need not
   * account for its bits at all. Decided once, when the budget is made. */
  bool word_unlimited = false;
  /* The owning budget's full state, for the rare paths that need it. */
  void* owner = nullptr;
};

/* The state of the scope now active on this thread, or null. One read per
 * operation; set and cleared by NumberOperationScope. */
extern thread_local void* active_number_state;

inline std::uint64_t saturatedIncrement(std::uint64_t value) noexcept
{
  return value == std::numeric_limits<std::uint64_t>::max() ? value
                                                            : value + 1;
}

struct BudgetAccess
{
  [[noreturn]] static void throwNoScope(char const* operation);
  static void* requireActive(char const* operation)
  {
    void* state = active_number_state;
    if (state == nullptr)
      throwNoScope(operation);
    return state;
  }
  static void* active() noexcept { return active_number_state; }
  static NumberHotState& hot(void* state) noexcept
  {
    return *static_cast<NumberHotState*>(state);
  }
  static NumberLimits const& limits(void* state) noexcept
  {
    return hot(state).limits;
  }
  static bool verifyCanonical(void* state) noexcept
  {
    return hot(state).verify_canonical;
  }
  static bool wordUnlimited(void* state) noexcept
  {
    return hot(state).word_unlimited;
  }
  static void record(void* state, NumberMetricEvent event) noexcept
  {
    NumberMetrics& metrics = hot(state).metrics;
    std::uint64_t* counter = nullptr;
    switch (event)
    {
      case NumberMetricEvent::Construct: counter = &metrics.constructs; break;
      case NumberMetricEvent::Copy: counter = &metrics.copies; break;
      case NumberMetricEvent::Move: counter = &metrics.moves; break;
      case NumberMetricEvent::Destroy: counter = &metrics.destroys; break;
      case NumberMetricEvent::Parse: counter = &metrics.parses; break;
      case NumberMetricEvent::Canonicalize:
        counter = &metrics.canonicalizations;
        break;
      case NumberMetricEvent::Compare: counter = &metrics.comparisons; break;
      case NumberMetricEvent::Add: counter = &metrics.additions; break;
      case NumberMetricEvent::Subtract: counter = &metrics.subtractions; break;
      case NumberMetricEvent::Multiply:
        counter = &metrics.multiplications;
        break;
      case NumberMetricEvent::Divide: counter = &metrics.divisions; break;
      case NumberMetricEvent::Gcd: counter = &metrics.gcds; break;
      case NumberMetricEvent::FloorDivide:
        counter = &metrics.floor_divisions;
        break;
      case NumberMetricEvent::NativeMaterialize:
        counter = &metrics.native_materializations;
        break;
      case NumberMetricEvent::NativeDemote:
        counter = &metrics.native_demotions;
        break;
      case NumberMetricEvent::NativeAdd:
        counter = &metrics.native_additions;
        break;
      case NumberMetricEvent::NativeSubtract:
        counter = &metrics.native_subtractions;
        break;
      case NumberMetricEvent::NativeMultiply:
        counter = &metrics.native_multiplications;
        break;
      case NumberMetricEvent::NativeDivide:
        counter = &metrics.native_divisions;
        break;
      case NumberMetricEvent::BigOperation:
        counter = &metrics.big_operations;
        break;
    }
    if (counter != nullptr)
      *counter = saturatedIncrement(*counter);
  }
  static void valueCreated(void* state) noexcept
  {
    NumberMetrics& metrics = hot(state).metrics;
    metrics.current_values = saturatedIncrement(metrics.current_values);
    metrics.peak_values = std::max(metrics.peak_values, metrics.current_values);
  }
  /* A value that leaves the big state by demotion is no longer held; it is
   * not a destruction, so only the live count moves. */
  static void valueReleased(void* state) noexcept
  {
    NumberMetrics& metrics = hot(state).metrics;
    if (metrics.current_values == 0)
    {
      valueUnderflow(state);
      return;
    }
    --metrics.current_values;
  }
  static void valueDestroyed(void* state) noexcept
  {
    NumberMetrics& metrics = hot(state).metrics;
    record(state, NumberMetricEvent::Destroy);
    if (metrics.current_values == 0)
    {
      valueUnderflow(state);
      return;
    }
    --metrics.current_values;
  }
  static void observeValue(void* state,
                           std::uint64_t numerator_bits,
                           std::uint64_t denominator_bits) noexcept
  {
    NumberMetrics& metrics = hot(state).metrics;
    metrics.maximum_numerator_bits =
        std::max(metrics.maximum_numerator_bits, numerator_bits);
    metrics.maximum_denominator_bits =
        std::max(metrics.maximum_denominator_bits, denominator_bits);
  }
  [[noreturn]] static void preflightStop(void* state,
                                         char const* operation,
                                         std::string detail);
  [[noreturn]] static void postResultStop(void* state,
                                          char const* operation,
                                          std::string detail);
  static NumberFailure allocationFailure(char const* operation,
                                         std::string detail = {});

private:
  static void valueUnderflow(void* state) noexcept;
};
}  // namespace detail

class NumberBudget final
{
 public:
  explicit NumberBudget(NumberLimits);
  ~NumberBudget() noexcept;
  NumberBudget(NumberBudget&&) noexcept;
  NumberBudget& operator=(NumberBudget&&) noexcept;
  NumberBudget(NumberBudget const&) = delete;
  NumberBudget& operator=(NumberBudget const&) = delete;

  /* Whether newly created budgets re-derive the canonical form of a result
   * whose construction already proves it canonical.
   *
   * It is a self-check on this layer's own arithmetic, so it is worth its
   * cost in a test and not in a solve. It used to be a compile-time define,
   * which meant the tests exercised a different compilation of these sources
   * than the shipped solver ran -- so a mistake in a path the define guarded
   * was checked exactly where it could not happen and unchecked where it
   * could. Budgets verify unless something turns it off, so every test and
   * every API caller keeps the check; the command-line solver turns it off
   * from its own flag. Set before any exact value is built. */
  static void setCanonicalVerificationDefault(bool enabled) noexcept;
  static bool canonicalVerificationDefault() noexcept;

  NumberLimits limits() const noexcept;
  NumberMetrics metrics() const noexcept;
  void resetAccounting() noexcept;
  bool stopped() const noexcept;

 private:
  struct State;
  std::unique_ptr<State> state_;

  friend class NumberOperationScope;
  friend struct detail::BudgetAccess;
};

class NumberOperationScope final
{
 public:
  explicit NumberOperationScope(NumberBudget&);
  ~NumberOperationScope() noexcept;
  NumberOperationScope(NumberOperationScope const&) = delete;
  NumberOperationScope& operator=(NumberOperationScope const&) = delete;

 private:
  NumberBudget* previous_;
};


}  // namespace stp::lra

#endif

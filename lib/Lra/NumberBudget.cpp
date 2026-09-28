#include "NumberBudget.h"

#include <atomic>

#include <algorithm>
#include <cstdlib>
#include <limits>
#include <utility>

namespace stp::lra {

thread_local void* detail::active_number_state = nullptr;

namespace {

thread_local NumberBudget* active_budget;
using detail::saturatedIncrement;

std::string failureMessage(char const* operation, std::string const& detail)
{
  std::string result(operation == nullptr ? "number operation" : operation);
  if (!detail.empty())
  {
    result += ": ";
    result += detail;
  }
  return result;
}

}  // namespace

namespace {
/* Read once per budget, so a solve that turned it off cannot have it turned
 * back on underneath it. Atomic because budgets are built on more than one
 * thread; set before any of them exist. */
std::atomic<bool> g_verify_canonical{true};
}  // namespace

void NumberBudget::setCanonicalVerificationDefault(bool enabled) noexcept
{
  g_verify_canonical.store(enabled, std::memory_order_relaxed);
}

bool NumberBudget::canonicalVerificationDefault() noexcept
{
  return g_verify_canonical.load(std::memory_order_relaxed);
}

struct NumberBudget::State
{
  explicit State(NumberLimits configured)
  {
    hot.limits = configured;
    hot.verify_canonical = g_verify_canonical.load(std::memory_order_relaxed);
    /* A word holds at most 63 bits and a product of two words at most 126:
     * limits at or above those can never be crossed by word arithmetic, so
     * the word paths need not account for their bits at all. */
    hot.word_unlimited = configured.maximum_operand_bits >= 64 &&
                         configured.maximum_result_bits >= 128;
    hot.owner = this;
    stp_lra_imath_budget_init(&allocation,
                              configured.maximum_allocation_bytes);
  }

  /* What every operation reads; handed out as the opaque state pointer. */
  detail::NumberHotState hot;
  stp_lra_imath_budget_state allocation{};
  std::uint64_t active_scopes = 0;
};

// The full state behind a hot-state pointer. Only BudgetAccess, a friend of
// the budget, can name the type.
#define STP_LRA_OWNING(opaque) \
  (*static_cast<NumberBudget::State*>(detail::BudgetAccess::hot(opaque).owner))

NumberFailure::NumberFailure(NumberFailureKind kind,
                             char const* operation,
                             std::string detail)
    : std::runtime_error(failureMessage(operation, detail)),
      kind_(kind),
      operation_(operation)
{
}

NumberFailureKind NumberFailure::kind() const noexcept
{
  return kind_;
}

char const* NumberFailure::operation() const noexcept
{
  return operation_;
}

NumberBudget::NumberBudget(NumberLimits limits)
    : state_(std::make_unique<State>(limits))
{
}

NumberBudget::~NumberBudget() noexcept
{
  if (state_ != nullptr &&
      (state_->active_scopes != 0 || state_->allocation.live_bytes != 0 ||
       state_->hot.metrics.current_values != 0))
  {
    std::terminate();
  }
}

NumberBudget::NumberBudget(NumberBudget&& other) noexcept
    : state_(std::move(other.state_))
{
  if (active_budget == &other)
  {
    active_budget = this;
  }
}

NumberBudget& NumberBudget::operator=(NumberBudget&& other) noexcept
{
  if (this == &other)
  {
    return *this;
  }
  if (state_ != nullptr &&
      (state_->active_scopes != 0 || state_->allocation.live_bytes != 0 ||
       state_->hot.metrics.current_values != 0))
  {
    std::terminate();
  }
  state_ = std::move(other.state_);
  if (active_budget == &other)
  {
    active_budget = this;
  }
  return *this;
}

NumberLimits NumberBudget::limits() const noexcept
{
  return state_ == nullptr ? NumberLimits{} : state_->hot.limits;
}

NumberMetrics NumberBudget::metrics() const noexcept
{
  if (state_ == nullptr)
  {
    return {};
  }
  NumberMetrics result = state_->hot.metrics;
  result.allocation_calls = state_->allocation.allocation_calls;
  result.allocated_bytes = state_->allocation.allocated_bytes;
  result.peak_live_bytes = state_->allocation.peak_live_bytes;
  result.allocation_stops = state_->allocation.allocation_stops;
  for (std::size_t site = 0; site < result.allocation_sites.size(); ++site)
  {
    result.allocation_sites[site].calls =
        state_->allocation.allocation_calls_by_site[site];
    result.allocation_sites[site].bytes =
        state_->allocation.allocated_bytes_by_site[site];
  }
  return result;
}

void NumberBudget::resetAccounting() noexcept
{
  if (state_ == nullptr)
  {
    return;
  }
  if (state_->active_scopes != 0)
  {
    state_->allocation.stopped = 1;
    return;
  }
  std::uint64_t const current_values = state_->hot.metrics.current_values;
  state_->hot.metrics = {};
  state_->hot.metrics.current_values = current_values;
  state_->hot.metrics.peak_values = current_values;
  stp_lra_imath_budget_reset_accounting(&state_->allocation);
}

bool NumberBudget::stopped() const noexcept
{
  return state_ != nullptr && state_->allocation.stopped != 0;
}

NumberOperationScope::NumberOperationScope(NumberBudget& budget)
    : previous_(active_budget)
{
  if (budget.state_ == nullptr)
  {
    throw NumberFailure(NumberFailureKind::InternalError,
                        "NumberOperationScope",
                        "moved-from budget");
  }
  if (previous_ != nullptr && previous_ != &budget)
  {
    throw NumberFailure(NumberFailureKind::InternalError,
                        "NumberOperationScope",
                        "nested scope uses a different budget");
  }
  stp_lra_imath_budget_state* previous_state =
      stp_lra_imath_exchange_active_budget(&budget.state_->allocation);
  if (previous_state != nullptr &&
      previous_state != &budget.state_->allocation)
  {
    stp_lra_imath_exchange_active_budget(previous_state);
    throw NumberFailure(NumberFailureKind::InternalError,
                        "NumberOperationScope",
                        "C and C++ allocation dispatch disagree");
  }
  active_budget = &budget;
  detail::active_number_state = &budget.state_->hot;
  budget.state_->active_scopes =
      saturatedIncrement(budget.state_->active_scopes);
}

NumberOperationScope::~NumberOperationScope() noexcept
{
  NumberBudget* current = active_budget;
  if (current == nullptr || current->state_ == nullptr ||
      current->state_->active_scopes == 0)
  {
    std::terminate();
  }
  --current->state_->active_scopes;
  active_budget = previous_;
  detail::active_number_state =
      previous_ == nullptr ? nullptr : &previous_->state_->hot;
  stp_lra_imath_exchange_active_budget(
      previous_ == nullptr ? nullptr : &previous_->state_->allocation);
}

[[noreturn]] void detail::BudgetAccess::throwNoScope(char const* operation)
{
  throw NumberFailure(NumberFailureKind::InternalError,
                      operation,
                      "no active NumberOperationScope");
}

void detail::BudgetAccess::valueUnderflow(void* opaque) noexcept
{
  STP_LRA_OWNING(opaque).allocation.stopped = 1;
}

[[noreturn]] void detail::BudgetAccess::preflightStop(
    void* opaque,
    char const* operation,
    std::string detail)
{
  NumberBudget::State& state = STP_LRA_OWNING(opaque);
  state.hot.metrics.preflight_stops =
      saturatedIncrement(state.hot.metrics.preflight_stops);
  state.allocation.stopped = 1;
  throw NumberFailure(NumberFailureKind::ResourceLimit,
                      operation,
                      std::move(detail));
}

[[noreturn]] void detail::BudgetAccess::postResultStop(
    void* opaque,
    char const* operation,
    std::string detail)
{
  STP_LRA_OWNING(opaque).allocation.stopped = 1;
  throw NumberFailure(NumberFailureKind::ResourceLimit,
                      operation,
                      std::move(detail));
}

NumberFailure detail::BudgetAccess::allocationFailure(char const* operation,
                                                      std::string detail)
{
  switch (stp_lra_imath_last_failure())
  {
    case STP_LRA_IMATH_FAILURE_RESOURCE_LIMIT:
      return NumberFailure(NumberFailureKind::ResourceLimit,
                           operation,
                           std::move(detail));
    case STP_LRA_IMATH_FAILURE_SYSTEM_ALLOCATION:
      return NumberFailure(NumberFailureKind::AllocationFailure,
                           operation,
                           std::move(detail));
    case STP_LRA_IMATH_FAILURE_MISSING_SCOPE:
      return NumberFailure(NumberFailureKind::InternalError,
                           operation,
                           "native allocation without an active scope");
    case STP_LRA_IMATH_FAILURE_CORRUPT_METADATA:
      return NumberFailure(NumberFailureKind::InternalError,
                           operation,
                           "corrupt, foreign, or cross-thread allocation metadata");
    case STP_LRA_IMATH_FAILURE_NONE:
      return NumberFailure(NumberFailureKind::AllocationFailure,
                           operation,
                           std::move(detail));
  }
  return NumberFailure(NumberFailureKind::InternalError,
                       operation,
                       "unknown allocation failure category");
}

}  // namespace stp::lra

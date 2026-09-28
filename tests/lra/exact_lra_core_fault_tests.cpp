#include "ExactLraCore.h"
#include "ImathAllocHooks.h"

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <new>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace allocation_fault {
thread_local std::int64_t fail_after = -1;
thread_local bool fault_enabled = false;
thread_local bool count_enabled = false;
thread_local std::uint64_t allocation_count = 0;
thread_local std::uint64_t allocation_bytes = 0;

void beforeAllocation(std::size_t size)
{
  if (count_enabled && fault_enabled)
  {
    ++allocation_count;
    allocation_bytes += static_cast<std::uint64_t>(size);
  }
  if (!fault_enabled)
  {
    return;
  }
  if (fail_after == 0)
  {
    fail_after = -1;
    fault_enabled = false;
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
  fault_enabled = false;
}
void enable() noexcept { fault_enabled = true; }
void pause() noexcept { fault_enabled = false; }
void disarm() noexcept
{
  fail_after = -1;
  fault_enabled = false;
}
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

void* operator new(std::size_t size)
{
  allocation_fault::beforeAllocation(size);
  if (void* memory = std::malloc(size == 0 ? 1 : size))
  {
    return memory;
  }
  throw std::bad_alloc();
}
void* operator new[](std::size_t size) { return ::operator new(size); }
void operator delete(void* memory) noexcept { std::free(memory); }
void operator delete[](void* memory) noexcept { std::free(memory); }
void operator delete(void* memory, std::size_t) noexcept { std::free(memory); }
void operator delete[](void* memory, std::size_t) noexcept
{
  std::free(memory);
}

namespace {

using namespace stp::lra;

constexpr NumberLimits limits{
    65536, 65536, UINT64_C(268435456), UINT64_C(16777216)};
constexpr std::uint64_t no_native_failure =
    std::numeric_limits<std::uint64_t>::max();

[[noreturn]] void fail(std::string const& message)
{
  allocation_fault::disarm();
  stp_lra_imath_test_disable_failures();
  throw std::runtime_error(message);
}

void require(bool condition, std::string const& message)
{
  if (!condition)
  {
    fail(message);
  }
}

class Observer final : public ExactLraResourceObserver
{
 public:
  StopReason pollBeforePivot() noexcept override
  {
    return StopReason::Continue;
  }
  void accountPivot(bool) noexcept override {}
};

struct Harness final
{
  Harness() : input(limits), core(limits) {}

  ExactRational rational(char const* text)
  {
    NumberOperationScope scope(input);
    return ExactRational::parseDecimalOrFraction(text);
  }

  NumberBudget input;
  ExactLraCore core;
};

template <class Operation>
auto productionCall(Operation&& operation)
{
  allocation_fault::enable();
  auto result = operation();
  allocation_fault::pause();
  return result;
}

void recoveryCheck(ExactLraCore& core)
{
  core.reset();
  require(core.status() == CheckStatus::Ready,
          "reset did not recover the invalidated core");
  auto variable = core.addVariable();
  require(variable.status == InputStatus::Accepted,
          "recovery variable registration failed");
  require(core.initialize() == InputStatus::Accepted,
          "recovery initialization failed");
  auto checkpoint = core.push();
  require(checkpoint.value.has_value(), "recovery push failed");
  Observer observer;
  CheckResult result = core.check(observer);
  require(result.status == CheckStatus::Consistent && result.model,
          "recovery free model failed");
  require(core.pop(*checkpoint.value) == InputStatus::Accepted,
          "recovery pop failed");
}

bool runCppWorkload(std::optional<std::uint64_t> failure_index)
{
  Harness harness;
  if (failure_index)
  {
    allocation_fault::arm(*failure_index);
  }
  bool injected = false;

  auto variable = productionCall([&] { return harness.core.addVariable(); });
  if (variable.status == InputStatus::InternalError)
  {
    injected = true;
  }
  if (!injected)
  {
    require(variable.value.has_value(), "fault workload variable failed");
    LinearTerm first_term{*variable.value, harness.rational("1")};
    auto first_row = productionCall(
        [&] { return harness.core.addRow(&first_term, &first_term + 1); });
    if (first_row.status == InputStatus::InternalError)
    {
      injected = true;
    }
    if (!injected)
    {
      require(first_row.value.has_value(), "fault workload first row failed");
      LinearTerm second_term{*variable.value, harness.rational("1")};
      auto second_row = productionCall([&] {
        return harness.core.addRow(&second_term, &second_term + 1);
      });
      if (second_row.status == InputStatus::InternalError)
      {
        injected = true;
      }
      if (!injected)
      {
        require(second_row.value.has_value(),
                "fault workload second row failed");
        ExactRational zero = harness.rational("0");
        auto upper = productionCall([&] {
          return harness.core.addAtom(
              *first_row.value, Relation::LessEqual, zero, OriginId{1, 1},
              OriginId{1, 2});
        });
        if (upper.status == InputStatus::InternalError)
        {
          injected = true;
        }
        if (!injected)
        {
          require(upper.value.has_value(), "fault workload upper atom failed");
          ExactRational one = harness.rational("1");
          auto lower = productionCall([&] {
            return harness.core.addAtom(
                *second_row.value, Relation::GreaterEqual, one,
                OriginId{1, 3}, OriginId{1, 4});
          });
          if (lower.status == InputStatus::InternalError)
          {
            injected = true;
          }
          if (!injected)
          {
            require(lower.value.has_value(),
                    "fault workload lower atom failed");
            InputStatus initialized =
                productionCall([&] { return harness.core.initialize(); });
            if (initialized == InputStatus::InternalError)
            {
              injected = true;
            }
            if (!injected)
            {
              require(initialized == InputStatus::Accepted,
                      "fault workload initialization failed");
              auto checkpoint =
                  productionCall([&] { return harness.core.push(); });
              if (checkpoint.status == InputStatus::InternalError)
              {
                injected = true;
              }
              if (!injected)
              {
                require(checkpoint.value.has_value(),
                        "fault workload push failed");
                AssertResult first = productionCall(
                    [&] { return harness.core.assertLiteral(*upper.value, true); });
                if (first.status == InputStatus::InternalError)
                {
                  injected = true;
                }
                if (!injected)
                {
                  require(first.status == InputStatus::Accepted,
                          "fault workload first assertion failed");
                  AssertResult second = productionCall([&] {
                    return harness.core.assertLiteral(*lower.value, true);
                  });
                  if (second.status == InputStatus::InternalError)
                  {
                    injected = true;
                  }
                  if (!injected)
                  {
                    require(second.status == InputStatus::Accepted,
                            "fault workload second assertion failed");
                    Observer observer;
                    CheckResult result = productionCall(
                        [&] { return harness.core.check(observer); });
                    if (result.status == CheckStatus::InternalError)
                    {
                      injected = true;
                    }
                    if (!injected)
                    {
                      require(result.status == CheckStatus::Conflict &&
                                  result.conflict,
                              "fault workload conflict failed");
                      InputStatus popped = productionCall(
                          [&] { return harness.core.pop(*checkpoint.value); });
                      if (popped == InputStatus::InternalError)
                      {
                        injected = true;
                      }
                      else
                      {
                        require(popped == InputStatus::Accepted,
                                "fault workload pop failed");
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  allocation_fault::pause();
  if (failure_index)
  {
    require(injected, "armed C++ allocation point did not fail");
    require(harness.core.status() == CheckStatus::InternalError,
            "C++ allocation failure did not invalidate the result path");
    recoveryCheck(harness.core);
  }
  else
  {
    require(!injected, "measurement workload failed");
  }
  allocation_fault::disarm();
  return injected;
}

void runCppSweep()
{
  allocation_fault::beginCount();
  allocation_fault::arm(no_native_failure);
  (void)runCppWorkload(std::nullopt);
  auto const measured = allocation_fault::endCount();
  require(measured.first >= 80,
          "C++ fault workload exposed too few allocation points");
  std::uint64_t injected = 0;
  for (std::uint64_t index = 0; index != measured.first; ++index)
  {
    injected += runCppWorkload(index) ? 1U : 0U;
  }
  require(injected == measured.first,
          "C++ allocation sweep did not cover every observed point");
  std::cout << "CPP_FAULT points=" << measured.first
            << " bytes=" << measured.second << " injected=" << injected
            << " recovery=true\n";
}

enum class NativeStage : std::uint8_t
{
  Row,
  Atom,
  Initialize,
  SatisfiableCheck,
  ConflictCheck,
  Pop
};

struct NativeOutcome
{
  std::uint64_t attempts;
  bool failed_closed;
};

NativeOutcome runNativeStage(NativeStage stage,
                             std::uint64_t failure_index)
{
  stp_lra_imath_test_disable_failures();
  Harness harness;
  auto x = harness.core.addVariable();
  require(x.value.has_value(), "native stage variable setup failed");
  /* Wider than the wide arithmetic lane (127 bits over 19): every stage
   * flows through this coefficient, so the staged operations genuinely
   * reach the IMath allocator the sweep exists to exercise. */
  LinearTerm x_term{
      *x.value,
      harness.rational(
          "170141183460469231731687303715884105727/19")};

  if (stage == NativeStage::Row)
  {
    stp_lra_imath_test_fail_nth(failure_index);
    auto result = harness.core.addRow(&x_term, &x_term + 1);
    std::uint64_t const attempts = stp_lra_imath_test_allocation_attempts();
    stp_lra_imath_test_disable_failures();
    bool const failed = result.status == InputStatus::InternalError;
    if (failure_index != no_native_failure)
    {
      require(failed && harness.core.status() == CheckStatus::InternalError,
              "native row fault did not fail closed");
      recoveryCheck(harness.core);
    }
    return NativeOutcome{attempts, failed};
  }

  auto row = harness.core.addRow(&x_term, &x_term + 1);
  require(row.value.has_value(), "native stage row setup failed");
  ExactRational zero = harness.rational("0");
  if (stage == NativeStage::Atom)
  {
    stp_lra_imath_test_fail_nth(failure_index);
    auto result = harness.core.addAtom(
        *row.value, Relation::Greater, zero, OriginId{2, 1}, OriginId{2, 2});
    std::uint64_t const attempts = stp_lra_imath_test_allocation_attempts();
    stp_lra_imath_test_disable_failures();
    bool const failed = result.status == InputStatus::InternalError;
    if (failure_index != no_native_failure)
    {
      require(failed && harness.core.status() == CheckStatus::InternalError,
              "native atom fault did not fail closed");
      recoveryCheck(harness.core);
    }
    return NativeOutcome{attempts, failed};
  }

  if (stage == NativeStage::ConflictCheck)
  {
    auto y = harness.core.addVariable();
    require(y.value.has_value(), "native conflict y setup failed");
    LinearTerm y_term{*y.value, harness.rational("1")};
    auto y_row = harness.core.addRow(&y_term, &y_term + 1);
    require(y_row.value.has_value(), "native conflict y row setup failed");
    LinearTerm sum_terms[] = {{*x.value, harness.rational("1")},
                              {*y.value, harness.rational("1")}};
    auto sum_row = harness.core.addRow(sum_terms, sum_terms + 2);
    require(sum_row.value.has_value(),
            "native conflict sum row setup failed");
    auto x_upper = harness.core.addAtom(
        *row.value, Relation::LessEqual, zero, OriginId{3, 1},
        OriginId{3, 2});
    auto y_upper = harness.core.addAtom(
        *y_row.value, Relation::LessEqual, zero, OriginId{3, 3},
        OriginId{3, 4});
    ExactRational one = harness.rational("1");
    auto sum_lower = harness.core.addAtom(
        *sum_row.value, Relation::GreaterEqual, one, OriginId{3, 5},
        OriginId{3, 6});
    require(x_upper.value && y_upper.value && sum_lower.value,
            "native conflict atom setup failed");
    require(harness.core.initialize() == InputStatus::Accepted,
            "native conflict initialization failed");
    auto checkpoint = harness.core.push();
    require(checkpoint.value.has_value(),
            "native conflict push setup failed");
    require(harness.core.assertLiteral(*x_upper.value, true).status ==
                InputStatus::Accepted &&
                harness.core.assertLiteral(*y_upper.value, true).status ==
                    InputStatus::Accepted &&
                harness.core.assertLiteral(*sum_lower.value, true).status ==
                    InputStatus::Accepted,
            "native conflict assertion setup failed");
    Observer observer;
    stp_lra_imath_test_fail_nth(failure_index);
    CheckResult result = harness.core.check(observer);
    std::uint64_t const attempts = stp_lra_imath_test_allocation_attempts();
    stp_lra_imath_test_disable_failures();
    bool const failed = result.status == CheckStatus::InternalError;
    if (failure_index != no_native_failure)
    {
      require(failed && harness.core.status() == CheckStatus::InternalError &&
                  !result.model && !result.conflict,
              "native conflict-check fault did not fail closed");
      recoveryCheck(harness.core);
    }
    else
    {
      require(result.status == CheckStatus::Conflict && result.conflict &&
                  !result.model,
              "native conflict measurement did not export a conflict");
    }
    return NativeOutcome{attempts, failed};
  }

  std::vector<AtomId> atoms;
  for (std::uint64_t index = 0; index != 8; ++index)
  {
    std::string const text = std::to_string(index + 1U) + "/13";
    ExactRational threshold = harness.rational(text.c_str());
    auto atom = harness.core.addAtom(
        *row.value, index % 2U == 0 ? Relation::Greater : Relation::Less,
        threshold, OriginId{2, 10U + index * 2U},
        OriginId{2, 11U + index * 2U});
    require(atom.value.has_value(), "native stage atom setup failed");
    atoms.push_back(*atom.value);
  }
  if (stage == NativeStage::Initialize)
  {
    stp_lra_imath_test_fail_nth(failure_index);
    InputStatus const result = harness.core.initialize();
    std::uint64_t const attempts = stp_lra_imath_test_allocation_attempts();
    stp_lra_imath_test_disable_failures();
    bool const failed = result == InputStatus::InternalError;
    if (failure_index != no_native_failure)
    {
      require(failed && harness.core.status() == CheckStatus::InternalError,
              "native initialize fault did not fail closed");
      recoveryCheck(harness.core);
    }
    return NativeOutcome{attempts, failed};
  }

  require(harness.core.initialize() == InputStatus::Accepted,
          "native stage initialization setup failed");
  auto checkpoint = harness.core.push();
  require(checkpoint.value.has_value(), "native stage push setup failed");

  if (stage == NativeStage::SatisfiableCheck || stage == NativeStage::Pop)
  {
    require(harness.core.assertLiteral(atoms.front(), true).status ==
                InputStatus::Accepted,
            "native SAT assertion setup failed");
    Observer observer;
    if (stage == NativeStage::SatisfiableCheck)
    {
      stp_lra_imath_test_fail_nth(failure_index);
      CheckResult result = harness.core.check(observer);
      std::uint64_t const attempts = stp_lra_imath_test_allocation_attempts();
      stp_lra_imath_test_disable_failures();
      bool const failed = result.status == CheckStatus::InternalError;
      if (failure_index != no_native_failure)
      {
        require(failed && harness.core.status() == CheckStatus::InternalError,
                "native SAT-check fault did not fail closed");
        recoveryCheck(harness.core);
      }
      return NativeOutcome{attempts, failed};
    }
    CheckResult result = harness.core.check(observer);
    require(result.status == CheckStatus::Consistent && result.model,
            "native pop model setup failed");
    stp_lra_imath_test_fail_nth(failure_index);
    InputStatus const popped = harness.core.pop(*checkpoint.value);
    std::uint64_t const attempts = stp_lra_imath_test_allocation_attempts();
    stp_lra_imath_test_disable_failures();
    bool const failed = popped == InputStatus::InternalError;
    if (failure_index != no_native_failure)
    {
      require(failed && harness.core.status() == CheckStatus::InternalError,
              "native pop fault did not fail closed");
      recoveryCheck(harness.core);
    }
    return NativeOutcome{attempts, failed};
  }

  fail("unknown native fault stage");
}

char const* stageName(NativeStage stage)
{
  switch (stage)
  {
    case NativeStage::Row: return "row";
    case NativeStage::Atom: return "atom";
    case NativeStage::Initialize: return "initialize";
    case NativeStage::SatisfiableCheck: return "sat-check";
    case NativeStage::ConflictCheck: return "conflict-check";
    case NativeStage::Pop: return "pop";
  }
  return "invalid";
}

void runNativeSweep()
{
  NativeStage const stages[] = {
      NativeStage::Row,          NativeStage::Atom,
      NativeStage::Initialize,   NativeStage::SatisfiableCheck,
      NativeStage::ConflictCheck, NativeStage::Pop};
  std::uint64_t total_points = 0;
  std::uint64_t total_injected = 0;
  for (NativeStage stage : stages)
  {
    NativeOutcome const measured = runNativeStage(stage, no_native_failure);
    std::uint64_t injected = 0;
    for (std::uint64_t index = 0; index != measured.attempts; ++index)
    {
      NativeOutcome const outcome = runNativeStage(stage, index);
      require(outcome.failed_closed,
              std::string("native fault escaped at ") + stageName(stage));
      ++injected;
    }
    total_points += measured.attempts;
    total_injected += injected;
    std::cout << "IMATH_FAULT stage=" << stageName(stage)
              << " points=" << measured.attempts
              << " injected=" << injected << "\n";
  }
  require(total_points != 0 && total_points == total_injected,
          "native allocation sweep was incomplete");
  std::cout << "IMATH_FAULT total_points=" << total_points
            << " total_injected=" << total_injected
            << " recovery=true\n";
}

enum class VerifierKind : std::uint8_t
{
  Model,
  Conflict
};

/* The coefficient is deliberately wider than ExactRational's word state.
 * Word-sized values live in machine integers and never build an IMath object,
 * so a fixture of 1 and 0 would leave the native allocation sweep below with
 * nothing to inject at. */
Model prepareModel(Harness& harness)
{
  auto x = harness.core.addVariable();
  require(x.value.has_value(), "verifier model variable setup failed");
  LinearTerm term{*x.value, harness.rational("123456789012345678901234567890/97")};
  auto row = harness.core.addRow(&term, &term + 1);
  require(row.value.has_value(), "verifier model row setup failed");
  ExactRational zero = harness.rational("0");
  auto lower = harness.core.addAtom(
      *row.value, Relation::GreaterEqual, zero,
      OriginId{20, 1}, OriginId{20, 2});
  require(lower.value.has_value(), "verifier model atom setup failed");
  require(harness.core.initialize() == InputStatus::Accepted,
          "verifier model initialization failed");
  auto checkpoint = harness.core.push();
  require(checkpoint.value.has_value(), "verifier model push failed");
  require(harness.core.assertLiteral(*lower.value, true).status ==
              InputStatus::Accepted,
          "verifier model assertion failed");
  Observer observer;
  CheckResult result = harness.core.check(observer);
  require(result.status == CheckStatus::Consistent && result.model,
          "verifier model production failed");
  return std::move(*result.model);
}

/* The coefficient is deliberately wider than ExactRational's word state.
 * Word-sized values live in machine integers and never build an IMath object,
 * so a fixture of 1 and 0 would leave the native allocation sweep below with
 * nothing to inject at. */
Conflict prepareConflict(Harness& harness)
{
  auto x = harness.core.addVariable();
  require(x.value.has_value(), "verifier conflict variable setup failed");
  LinearTerm term{*x.value, harness.rational("123456789012345678901234567890/97")};
  auto row = harness.core.addRow(&term, &term + 1);
  require(row.value.has_value(), "verifier conflict row setup failed");
  ExactRational zero = harness.rational("0");
  auto strict = harness.core.addAtom(
      *row.value, Relation::Less, zero,
      OriginId{21, 1}, OriginId{21, 2});
  require(strict.value.has_value(), "verifier conflict atom setup failed");
  require(harness.core.initialize() == InputStatus::Accepted,
          "verifier conflict initialization failed");
  auto checkpoint = harness.core.push();
  require(checkpoint.value.has_value(), "verifier conflict push failed");
  require(harness.core.assertLiteral(*strict.value, true).status ==
              InputStatus::Accepted,
          "verifier conflict first assertion failed");
  AssertResult result = harness.core.assertLiteral(*strict.value, false);
  require(result.status == InputStatus::Accepted &&
              result.immediate_conflict,
          "verifier conflict production failed");
  return std::move(*result.immediate_conflict);
}

bool runCppVerifier(VerifierKind kind,
                    std::optional<std::uint64_t> failure_index)
{
  Harness harness;
  if (kind == VerifierKind::Model)
  {
    Model witness = prepareModel(harness);
    if (failure_index)
    {
      allocation_fault::arm(*failure_index);
    }
    VerificationResult result = productionCall(
        [&] { return harness.core.verifyModel(witness); });
    bool const failed = result.error == VerificationError::InternalError;
    if (failure_index)
    {
      require(failed && harness.core.status() == CheckStatus::Consistent,
              "C++ model-verifier fault was not strongly preserved");
      require(harness.core.verifyModel(witness).verified(),
              "C++ model-verifier retry failed");
    }
    else
    {
      require(result.verified(), "C++ model-verifier measurement failed");
    }
    allocation_fault::disarm();
    return failed;
  }

  Conflict witness = prepareConflict(harness);
  if (failure_index)
  {
    allocation_fault::arm(*failure_index);
  }
  VerificationResult result = productionCall(
      [&] { return harness.core.verifyConflict(witness); });
  bool const failed = result.error == VerificationError::InternalError;
  if (failure_index)
  {
    require(failed && harness.core.status() == CheckStatus::Conflict,
            "C++ conflict-verifier fault was not strongly preserved");
    require(harness.core.verifyConflict(witness).verified(),
            "C++ conflict-verifier retry failed");
  }
  else
  {
    require(result.verified(), "C++ conflict-verifier measurement failed");
  }
  allocation_fault::disarm();
  return failed;
}

NativeOutcome runNativeVerifier(VerifierKind kind,
                                std::uint64_t failure_index)
{
  stp_lra_imath_test_disable_failures();
  Harness harness;
  if (kind == VerifierKind::Model)
  {
    Model witness = prepareModel(harness);
    stp_lra_imath_test_fail_nth(failure_index);
    VerificationResult result = harness.core.verifyModel(witness);
    std::uint64_t const attempts = stp_lra_imath_test_allocation_attempts();
    stp_lra_imath_test_disable_failures();
    bool const failed = result.error == VerificationError::InternalError;
    if (failure_index != no_native_failure)
    {
      require(failed && harness.core.status() == CheckStatus::Consistent,
              "native model-verifier fault was not strongly preserved");
      require(harness.core.verifyModel(witness).verified(),
              "native model-verifier retry failed");
    }
    else
    {
      require(result.verified(),
              "native model-verifier measurement failed");
    }
    return NativeOutcome{attempts, failed};
  }

  Conflict witness = prepareConflict(harness);
  stp_lra_imath_test_fail_nth(failure_index);
  VerificationResult result = harness.core.verifyConflict(witness);
  std::uint64_t const attempts = stp_lra_imath_test_allocation_attempts();
  stp_lra_imath_test_disable_failures();
  bool const failed = result.error == VerificationError::InternalError;
  if (failure_index != no_native_failure)
  {
    require(failed && harness.core.status() == CheckStatus::Conflict,
            "native conflict-verifier fault was not strongly preserved");
    require(harness.core.verifyConflict(witness).verified(),
            "native conflict-verifier retry failed");
  }
  else
  {
    require(result.verified(),
            "native conflict-verifier measurement failed");
  }
  return NativeOutcome{attempts, failed};
}

char const* verifierName(VerifierKind kind)
{
  return kind == VerifierKind::Model ? "model" : "conflict";
}

void runVerifierSweep()
{
  VerifierKind const kinds[] = {VerifierKind::Model,
                                VerifierKind::Conflict};
  for (VerifierKind kind : kinds)
  {
    allocation_fault::beginCount();
    allocation_fault::arm(no_native_failure);
    (void)runCppVerifier(kind, std::nullopt);
    auto const cpp_measured = allocation_fault::endCount();
    require(cpp_measured.first != 0,
            "verifier C++ sweep observed no allocations");
    std::uint64_t cpp_injected = 0;
    for (std::uint64_t index = 0; index != cpp_measured.first; ++index)
    {
      cpp_injected += runCppVerifier(kind, index) ? 1U : 0U;
    }
    require(cpp_injected == cpp_measured.first,
            "verifier C++ allocation sweep was incomplete");

    NativeOutcome const native_measured =
        runNativeVerifier(kind, no_native_failure);
    require(native_measured.attempts != 0,
            "verifier native sweep observed no allocations");
    std::uint64_t native_injected = 0;
    for (std::uint64_t index = 0; index != native_measured.attempts; ++index)
    {
      NativeOutcome const outcome = runNativeVerifier(kind, index);
      require(outcome.failed_closed,
              "verifier native allocation escaped");
      ++native_injected;
    }
    std::cout << "VERIFIER_FAULT kind=" << verifierName(kind)
              << " cpp_points=" << cpp_measured.first
              << " cpp_injected=" << cpp_injected
              << " native_points=" << native_measured.attempts
              << " native_injected=" << native_injected
              << " retry=true\n";
  }
}

}  // namespace

int main(int argc, char** argv)
{
  if (argc != 2)
  {
    std::cerr << "usage: exact_lra_core_fault_tests cpp|imath|verifier\n";
    return EXIT_FAILURE;
  }
  try
  {
    std::string const mode(argv[1]);
    if (mode == "cpp")
    {
      runCppSweep();
    }
    else if (mode == "imath")
    {
      runNativeSweep();
    }
    else if (mode == "verifier")
    {
      runVerifierSweep();
    }
    else
    {
      fail("unknown fault mode");
    }
    std::cout << "PASS " << mode << '\n';
    return EXIT_SUCCESS;
  }
  catch (std::exception const& error)
  {
    std::cerr << "FAIL " << argv[1] << ": " << error.what() << '\n';
    return EXIT_FAILURE;
  }
}

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

namespace cpp_fault
{

thread_local bool enabled = false;
thread_local bool hit = false;
thread_local std::uint64_t requested = UINT64_MAX;
thread_local std::uint64_t attempts = 0;
thread_local std::size_t last_size = 0;

void beforeAllocation(std::size_t size)
{
  if (!enabled)
  {
    return;
  }
  last_size = size;
  std::uint64_t const current = attempts++;
  if (current == requested)
  {
    enabled = false;
    hit = true;
    throw std::bad_alloc();
  }
}

void arm(std::uint64_t index) noexcept
{
  requested = index;
  attempts = 0;
  last_size = 0;
  hit = false;
  enabled = true;
}

void pause() noexcept
{
  enabled = false;
}

} // namespace cpp_fault

void* operator new(std::size_t size)
{
  cpp_fault::beforeAllocation(size);
  if (void* memory = std::malloc(size == 0 ? 1 : size))
  {
    return memory;
  }
  throw std::bad_alloc();
}

void* operator new[](std::size_t size)
{
  return ::operator new(size);
}
void operator delete(void* memory) noexcept
{
  std::free(memory);
}
void operator delete[](void* memory) noexcept
{
  std::free(memory);
}
void operator delete(void* memory, std::size_t) noexcept
{
  std::free(memory);
}
void operator delete[](void* memory, std::size_t) noexcept
{
  std::free(memory);
}

namespace
{

using namespace stp::lra;

constexpr NumberLimits limits{UINT64_C(65536), UINT64_C(65536),
                              UINT64_C(268435456), UINT64_C(16777216)};

class Observer final : public ExactLraResourceObserver
{
public:
  StopReason pollBeforePivot() noexcept override
  {
    return StopReason::Continue;
  }
  void accountPivot(bool) noexcept override {}
};

[[noreturn]] void fail(std::string const& message)
{
  cpp_fault::pause();
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

char const* thresholdFrom(std::string const& key)
{
  if (key == "blocker")
  {
    return "-123456789012345678901234567890/97";
  }
  if (key == "positive")
  {
    return "123456789012345678901234567890/97";
  }
  if (key == "small")
  {
    return "0";
  }
  if (key == "noninline")
  {
    return "123456789012345678901/19";
  }
  fail("invalid threshold key");
}

struct Fixture final
{
  Fixture() : input(limits), core(limits) {}

  ExactRational rational(char const* text)
  {
    NumberOperationScope scope(input);
    return ExactRational::parseDecimalOrFraction(text);
  }

  NumberBudget input;
  ExactLraCore core;
};

struct Registration
{
  VariableId x;
  std::optional<VariableId> y;
  RowId row;
};

Registration registerRow(Fixture& fixture, unsigned terms)
{
  InputResult<VariableId> const x = fixture.core.addVariable();
  require(x.status == InputStatus::Accepted && x.value,
          "x registration failed");
  if (terms == 1)
  {
    LinearTerm row_terms[] = {{*x.value, fixture.rational("17/19")}};
    InputResult<RowId> const row =
        fixture.core.addRow(row_terms, row_terms + 1);
    require(row.status == InputStatus::Accepted && row.value,
            "one-term row registration failed");
    return Registration{*x.value, std::nullopt, *row.value};
  }
  require(terms == 2, "invalid row width");
  InputResult<VariableId> const y = fixture.core.addVariable();
  require(y.status == InputStatus::Accepted && y.value,
          "y registration failed");
  LinearTerm row_terms[] = {{*x.value, fixture.rational("17/19")},
                            {*y.value, fixture.rational("1")}};
  InputResult<RowId> const row = fixture.core.addRow(row_terms, row_terms + 2);
  require(row.status == InputStatus::Accepted && row.value,
          "two-term row registration failed");
  return Registration{*x.value, *y.value, *row.value};
}

void freshCycle(Fixture& fixture)
{
  Registration const registration = registerRow(fixture, 1);
  ExactRational const zero = fixture.rational("0");
  InputResult<AtomId> const atom =
      fixture.core.addAtom(registration.row, Relation::LessEqual, zero,
                           OriginId{9, 1}, OriginId{9, 2});
  require(atom.status == InputStatus::Accepted && atom.value,
          "fresh atom registration failed");
  require(fixture.core.initialize() == InputStatus::Accepted,
          "fresh initialization failed");
  InputResult<Checkpoint> const checkpoint = fixture.core.push();
  require(checkpoint.status == InputStatus::Accepted && checkpoint.value,
          "fresh checkpoint failed");
  require(fixture.core.assertLiteral(*atom.value, true).status ==
              InputStatus::Accepted,
          "fresh assertion failed");
  Observer observer;
  CheckResult const result = fixture.core.check(observer);
  require(result.status == CheckStatus::Consistent && result.model &&
              !result.conflict,
          "fresh semantic retry failed");
  require(fixture.core.verifyModel(*result.model).verified(),
          "fresh model verification failed");
}

void peerCycle()
{
  Fixture peer;
  freshCycle(peer);
}

ExactLraCore invalidCore(NumberBudget& input)
{
  ExactLraCore core(limits);
  InputResult<VariableId> const x = core.addVariable();
  require(x.value.has_value(), "invalid move fixture variable failed");
  ExactRational coefficient = [&]
  {
    NumberOperationScope scope(input);
    return ExactRational(std::int64_t{1});
  }();
  LinearTerm term{*x.value, std::move(coefficient)};
  InputResult<RowId> const row = core.addRow(&term, &term + 1);
  require(row.value.has_value(), "invalid move fixture row failed");
  ExactRational threshold = [&]
  {
    NumberOperationScope scope(input);
    return ExactRational::parseDecimalOrFraction(thresholdFrom("blocker"));
  }();
  stp_lra_imath_test_fail_nth(0);
  InputResult<AtomId> const atom =
      core.addAtom(*row.value, Relation::LessEqual, threshold, OriginId{8, 1},
                   OriginId{8, 2});
  stp_lra_imath_test_disable_failures();
  require(atom.status == InputStatus::InternalError &&
              core.status() == CheckStatus::InternalError,
          "invalid move fixture did not fail");
  return core;
}

void lifecycleCase()
{
  Fixture witness_fixture;
  Registration const registration = registerRow(witness_fixture, 1);
  ExactRational const zero = witness_fixture.rational("0");
  InputResult<AtomId> const atom =
      witness_fixture.core.addAtom(registration.row, Relation::GreaterEqual,
                                   zero, OriginId{6, 1}, OriginId{6, 2});
  require(atom.value.has_value() &&
              witness_fixture.core.initialize() == InputStatus::Accepted,
          "witness lifecycle setup failed");
  InputResult<Checkpoint> const checkpoint = witness_fixture.core.push();
  require(checkpoint.value &&
              witness_fixture.core.assertLiteral(*atom.value, true).status ==
                  InputStatus::Accepted,
          "witness lifecycle assertion failed");
  Observer observer;
  CheckResult witness_result = witness_fixture.core.check(observer);
  require(witness_result.model.has_value(), "witness lifecycle model failed");
  Model stale = std::move(*witness_result.model);
  CoreGeneration const old_generation = witness_fixture.core.generation();
  witness_fixture.core.reset();
  require(
      isImmediateSuccessor(old_generation, witness_fixture.core.generation()),
      "witness reset did not advance one generation");
  freshCycle(witness_fixture);
  require(witness_fixture.core.verifyModel(stale).error ==
              VerificationError::StaleId,
          "stale witness/reset ownership failed");

  Fixture healthy_fixture;
  Registration const healthy_registration = registerRow(healthy_fixture, 1);
  ExactLraCore healthy_moved(std::move(healthy_fixture.core));
  require(healthy_fixture.core.status() == CheckStatus::InternalError &&
              healthy_moved.status() == CheckStatus::Ready &&
              healthy_moved.generation() ==
                  healthy_registration.row.generation(),
          "healthy move construction failed");

  NumberBudget invalid_input(limits);
  ExactLraCore invalid = invalidCore(invalid_input);
  ExactLraCore invalid_moved(std::move(invalid));
  require(invalid.status() == CheckStatus::InternalError &&
              invalid_moved.status() == CheckStatus::InternalError,
          "invalid move construction failed");
  invalid_moved.reset();
  require(invalid_moved.status() == CheckStatus::Ready,
          "moved invalid core did not recover");

  Fixture assignment_source;
  (void)registerRow(assignment_source, 1);
  ExactLraCore assignment_target(limits);
  assignment_target = std::move(assignment_source.core);
  require(assignment_target.status() == CheckStatus::Ready &&
              assignment_source.core.status() == CheckStatus::InternalError,
          "healthy move assignment failed");

  ExactLraCore invalid_assignment_source = invalidCore(invalid_input);
  ExactLraCore invalid_assignment_target(limits);
  invalid_assignment_target = std::move(invalid_assignment_source);
  require(invalid_assignment_target.status() == CheckStatus::InternalError &&
              invalid_assignment_source.status() == CheckStatus::InternalError,
          "invalid move assignment failed");
  invalid_assignment_target.reset();
  require(invalid_assignment_target.status() == CheckStatus::Ready,
          "move-assigned invalid core did not recover");
  peerCycle();
  std::cout << "{\"mode\":\"lifecycle\",\"passed\":true,"
               "\"stale_witness\":\"rejected\",\"healthy_move\":true,"
               "\"invalid_move\":true,\"move_assignment\":true,"
               "\"peer_ok\":true}"
            << std::endl;
}

void destructionStressCase(int argc, char** argv)
{
  require(argc == 3, "stress usage: stress CYCLES");
  std::uint64_t const cycles = std::stoull(argv[2]);
  require(cycles >= UINT64_C(10000),
          "destruction stress requires at least 10000 cycles");
  std::uint64_t categories[7] = {};
  for (std::uint64_t cycle = 0; cycle != cycles; ++cycle)
  {
    unsigned const category = static_cast<unsigned>(cycle % 7U);
    ++categories[category];
    if (category == 0)
    {
      Fixture fixture;
      Registration const registration = registerRow(fixture, 1);
      ExactRational const zero = fixture.rational("0");
      require(fixture.core
                      .addAtom(registration.row, Relation::LessEqual, zero,
                               OriginId{cycle + 1U, 1}, OriginId{cycle + 1U, 2})
                      .status == InputStatus::Accepted,
              "stress successful registration failed");
    }
    else if (category == 1)
    {
      Fixture fixture;
      Registration const registration = registerRow(fixture, 1);
      ExactRational const zero = fixture.rational("0");
      RowId const stale(CoreGeneration{registration.row.generation().value},
                        registration.row.ordinal() + 100U);
      require(fixture.core
                      .addAtom(stale, Relation::LessEqual, zero,
                               OriginId{cycle + 1U, 1}, OriginId{cycle + 1U, 2})
                      .status == InputStatus::InvalidId,
              "stress transactional invalid-ID failure changed status");
      require(fixture.core
                      .addAtom(registration.row, Relation::LessEqual, zero,
                               OriginId{cycle + 2U, 1}, OriginId{cycle + 2U, 2})
                      .status == InputStatus::Accepted,
              "stress transactional retry failed");
    }
    else if (category == 2)
    {
      NumberBudget input(limits);
      ExactLraCore invalid = invalidCore(input);
      require(invalid.status() == CheckStatus::InternalError,
              "stress invalid destruction setup failed");
    }
    else if (category == 3)
    {
      NumberBudget input(limits);
      ExactLraCore invalid = invalidCore(input);
      invalid.reset();
      require(invalid.status() == CheckStatus::Ready,
              "stress invalid reset failed");
    }
    else if (category == 4)
    {
      Fixture fixture;
      (void)registerRow(fixture, 1);
      CoreGeneration const generation = fixture.core.generation();
      cpp_fault::arm(0);
      fixture.core.reset();
      cpp_fault::pause();
      require(cpp_fault::hit &&
                  fixture.core.status() == CheckStatus::InternalError &&
                  fixture.core.generation() == generation,
              "stress reset-construction failure was not retryable");
      fixture.core.reset();
      require(fixture.core.status() == CheckStatus::Ready &&
                  isImmediateSuccessor(generation, fixture.core.generation()),
              "stress repeated reset did not recover");
    }
    else if (category == 5)
    {
      Fixture healthy;
      (void)registerRow(healthy, 1);
      ExactLraCore moved(std::move(healthy.core));
      require(moved.status() == CheckStatus::Ready &&
                  healthy.core.status() == CheckStatus::InternalError,
              "stress healthy move failed");
      NumberBudget input(limits);
      ExactLraCore invalid = invalidCore(input);
      ExactLraCore invalid_target(limits);
      invalid_target = std::move(invalid);
      require(invalid_target.status() == CheckStatus::InternalError,
              "stress invalid move assignment failed");
    }
    else
    {
      peerCycle();
      peerCycle();
    }
  }
  std::cout << "{\"mode\":\"stress\",\"passed\":true,\"cycles\":" << cycles
            << ",\"successful_registration\":" << categories[0]
            << ",\"transactional_retry\":" << categories[1]
            << ",\"invalid_destroy\":" << categories[2]
            << ",\"invalid_reset\":" << categories[3]
            << ",\"failed_reset_retry\":" << categories[4]
            << ",\"move_healthy_invalid\":" << categories[5]
            << ",\"peer_isolation\":" << categories[6] << "}" << std::endl;
}

} // namespace

int main(int argc, char** argv)
{
  try
  {
    require(argc >= 2, "missing mode");
    std::string const mode(argv[1]);
    if (mode == "lifecycle")
    {
      require(argc == 2, "lifecycle takes no arguments");
      lifecycleCase();
    }
    else if (mode == "stress")
    {
      destructionStressCase(argc, argv);
    }
    else
    {
      fail("unknown mode");
    }
    return 0;
  }
  catch (std::exception const& error)
  {
    cpp_fault::pause();
    stp_lra_imath_test_disable_failures();
    std::cerr << "FAIL " << error.what() << std::endl;
    return 1;
  }
}

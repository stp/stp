#ifndef STP_TEST_CPP_ALLOCATION_FAULT_H
#define STP_TEST_CPP_ALLOCATION_FAULT_H

// Include in exactly one translation unit per test executable. Faults apply
// only to explicitly armed operations; assertions and recovery run disarmed.
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <new>

#include "NoInline.h"

namespace allocation_fault {
thread_local std::int64_t fail_after = -1;
thread_local bool enabled = false;
thread_local bool counting = false;
thread_local std::uint64_t attempts = 0;

void before(std::size_t)
{
  if (enabled && counting)
    ++attempts;
  if (!enabled)
    return;
  if (fail_after == 0)
  {
    enabled = false;
    fail_after = -1;
    throw std::bad_alloc();
  }
  if (fail_after > 0)
    --fail_after;
}

void arm(std::uint64_t index) noexcept
{
  fail_after = static_cast<std::int64_t>(index);
  enabled = true;
}
void disable() noexcept
{
  fail_after = -1;
  enabled = false;
}
void begin() noexcept
{
  attempts = 0;
  counting = true;
  enabled = true;
}
std::uint64_t end() noexcept
{
  enabled = false;
  counting = false;
  return attempts;
}
} // namespace allocation_fault

STP_LRA_TEST_NOINLINE void* operator new(std::size_t size)
{
  allocation_fault::before(size);
  if (void* result = std::malloc(size == 0 ? 1 : size))
    return result;
  throw std::bad_alloc();
}
STP_LRA_TEST_NOINLINE void* operator new[](std::size_t size)
{
  return ::operator new(size);
}
STP_LRA_TEST_NOINLINE void operator delete(void* pointer) noexcept
{
  std::free(pointer);
}
STP_LRA_TEST_NOINLINE void operator delete[](void* pointer) noexcept
{
  std::free(pointer);
}
STP_LRA_TEST_NOINLINE void operator delete(void* pointer, std::size_t) noexcept
{
  std::free(pointer);
}
STP_LRA_TEST_NOINLINE void operator delete[](void* pointer, std::size_t) noexcept
{
  std::free(pointer);
}

#endif

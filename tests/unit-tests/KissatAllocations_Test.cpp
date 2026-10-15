/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: October, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#include "KissatAllocations.h"
#include "stp/Sat/Kissat.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <limits>
#include <vector>

using Owner = stp::detail::KissatAllocations;

namespace
{
std::size_t liveBlocks(const Owner& owner)
{
  std::size_t count = 0;
  const Owner::Block* previous = nullptr;
  for (const Owner::Block* block = owner.blocks; block; block = block->next)
  {
    EXPECT_EQ(block->previous, previous);
    previous = block;
    ++count;
  }
  return count;
}

struct FailingAllocator
{
  Owner owner;
  unsigned calls = 0;
  unsigned fail_at = 0;

  void beforeAllocation()
  {
    if (++calls == fail_at)
    {
      owner.failed = true;
      throw std::bad_alloc();
    }
  }

  static void* allocate(void* state, std::size_t bytes)
  {
    auto& self = *static_cast<FailingAllocator*>(state);
    self.beforeAllocation();
    return Owner::allocate(&self.owner, bytes);
  }

  static void* resize(void* state, void* ptr, std::size_t bytes)
  {
    auto& self = *static_cast<FailingAllocator*>(state);
    self.beforeAllocation();
    return Owner::resize(&self.owner, ptr, bytes);
  }

  static void deallocate(void* state, void* ptr)
  {
    auto& self = *static_cast<FailingAllocator*>(state);
    Owner::deallocate(&self.owner, ptr);
  }
};
} // namespace

TEST(KissatAllocations, PayloadsMatchCallbackAlignmentAndUnlinkInAnyOrder)
{
  Owner owner;
  std::vector<void*> pointers;
  for (std::size_t bytes = 0; bytes != 129; ++bytes)
  {
    void* ptr = Owner::allocate(&owner, bytes);
    ASSERT_NE(ptr, nullptr);
    const std::size_t scalar_alignment =
        std::max({alignof(void*), alignof(double), alignof(std::uint64_t)});
    std::size_t required_alignment = 1;
    while (required_alignment < scalar_alignment &&
           2 * required_alignment <= bytes)
      required_alignment *= 2;
    EXPECT_EQ(reinterpret_cast<std::uintptr_t>(ptr) % required_alignment, 0u);
    std::memset(ptr, 0x5a, bytes);
    pointers.push_back(ptr);
  }
  EXPECT_EQ(liveBlocks(owner), pointers.size());
  // Remove the head, tail and interior entries while their neighbours live.
  for (std::size_t i : {128u, 0u, 64u})
  {
    Owner::deallocate(&owner, pointers[i]);
    pointers[i] = nullptr;
  }
  EXPECT_EQ(liveBlocks(owner), 126u);
  for (void* ptr : pointers)
    Owner::deallocate(&owner, ptr);
  EXPECT_EQ(owner.blocks, nullptr);
  EXPECT_FALSE(owner.failed);
}

TEST(KissatAllocations, ResizePreservesPayloadAndOwnership)
{
  Owner owner;
  void* tail = Owner::allocate(&owner, 17);
  void* middle = Owner::resize(&owner, nullptr, 19);
  void* head = Owner::allocate(&owner, 23);
  for (void** pointer : {&head, &middle, &tail})
  {
    auto* ptr = static_cast<unsigned char*>(*pointer);
    std::memset(ptr, 0xa5, 16);
    for (std::size_t bytes : {1048576u, 16u, 4194304u, 0u})
    {
      ptr = static_cast<unsigned char*>(Owner::resize(&owner, ptr, bytes));
      EXPECT_EQ(liveBlocks(owner), 3u);
      EXPECT_EQ(reinterpret_cast<std::uintptr_t>(ptr) %
                    alignof(std::max_align_t),
                0u);
      for (std::size_t i = 0; i != std::min(bytes, std::size_t(16)); ++i)
        EXPECT_EQ(ptr[i], 0xa5);
    }
    *pointer = ptr;
  }
  // The owner also cleans up blocks a partial solver did not release.
  EXPECT_FALSE(owner.failed);
}

TEST(KissatAllocations, FailedResizeKeepsTheOriginalOwnedBlock)
{
  Owner owner;
  auto* ptr = static_cast<unsigned char*>(Owner::allocate(&owner, 32));
  std::memset(ptr, 0x6b, 32);
  EXPECT_THROW(
      Owner::resize(&owner, ptr, std::numeric_limits<std::size_t>::max()),
      std::bad_alloc);
  EXPECT_TRUE(owner.failed);
  EXPECT_EQ(liveBlocks(owner), 1u);
  for (std::size_t i = 0; i != 32; ++i)
    EXPECT_EQ(ptr[i], 0x6b);
  EXPECT_THROW(Owner::allocate(&owner, std::numeric_limits<std::size_t>::max()),
               std::bad_alloc);
  EXPECT_EQ(liveBlocks(owner), 1u);
}

TEST(KissatAllocations, InterruptedCInitializationAndGrowthLeaveOwnedBlocks)
{
  for (unsigned failure = 0; failure != 17; ++failure)
  {
    SCOPED_TRACE(failure);
    FailingAllocator state;
    state.fail_at = failure;
    const kissat_allocator allocator = {&state, FailingAllocator::allocate,
                                        FailingAllocator::resize,
                                        FailingAllocator::deallocate};
    bool interrupted = false;
    try
    {
      kissat* solver = kissat_init_with_allocator(&allocator);
      kissat_set_option(solver, "quiet", 1);
      kissat_set_option(solver, "incremental", 1);
      kissat_set_option(solver, "factor", 0);
      kissat_set_option(solver, "probe", 0);
      kissat_reserve(solver, 4096);
      for (int variable = 1; variable <= 512; ++variable)
      {
        kissat_add(solver, variable);
        kissat_add(solver, variable % 512 + 1);
        kissat_add(solver, 0);
      }
      EXPECT_EQ(kissat_solve(solver), 10);
      kissat_release(solver);
    }
    catch (const std::bad_alloc&)
    {
      interrupted = true;
      EXPECT_TRUE(state.owner.failed);
      EXPECT_EQ(state.calls, failure);
      // The adapter discards a failed C solver through its owner. Do not
      // ask the C destructor to walk the interrupted structures.
      EXPECT_EQ(liveBlocks(state.owner) == 0, failure == 1);
    }
    EXPECT_EQ(interrupted, failure != 0);
    if (!interrupted)
    {
      EXPECT_FALSE(state.owner.failed);
      EXPECT_EQ(state.owner.blocks, nullptr);
    }
    // Scope exit frees every tracked block, including the partial C solver.
  }
}

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

// An endpoint out of memory: this executable replaces operator new so that
// the k-th allocation from a point on fails (or every one does), and drives
// a poll's selection (begin_import) and its hand-over (next) through every
// such failure, on a fresh endpoint's first poll and on later ones. A poll
// that fails hands nothing over, allocates nothing while it gives up (both
// run noexcept: an allocation that throws there would terminate), and the
// next poll imports as if nothing had happened.
#include "Exchange.h"
#include <gtest/gtest.h>
#include <algorithm>
#include <atomic>
#include <cstdlib>
#include <new>
#include <set>

namespace
{
std::atomic<long> countdown{-1}; // allocations left before one fails; -1 never
std::atomic<bool> fail_all{false}, fired{false};
} // namespace

void* operator new(std::size_t n)
{
  if (fail_all || (countdown >= 0 && countdown.fetch_sub(1) == 0))
  {
    fired = true;
    throw std::bad_alloc();
  }
  if (void* p = std::malloc(n ? n : 1))
    return p;
  throw std::bad_alloc();
}
// The other forms, replaced as pairs with their deletes, so that whatever
// allocates through one of them (gtest's std::stable_sort takes the nothrow
// form) frees through its own pair -- an address sanitizer checks that.
void* operator new(std::size_t n, const std::nothrow_t&) noexcept
{
  try
  {
    return ::operator new(n);
  }
  catch (...)
  {
    return nullptr;
  }
}
void* operator new[](std::size_t n)
{
  return ::operator new(n);
}
void* operator new[](std::size_t n, const std::nothrow_t&) noexcept
{
  return ::operator new(n, std::nothrow);
}
// The replacement pair allocates with malloc, so it frees with free.
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmismatched-new-delete"
#endif
void operator delete(void* p) noexcept
{
  std::free(p);
}
void operator delete(void* p, std::size_t) noexcept
{
  std::free(p);
}
void operator delete(void* p, const std::nothrow_t&) noexcept
{
  std::free(p);
}
void operator delete[](void* p) noexcept
{
  std::free(p);
}
void operator delete[](void* p, std::size_t) noexcept
{
  std::free(p);
}
void operator delete[](void* p, const std::nothrow_t&) noexcept
{
  std::free(p);
}
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic pop
#endif

namespace
{
void arm(long k)
{
  fired = false;
  countdown = k;
}
void disarm()
{
  countdown = -1;
  fail_all = false;
}
// Two writers, every clause size, a fresh variable each time; `written`
// holds every clause sorted.
struct Writers
{
  stpp::Rings& rings;
  stpp::Endpoint w0, w1;
  std::set<std::vector<int>> written;
  int v = 1;
  Writers(stpp::Rings& r, const stpp::Endpoint::Settings& s)
      : rings(r), w0(r, 0, s), w1(r, 1, s)
  {
  }
  void batch()
  {
    for (std::size_t size = 1; size <= 8; ++size)
      for (stpp::Endpoint* w : {&w0, &w1})
      {
        std::vector<int> c;
        for (std::size_t i = 0; i < size; ++i)
          c.push_back(i % 2 ? -(v++) : v++);
        w->learned(c.data(), c.size());
        std::sort(c.begin(), c.end());
        written.insert(c);
      }
  }
};
// Everything a poll hands over must have been written whole.
std::size_t drain(stpp::Endpoint& reader, const Writers& w)
{
  std::size_t n = 0;
  std::vector<int> c;
  while (reader.next(c))
  {
    std::sort(c.begin(), c.end());
    EXPECT_EQ(w.written.count(c), 1u) << "a clause never written";
    ++n;
  }
  return n;
}
} // namespace

// The selection: the k-th allocation of a poll fails, for every k the poll
// makes, on a fresh endpoint and after a first poll.
TEST(EndpointOutOfMemory, AFailedSelectionHandsNothingOver)
{
  stpp::Endpoint::Settings fast;
  fast.rate = 1e12;
  unsigned failures = 0;
  for (bool first : {true, false})
    for (long k = 0;; ++k)
    {
      stpp::Rings rings(3, 4096);
      Writers w(rings, fast);
      stpp::Endpoint reader(rings, 2, fast);
      if (!first)
      {
        w.batch();
        reader.begin_import(1000);
        drain(reader, w);
      }
      for (int i = 0; i < 8; ++i)
        w.batch();
      arm(k);
      reader.begin_import(1000);
      disarm();
      if (!fired)
      {
        EXPECT_GT(drain(reader, w), 0u) << "a poll with no failure imports";
        break;
      }
      ++failures;
      std::vector<int> c;
      ASSERT_FALSE(reader.next(c)) << "a failed selection hands nothing over";
      w.batch();
      reader.begin_import(1000);
      ASSERT_GT(drain(reader, w), 0u) << "the poll after a failed one imports";
    }
  EXPECT_GT(failures, 0u) << "no allocation failure was injected";
}

// Every allocation fails: giving up allocates nothing.
TEST(EndpointOutOfMemory, GivingUpAllocatesNothing)
{
  stpp::Endpoint::Settings fast;
  fast.rate = 1e12;
  stpp::Rings rings(3, 4096);
  Writers w(rings, fast);
  stpp::Endpoint reader(rings, 2, fast);
  for (int i = 0; i < 8; ++i)
    w.batch();
  fail_all = true;
  reader.begin_import(1000);
  std::vector<int> c;
  const bool handed = reader.next(c);
  disarm();
  EXPECT_FALSE(handed) << "nothing handed over with no memory at all";
  w.batch();
  reader.begin_import(1000);
  EXPECT_GT(drain(reader, w), 0u) << "the endpoint imports again";
}

// The hand-over: next() copies a clause into the caller's vector, which may
// allocate; a failure ends the poll, and the next poll imports.
TEST(EndpointOutOfMemory, AFailedHandOverEndsThePoll)
{
  stpp::Endpoint::Settings fast;
  fast.rate = 1e12;
  unsigned failures = 0;
  for (long k = 0; k < 4; ++k)
  {
    stpp::Rings rings(3, 4096);
    Writers w(rings, fast);
    stpp::Endpoint reader(rings, 2, fast);
    for (int i = 0; i < 4; ++i)
      w.batch();
    reader.begin_import(1000);
    std::vector<int> c; // empty: the first copy allocates
    arm(k);
    while (reader.next(c))
    {
    }
    disarm();
    if (fired)
    {
      ++failures;
      EXPECT_FALSE(reader.next(c)) << "a failed hand-over ends the poll";
    }
    w.batch();
    reader.begin_import(1000);
    EXPECT_GT(drain(reader, w), 0u) << "the poll after a failed hand-over imports";
  }
  EXPECT_GT(failures, 0u) << "no allocation failure was injected";
}

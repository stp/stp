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

// stp-p's component tests: the clause rings and the import polls, alone and
// under forced and stalled schedules. The query's shape is the library's to
// check (ParseMode::SINGLE_QUERY, tests/api/cpp/single-query.cpp).
#include "Exchange.h"
#include <gtest/gtest.h>
#include <algorithm>
#include <csignal>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

namespace stpp
{
// The forced schedules below play the writer's side of the ring protocol by
// hand, so that they can stop it between storing a clause and publishing it.
struct RingTestAccess
{
  static std::atomic<std::uint64_t>& written(const Rings& r, unsigned slot)
  {
    return r.header(slot)->written;
  }
  static int* data(const Rings& r, unsigned slot)
  {
    return r.data(slot);
  }
};
} // namespace stpp

namespace
{
// A failed check inside a helper ends its test with the reason.
void require(bool value, const char* why)
{
  if (!value)
    throw std::runtime_error(why);
}
// The clause the deterministic test writer exports as its i-th: one to
// three literals, a different clause for every i, so the writer's own
// duplicate filter never holds one back.
std::vector<int> ring_clause(unsigned i)
{
  std::vector<int> c{int(i + 1)};
  if (i % 3)
    c.push_back(-int(i + 1000001));
  if (i % 5 == 0)
    c.push_back(int(i + 2000001));
  std::sort(c.begin(), c.end());
  return c;
}

// Forced schedules: the writer laps a reader stalled in the middle of a
// poll's scan. The reader's first load from one protected page of the ring
// faults; the handler unprotects the page and runs the writer's steps -- it
// publishes max-size clauses until it has lapped the reader, then stores one
// more clause, published or not (a writer stalled between its last data
// store and its count) -- and the faulting load then reads the new data.
// Every interleaving so produced is a sequentially consistent one, so it is
// legal on every memory model. No clause the reader accepts may be one that
// was never written whole.
struct Forced
{
  stpp::Rings* rings = nullptr;
  std::set<std::vector<int>> written; // every clause ever stored, sorted
  int variable = 1;
  char* page = nullptr;
  long page_size = 0;
  std::uint64_t target = 0;
  bool publish_last = false;
  unsigned faults = 0;
};
Forced* forced = nullptr;
std::vector<int> fresh_clause(std::size_t size)
{
  std::vector<int> c;
  for (std::size_t i = 0; i < size; ++i, ++forced->variable)
    c.push_back(forced->variable % 2 ? forced->variable : -forced->variable);
  return c;
}
void store(const std::vector<int>& c, bool publish)
{
  auto& w = stpp::RingTestAccess::written(*forced->rings, 0);
  auto* d = stpp::RingTestAccess::data(*forced->rings, 0);
  const auto cap = forced->rings->capacity();
  const auto at = w.load(std::memory_order_relaxed);
  std::atomic_thread_fence(std::memory_order_release);
  for (std::size_t i = 0; i < c.size(); ++i)
    stpp::ring_store(&d[(at + i) % cap], c[i]);
  stpp::ring_store(&d[(at + c.size()) % cap], 0);
  if (publish)
    w.store(at + c.size() + 1, std::memory_order_release);
  auto sorted = c;
  std::sort(sorted.begin(), sorted.end());
  forced->written.insert(sorted);
}
std::uint64_t forced_written()
{
  return stpp::RingTestAccess::written(*forced->rings, 0).load();
}
void forced_writer(int, siginfo_t* info, void*)
{
  char* at = static_cast<char*>(info->si_addr);
  if (at < forced->page || at >= forced->page + forced->page_size)
    _exit(99); // a fault the schedule did not plan
  ++forced->faults;
  mprotect(forced->page, forced->page_size, PROT_READ | PROT_WRITE);
  while (forced_written() + 9 <= forced->target)
    store(fresh_clause(8), true);
  if (const auto rest = forced->target - forced_written())
    store(fresh_clause(rest - 1), true);
  store(fresh_clause(8), forced->publish_last);
}
// The fault handler a schedule installs, restored (and the schedule's state
// cleared) however the schedule ends.
struct Handler
{
  struct sigaction previous{};
  explicit Handler(void (*f)(int, siginfo_t*, void*))
  {
    struct sigaction handler{};
    handler.sa_sigaction = f;
    handler.sa_flags = SA_SIGINFO;
    sigaction(SIGSEGV, &handler, &previous);
  }
  ~Handler()
  {
    sigaction(SIGSEGV, &previous, nullptr);
    forced = nullptr;
  }
};
// The ring the schedules use: at least four pages of literals, so that a
// page-aligned index lies inside it on any page size. Its data follows a
// 64-byte header in a page-aligned mapping.
std::size_t schedule_capacity(long page)
{
  return std::max<std::size_t>(4096, 4 * std::size_t(page) / sizeof(int));
}
// The page-aligned literal index nearest `near`, past the mapping's first
// page (which also holds the header every scan loads first).
std::size_t aligned_index(long page, std::size_t near)
{
  std::size_t best = 0;
  for (std::size_t k = 2; (k * page - 64) / sizeof(int) < 2 * near + page; ++k)
  {
    const std::size_t i = (k * page - 64) / sizeof(int);
    if (!best || (i > near ? i - near : near - i) < (best > near ? best - near : near - best))
      best = i;
  }
  return best;
}
// One schedule: protect the page holding literal `index`, poll, check every
// clause accepted. Returns what the poll accepted; the reader's counters
// stay in `reader`.
unsigned forced_poll(stpp::Endpoint& reader, Forced& f, std::size_t index)
{
  auto* d = stpp::RingTestAccess::data(*f.rings, 0);
  char* at = reinterpret_cast<char*>(d + index);
  f.page = at - reinterpret_cast<std::uintptr_t>(at) % f.page_size;
  mprotect(f.page, f.page_size, PROT_NONE);
  reader.begin_import(1000);
  unsigned accepted = 0;
  std::vector<int> c;
  while (reader.next(c))
  {
    std::sort(c.begin(), c.end());
    require(f.written.count(c) == 1,
            "a forced schedule imported a clause never written whole");
    ++accepted;
  }
  mprotect(f.page, f.page_size, PROT_READ | PROT_WRITE);
  return accepted;
}
// Mid-scan laps: the scan window covers the whole ring (the clamp), and the
// writer laps the reader at the protected page, one ring later.
unsigned forced_schedules(unsigned& windowed, unsigned& whole)
{
  const long page_size = sysconf(_SC_PAGESIZE);
  const std::size_t cap = schedule_capacity(page_size);
  const std::size_t index = aligned_index(page_size, cap / 2);
  const Handler handler(forced_writer);
  unsigned accepted = 0, runs = 0, faults = 0;
  stpp::Endpoint::Settings settings;
  settings.rate = 1e12;
  settings.max_size = 8;
  // The fill puts the published end on both sides of the scan window (the
  // reader's clamp of it to the ring), on any page size: one poll scans the
  // whole pending range, another starts mid-ring at the window.
  const std::size_t window = std::min<std::size_t>(
      settings.scan_window, cap - (settings.max_size + 1) - 1);
  const unsigned fill0 = unsigned((window - 11) / 9 - 10);
  windowed = whole = 0;
  for (bool polled : {false, true})
    for (unsigned fill = fill0; fill < fill0 + 20; ++fill)
      for (int shift = -9; shift <= 9; ++shift)
      {
        stpp::Rings rings(2, cap);
        Forced f;
        f.rings = &rings;
        f.page_size = page_size;
        forced = &f;
        stpp::Endpoint reader(rings, 1, settings);
        // One lap and a half of clauses: a 2-literal one, `fill` of eight,
        // and a 7-literal one. The scan starts inside the first lap -- at
        // its beginning, or (`polled`) at a cursor a first poll left in the
        // middle of the ring.
        store(fresh_clause(2), true);
        for (unsigned k = 0; k < fill; ++k)
        {
          store(fresh_clause(8), true);
          if (polled && k == fill / 2)
          {
            reader.begin_import(1000);
            std::vector<int> c;
            while (reader.next(c))
            {
            }
          }
        }
        store(fresh_clause(7), true);
        // The writer laps to just below the faulting index, one ring later.
        f.target = std::uint64_t(index + cap - 8 + shift);
        accepted += forced_poll(reader, f, index);
        if (!polled)
          (reader.counters()["skipped_literals"].get<std::uint64_t>() ? windowed : whole) += 1;
        faults += f.faults;
        ++runs;
      }
  require(runs == 2 * 20 * 19, "forced schedules run");
  require(faults == runs, "every forced schedule's fault fired once");
  return accepted;
}
// The window's start: a scan window smaller than the ring (as stp-p's 2^16
// literals are of its 2^20), so a poll starts mid-ring and probes the literal
// before its start for a clause boundary. The protected page holds that
// literal: the writer runs before the probe, laps the reader and leaves a
// max-size clause whose zero lands on or near it, its count published or
// not. The clause the probe then seems to start may be the torn tail of an
// overwritten one; none may be accepted.
unsigned probe_schedules(unsigned& tears)
{
  const long page_size = sysconf(_SC_PAGESIZE);
  const std::size_t cap = schedule_capacity(page_size);
  const Handler handler(forced_writer);
  unsigned accepted = 0, runs = 0, faults = 0;
  tears = 0;
  stpp::Endpoint::Settings settings;
  settings.rate = 1e12;
  settings.max_size = 8;
  settings.scan_window = cap / 4;
  for (unsigned lead = 0; lead < 9; ++lead)
    for (int shift = -9; shift <= 9; ++shift)
      for (bool publish : {false, true})
      {
        stpp::Rings rings(2, cap);
        Forced f;
        f.rings = &rings;
        f.page_size = page_size;
        f.publish_last = publish;
        forced = &f;
        stpp::Endpoint reader(rings, 1, settings);
        // Half a ring of clauses, the first `lead` literals long, so that
        // clause boundaries fall everywhere relative to the window's start.
        if (lead)
          store(fresh_clause(lead), true);
        while (forced_written() + 9 <= cap / 2)
          store(fresh_clause(8), true);
        const std::uint64_t w = forced_written();
        const std::uint64_t start = w - settings.scan_window;
        // The unpublished clause's zero lands at start - 1 + shift, a ring
        // later.
        f.target = start + cap - 9 + std::uint64_t(std::int64_t(shift));
        accepted += forced_poll(reader, f, (start - 1) % cap);
        tears += reader.counters()["torn"].get<unsigned>();
        faults += f.faults;
        ++runs;
      }
  require(runs == 9 * 19 * 2, "probe schedules run");
  require(faults == runs, "every probe schedule's fault fired once");
  require(tears > 0, "no probe schedule tore a clause");
  return accepted;
}

// Writer-side schedules: stp-p's own writer (Endpoint::learned) stopped in
// the middle of storing a clause. The page under one of its slots -- a
// literal, or the clause's zero -- is protected, and the fault handler runs a
// whole reader poll before the store is retried. The reader may accept only
// clauses learned() has finished: a writer that published its count before
// its data would hand over the old lap's data or zeros as a clause.
struct Stopped
{
  stpp::Endpoint* reader = nullptr;
  std::set<std::vector<int>> finished;
  char* page = nullptr;
  long page_size = 0;
  unsigned faults = 0, accepted = 0, bad = 0;
};
Stopped* stopped = nullptr;
void stopped_writer(int, siginfo_t* info, void*)
{
  char* at = static_cast<char*>(info->si_addr);
  if (at < stopped->page || at >= stopped->page + stopped->page_size)
    _exit(99); // a fault the schedule did not plan
  ++stopped->faults;
  mprotect(stopped->page, stopped->page_size, PROT_READ | PROT_WRITE);
  stopped->reader->begin_import(1u << 20);
  std::vector<int> c;
  while (stopped->reader->next(c))
  {
    std::sort(c.begin(), c.end());
    ++stopped->accepted;
    stopped->bad += !stopped->finished.count(c);
  }
}
unsigned writer_schedules(unsigned& runs, unsigned& bad)
{
  const long page_size = sysconf(_SC_PAGESIZE);
  const std::size_t cap = 4 * std::size_t(page_size) / sizeof(int);
  // The first page boundary inside ring 0's data, as a literal index.
  const std::size_t boundary = (std::size_t(page_size) - 64) / sizeof(int);
  struct sigaction handler{}, previous{};
  handler.sa_sigaction = stopped_writer;
  handler.sa_flags = SA_SIGINFO;
  sigaction(SIGSEGV, &handler, &previous);
  struct Restore
  {
    struct sigaction& previous;
    ~Restore()
    {
      sigaction(SIGSEGV, &previous, nullptr);
      stopped = nullptr;
    }
  } restore{previous};
  unsigned accepted = 0, faults = 0;
  runs = bad = 0;
  stpp::Endpoint::Settings settings;
  settings.rate = 1e12;
  for (unsigned lap : {0u, 1u, 2u})
    for (unsigned size = 1; size <= 8; ++size)
      for (unsigned k = 1; k <= size; ++k) // the faulting slot: literal k, or the zero
      {
        stpp::Rings rings(2, cap);
        stpp::Endpoint writer(rings, 0, settings), reader(rings, 1, settings);
        Stopped st;
        st.reader = &reader;
        st.page_size = page_size;
        stopped = &st;
        int variable = 1;
        auto learn = [&](std::size_t n)
        {
          std::vector<int> c;
          for (std::size_t i = 0; i < n; ++i, ++variable)
            c.push_back(variable % 2 ? variable : -variable);
          writer.learned(c.data(), c.size());
          std::sort(c.begin(), c.end());
          st.finished.insert(c);
        };
        auto published = [&] { return stpp::RingTestAccess::written(rings, 0).load(); };
        // The clause starts at W, so that its slot W + k is the page's first.
        const std::uint64_t W = boundary - k + lap * cap;
        while (published() + 18 < W)
          learn(8);
        const std::uint64_t rest = W - published();
        if (rest == 10)
        {
          learn(4);
          learn(4);
        }
        else if (rest > 10)
        {
          learn(8);
          learn(rest - 10);
        }
        else if (rest >= 2)
          learn(rest - 1);
        require(published() == W, "the writer reaches the clause's start");
        reader.begin_import(1u << 20); // the reader catches up: its cursor is W
        std::vector<int> c;
        while (reader.next(c))
        {
        }
        auto* d = stpp::RingTestAccess::data(rings, 0);
        char* at = reinterpret_cast<char*>(d + (W + k) % cap);
        st.page = at - reinterpret_cast<std::uintptr_t>(at) % page_size;
        require(st.page == at, "the stopping slot starts a page");
        mprotect(st.page, page_size, PROT_NONE);
        learn(size);
        mprotect(st.page, page_size, PROT_READ | PROT_WRITE);
        require(st.faults == 1, "the writer stopped once, mid-clause");
        // After the store: the finished clause, and nothing else.
        reader.begin_import(1u << 20);
        while (reader.next(c))
        {
          std::sort(c.begin(), c.end());
          ++st.accepted;
          st.bad += !st.finished.count(c);
        }
        accepted += st.accepted;
        faults += st.faults;
        bad += st.bad;
        ++runs;
      }
  require(faults == runs, "every writer schedule stopped once");
  return accepted;
}

// A writer that stalls: clauses of up to max_size literals, each encoding
// its number, and now and then a pause between the last data store and the
// count, as a preemption there would cause. A reader polling with pauses of
// its own laps and is lapped; every clause it accepts must decode.
unsigned stall_size(std::uint64_t i)
{
  std::uint64_t x = i * 0x9e3779b97f4a7c15ull;
  x ^= x >> 29;
  return (x & 1) ? 8 : unsigned(1 + (x >> 1) % 7);
}
std::vector<int> stall_clause(std::uint64_t i)
{
  std::vector<int> c;
  for (unsigned j = 0; j < stall_size(i); ++j)
  {
    const int v = int((i % 100000000u) * 16 + j + 1);
    c.push_back(j % 2 ? -v : v);
  }
  return c;
}
bool stall_valid(std::vector<int> c)
{
  if (c.empty())
    return false;
  std::sort(c.begin(), c.end(), [](int a, int b) { return std::abs(a) < std::abs(b); });
  const int base = std::abs(c[0]) - 1;
  if (base % 16)
    return false;
  auto expected = stall_clause(std::uint64_t(base / 16));
  std::sort(expected.begin(), expected.end(),
            [](int a, int b) { return std::abs(a) < std::abs(b); });
  return c == expected;
}
} // namespace

using namespace stpp;

// Rings: a writer that laps a reader several times, and a reader that
// falls behind, must only ever see whole clauses that were written.
TEST(StppComponents, ALaggingReaderSeesOnlyWholeClauses)
{
  std::set<std::vector<int>> possible;
  for (unsigned i = 0; i < 200000; ++i)
    possible.insert(ring_clause(i));
  stpp::Rings rings(2, 64);
  stpp::Endpoint::Settings fast;
  fast.rate = 1e12;
  fast.scan_window = 64;
  stpp::Endpoint writer(rings, 0, fast), reader(rings, 1, fast);
  unsigned read = 0;
  std::vector<int> c;
  for (unsigned round = 0; round < 40; ++round)
  {
    for (unsigned i = round * 100; i < round * 100 + 100; ++i)
    {
      auto clause = ring_clause(i);
      writer.learned(clause.data(), clause.size());
    }
    if (round % 7 == 3) // the reader lags for a few rounds
      continue;
    reader.begin_import(1u << 20);
    while (reader.next(c))
    {
      std::sort(c.begin(), c.end());
      ASSERT_TRUE(possible.count(c) == 1) << "ring returned a clause never written";
      ++read;
    }
  }
  auto counters = reader.counters();
  ASSERT_TRUE(read > 0 && counters["lapped"].get<unsigned>() > 0) << "lagging reader not exercised";
  std::cout << "rings: lagging reader read " << read << " (lapped "
            << counters["lapped"] << ")\n";
}

// Import budget: a poll takes every unit, then exactly `budget` of the
// shortest other clauses in non-decreasing size, discards the rest, and
// moves every cursor past what it scanned.
TEST(StppComponents, ABudgetedPollTakesUnitsAndTheShortest)
{
  stpp::Rings rings(4, 4096);
  stpp::Endpoint::Settings fast;
  fast.rate = 1e12;
  std::map<std::vector<int>, unsigned> written; // sorted clause -> copies
  std::vector<std::size_t> longer;              // sizes of clauses > 1
  int variable = 1;
  auto write = [&](stpp::Endpoint& w, std::vector<int> c)
  {
    w.learned(c.data(), c.size());
    std::sort(c.begin(), c.end());
    if (!written[c]++ && c.size() > 1)
      longer.push_back(c.size());
  };
  std::vector<int> twice{-7001, 7002}; // written by two rings
  for (unsigned slot = 0; slot < 3; ++slot)
  {
    stpp::Endpoint w(rings, slot, fast);
    for (unsigned i = 0; i < 40; ++i)
    {
      std::vector<int> c;
      for (std::size_t k = 8 - (i * 3 + slot) % 8; k; --k, ++variable)
        c.push_back(k % 2 ? variable : -variable);
      write(w, c);
    }
    if (slot < 2)
      write(w, twice);
  }
  std::size_t units = 0;
  for (const auto& [c, n] : written)
    units += c.size() == 1;
  std::sort(longer.begin(), longer.end());
  const std::size_t budget = 25;
  ASSERT_TRUE(units > 0 && longer.size() > budget) << "budget backlog";
  stpp::Endpoint reader(rings, 3, fast);
  reader.begin_import(budget);
  std::vector<std::vector<int>> got;
  std::vector<int> c;
  while (reader.next(c))
  {
    std::sort(c.begin(), c.end());
    ASSERT_TRUE(written.count(c) == 1) << "budgeted poll invented a clause";
    got.push_back(c);
  }
  ASSERT_TRUE(got.size() == units + budget) << "a budgeted poll takes every unit and exactly the budget";
  std::set<std::vector<int>> distinct(got.begin(), got.end());
  ASSERT_TRUE(distinct.size() == got.size()) << "budgeted poll repeated a clause";
  for (std::size_t i = 0; i < got.size(); ++i)
    ASSERT_TRUE(i < units ? got[i].size() == 1
                      : got[i].size() > 1 && got[i].size() >= got[i - 1].size()) << "units first, then non-decreasing size";
  for (std::size_t i = 0; i < budget; ++i)
    ASSERT_TRUE(got[units + i].size() == longer[i]) << "the budget goes to the shortest clauses";
  auto counters = reader.counters();
  ASSERT_TRUE(counters["scanned"] == 3 * 40 + 2 &&
              counters["imported"] == units + budget &&
              counters["duplicates"] == 1 && // `twice`: not budgeted
              counters["discarded"] == longer.size() - budget &&
              counters["polls"] == 1) << "budgeted poll counters";
  // A second poll finds nothing stale: everything was taken or dropped.
  reader.begin_import(budget);
  ASSERT_TRUE(!reader.next(c)) << "a second budgeted poll found stale clauses";
  // What arrives after a poll is the next poll's.
  {
    stpp::Endpoint w(rings, 1, fast);
    for (int size : {4, 2, 3})
    {
      std::vector<int> fresh;
      for (int k = 0; k < size; ++k, ++variable)
        fresh.push_back(variable);
      w.learned(fresh.data(), fresh.size());
    }
  }
  reader.begin_import(budget);
  std::vector<std::size_t> sizes;
  while (reader.next(c))
    sizes.push_back(c.size());
  ASSERT_TRUE((sizes == std::vector<std::size_t>{2, 3, 4})) << "the next poll takes only what arrived, shortest first";
  ASSERT_TRUE(reader.counters()["polls"] == 3) << "polls counted as they start";
  // next() outside a poll hands over nothing.
  ASSERT_TRUE(!reader.next(c)) << "next() without a poll";
}

// Scan window: a ring holding more than the window delivers only the
// newest clauses, and the counters say how many literals were skipped.
TEST(StppComponents, AScanWindowDeliversTheNewestClauses)
{
  stpp::Rings rings(2, 4096);
  stpp::Endpoint::Settings small;
  small.rate = 1e12;
  small.scan_window = 64;
  stpp::Endpoint w(rings, 0, small), reader(rings, 1, small);
  std::vector<std::vector<int>> all;
  for (int i = 0; i < 100; ++i)
  {
    std::vector<int> c{3 * i + 1, -(3 * i + 2), 3 * i + 3};
    w.learned(c.data(), c.size());
    std::sort(c.begin(), c.end());
    all.push_back(c);
  }
  // 100 clauses of three literals and a zero: 400 literals, of which the
  // newest 64 are the newest 16 clauses.
  std::set<std::vector<int>> newest(all.end() - 16, all.end());
  reader.begin_import(1000);
  std::vector<int> c;
  std::set<std::vector<int>> got;
  while (reader.next(c))
  {
    std::sort(c.begin(), c.end());
    got.insert(c);
  }
  ASSERT_TRUE(got == newest) << "the scan window delivers the newest clauses";
  ASSERT_TRUE(reader.counters()["skipped_literals"] == 400 - 64) << "skipped literals counted";
}

// A poll's budget is the backend's cap on longer clauses: 0 takes the
// units alone. And each poll starts its hand-over at the next ring, so
// a binding budget reaches every ring in turn.
TEST(StppComponents, ABudgetOfZeroTakesUnitsAndTheBudgetRotates)
{
  stpp::Rings rings(3, 4096);
  stpp::Endpoint::Settings fast;
  fast.rate = 1e12;
  stpp::Endpoint w0(rings, 0, fast), w1(rings, 1, fast), reader(rings, 2, fast);
  int v = 1;
  auto clause = [&](stpp::Endpoint& w, std::size_t size)
  {
    std::vector<int> c;
    for (std::size_t k = 0; k < size; ++k)
      c.push_back(v++);
    w.learned(c.data(), c.size());
  };
  for (int i = 0; i < 3; ++i)
  {
    clause(w0, 1);
    clause(w1, 2);
  }
  reader.begin_import(0);
  std::vector<int> c;
  std::size_t units = 0, longer = 0;
  while (reader.next(c))
    (c.size() == 1 ? units : longer) += 1;
  ASSERT_TRUE(units == 3 && longer == 0) << "a budget of 0 takes units only";
  std::set<int> rings_served;
  for (int poll = 0; poll < 4; ++poll)
  {
    const int base0 = v;
    clause(w0, 2);
    clause(w1, 2);
    reader.begin_import(1);
    ASSERT_TRUE(reader.next(c) && c.size() == 2) << "a budgeted poll's clause";
    rings_served.insert(std::abs(c[0]) < base0 + 2 ? 0 : 1);
    while (reader.next(c))
    {
    }
  }
  ASSERT_TRUE(rings_served.size() == 2) << "the budget rotates across rings";
}

// Forced schedules: a reader stalled mid-scan past a lap of max-size
// clauses, a writer stalled before its count; and a window that starts
// mid-ring, its probe raced by the writer.
TEST(StppComponents, ForcedAndProbedSchedulesImportNoTornClause)
{
  unsigned windowed = 0, whole = 0;
  const unsigned accepted = forced_schedules(windowed, whole);
  ASSERT_TRUE(accepted > 0) << "forced schedules accepted nothing";
  ASSERT_TRUE(windowed > 0 && whole > 0)
      << "forced schedules: " << windowed << " windowed scans, " << whole << " whole";
  unsigned tears = 0;
  const unsigned probed = probe_schedules(tears);
  ASSERT_TRUE(probed > 0) << "probe schedules accepted nothing";
  std::cout << "forced schedules: " << 2 * 20 * 19 << " runs (" << windowed
            << " windowed, " << whole << " whole scans before a poll), " << accepted
            << " clauses accepted; window-start probe: " << 9 * 19 * 2
            << " runs, " << probed << " accepted, " << tears
            << " torn clauses refused; page " << sysconf(_SC_PAGESIZE)
            << "\n";
}

// The writer stopped mid-clause, at every slot of every size, in three laps:
// no poll hands over anything learned() had not finished.
TEST(StppComponents, AWriterStoppedMidClauseHandsOverNothingUnfinished)
{
  unsigned runs = 0, bad = 0;
  const unsigned accepted = writer_schedules(runs, bad);
  ASSERT_EQ(bad, 0u) << "a stopped writer's clause was handed over unfinished";
  ASSERT_TRUE(runs == 3 * 36 && accepted >= runs)
      << "writer schedules: " << runs << " runs, " << accepted << " accepted";
  std::cout << "writer schedules: " << runs << " runs, " << accepted
            << " clauses accepted\n";
}

// The hand-over's starting ring rotates over the other roots' rings only: a
// binding budget reaches each of them first equally often.
TEST(StppComponents, TheHandOverRotatesOverTheOtherRings)
{
  stpp::Rings rings(4, 4096);
  stpp::Endpoint::Settings fast;
  fast.rate = 1e12;
  std::vector<std::unique_ptr<stpp::Endpoint>> writers;
  for (unsigned s : {0u, 2u, 3u})
    writers.push_back(std::make_unique<stpp::Endpoint>(rings, s, fast));
  stpp::Endpoint reader(rings, 1, fast);
  std::map<unsigned, unsigned> first;
  int v = 1;
  for (int poll = 0; poll < 30; ++poll)
  {
    std::map<int, unsigned> owner;
    for (unsigned w = 0; w < writers.size(); ++w)
    {
      std::vector<int> c{v++, -(v++)};
      owner[c[0]] = w;
      writers[w]->learned(c.data(), c.size());
    }
    reader.begin_import(1);
    std::vector<int> c;
    ASSERT_TRUE(reader.next(c) && c.size() == 2);
    ++first[owner.at(std::max(c[0], c[1]))];
    while (reader.next(c))
    {
    }
  }
  ASSERT_EQ(first.size(), 3u);
  for (const auto& [w, n] : first)
    EXPECT_EQ(n, 10u) << "ring of writer " << w;
}

// A stalling writer in another process, max-size clauses, a small ring:
// budgeted polls lap and are lapped, and accept only whole clauses.
TEST(StppComponents, AStalledWriterInAnotherProcessTearsNothing)
{
  stpp::Endpoint::Settings fast;
  fast.rate = 1e12;
  fast.scan_window = 1u << 20; // clamped to the ring
  stpp::Rings shared(2, 512);
  pid_t child = fork();
  ASSERT_TRUE(child >= 0) << "ring writer fork";
  struct Reap
  {
    pid_t& pid;
    ~Reap()
    {
      if (pid > 0)
      {
        kill(pid, SIGKILL);
        waitpid(pid, nullptr, 0);
      }
    }
  } reap{child};
  if (!child)
  {
    auto& w = stpp::RingTestAccess::written(shared, 0);
    auto* d = stpp::RingTestAccess::data(shared, 0);
    const auto cap = shared.capacity();
    unsigned r = 7;
    for (std::uint64_t i = 0; i < 400000; ++i)
    {
      const auto c = stall_clause(i);
      const auto at = w.load(std::memory_order_relaxed);
      std::atomic_thread_fence(std::memory_order_release);
      for (std::size_t j = 0; j < c.size(); ++j)
        stpp::ring_store(&d[(at + j) % cap], c[j]);
      stpp::ring_store(&d[(at + c.size()) % cap], 0);
      r = r * 1103515245u + 12345u;
      if ((r >> 8) % 512 == 0)
        usleep(20); // stalled between the data and the count
      w.store(at + c.size() + 1, std::memory_order_release);
    }
    _exit(0);
  }
  stpp::Endpoint reader(shared, 1, fast);
  std::uint64_t seen = 0;
  std::vector<int> c;
  unsigned r = 11;
  for (const double until = now() + 60; now() < until;)
  {
    int status = 0;
    const bool done = waitpid(child, &status, WNOHANG) == child;
    if (done)
      child = -1;
    reader.begin_import(1u << 20);
    while (reader.next(c))
    {
      ASSERT_TRUE(stall_valid(c)) << "a stalled writer's ring returned a torn clause";
      ++seen;
    }
    if (done)
      break;
    r = r * 1103515245u + 12345u;
    if ((r >> 16) % 4 == 0)
      usleep((r >> 8) % 200); // the reader falls behind
  }
  auto counters = reader.counters();
  ASSERT_TRUE(seen > 0 && counters["lapped"].get<std::uint64_t>() > 0) << "the stalling writer's reader saw nothing or never fell behind";
  std::cout << "stalled writer: reader accepted " << seen << " (lapped "
            << counters["lapped"] << ", torn " << counters["torn"] << ")\n";
}

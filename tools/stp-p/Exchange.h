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

#pragma once
#include "Common.h"
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <vector>

namespace stpp
{
// Learned-clause rings shared by the roots of one batch group. The group's
// owner maps them before it forks anything; every root forked later sees the
// same memory. Each root writes only its own ring and reads every other ring
// with cursors of its own. A ring is lossy: a writer never waits, and a
// reader that falls more than a ring behind skips to what is still there.
// No lock is taken on the data path, and the owner never reads or writes
// clause data.
//
// A clause is its literals followed by a zero; literals are the SAT
// backend's own numbering, identical in every root because every root is
// forked from the same backend at the check's before-search point. The
// literals are plain ints in the zero-filled mapping, read and written with
// the atomic builtins (what std::atomic_ref is made of): an atomic object
// constructed per literal would write, and so commit, every page of every
// ring as soon as the rings are made.
//
// Agreement between roots is no check of soundness: a clause imported torn
// reaches every root through the rings, so all of them can agree on the same
// wrong answer. What keeps imports whole is the overwrite check below.
class Rings
{
public:
  Rings(unsigned slots, std::size_t literals_per_ring);
  ~Rings();
  Rings(const Rings&) = delete;
  Rings& operator=(const Rings&) = delete;
  unsigned slots() const { return count; }
  std::size_t capacity() const { return cap; }
  Json audit() const; // literals written per ring (header reads only)

private:
  friend class Endpoint;
  friend struct RingTestAccess; // the component tests' forced schedules
  struct alignas(64) Header
  {
    std::atomic<std::uint64_t> written; // literals published, monotone
  };
  Header* header(unsigned slot) const;
  int* data(unsigned slot) const;
  void* base = nullptr;
  std::size_t bytes = 0, cap = 0, stride = 0;
  unsigned count = 0;
};
// The rings live in shared memory that other processes access concurrently:
// an atomic that falls back to a lock would put the lock in that memory.
static_assert(std::atomic<std::uint64_t>::is_always_lock_free &&
                  __atomic_always_lock_free(sizeof(int), 0),
              "clause rings need lock-free 64-bit and int atomics");
inline int ring_load(const int* at)
{
  return __atomic_load_n(at, __ATOMIC_RELAXED);
}
inline void ring_store(int* at, int value)
{
  __atomic_store_n(at, value, __ATOMIC_RELAXED);
}

// One root's end of the rings, built in that root after the fork.
class Endpoint final : public stp::ClauseExchange
{
public:
  struct Settings
  {
    std::uint32_t max_size = 8; // longest clause exported
    double rate = 2000;         // non-unit clauses per second, exported
    // A poll scans at most this many of each ring's newest pending literals;
    // anything older is skipped.
    std::size_t scan_window = 1u << 16;
  };
  Endpoint(const Rings&, unsigned slot, const Settings&);
  void learned(const int* literals, std::size_t size) noexcept override;
  // A poll is selected here: every other ring's pending range is scanned
  // (at most scan_window literals each, newest), every cursor moves to the
  // end of what it scanned, and next() then hands over every unit, then the
  // `budget` shortest other clauses (the backend announces its cap) --
  // within a size, round-robin across rings, newest first, starting each
  // poll at the next ring. The rest is discarded. Duplicates are skipped at
  // hand-over and do not use the budget. A poll whose selection runs out of
  // memory imports nothing.
  void begin_import(std::size_t budget) noexcept override;
  bool next(std::vector<int>& literals) noexcept override;
  Json counters() const;

private:
  friend struct RingTestAccess;
  bool fresh(std::vector<int>& literals) noexcept; // dedupe
  void scan();              // a poll's selection
  bool pick(std::uint32_t& at, std::size_t& size) noexcept; // its order
  void end_poll() noexcept; // a poll's leftovers
  const Rings& rings;
  const unsigned slot;
  const Settings settings;
  std::vector<std::uint64_t> cursor; // per ring, in literals
  std::vector<std::uint64_t> seen;   // direct-mapped clause hashes
  std::vector<int> scratch;
  double tokens = 0, refilled = 0;
  // A poll in progress: the scanned clauses' literals, one queue per (size,
  // ring) of offsets into `pool` (newest first), and where the hand-over
  // stands. The queues and their heads are sized once, at construction, so
  // that a poll that fails to allocate can still be emptied.
  bool selecting = false;
  std::size_t budget = 0, taken = 0, size_now = 1, ring_now = 0, ring_first = 0;
  std::vector<int> pool;
  std::vector<std::vector<std::uint32_t>> queues; // [size * slots + ring]
  std::vector<std::size_t> heads;                 // per queue
  struct Found
  {
    std::uint32_t at, size;
    // The oldest ring position the clause depends on: the zero before its
    // first literal, or its first literal when the scan starts at a known
    // clause boundary (the cursor, where the last poll ended).
    std::uint64_t position;
  };
  std::vector<Found> found; // one ring's clauses, oldest first
  std::uint64_t exported = 0, exported_units = 0, exported_binaries = 0,
                rate_limited = 0, oversize = 0, imported = 0,
                imported_units = 0, imported_binaries = 0, duplicates = 0,
                lapped = 0, torn = 0, polls = 0, scanned = 0, skipped = 0,
                discarded = 0;
};
// A root's frozen transport settings, from the options; `import` false
// connects the root for export only.
Endpoint::Settings endpoint_settings(const Options&);
stp::ClauseExchangeSettings exchange_settings(const Options&, bool import);
} // namespace stpp

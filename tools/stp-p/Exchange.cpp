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

#include "Exchange.h"
#include <algorithm>
#include <cerrno>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <limits>
#include <new>
#include <stdexcept>
#include <sys/mman.h>

namespace stpp
{
namespace
{
double coarse_now()
{
  timespec t{};
  clock_gettime(CLOCK_MONOTONIC_COARSE, &t);
  return double(t.tv_sec) + t.tv_nsec / 1e9;
}
std::uint64_t mix(std::uint64_t x)
{
  x += 0x9e3779b97f4a7c15ull;
  x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ull;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebull;
  return x ^ (x >> 31);
}
constexpr std::size_t seen_slots = 1u << 16;
} // namespace

Rings::Rings(unsigned slots, std::size_t literals_per_ring)
    : cap(literals_per_ring), count(slots)
{
  if (!slots || literals_per_ring < 64 || literals_per_ring > (std::size_t(1) << 30))
    throw std::runtime_error("clause rings need slots and capacity");
  stride = sizeof(Header) + cap * sizeof(int);
  stride = (stride + 63) / 64 * 64;
  bytes = stride * slots;
  base = mmap(nullptr, bytes, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS,
              -1, 0);
  if (base == MAP_FAILED)
  {
    const int error = errno;
    base = nullptr;
    throw std::runtime_error("cannot map the clause rings (" +
                             std::to_string(bytes >> 20) + " MiB): " +
                             strerror(error));
  }
  // Anonymous shared memory is zero-filled: every counter and literal is
  // already zero, and a page is committed only when a root writes it. The
  // counters are atomic objects, constructed in place; the literals are
  // plain ints (ring_load, ring_store).
  for (unsigned s = 0; s < slots; ++s)
    new (header(s)) Header{};
}
Rings::~Rings()
{
  if (base)
    munmap(base, bytes);
}
Rings::Header* Rings::header(unsigned s) const
{
  return reinterpret_cast<Header*>(static_cast<char*>(base) + stride * s);
}
int* Rings::data(unsigned s) const
{
  return reinterpret_cast<int*>(static_cast<char*>(base) + stride * s +
                                sizeof(Header));
}
Json Rings::audit() const
{
  Json out = Json::array();
  for (unsigned s = 0; s < count; ++s)
    out.push_back(header(s)->written.load(std::memory_order_acquire));
  return out;
}

Endpoint::Endpoint(const Rings& r, unsigned own, const Settings& s)
    : rings(r), slot(own), settings(s), cursor(r.slots(), 0),
      seen(seen_slots, 0), queues((std::size_t(s.max_size) + 1) * r.slots()),
      heads(queues.size(), 0)
{
  // A root forked after the rings filled starts at their beginning too: its
  // first poll's window takes the newest clauses, as every poll's does.
  if (own >= r.slots())
    throw std::runtime_error("clause ring slot");
  tokens = settings.rate;
  refilled = coarse_now();
}

bool Endpoint::fresh(std::vector<int>& literals) noexcept
{
  std::sort(literals.begin(), literals.end());
  std::uint64_t h = 0x84222325cbf29ce4ull ^ literals.size();
  for (int l : literals)
    h = mix(h ^ std::uint64_t(std::uint32_t(l)));
  h |= 1; // zero marks an empty slot
  auto& entry = seen[h & (seen_slots - 1)];
  if (entry == h)
    return false;
  entry = h;
  return true;
}

void Endpoint::learned(const int* literals, std::size_t size) noexcept
{
  if (!size)
    return;
  if (size > settings.max_size)
  {
    ++oversize;
    return;
  }
  if (size > 1)
  {
    const double t = coarse_now();
    tokens = std::min(settings.rate, tokens + (t - refilled) * settings.rate);
    refilled = t;
    if (tokens < 1)
    {
      ++rate_limited;
      return;
    }
    tokens -= 1;
  }
  try
  {
    scratch.assign(literals, literals + size);
  }
  catch (...)
  {
    return; // out of memory for a copy of at most max_size literals
  }
  if (!fresh(scratch))
    return; // this root already exported or imported it
  auto* h = rings.header(slot);
  auto* d = rings.data(slot);
  const std::size_t cap = rings.capacity();
  const auto w = h->written.load(std::memory_order_relaxed);
  // Pairs with the reader's acquire fence: a reader that sees any literal of
  // this clause also sees the count published before it, which is what its
  // overwrite check compares against.
  std::atomic_thread_fence(std::memory_order_release);
  for (std::size_t i = 0; i < size; ++i)
    ring_store(&d[(w + i) % cap], literals[i]);
  ring_store(&d[(w + size) % cap], 0);
  h->written.store(w + size + 1, std::memory_order_release);
  ++exported;
  exported_units += size == 1;
  exported_binaries += size == 2;
}

bool Endpoint::next(std::vector<int>& out) noexcept
{
  if (!selecting)
    return false;
  std::uint32_t at = 0;
  std::size_t size = 0;
  // Units are all handed over before the first longer clause, and longer
  // clauses only while the budget lasts.
  while (pick(at, size))
  {
    if (size > 1 && taken >= budget)
    {
      ++discarded; // this one, and end_poll the rest
      break;
    }
    try
    {
      out.assign(pool.begin() + at, pool.begin() + at + size);
    }
    catch (...)
    {
      break; // out of memory for at most max_size literals: end the poll
    }
    if (!fresh(out))
    {
      ++duplicates; // not part of the budget
      continue;
    }
    ++imported;
    imported_units += size == 1;
    imported_binaries += size == 2;
    taken += size > 1;
    return true;
  }
  end_poll();
  return false;
}

void Endpoint::begin_import(std::size_t b) noexcept
{
  if (selecting)
    end_poll(); // the backend left the last poll early (a refutation)
  ++polls;
  budget = b;
  selecting = true;
  try
  {
    scan();
  }
  catch (...)
  {
    // Out of memory for the selection: this poll imports nothing. The queues
    // and heads were sized at construction, so emptying them allocates
    // nothing; the cursors already moved stay where they are.
    for (auto& q : queues)
      q.clear();
    std::fill(heads.begin(), heads.end(), std::size_t(0));
    selecting = false;
  }
}

void Endpoint::scan()
{
  const unsigned n = rings.slots();
  const std::size_t cap = rings.capacity();
  // A writer stores one clause (at most max_size literals and its zero)
  // before it publishes the new count, so the slots that far behind the
  // published end may be changing under a reader: they count as gone.
  const std::uint64_t margin = settings.max_size + 1;
  // One literal more than the window is read (the zero before it). The
  // clamp keeps all of it outside the margin when the scan starts; it only
  // saves reading slots the overwrite check below would reject anyway.
  const std::uint64_t window = std::min<std::uint64_t>(
      settings.scan_window, cap > margin + 1 ? cap - margin - 1 : 0);
  for (auto& q : queues)
    q.clear();
  std::fill(heads.begin(), heads.end(), std::size_t(0));
  pool.clear();
  taken = 0;
  size_now = 1;
  // Each poll's hand-over starts at the next of the other rings, so that a
  // binding budget favours none of them (this root's own is always empty).
  ring_first = ring_now = n > 1 ? (slot + 1 + polls % (n - 1)) % n : 0;
  for (unsigned s = 0; s < n; ++s)
  {
    if (s == slot)
      continue;
    auto* h = rings.header(s);
    auto* d = rings.data(s);
    const auto w = h->written.load(std::memory_order_acquire);
    auto& c = cursor[s];
    if (c >= w)
      continue;
    if (w - c + margin > cap)
      ++lapped; // overrun since the last poll; the window skips it anyway
    std::uint64_t start = c;
    bool partial = false; // the first zero ends a clause not ours
    if (w - start > window)
    {
      skipped += w - window - start;
      start = w - window;
      partial = true;
    }
    // Every clause depends on the ring from the zero before it (which marks
    // its start) to its own zero; `position` is the oldest of those slots.
    std::uint64_t position = start;
    if (partial && start && !ring_load(&d[(start - 1) % cap]))
    {
      partial = false; // the window starts a clause
      position = start - 1;
    }
    found.clear();
    std::size_t at = pool.size();
    for (std::uint64_t p = start; p < w;)
    {
      const int v = ring_load(&d[p % cap]);
      ++p;
      if (v)
      {
        pool.push_back(v);
        continue;
      }
      const std::size_t size = pool.size() - at;
      const bool whole = !partial && size && size <= settings.max_size;
      torn += !partial && !whole;
      partial = false;
      if (whole)
        found.push_back({std::uint32_t(at), std::uint32_t(size), position});
      else
        pool.resize(at);
      at = pool.size();
      // The zero just read marks where the next clause starts: that clause
      // depends on it, so it is the next clause's oldest position.
      position = p - 1;
    }
    pool.resize(at); // the published end is a clause end: nothing is left
    // The writer may have lapped this reader while it read: a clause whose
    // oldest slot is within a ring (and the margin) of the count now
    // published may have been overwritten, its start or its end.
    std::atomic_thread_fence(std::memory_order_acquire);
    const auto after = h->written.load(std::memory_order_relaxed);
    for (auto i = found.size(); i-- > 0;) // newest first within a size
    {
      if (after + margin > found[i].position + cap)
      {
        ++torn;
        continue;
      }
      ++scanned;
      queues[found[i].size * n + s].push_back(found[i].at);
    }
    c = w;
  }
}

bool Endpoint::pick(std::uint32_t& at, std::size_t& size) noexcept
{
  // By size; within a size one clause from each ring in turn.
  const unsigned n = rings.slots();
  while (size_now <= settings.max_size)
  {
    for (unsigned tried = 0; tried < n; ++tried)
    {
      const std::size_t k = size_now * n + ring_now;
      ring_now = (ring_now + 1) % n;
      if (heads[k] < queues[k].size())
      {
        at = queues[k][heads[k]++];
        size = size_now;
        return true;
      }
    }
    ++size_now;
    ring_now = ring_first;
  }
  return false;
}

void Endpoint::end_poll() noexcept
{
  for (std::size_t k = 0; k < queues.size(); ++k)
  {
    discarded += queues[k].size() - heads[k];
    heads[k] = queues[k].size();
  }
  selecting = false;
}

Endpoint::Settings endpoint_settings(const Options& o)
{
  Endpoint::Settings settings;
  settings.max_size = o.exchange_size;
  settings.rate = o.exchange_rate;
  settings.scan_window = o.import_window;
  return settings;
}
stp::ClauseExchangeSettings exchange_settings(const Options& o, bool import)
{
  stp::ClauseExchangeSettings exchange;
  exchange.max_size = o.exchange_size;
  exchange.import_interval = o.exchange_interval;
  // b per own conflict: a poll comes every import interval of conflicts.
  exchange.import_budget = std::uint32_t(std::min<std::uint64_t>(
      std::uint64_t(o.import_budget) * o.exchange_interval, 1u << 30));
  exchange.import = import;
  return exchange;
}

Json Endpoint::counters() const
{
  return {{"slot", slot},
          {"exported", exported},
          {"exported_units", exported_units},
          {"exported_binaries", exported_binaries},
          {"rate_limited", rate_limited},
          {"oversize", oversize},
          {"imported", imported},
          {"imported_units", imported_units},
          {"imported_binaries", imported_binaries},
          {"duplicates", duplicates},
          {"lapped", lapped},
          {"torn", torn},
          {"polls", polls},
          {"scanned", scanned},
          {"skipped_literals", skipped},
          {"discarded", discarded}};
}
} // namespace stpp

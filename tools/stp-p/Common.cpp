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

#include "Common.h"
#include "Portfolio.h"
#include <algorithm>
#include <cerrno>
#include <fstream>
#include <limits>
#include <poll.h>
#include <sched.h>
#include <signal.h>
#include <stdexcept>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <unistd.h>

// The allocator's own release, where one is linked: mimalloc's when stp-p
// runs on it, else glibc's. Weak, so that neither is required.
extern "C" void mi_collect(bool force) __attribute__((weak));
extern "C" int malloc_trim(std::size_t pad) __attribute__((weak));

namespace stpp
{
double now()
{
  return std::chrono::duration<double>(
             std::chrono::steady_clock::now().time_since_epoch())
      .count();
}
stp::Options solver_options(const Options& o, bool retained)
{
  stp::Options result;
  result.set_bool("produce-models", false);
  result.set_bool("lra-verify-canonical", false);
  const auto& c = config(o.config);
  if (o.seed || c.seed_offset)
    result.set_uint("random-seed",
                    std::uint32_t(o.seed.value_or(0) + c.seed_offset));
  if (retained)
  {
    // The hedge: the incremental driver from the first check, on CaDiCaL,
    // which its configuration was chosen for; a build without CaDiCaL keeps
    // its own default.
    result.set("incremental", "on");
    if (stp::has_sat_backend("cadical"))
      result.set("sat-backend", "cadical");
  }
  else
    for (const auto& [name, value] : c.options)
      result.set(name, value);
  return result;
}
void memory_limit(std::uint64_t mib)
{
  if (!mib)
    return;
  if (mib > std::numeric_limits<rlim_t>::max() / (1024 * 1024))
    throw std::runtime_error("worker memory limit overflow");
  rlimit lim{};
  if (getrlimit(RLIMIT_AS, &lim))
    throw std::runtime_error("getrlimit failed");
  lim.rlim_cur = std::min(lim.rlim_cur, static_cast<rlim_t>(mib * 1024 * 1024));
  if (setrlimit(RLIMIT_AS, &lim))
    throw std::runtime_error("setrlimit failed");
}
void parent_death(int expected_parent)
{
  if (prctl(PR_SET_PDEATHSIG, SIGKILL) || getppid() != expected_parent)
    _exit(2);
}
namespace
{
std::vector<std::string> injections(const Options& o)
{
  std::vector<std::string> out;
  for (std::size_t at = 0; !o.inject.empty() && at <= o.inject.size();)
  {
    auto comma = o.inject.find(',', at);
    if (comma == std::string::npos)
      comma = o.inject.size();
    out.push_back(o.inject.substr(at, comma - at));
    at = comma + 1;
  }
  return out;
}
} // namespace
bool injected(const Options& o, const std::string& kind)
{
  for (const auto& item : injections(o))
    if (item == kind)
      return true;
  return false;
}
bool injected_hold(const Options& o, unsigned slot)
{
  return injected(o, "hold-root=" + std::to_string(slot));
}
std::string injected_answer(const Options& o, unsigned slot)
{
  const std::string prefix = "wrong-root=" + std::to_string(slot) + ":";
  for (const auto& item : injections(o))
    if (item.rfind(prefix, 0) == 0)
      return item.substr(prefix.size());
  return "";
}
std::vector<int> allowed_cpus()
{
  // A set sized for the CPUs the system is configured with, and larger
  // while the kernel's own mask does not fit it.
  for (long n = std::max(sysconf(_SC_NPROCESSORS_CONF), 1024L);; n *= 2)
  {
    cpu_set_t* set = CPU_ALLOC(n);
    if (!set)
      throw std::runtime_error("cannot discover allowed CPUs");
    const std::size_t bytes = CPU_ALLOC_SIZE(n);
    CPU_ZERO_S(bytes, set);
    if (sched_getaffinity(0, bytes, set))
    {
      const int error = errno;
      CPU_FREE(set);
      if (error == EINVAL && n < (1L << 20))
        continue;
      throw std::runtime_error("cannot discover allowed CPUs");
    }
    std::vector<int> cpus;
    for (long cpu = 0; cpu < n; ++cpu)
      if (CPU_ISSET_S(cpu, bytes, set))
        cpus.push_back(int(cpu));
    CPU_FREE(set);
    return cpus;
  }
}
unsigned default_jobs()
{
  if (stp::capabilities()["sat.clause-exchange"] != "true")
    return 1;
  return unsigned(std::min<std::size_t>(allowed_cpus().size(), 8));
}
std::uint64_t own_rss()
{
  std::ifstream statm("/proc/self/statm");
  std::uint64_t total = 0, resident = 0;
  if (!(statm >> total >> resident))
    return 0;
  return resident * static_cast<std::uint64_t>(sysconf(_SC_PAGESIZE));
}
std::uint64_t peak_rss()
{
  std::ifstream status("/proc/self/status");
  std::string key;
  std::uint64_t kib = 0;
  while (status >> key)
  {
    if (key == "VmHWM:" && status >> kib)
      return kib * 1024;
    status.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
  }
  return 0;
}
bool memory_rollup(int pid, std::uint64_t& rss_kib, std::uint64_t& pss_kib)
{
  std::ifstream in("/proc/" + std::to_string(pid) + "/smaps_rollup");
  if (!in)
    return false;
  std::string key;
  std::uint64_t value = 0;
  bool rss = false, pss = false;
  while (in >> key)
  {
    if (key == "Rss:" && in >> value)
      rss_kib = value, rss = true;
    else if (key == "Pss:" && in >> value)
      pss_kib = value, pss = true;
    in.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
  }
  return rss && pss;
}
void write_bounded(int fd, const std::string& text, double deadline)
{
  std::size_t at = 0;
  while (at < text.size())
  {
    if (deadline && now() >= deadline)
      throw std::runtime_error("publication deadline");
    const auto n = write(fd, text.data() + at, text.size() - at);
    if (n > 0)
    {
      at += static_cast<std::size_t>(n);
      continue;
    }
    if (n < 0 && errno == EINTR)
      continue;
    if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK))
    {
      pollfd p{fd, POLLOUT, 0};
      poll(&p, 1, 10);
      continue;
    }
    throw std::runtime_error("output channel failed");
  }
}
std::vector<Json> Channel::take(const char* data, std::size_t size,
                                std::size_t limit)
{
  std::vector<Json> completed;
  if (overflow)
    return completed;
  bytes += size;
  if (bytes > limit)
  {
    overflow = true;
    pending.clear();
    return completed;
  }
  pending.append(data, size);
  std::size_t from = 0;
  for (std::size_t nl; (nl = pending.find('\n', from)) != std::string::npos;
       from = nl + 1)
  {
    std::string line = pending.substr(from, nl - from);
    Json record;
    try
    {
      record = Json::parse(line);
    }
    catch (...)
    {
      record = nullptr;
    }
    if (record.is_object() && record.size() == 1 && record.contains("note"))
    {
      evidence.push_back(record["note"]);
      completed.push_back(record["note"]);
    }
    else
    {
      malformed = malformed || !record.is_object();
      report = std::move(line);
    }
  }
  pending.erase(0, from);
  return completed;
}
void Channel::end()
{
  if (!pending.empty() && !overflow)
  {
    report = std::move(pending);
    cut = true;
  }
  pending.clear();
}
std::string evidence_answer(const Json& j)
{
  if (!j.is_object() || j.contains("error"))
    return "";
  const auto found = j.find("answer");
  if (found == j.end() || !found->is_string())
    return "";
  const auto a = found->get<std::string>();
  return a == "sat" || a == "unsat" ? a : "";
}
void release_memory()
{
  if (mi_collect)
    mi_collect(true);
  else if (malloc_trim)
    malloc_trim(0);
}
} // namespace stpp

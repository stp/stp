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
#include "Exchange.h"
#include "Source.h"
#include "Portfolio.h"
#include <cerrno>
#include <cstring>
#include <dirent.h>
#include <fcntl.h>
#include <memory>
#include <poll.h>
#include <sched.h>
#include <signal.h>
#include <stdexcept>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

namespace stpp
{
namespace
{
// Everything but stderr and `keep`: a root holds no other root's channel, so
// a killed root cannot keep a pipe it inherited open.
void close_except(int keep)
{
  DIR* dir = opendir("/proc/self/fd");
  if (!dir)
    _exit(2);
  std::vector<int> descriptors;
  while (auto* entry = readdir(dir))
  {
    char* end = nullptr;
    auto n = strtol(entry->d_name, &end, 10);
    if (*entry->d_name && !*end && n != 2 && n != keep && n != dirfd(dir))
      descriptors.push_back(int(n));
  }
  closedir(dir);
  for (int fd : descriptors)
    close(fd);
}
double cpu_seconds(const rusage& u)
{
  return u.ru_utime.tv_sec + u.ru_utime.tv_usec / 1e6 + u.ru_stime.tv_sec +
         u.ru_stime.tv_usec / 1e6;
}
// The reason the owner's check gives when its roots took the search over.
const char* const handoff =
    "handed to the batch group: the owner does not search";
// The frozen diversification table of the roots: root 0 is the backend's own
// search; root i > 0 takes the base seed plus i and something only that seed
// decides -- pseudo-random saved phases for odd i, a shuffled decision order
// for even i (whose phases are false for i = 2 mod 4) -- so no two roots
// repeat one search; and focused-only search for i = 1 mod 3, stable-only
// for i = 2 mod 3. The same table for every input. CaDiCaL's seed is in
// 0..2e9.
stp::SearchDiversification root_diversity(unsigned i, std::uint64_t seed)
{
  stp::SearchDiversification d;
  d.seed = std::int32_t((seed + i) % 2000000000u);
  d.phase = i % 2 ? 0 : i % 4 == 2 ? -1 : 2;
  d.shuffle = i && i % 2 == 0;
  d.mode = i % 3 == 1 ? 1 : i % 3 == 2 ? 2 : 0;
  return d;
}
std::string answer_text(const stp::Result& r)
{
  return r.is_sat() ? "sat" : r.is_unsat() ? "unsat" : "unknown";
}
// A root writes one report (its answer, or its error) and exits.
[[noreturn]] void root_exit(int fd, const Json& report)
{
  try
  {
    write_bounded(fd, dump(report) + "\n", now() + 1);
  }
  catch (...)
  {
  }
  _exit(report.contains("error") ? 2 : 0);
}
} // namespace

// One forked process of the group, as its owner sees it: a root, or the
// hedge.
struct Root
{
  pid_t pid = -1;
  int fd = -1;
  unsigned slot = 0;
  bool hedge = false;
  double forked_at = 0, ended_at = 0;
  Channel channel;
  bool eof = false, reaped = false, killed = false, noted = false;
  int status = 0;
  rusage usage{};
};
namespace
{
Json root_report(const Root& c)
{
  if (c.channel.overflow || c.channel.report.empty())
    return nullptr;
  try
  {
    return Json::parse(c.channel.report);
  }
  catch (...)
  {
    return nullptr;
  }
}
// Who a record is about: {"root": slot} or {"hedge": true}.
Json who(const Root& c)
{
  return c.hedge ? Json{{"hedge", true}} : Json{{"root", c.slot}};
}
std::string name(const Root& c)
{
  return c.hedge ? "hedge" : "root " + std::to_string(c.slot);
}
// A complete report: its answer, whatever became of the process after it
// wrote it (a report is one line, so what parses is whole). Evidence for the
// comparison.
std::string reported(const Root& c)
{
  const auto a = evidence_answer(root_report(c));
  return a.empty() ? "unknown" : a;
}
// A decision: a complete report from a process that exited normally.
std::string decided(const Root& c)
{
  if (!c.eof || !c.reaped || !WIFEXITED(c.status) || WEXITSTATUS(c.status))
    return "unknown";
  return reported(c);
}
// How a process that ended without an answer ended: its error, or its
// signal or exit status; "" when it ended with a report of its own.
std::string failure(const Root& c)
{
  const Json r = root_report(c);
  if (r.is_object() && r.contains("error"))
    return r["error"].is_string() ? r["error"].get<std::string>() : "error";
  if (WIFEXITED(c.status) && !WEXITSTATUS(c.status) && r.is_object())
    return "";
  return WIFSIGNALED(c.status) ? "signal " + std::to_string(WTERMSIG(c.status))
                               : "exit " + std::to_string(WEXITSTATUS(c.status));
}
// Reads what a process wrote and reaps it if it has ended. The first time
// its report is complete, or it ends without one, the parent hears of it
// (Options::note): evidence that outlives this process if it is killed.
void observe(Root& c, const Options& o)
{
  if (!c.eof)
  {
    char raw[16384];
    for (;;)
    {
      auto n = read(c.fd, raw, sizeof raw);
      if (n > 0)
      {
        c.channel.take(raw, std::size_t(n));
        if (c.channel.overflow)
        {
          kill(c.pid, SIGKILL);
          c.killed = true;
          c.eof = true;
          break;
        }
        continue;
      }
      if (!n)
      {
        c.eof = true;
        c.ended_at = now();
        c.channel.end();
      }
      else if (errno == EINTR)
        continue;
      break;
    }
  }
  if (!c.reaped && wait4(c.pid, &c.status, WNOHANG, &c.usage) == c.pid)
    c.reaped = true;
  if (c.noted || !o.note)
    return;
  const auto a = reported(c);
  if (a != "unknown")
  {
    c.noted = true;
    Json n = who(c);
    n["answer"] = a;
    n["report"] = root_report(c);
    o.note(n);
  }
  else if (c.eof && c.reaped && !c.killed)
  {
    c.noted = true;
    const auto f = failure(c);
    Json n = who(c);
    if (f.empty())
      n["ended"] = root_report(c).value("reason", std::string("unknown"));
    else
      n["failed"] = f;
    o.note(n);
  }
}
Json row(const Root& c)
{
  Json r = {{"role", c.hedge ? "hedge" : "root"},
            {"pid", c.pid},
            {"answer", decided(c)},
            {"reported", reported(c)},
            {"wait_status", c.status},
            {"signal", WIFSIGNALED(c.status) ? WTERMSIG(c.status) : 0},
            {"killed", c.killed},
            {"cpu_s", cpu_seconds(c.usage)},
            {"max_rss_kib", c.usage.ru_maxrss},
            {"wall_s", c.ended_at > 0 ? c.ended_at - c.forked_at : -1.0},
            {"report", root_report(c)}};
  if (!c.hedge)
    r["slot"] = c.slot;
  return r;
}
Json root_rows(const std::vector<Root>& children)
{
  Json out = Json::array();
  for (const auto& c : children)
    if (!c.hedge)
      out.push_back(row(c));
  return out;
}
Json rows(const std::vector<Root>& children)
{
  Json out = Json::array();
  for (const auto& c : children)
    out.push_back(row(c));
  return out;
}
bool disagree(const std::vector<Root>& children, std::string first = "")
{
  for (const auto& c : children)
  {
    const auto a = reported(c);
    if (a == "unknown")
      continue;
    if (first.empty())
      first = a;
    else if (a != first)
      return true;
  }
  return false;
}
void kill_all(std::vector<Root>& children)
{
  for (auto& c : children)
    if (!c.reaped)
    {
      kill(c.pid, SIGKILL);
      c.killed = true;
    }
}
void reap_all(std::vector<Root>& children)
{
  for (auto& c : children)
    while (!c.reaped)
    {
      if (wait4(c.pid, &c.status, 0, &c.usage) == c.pid)
        c.reaped = true;
      else if (errno != EINTR)
        break;
    }
}
const char* const disagreement = "complete answers in the group disagree";
// The owner's check stops at the deadline, and when the hedge decides first
// (its pipe is read at most every 10 ms). Polled by the library: it must not
// throw.
struct Watch final : stp::Terminator
{
  double end;
  Root* hedge;
  const Options& o;
  double next = 0;
  bool answered = false;
  Watch(double e, Root* h, const Options& options) : end(e), hedge(h), o(options) {}
  bool terminate() override
  {
    if (end && now() >= end)
      return true;
    if (!hedge || answered)
      return answered;
    const double t = now();
    if (t < next)
      return false;
    next = t + .01;
    try
    {
      observe(*hedge, o);
      answered = decided(*hedge) != "unknown";
    }
    catch (...)
    {
    }
    return answered;
  }
};
} // namespace
// The group's end: every process killed and reaped, its pipe drained to its
// end -- a report complete before the kill still counts -- and every
// complete report compared, with the owner's own answer when it has one
// (`owner`): two that disagree end the whole invocation.
void settle(std::vector<Root>& children, const Options& o,
            const std::string& owner = "")
{
  kill_all(children);
  reap_all(children);
  for (auto& c : children)
    observe(c, o);
  if (disagree(children, owner))
    throw Failure(disagreement, {{"engine", "batch-group"},
                                 {"owner_answer", owner},
                                 {"children", rows(children)}});
}

// The batch group: N batch roots over ordinary STP's own CNF, beside the
// hedge. The owner parses the query once. On QF_BV it then forks the hedge
// -- its own solver, the incremental driver, over the same terms -- and
// checks the query as ordinary STP does; at the before-search point (the
// CNF in its SAT backend, nothing searched) it forks one root per slot, and
// every root holds the loaded backend. Root 0 is ordinary STP itself (on
// CaDiCaL); root i > 0 is diversified by the frozen table; with sharing (two
// roots or more) every root is joined to the clause rings, mapped before the
// first fork. The owner's own check is then abandoned with the hand-off
// reason: it never searches, and it drops its solver while the roots search.
// On any other logic there is no hedge, and the roots take its CPU.
//
// A check that cannot offer the point (it may refine after its first solve:
// lazy array axioms with symbolic reads, uninterpreted functions, an
// abstraction) is searched in place by the owner, once, as -j1 searches it
// (NoSearchPoint::search); the library says why, and the report does. So
// does a check whose roots could not be forked, and a group whose rings
// cannot be mapped runs its roots without sharing. A check that
// preprocessing decides answers without ever reaching the point.
//
// Test controls (only stpp-drive takes them): batch-handoff forks no
// root at all, so the owner's own hand-off is the published answer
// (unknown); batch-all lets every root run to its own answer instead of
// stopping at the first.
//
// A root's answer is the query's: its database is the batch CNF plus clauses
// implied by it, and it assumed nothing. The first complete answer from a
// root or the hedge that exited normally wins (or the owner's, when it
// searched or preprocessing decided); the rest are killed and reaped. Every
// complete report read before or after the kill is compared, and passed on
// to the parent as it arrives: two that disagree end the whole invocation.
// That is a check against a defect, not the soundness argument -- a torn
// import reaches every root through the rings, so roots can agree on the
// same wrong answer. A root, or the hedge, that ends unknown before the
// deadline has answered unknown, with the library's reason; only a death or
// a failed setup is a failure.
Json batch_group(Source& input, const Options& o)
{
  const double started = now();
  auto tm = std::make_unique<stp::TermManager>();
  // The roots exchange clauses through CaDiCaL's clause-import extension, so
  // the group runs on CaDiCaL even in a build whose default is another
  // backend; where CaDiCaL is the default this changes nothing.
  stp::Options options = solver_options(o);
  if (!options.is_set("sat-backend"))
    options.set("sat-backend", "cadical");
  auto solver = std::make_unique<stp::Solver>(*tm, options);
  const std::string logic = parse_query(*solver, input);
  admit_logic(logic, true);
  release_memory();
  const double parsed = now();
  {
    // The owner forks the hedge here and its roots inside the check: it must
    // be single-threaded.
    DIR* dir = opendir("/proc/self/task");
    if (!dir)
      throw std::runtime_error("owner thread check");
    unsigned threads = 0;
    while (auto* entry = readdir(dir))
      if (entry->d_name[0] != '.')
        ++threads;
    closedir(dir);
    if (threads != 1)
      throw std::runtime_error("batch group owner is not single-threaded");
  }
  // Placement is the scheduler's, within the allowed CPUs; the test driver's
  // --pin binds root i to the i-th allowed CPU and the hedge to the last
  // of the group's.
  std::vector<int> cpus;
  if (o.pin)
    cpus = allowed_cpus();
  const pid_t owner = getpid();
  std::vector<Root> children;
  // The hedge, and the roots after it: never reallocated, so that the
  // owner's check can watch the hedge while the hook forks the roots.
  children.reserve(std::size_t(o.roots) + 2);
  const bool hedge_wanted = o.hedge != "none" && o.control.empty();
  Json hedge = nullptr; // why there is none
  if (hedge_wanted && !hedge_logic(logic))
    hedge = {{"forked", false},
             {"reason", "the hedge takes QF_BV only, and the script names " +
                            (logic.empty() ? std::string("no logic") : logic)}};
  else if (hedge_wanted)
  {
    // The hedge: forked once the parse has read the logic, before the check.
    // It asserts the parsed terms in a solver of its own over the same
    // manager, shared copy-on-write: nothing is parsed twice.
    const auto assertions = solver->assertions();
    int channel[2];
    const pid_t pid = pipe2(channel, O_CLOEXEC | O_NONBLOCK) ? -1
                      : injected(o, "fork-fails")          ? (errno = EAGAIN, -1)
                                                            : fork();
    if (pid < 0)
    {
      hedge = {{"forked", false}, {"reason", std::string("fork: ") + strerror(errno)}};
      close(channel[0]);
      close(channel[1]);
    }
    else if (!pid)
    {
      const int fd = channel[1];
      try
      {
        parent_death(owner);
        signal(SIGINT, SIG_DFL);
        signal(SIGTERM, SIG_DFL);
        close_except(fd);
        prctl(PR_SET_NAME, "stp-p hedge");
        if (o.pin)
        {
          cpu_set_t affinity;
          CPU_ZERO(&affinity);
          CPU_SET(cpus.at(o.jobs - 1), &affinity);
          if (sched_setaffinity(0, sizeof affinity, &affinity))
            throw std::runtime_error("hedge affinity");
        }
        if (injected(o, "hold-hedge"))
        {
          // A test fault: the hedge starts 30 s late, so that the roots
          // answer (or fail) first.
          const double until = now() + 30;
          while (now() < until && !(o.deadline && now() >= o.deadline))
            poll(nullptr, 0, 10);
        }
        stp::Solver own(*tm, solver_options(o, true));
        for (const auto& t : assertions)
          own.assert_formula(t);
        root_exit(fd, hedge_check(own, o, logic));
      }
      catch (const std::exception& e)
      {
        root_exit(fd, {{"error", std::string("hedge: ") + e.what()}});
      }
      catch (...)
      {
        _exit(2);
      }
    }
    else
    {
      close(channel[1]);
      Root h;
      h.pid = pid;
      h.fd = channel[0];
      h.hedge = true;
      h.forked_at = now();
      children.push_back(std::move(h));
    }
  }
  const bool hedged = !children.empty();
  // Without the hedge, the roots take its CPU.
  const unsigned roots = o.control == "batch-handoff" ? 0
                         : o.roots + (hedge_wanted && !hedged ? 1 : 0);
  if (o.pin && roots > cpus.size())
    throw std::runtime_error("CPU capacity changed");
  // The rings serve an exchange: between two roots or more. Rings that
  // cannot be mapped (a small address-space limit) leave the roots
  // independent.
  std::unique_ptr<Rings> rings;
  std::string unshared;
  if (roots >= 2 && o.sharing)
  {
    try
    {
      rings = std::make_unique<Rings>(roots, o.ring_literals);
    }
    catch (const std::exception& e)
    {
      unshared = e.what();
    }
  }
  const std::uint64_t seed = o.seed.value_or(0) + config(o.config).seed_offset;

  Json fork_errors = Json::array();
  // -1 in the owner; a root's slot in that root, from its fork on.
  int role = -1;
  int report_fd = -1;
  bool hook_ran = false;
  double fork_point = 0, forks_done = 0;
  std::uint64_t variables = 0;
  std::unique_ptr<Endpoint> endpoint;
  Json joined;
  Watch watch(o.deadline, hedged ? &children.front() : nullptr, o);
  auto forked_roots = [&] { return children.size() - (hedged ? 1 : 0); };

  solver->set_before_search(
      [&](stp::SearchPoint& point)
      {
        hook_ran = true;
        fork_point = now();
        variables = point.variables();
        for (unsigned slot = 0; slot < roots; ++slot)
        {
          int channel[2];
          if (pipe2(channel, O_CLOEXEC | O_NONBLOCK))
          {
            fork_errors.push_back({{"slot", slot}, {"pipe", strerror(errno)}});
            break; // fewer roots
          }
          const double forked_at = now();
          const pid_t pid = injected(o, "fork-fails") ? (errno = EAGAIN, -1)
                                                      : fork();
          if (pid < 0)
          {
            fork_errors.push_back({{"slot", slot}, {"fork", strerror(errno)}});
            close(channel[0]);
            close(channel[1]);
            break;
          }
          if (!pid)
          {
            // A root. From here on this process only searches and reports;
            // one whose setup fails is a failed root, never a search.
            role = int(slot);
            report_fd = channel[1];
            watch.hedge = nullptr; // the owner's, not this root's
            try
            {
              parent_death(owner);
              signal(SIGINT, SIG_DFL);
              signal(SIGTERM, SIG_DFL);
              close_except(report_fd);
              prctl(PR_SET_NAME, "stp-p root");
              joined = {{"slot", slot}};
              if (injected(o, "fail-root-setup"))
                throw std::runtime_error("injected");
              if (o.pin)
              {
                cpu_set_t affinity;
                CPU_ZERO(&affinity);
                CPU_SET(cpus[slot], &affinity);
                if (sched_setaffinity(0, sizeof affinity, &affinity))
                  throw std::runtime_error("root affinity");
                joined["cpu"] = cpus[slot];
              }
              const auto wrong = injected_answer(o, slot);
              if (!wrong.empty())
              {
                // A test fault: this root reports a fixed answer at once and
                // then waits to be killed, as an unsound root would.
                try
                {
                  write_bounded(report_fd,
                                dump(Json{{"answer", wrong},
                                          {"reason", "injected"},
                                          {"joined", joined}}) +
                                    "\n",
                                0);
                }
                catch (...)
                {
                }
                for (;;)
                  pause();
              }
              if (slot)
              {
                const auto d = root_diversity(slot, seed);
                joined["diversified"] = point.diversify(d);
                joined["seed"] = d.seed;
                joined["phase"] = d.phase;
                joined["shuffle"] = d.shuffle;
                joined["mode"] = d.mode;
              }
              if (rings)
              {
                // Root 0 is ordinary STP itself (on CaDiCaL); without
                // root0_import it exports only, and its search is ordinary
                // STP's.
                const bool import = slot || o.root0_import;
                endpoint = std::make_unique<Endpoint>(*rings, slot,
                                                      endpoint_settings(o));
                joined["exchange"] = point.connect_clause_exchange(
                    endpoint.get(), exchange_settings(o, import));
                joined["imports"] = import;
              }
              if (injected_hold(o, slot))
              {
                // A test fault: this root starts its search 30 s late.
                const double until = now() + 30;
                while (now() < until && !(o.deadline && now() >= o.deadline))
                  poll(nullptr, 0, 10);
              }
            }
            catch (const std::exception& e)
            {
              root_exit(report_fd,
                        {{"error", std::string("root setup failed: ") + e.what()}});
            }
            return true;
          }
          close(channel[1]);
          Root c;
          c.pid = pid;
          c.fd = channel[0];
          c.slot = slot;
          c.forked_at = forked_at;
          children.push_back(std::move(c));
        }
        // Each fork copies the loaded solver's page tables, serially here.
        forks_done = now();
        // With no root to hand it to, the owner searches itself.
        return roots > 0 && forked_roots() == 0;
      },
      handoff, stp::NoSearchPoint::search);

  solver->set_terminator(&watch);
  const double check_started = now();
  stp::Result result;
  std::string check_error;
  try
  {
    result = solver->check_sat();
  }
  catch (const std::exception& e)
  {
    if (role >= 0)
      root_exit(report_fd, {{"error", e.what()}}); // its check failed
    check_error = e.what();
  }

  if (role >= 0)
  {
    // A root: report, and leave without touching anything of the owner's.
    // An unknown is an answer too, with the library's reason.
    try
    {
      solver->set_terminator(nullptr);
      auto stats = solver->statistics();
      Json data = {{"answer", answer_text(result)},
                   {"reason", result.reason_message()},
                   {"check_s", now() - check_started},
                   {"sat_s", stats.real("time.sat_ms") / 1000.0},
                   {"joined", joined}};
      if (endpoint)
      {
        auto x = endpoint->counters();
        for (const char* key : {"exported", "filtered", "polls", "imported",
                                "import-units", "import-dropped",
                                "import-satisfied", "import-backtracks"})
          x[std::string("backend_") + key] =
              stats.uint64(std::string("sat.exchange.") + key);
        data["exchange"] = x;
      }
      root_exit(report_fd, data);
    }
    catch (const std::exception& e)
    {
      root_exit(report_fd, {{"error", e.what()}});
    }
  }

  // The owner.
  solver->set_terminator(nullptr);
  Json owner_check = {{"answer", answer_text(result)},
                      {"reason", result.reason_message()},
                      {"error", check_error},
                      {"hook_ran", hook_ran}};
  std::string outcome, refusal;
  std::uint64_t owner_checks = 0;
  if (check_error.empty())
  {
    auto stats = solver->statistics();
    outcome = stats.str("before-search.outcome");
    refusal = stats.str("before-search.refusal");
    owner_checks = stats.uint64("checks.total");
    owner_check["outcome"] = outcome;
  }
  const std::size_t handed = forked_roots();
  if (hook_ran && handed &&
      (!result.is_unknown() ||
       result.reason_message().find(handoff) == std::string::npos))
  {
    // The library answered a check whose search it had handed over: a
    // broken contract, which no other answer may cover.
    try
    {
      settle(children, o);
    }
    catch (const Failure&)
    {
    }
    throw Failure("batch group owner's check did not hand off", owner_check);
  }
  // The owner's check searched in place: the point could not be offered, or
  // no root could be forked. Its answer is -j1's.
  const bool searched = outcome == "refused" || (hook_ran && !handed && roots);
  // The owner's copy of the query goes: the roots and the hedge hold their
  // own. Its resident and proportional sizes before and after say what that
  // saved.
  std::uint64_t rss_kib = 0, pss_kib = 0, rss_after_kib = 0, pss_after_kib = 0;
  memory_rollup(getpid(), rss_kib, pss_kib);
  solver.reset();
  tm.reset();
  release_memory();
  memory_rollup(getpid(), rss_after_kib, pss_after_kib);

  std::string decision = "unknown", decided_by;
  double decision_at = 0;
  int winner_slot = -1;
  auto record = [&](const std::string& answer, const std::string& by)
  {
    decision = answer;
    decided_by = by;
    decision_at = now();
    // Passed on before the group settles: a stop that comes during the
    // teardown still finds the answer.
    if (o.note)
      o.note({{"decided", answer}, {"by", by}});
  };
  if (check_error.empty() && !result.is_unknown())
    record(answer_text(result), "owner");
  bool ended = false; // every process ended on its own, before the deadline
  if (decision == "unknown")
  {
    for (;;)
    {
      std::vector<pollfd> fds;
      for (auto& c : children)
        if (!c.eof)
          fds.push_back({c.fd, POLLIN, 0});
      if (!fds.empty())
        poll(fds.data(), fds.size(), 2);
      bool all_done = true;
      for (auto& c : children)
      {
        observe(c, o);
        all_done = all_done && c.eof && c.reaped;
      }
      if (disagree(children))
      {
        settle(children, o);
        throw Failure(disagreement, {{"engine", "batch-group"},
                                     {"children", rows(children)}});
      }
      for (auto& c : children)
      {
        const auto a = decided(c);
        if (a != "unknown" && decision == "unknown")
        {
          record(a, name(c));
          winner_slot = c.hedge ? -1 : int(c.slot);
        }
      }
      if (all_done)
        ended = true;
      // The test control batch-all lets every root reach its own answer (the
      // fork-in-hook test checks each against an oracle).
      if ((decision != "unknown" && o.control != "batch-all") || all_done)
        break;
      if (o.deadline && now() >= o.deadline)
        break;
      if (!fds.empty())
        continue;
      poll(nullptr, 0, 2);
    }
  }
  // A decision found before the deadline stands, whenever it is published.
  settle(children, o, decided_by == "owner" ? decision : "");
  std::string reason;
  if (decision == "unknown")
  {
    if (!check_error.empty() && (!hedged || ended))
      throw std::runtime_error("batch group owner's check failed: " + check_error);
    // Every process that searched ended before the deadline without an
    // answer. Each that ended with a report of its own answered unknown,
    // with the library's reason; when none did -- each died, or failed its
    // setup -- the group failed, as -j1 fails when its process does.
    std::string why;
    bool failed = ended && (handed || hedged) && !searched;
    for (const auto& c : children)
    {
      const auto f = failure(c);
      if (f.empty())
      {
        failed = false;
        if (reason.empty())
          reason = root_report(c).value("reason", std::string());
      }
      why += (why.empty() ? "" : "; ") + name(c) + ": " +
             (f.empty() ? std::string("unknown") : f);
    }
    if (failed)
      throw std::runtime_error("every batch root failed (" + why + ")");
    if (reason.empty())
      reason = searched || !hook_ran ? owner_check["reason"].get<std::string>()
                                     : "no complete decision";
  }
  for (auto& c : children)
    close(c.fd);
  Json hedge_row = hedged ? row(children.front()) : hedge;
  if (hedged)
    hedge_row["forked"] = true;
  Json report = {{"answer", decision},
                 {"decision_at", decision_at},
                 {"engine", "batch-group"},
                 {"logic", logic},
                 {"requested_jobs", o.jobs},
                 {"winner", decided_by.empty() ? Json("none")
                            : decided_by == "owner" || decided_by == "hedge"
                                ? Json(decided_by)
                                : Json("root")},
                 {"winner_slot", winner_slot},
                 {"fork_point", !hook_ran ? (outcome == "refused" ? "refused" : "none")
                                : searched ? "failed"
                                           : "forked"},
                 {"roots", handed ? roots : 0},
                 {"forked", handed},
                 {"fork_errors", fork_errors},
                 {"sharing", bool(rings)},
                 {"hedge", hedge_row},
                 {"variables", variables},
                 {"parse_s", parsed - started},
                 {"base_config", o.config},
                 {"owner_checks", owner_checks},
                 {"owner_check", owner_check},
                 {"owner_check_s", now() - check_started},
                 {"children", root_rows(children)}};
  if (!reason.empty())
    report["reason"] = reason;
  if (!unshared.empty())
    report["sharing_off"] = unshared;
  if (outcome == "refused")
    report["fork_point_reason"] = refusal;
  else if (searched)
    report["fork_point_reason"] = "no root could be forked";
  if (!hook_ran)
    report["decided_before_search"] = decided_by == "owner";
  if (hook_ran && !searched)
  {
    report["fork_point_s"] = fork_point - started;
    report["fork_span_s"] = forks_done - fork_point;
    report["rings"] = rings ? rings->audit() : Json();
    report["owner_memory_kib"] = {{"rss_before_drop", rss_kib},
                                  {"pss_before_drop", pss_kib},
                                  {"rss_after_drop", rss_after_kib},
                                  {"pss_after_drop", pss_after_kib}};
  }
  return report;
}
} // namespace stpp

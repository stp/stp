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
#include "Source.h"
#include <atomic>
#include <cerrno>
#include <cstring>
#include <fcntl.h>
#include <poll.h>
#include <sched.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/wait.h>
#include <unistd.h>

namespace stpp
{
namespace
{
// Two initial encodings and at most one replacement for a failed group.
// Stop requests leave the owner alive to drain and compare its roots' reports.
constexpr unsigned max_groups = 3;
struct Group
{
  std::string config;
  unsigned jobs = 0;
  bool hedge = false, done = false, eof = false, cancelled = false;
  bool reaped = false, forced = false;
  pid_t pid = -1;
  int fd = -1, status = 0;
  double stopped_at = 0, ended_at = 0;
  std::vector<int> cpus;
  Channel channel;
  Json report;
  std::string decision;
};
struct Groups
{
  std::vector<Group> groups;
  std::atomic<bool>* stops = nullptr;
  Groups()
  {
    static_assert(std::atomic<bool>::is_always_lock_free,
                  "encoding cancellation must be shared between processes");
    void* p = mmap(nullptr, max_groups * sizeof(*stops), PROT_READ | PROT_WRITE,
                   MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (p == MAP_FAILED)
      throw std::runtime_error("encoding stop mapping");
    stops = static_cast<std::atomic<bool>*>(p);
    for (unsigned i = 0; i < max_groups; ++i)
      new (stops + i) std::atomic<bool>(false);
    groups.reserve(max_groups);
  }
  // The owner remains unreaped until the kill, so its process-group ID
  // cannot be recycled. Orphaned roots are reparented to this subreaper.
  bool reap(Group& g)
  {
    if (g.reaped || g.pid <= 0)
      return true;
    kill(-g.pid, SIGKILL);
    kill(g.pid, SIGKILL);
    const double until = now() + 5;
    bool owner_reaped = false;
    for (;;)
    {
      int status = 0;
      // Reap the owner by PID even if its process-group setup failed.
      const pid_t p = waitpid(owner_reaped ? -g.pid : g.pid, &status, WNOHANG);
      if (p > 0)
      {
        if (p == g.pid)
        {
          owner_reaped = true;
          g.status = status;
          g.done = true;
        }
        continue;
      }
      if (p < 0 && errno == ECHILD)
      {
        if (!owner_reaped)
        {
          owner_reaped = true;
          continue;
        }
        g.reaped = true;
        return true;
      }
      if ((p < 0 && errno != EINTR) || now() >= until)
        return false;
      poll(nullptr, 0, 1);
    }
  }
  ~Groups()
  {
    for (auto& g : groups)
    {
      reap(g);
      if (g.fd >= 0)
        close(g.fd);
    }
    munmap(stops, max_groups * sizeof(*stops));
  }
};

Json group_rows(const Groups& state)
{
  Json rows = Json::array();
  for (const auto& g : state.groups)
    rows.push_back({{"config", g.config},
                    {"slots", g.jobs},
                    {"pid", g.pid},
                    {"cancelled", g.cancelled},
                    {"forced_stop", g.forced},
                    {"wait_status", g.status},
                    {"stop_requested_at", g.stopped_at},
                    {"ended_at", g.ended_at},
                    {"evidence", g.channel.evidence},
                    {"report", g.report}});
  return rows;
}

void consistent(const Groups& state)
{
  std::string seen;
  auto check = [&](const Json& record)
  {
    auto answer = evidence_answer(record);
    if (answer.empty() && record.is_object() && !record.contains("error"))
    {
      const auto decided = record.find("decided");
      if (decided != record.end() && decided->is_string() &&
          (*decided == "sat" || *decided == "unsat"))
        answer = decided->get<std::string>();
    }
    if (answer.empty())
      return;
    if (!seen.empty() && seen != answer)
      throw Failure("complete answers across encodings disagree",
                    {{"groups", group_rows(state)}});
    seen = answer;
  };
  for (const auto& g : state.groups)
  {
    for (const auto& e : g.channel.evidence)
      check(e);
    check(g.report);
    if (g.report.is_object() && g.report.value("fatal", false))
      throw Failure(g.report.value("error", std::string("encoding failed")),
                    {{"groups", group_rows(state)}});
  }
}

void observe(Group& g, const Options& o, unsigned index)
{
  if (g.fd >= 0 && !g.eof)
  {
    char buffer[16384];
    for (;;)
    {
      const auto n = read(g.fd, buffer, sizeof buffer);
      if (n > 0)
      {
        for (auto& note : g.channel.take(buffer, std::size_t(n)))
        {
          if (note.is_object())
          {
            const auto decision = note.find("decided");
            if (decision != note.end() && decision->is_string() &&
                (*decision == "sat" || *decision == "unsat"))
              g.decision = decision->get<std::string>();
            note["encoding_group"] = index;
            note["encoding"] = g.config;
          }
          if (o.note)
            o.note(note);
        }
        if (g.channel.overflow)
          throw Failure("encoding report exceeds protocol limit",
                        {{"encoding_group", index}});
        continue;
      }
      if (!n)
      {
        g.eof = true;
        g.channel.end();
      }
      else if (errno == EINTR)
        continue;
      else if (errno != EAGAIN && errno != EWOULDBLOCK)
        throw std::runtime_error("encoding report read failed");
      break;
    }
  }
  if (!g.done && g.pid > 0)
  {
    siginfo_t info{};
    if (waitid(P_PID, g.pid, &info, WEXITED | WNOHANG | WNOWAIT) < 0)
    {
      if (errno != EINTR)
        throw std::runtime_error("encoding wait failed");
    }
    else if (info.si_pid)
    {
      g.done = true;
      g.ended_at = now();
      g.status =
          info.si_code == CLD_EXITED ? info.si_status << 8 : info.si_status;
    }
  }
  // A whole report remains evidence even if its writer is killed afterwards.
  // Only a normal exit, or the owner's validated 'decided' note, decides.
  if (!g.channel.report.empty() && !g.channel.cut)
  {
    try
    {
      g.report = Json::parse(g.channel.report);
    }
    catch (...)
    {
      g.report = nullptr;
    }
    if (g.done && WIFEXITED(g.status) && !WEXITSTATUS(g.status) &&
        g.report.is_object() && !g.report.contains("error"))
    {
      const auto answer = evidence_answer(g.report);
      if (!answer.empty())
        g.decision = answer;
    }
  }
}

[[noreturn]] void run_group(Source& input, const Options& o, ParsedQuery& query,
                            Groups& state, unsigned index, int output,
                            pid_t parent)
{
  try
  {
    if (setpgid(0, 0))
      throw std::runtime_error("encoding process group");
    parent_death(parent);
    signal(SIGINT, SIG_DFL);
    signal(SIGTERM, SIG_DFL);
    for (const auto& g : state.groups)
      if (g.fd >= 0)
        close(g.fd);
    const auto& group = state.groups[index];
    Options local = o;
    local.encoding_groups = false;
    local.jobs = group.jobs;
    local.config = group.config;
    local.hedge = group.hedge ? o.hedge : "none";
    local.roots = local.jobs - (local.hedge == "none" ? 0 : 1);
    local.stop = [flag = state.stops + index] { return flag->load(); };
    local.note = [output](const Json& note)
    { write_bounded(output, dump(Json{{"note", note}}) + "\n", now() + 1); };
    if (index >= 2)
      local.seed = (o.seed.value_or(0) + o.jobs) % 2000000000u;
    if (o.pin)
    {
      cpu_set_t mask;
      CPU_ZERO(&mask);
      for (int cpu : group.cpus)
        CPU_SET(cpu, &mask);
      if (sched_setaffinity(0, sizeof mask, &mask))
        throw std::runtime_error("encoding affinity");
    }
    Json report;
    try
    {
      if (index < 2 && injected(o, "fail-encoding=" + group.config))
        throw std::runtime_error("injected encoding failure");
      if (index < 2 && injected(o, "crash-encoding=" + group.config))
        _exit(2);
      if (injected(o, "unresponsive-encoding=" + group.config))
        for (;;)
          pause();
      if (index < 2 && injected(o, "hold-encoding=" + group.config))
        while (!local.cancelled() && !(o.deadline && now() >= o.deadline))
          poll(nullptr, 0, 1);
      report = batch_group(input, local, &query);
      if (injected(o, "linger-encoding=" + group.config))
      {
        const double until = now() + .15;
        while (now() < until)
          poll(nullptr, 0, 1);
      }
    }
    catch (const Failure& e)
    {
      report = {{"error", e.what()}, {"fatal", true}, {"evidence", e.evidence}};
    }
    catch (const std::exception& e)
    {
      report = {{"error", e.what()}};
    }
    write_bounded(output, dump(report) + "\n", now() + 1);
    _exit(report.contains("error") ? 2 : 0);
  }
  catch (...)
  {
    _exit(2);
  }
}

void launch(Source& input, const Options& o, ParsedQuery& query, Groups& state,
            unsigned index)
{
  auto& g = state.groups[index];
  int pipe[2];
  if (pipe2(pipe, O_CLOEXEC | O_NONBLOCK))
  {
    g.done = g.eof = true;
    g.report = {{"error", std::string("encoding pipe: ") + strerror(errno)}};
    return;
  }
  g.fd = pipe[0];
  const pid_t parent = getpid();
  g.pid = injected(o, "fork-fails") ? (errno = EAGAIN, -1) : fork();
  if (!g.pid)
    run_group(input, o, query, state, index, pipe[1], parent);
  close(pipe[1]);
  if (g.pid < 0)
  {
    g.done = g.eof = true;
    g.report = {{"error", std::string("encoding fork: ") + strerror(errno)}};
  }
  else
    setpgid(g.pid, g.pid); // child does it too, before it can fork a root
}
} // namespace

Json encoding_groups(Source& input, const Options& o)
{
  const double started = now();
  ParsedQuery query;
  query.manager = std::make_unique<stp::TermManager>();
  {
    stp::Solver solver(*query.manager, solver_options(o));
    query.logic = parse_query(solver, input);
    admit_logic(query.logic, true);
    query.assertions = solver.assertions();
  }
  const double parsed = now();
  if (query.logic != "QF_BV")
  {
    auto report = batch_group(input, o, &query);
    report["parse_s"] = parsed - started;
    report["encoding_groups_fallback"] = "requires named QF_BV";
    return report;
  }
  if (prctl(PR_SET_CHILD_SUBREAPER, 1))
    throw std::runtime_error("encoding coordinator cannot own descendants");
  Groups state;
  auto cpus = o.pin ? allowed_cpus() : std::vector<int>();
  for (unsigned i = 0; i < 2; ++i)
  {
    Group group;
    group.config = i ? "cnf-gia-high" : "default";
    group.jobs = i ? o.jobs / 2 : (o.jobs + 1) / 2;
    group.hedge = !i;
    if (o.pin)
    {
      const unsigned begin = i ? (o.jobs + 1) / 2 : 0;
      for (unsigned j = 0; j < group.jobs; ++j)
        group.cpus.push_back(cpus.at(begin + j));
    }
    state.groups.push_back(std::move(group));
    launch(input, o, query, state, i);
  }
  if (state.groups[0].pid < 0 && state.groups[1].pid < 0)
  {
    auto report = batch_group(input, o, &query);
    report["parse_s"] = parsed - started;
    report["encoding_groups_fallback"] = "both encoding forks failed";
    return report;
  }
  int winner = -1;
  double decision_at = 0;
  bool cleanup_complete = true;
  Json recovery = nullptr;
  for (;;)
  {
    for (unsigned i = 0; i < state.groups.size(); ++i)
      observe(state.groups[i], o, i);
    consistent(state);
    if (winner < 0)
      for (unsigned i = 0; i < state.groups.size(); ++i)
        if (!state.groups[i].decision.empty())
        {
          winner = int(i);
          decision_at = now();
          break;
        }
    const bool stopping = winner >= 0 || (o.deadline && now() >= o.deadline);
    if (stopping)
      for (unsigned i = 0; i < state.groups.size(); ++i)
      {
        auto& g = state.groups[i];
        if (!g.done && int(i) != winner && !g.cancelled)
        {
          g.cancelled = true;
          g.stopped_at = now();
          state.stops[i].store(true);
        }
        // An encoder inside an uninterruptible library call may not observe
        // the request. Bound the grace period before forcibly stopping it.
        if (g.cancelled && !g.done && now() >= g.stopped_at + .25)
        {
          g.forced = true;
          cleanup_complete &= state.reap(g);
          observe(g, o, i);
        }
      }
    if (!stopping && state.groups.size() == 2)
      for (unsigned i = 0; i < 2; ++i)
      {
        auto& failed = state.groups[i];
        const auto& survivor = state.groups[1 - i];
        if (!failed.done || !failed.eof || survivor.done ||
            (failed.report.is_object() && !failed.report.contains("error") &&
             WIFEXITED(failed.status) && !WEXITSTATUS(failed.status)))
          continue;
        // No replacement starts until every process of the failed group
        // has gone. The surviving group keeps its existing search state.
        if (!state.reap(failed))
          throw std::runtime_error(
              "failed encoding descendants could not be reaped");
        Group replacement;
        replacement.config = survivor.config;
        replacement.jobs = failed.jobs;
        replacement.cpus = failed.cpus;
        recovery = {{"failed_group", i},
                    {"replacement_group", 2},
                    {"config", replacement.config},
                    {"slots", replacement.jobs}};
        state.groups.push_back(std::move(replacement));
        launch(input, o, query, state, 2);
        break;
      }
    bool complete = true;
    for (const auto& g : state.groups)
      complete &= g.done && g.eof;
    if (complete)
      break;
    poll(nullptr, 0, 1);
  }
  for (unsigned i = 0; i < state.groups.size(); ++i)
  {
    cleanup_complete &= state.reap(state.groups[i]);
    observe(state.groups[i], o, i);
  }
  consistent(state);
  bool all_failed = true;
  for (const auto& g : state.groups)
    if (g.report.is_object() && !g.report.contains("error"))
      all_failed = false;
  if (winner < 0 && all_failed)
    throw Failure("every encoding group failed",
                  {{"groups", group_rows(state)}});
  return {{"answer", winner < 0 ? "unknown" : state.groups[winner].decision},
          {"decision_at", decision_at},
          {"engine", "encoding-groups"},
          {"requested_jobs", o.jobs},
          {"shared_parse_s", parsed - started},
          {"winner_group", winner},
          {"recovery", recovery},
          {"groups_cleanup_complete", cleanup_complete},
          {"groups", group_rows(state)}};
}
} // namespace stpp

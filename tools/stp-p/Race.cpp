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
#include "Portfolio.h"
#include <cerrno>
#include <cmath>
#include <cstring>
#include <functional>
#include <fcntl.h>
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
enum class Role { Ordinary, Retained };
const char* name(Role role)
{
  return role == Role::Ordinary ? "ordinary-root" : "retained-root";
}
struct Side
{
  Role role = Role::Ordinary;
  std::string config = "default";
  unsigned slots = 1;
  int cpu = -1;
  pid_t pid = -1;
  int read_fd = -1, write_fd = -1;
  bool eof = false, done = false, normal = false, parsed = false;
  bool cancelled = false, invalid = false, cancellation_sent = false;
  bool noted = false; // its death passed on
  int wait_code = 0, wait_value = 0;
  std::string fork_error; // why the side could not be forked
  Channel channel;        // its evidence records and its report
  Json report;
};
struct Children
{
  std::vector<Side> sides;
  bool cleaned = false;
  Json reaped = Json::array();
  // Kills and reaps every side; false when one is still not reaped five
  // seconds on (the supervisor then reaps what is left).
  bool cleanup()
  {
    if (cleaned) return true;
    for (auto& s : sides)
      if (s.pid > 0) kill(s.pid, SIGKILL);
    // Side owners and workers bind death to their actual pre-fork parent.
    // The race subreaper owns descendants after an owner exits unexpectedly.
    const double until = now() + 5;
    for (;;)
    {
      int status;
      rusage usage{};
      pid_t pid = wait4(-1, &status, WNOHANG, &usage);
      if (pid > 0)
      {
        for (auto& s : sides)
          if (s.pid == pid)
          {
            s.pid = -1;
            s.done = true;
            s.normal = WIFEXITED(status) && WEXITSTATUS(status) == 0;
            s.wait_code = WIFEXITED(status) ? CLD_EXITED :
                          WCOREDUMP(status) ? CLD_DUMPED : CLD_KILLED;
            s.wait_value = WIFEXITED(status) ? WEXITSTATUS(status) : WTERMSIG(status);
          }
        reaped.push_back({{"pid", pid}, {"wait_status", status},
                         {"cpu_s", usage.ru_utime.tv_sec + usage.ru_utime.tv_usec / 1e6 +
                                   usage.ru_stime.tv_sec + usage.ru_stime.tv_usec / 1e6}});
        continue;
      }
      if (pid < 0 && errno == ECHILD) { cleaned = true; return true; }
      if (pid < 0 && errno != EINTR)
        throw std::runtime_error("race reap failed");
      if (now() >= until)
        return false;
      poll(nullptr, 0, 2);
    }
  }
  ~Children()
  {
    try { cleanup(); } catch (...) {}
    for (auto& s : sides)
    {
      if (s.read_fd >= 0) close(s.read_fd);
      if (s.write_fd >= 0) close(s.write_fd);
    }
  }
};
void reject(Side& s, const std::string& reason)
{
  s.invalid = s.parsed = s.eof = true;
  s.report = {{"error", reason}};
  if (s.read_fd >= 0) close(s.read_fd);
  s.read_fd = -1;
  if (s.pid > 0) kill(s.pid, SIGKILL);
}
// Reads what a side wrote; its evidence records go on to `forward` (this
// process's own parent) as they complete.
void drain(Side& s, const std::function<void(const Json&)>& forward = nullptr)
{
  if (s.eof) return;
  char raw[16384];
  for (;;)
  {
    const auto n = read(s.read_fd, raw, sizeof raw);
    if (n > 0)
    {
      for (auto& e : s.channel.take(raw, static_cast<std::size_t>(n)))
        if (forward)
        {
          Json record = e;
          if (record.is_object())
            record["side"] = name(s.role);
          forward(record);
        }
      if (s.channel.overflow)
      {
        reject(s, "side report exceeds protocol limit");
        return;
      }
    }
    else if (!n) { s.eof = true; s.channel.end(); break; }
    else if (errno != EINTR)
    {
      if (errno != EAGAIN && errno != EWOULDBLOCK)
        reject(s, "side report read failed");
      break;
    }
  }
}
void parse_report(Side& s)
{
  if (!s.done || !s.eof || s.parsed) return;
  s.parsed = true;
  try
  {
    if (s.channel.report.empty()) throw std::runtime_error("missing side report");
    s.report = Json::parse(s.channel.report);
    if (!s.report.is_object()) throw std::runtime_error("non-object side report");
  }
  catch (...) { s.invalid = true; s.report = {{"error", "missing or malformed side report"}}; }
}
std::string death(const Side& s); // below
void observe(Side& s, const std::function<void(const Json&)>& forward = nullptr)
{
  drain(s, forward);
  if (!s.done)
  {
    siginfo_t info{};
    int got;
    do { got = waitid(P_PID, s.pid, &info, WEXITED | WNOHANG | WNOWAIT); }
    while (got < 0 && errno == EINTR);
    if (got < 0) throw std::runtime_error("race wait failed");
    if (info.si_pid == s.pid)
    {
      s.done = true;
      s.wait_code = info.si_code;
      s.wait_value = info.si_status;
      s.normal = info.si_code == CLD_EXITED && info.si_status == 0;
      drain(s, forward);
    }
  }
  parse_report(s);
  // A side that died on its own without a report is passed on, so that its
  // death is in the stats even if the run ends at the deadline first.
  if (forward && !s.noted && s.parsed && s.invalid && !s.cancelled)
  {
    s.noted = true;
    forward({{"side", name(s.role)}, {"failed", death(s)}});
  }
}
// A decision: the complete report of a side that exited normally.
std::string answer(const Side& s)
{
  if (!s.parsed || !s.normal || s.invalid || s.report.contains("error"))
    return "unknown";
  const auto found = s.report.find("answer");
  if (found == s.report.end() || !found->is_string()) return "unknown";
  const auto a = found->get<std::string>();
  return a == "sat" || a == "unsat" ? a : "unknown";
}
double decision_time(const Side& s, double fallback)
{
  const auto found = s.report.find("decision_at");
  if (found == s.report.end() || !found->is_number()) return fallback;
  const double value = found->get<double>();
  return value > 0 && std::isfinite(value) ? value : fallback;
}
// Every complete answer in hand, whatever became of the process that gave
// it: a side's report once its line is whole (a side killed after writing it
// included), and the evidence records a side passed on (the group's roots).
std::vector<std::pair<std::string, Json>> evidence(const Side& s)
{
  std::vector<std::pair<std::string, Json>> out;
  for (const auto& e : s.channel.evidence)
    if (!evidence_answer(e).empty())
      out.emplace_back(evidence_answer(e), e);
  if (!s.invalid && !s.channel.report.empty())
  {
    Json r;
    try { r = Json::parse(s.channel.report); } catch (...) {}
    if (!evidence_answer(r).empty())
      out.emplace_back(evidence_answer(r), r);
  }
  return out;
}
Json side_rows(const Children& children)
{
  Json rows = Json::array();
  for (const auto& s : children.sides)
    rows.push_back({{"role", name(s.role)},
                    {"config", s.config},
                    {"pid", s.pid},
                    {"wait_code", s.wait_code}, {"wait_value", s.wait_value},
                    {"evidence", s.channel.evidence},
                    {"report", s.report}});
  return rows;
}
// Two complete answers that disagree, anywhere in hand, end the invocation
// with the evidence: neither may stand as the result.
void consistent(const Children& children)
{
  std::string previous;
  for (const auto& s : children.sides)
    for (const auto& [a, record] : evidence(s))
    {
      if (!previous.empty() && a != previous)
        throw Failure("race sides have contradictory complete answers",
                      {{"engine", "root-race"}, {"sides", side_rows(children)}});
      previous = a;
    }
}
// A side whose report is fatal ends the whole invocation: no other side's
// answer may stand in for it.
void refuse_fatal(const Children& children)
{
  for (const auto& s : children.sides)
    if (s.parsed && s.report.is_object() && s.report.value("fatal", false))
    {
      const auto found = s.report.find("error");
      throw Failure(found != s.report.end() && found->is_string()
                        ? found->get<std::string>()
                        : "fatal side report",
                    s.report.value("evidence", Json()));
    }
}
// How a side that left no report of its own ended.
std::string death(const Side& s)
{
  return std::string(name(s.role)) +
         (!s.fork_error.empty()        ? " could not be forked: " + s.fork_error
          : s.wait_code == CLD_EXITED ? " exited " + std::to_string(s.wait_value)
                                      : " died, signal " + std::to_string(s.wait_value));
}
// After the race: every side killed and reaped, what each wrote drained, and
// the evidence compared once more -- a report queued during cancellation,
// a fatal one included, still counts.
bool settle(Children& children, const std::function<void(const Json&)>& forward)
{
  const bool reaped = children.cleanup();
  for (auto& s : children.sides) { drain(s, forward); parse_report(s); }
  consistent(children);
  refuse_fatal(children);
  return reaped;
}
[[noreturn]] void child(Source& input, const Options& o,
                        const Children& children, unsigned index, pid_t parent)
{
  // Never unwind inherited parent-owned RAII after a failed child allocation.
  try
  {
    parent_death(parent);
    const auto& side = children.sides[index];
    for (unsigned j = 0; j != children.sides.size(); ++j)
    {
      const auto& other = children.sides[j];
      if (other.read_fd >= 0) close(other.read_fd);
      if (j != index && other.write_fd >= 0) close(other.write_fd);
    }
    Options local = o;
    local.portfolio.clear();
    local.jobs = side.slots;
    const int to_race = side.write_fd;
    local.note = [to_race](const Json& e)
    {
      try
      {
        write_bounded(to_race, dump(Json{{"note", e}}) + "\n", now() + 1);
      }
      catch (...)
      {
      }
    };
    local.roots = 0;
    // A portfolio's ordinary side takes QF_BV only (Common.h); the retained
    // side keeps its own route.
    local.strict_logic = side.role == Role::Ordinary;
    local.config = side.role == Role::Ordinary ? side.config : "default";
    if (side.cpu >= 0)
    {
      cpu_set_t affinity;
      CPU_ZERO(&affinity);
      CPU_SET(side.cpu, &affinity);
      if (sched_setaffinity(0, sizeof affinity, &affinity))
        throw std::runtime_error("root affinity");
    }
    Json result;
    try
    {
      result = side.role == Role::Ordinary ? ordinary(input, local)
                                           : retained(input, local);
    }
    catch (const Failure& e)
    {
      result = {{"error", e.what()}, {"fatal", true}, {"evidence", e.evidence}};
    }
    catch (const std::exception& e) { result = {{"error", e.what()}}; }
    write_bounded(side.write_fd, dump(result) + "\n", now() + 1);
    _exit(result.contains("error") ? 2 : 0);
  }
  catch (...) { _exit(2); }
}
} // namespace

// The test driver's portfolio: one single-CPU side per configuration.
Json race(Source& input, const Options& o)
{
  const double started = now();
  const unsigned root_slots = unsigned(o.portfolio.size());
  if (o.jobs != root_slots || o.jobs < 2)
    throw std::runtime_error("a race needs a slot per side and two sides");
  if (prctl(PR_SET_CHILD_SUBREAPER, 1))
    throw std::runtime_error("race cannot own descendants");
  // Placement is the scheduler's, within the allowed CPUs. With the test
  // driver's --pin, the sides take the last allowed CPUs, in portfolio
  // order.
  std::vector<int> cpus;
  if (o.pin)
  {
    cpus = allowed_cpus();
    if (cpus.size() < o.jobs)
      throw std::runtime_error("race CPU capacity changed");
  }
  Children children;
  for (unsigned i = 0; i != root_slots; ++i)
  {
    Side s;
    s.config = o.portfolio[i];
    s.role = config(s.config).route == Config::Route::Retained ? Role::Retained
                                                               : Role::Ordinary;
    if (o.pin)
      s.cpu = cpus[o.jobs - 1 - i];
    children.sides.push_back(std::move(s));
  }
  for (auto& s : children.sides)
  {
    int channel[2];
    if (pipe2(channel, O_CLOEXEC | O_NONBLOCK))
      throw std::runtime_error("race result pipe");
    s.read_fd = channel[0]; s.write_fd = channel[1];
  }
  std::vector<pid_t> identities(children.sides.size());
  bool launched = false;
  for (unsigned i = 0; i != children.sides.size(); ++i)
  {
    auto& s = children.sides[i];
    const pid_t parent = getpid();
    s.pid = injected(o, "fork-fails") ? (errno = EAGAIN, -1) : fork();
    if (s.pid < 0)
    {
      s.done = true;
      s.fork_error = strerror(errno);
      reject(s, "side fork failed: " + s.fork_error);
    }
    if (!s.pid) child(input, o, children, i, parent);
    launched = launched || s.pid > 0;
    identities[i] = s.pid;
    close(s.write_fd); s.write_fd = -1;
  }
  if (!launched)
  {
    // No side could be forked: this process runs the first side's route
    // itself, on its own CPU, rather than fail where -j1 would answer.
    Options local = o;
    local.portfolio.clear();
    local.jobs = 1;
    local.strict_logic = children.sides[0].role == Role::Ordinary;
    local.config = local.strict_logic ? children.sides[0].config : "default";
    Json errors = Json::array();
    for (const auto& s : children.sides)
      errors.push_back(s.fork_error);
    Json result = children.sides[0].role == Role::Ordinary ? ordinary(input, local)
                                                           : retained(input, local);
    result["race_fork_errors"] = errors;
    result["portfolio"] = o.portfolio;
    return result;
  }
  // Every side holds its own copy of the query; the race's goes.
  input.release();
  release_memory();
  int winner = -1;
  double first = 0;
  bool ended = false; // every side finished on its own, before the deadline
  for (;;)
  {
    try
    {
      for (auto& s : children.sides) observe(s, o.note);
      consistent(children);
      refuse_fatal(children);
    }
    catch (...)
    {
      settle(children, o.note);
      throw;
    }
    if (winner < 0)
    {
      double earliest = 0;
      for (unsigned i = 0; i != children.sides.size(); ++i)
        if (answer(children.sides[i]) != "unknown")
        {
          const double at = decision_time(children.sides[i], now());
          if (winner < 0 || at < earliest) { winner = int(i); earliest = at; }
        }
      if (winner >= 0)
      {
        // Losing work cannot change a complete answer: stop it at once rather
        // than wait for its report. Reports already queued stay observable.
        first = now();
        for (unsigned i = 0; i != children.sides.size(); ++i)
        {
          auto& s = children.sides[i];
          if (int(i) == winner || s.done) continue;
          s.cancelled = true;
          s.cancellation_sent = kill(s.pid, SIGKILL) == 0;
        }
        break;
      }
    }
    bool complete = true;
    std::vector<pollfd> fds;
    for (const auto& s : children.sides)
    {
      complete &= s.parsed;
      if (!s.eof) fds.push_back({s.read_fd, POLLIN, 0});
    }
    if (complete) { ended = true; break; }
    if (o.deadline && now() >= o.deadline) break;
    poll(fds.data(), fds.size(), 2);
  }
  const bool reaped = settle(children, o.note);
  // Every side ended on its own, before the deadline, without an answer and
  // with an error report or none at all (it crashed): that is the
  // invocation's error, as at -j1, not an unknown. A side that answered
  // unknown in time is not a failure.
  if (winner < 0 && ended)
  {
    std::string error, deaths;
    bool all_failed = true;
    for (const auto& s : children.sides)
    {
      const auto found = s.report.is_object() ? s.report.find("error") : s.report.end();
      // An invalid side left no report of its own (it died, or wrote
      // something unreadable); its error is the reader's, not the side's.
      const bool said = !s.invalid && found != s.report.end() && found->is_string();
      if (!said && !s.invalid)
      {
        all_failed = false;
        break;
      }
      if (said && error.empty())
        error = found->get<std::string>();
      if (!said)
        deaths += (deaths.empty() ? "" : "; ") + death(s);
    }
    if (all_failed)
      throw std::runtime_error(!error.empty() ? error : "every side failed (" + deaths + ")");
  }
  Json sides = Json::array();
  for (unsigned i = 0; i != children.sides.size(); ++i)
  {
    const auto& s = children.sides[i];
    sides.push_back({{"role", name(s.role)},
                     {"config", s.config},
                     {"slots", s.slots}, {"cpu", s.cpu},
                     {"pid", identities[i]}, {"launched", identities[i] > 0},
                     {"cancelled", s.cancelled},
                     {"cancellation_sent", s.cancellation_sent},
                     {"completed_report", s.parsed && !s.invalid},
                     {"fork_error", s.fork_error},
                     {"wait_code", s.wait_code}, {"wait_value", s.wait_value},
                     {"evidence", s.channel.evidence},
                     {"report", s.report}});
  }
  unsigned ordinary_slots = 0, retained_slots = 0;
  for (const auto& s : children.sides)
  {
    ordinary_slots += s.role == Role::Ordinary;
    retained_slots += s.role == Role::Retained;
  }
  const Side* won = winner < 0 ? nullptr : &children.sides[winner];
  Json result = {{"answer", won ? answer(*won) : "unknown"},
                {"engine", "root-race"},
                {"portfolio", o.portfolio},
                {"winner", won ? name(won->role) : "none"},
                {"winner_config", won ? Json(won->config) : Json()},
                {"requested_jobs", o.jobs},
                {"ordinary_slots", ordinary_slots}, {"retained_slots", retained_slots},
                {"race_first_complete_s", winner < 0 ? 0 : first - started},
                {"decision_at", winner < 0 ? 0 : decision_time(children.sides[winner], first)},
                {"sides", sides}, {"race_reap", children.reaped},
                {"race_cleanup_complete", reaped}};
  if (winner < 0) result["reason"] = "no complete decision from any side";
  return result;
}
} // namespace stpp

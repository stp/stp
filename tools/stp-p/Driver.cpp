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
#include <cstring>
#include <fcntl.h>
#include <fstream>
#include <iostream>
#include <poll.h>
#include <signal.h>
#include <sstream>
#include <stdexcept>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

namespace stpp
{
namespace
{
volatile sig_atomic_t interrupted = 0;
void on_signal(int sig)
{
  interrupted = sig;
}
// Summed RSS of the process tree, from statm; with `pss`, also the summed
// PSS from smaps_rollup. Processes forked from one owner share its pages
// copy-on-write, and RSS counts a shared page once per process: PSS, which
// splits it between them, is what the tree actually holds. Reading PSS walks
// page tables (about 10 ms per GiB mapped, per process), so the guard asks
// for it only when the RSS sum is over the limit -- the PSS sum is never
// above the RSS sum -- and a walk stops early at the deadline or a signal.
std::uint64_t resident_tree(pid_t root, double deadline, std::uint64_t* pss = nullptr)
{
  std::vector<pid_t> pending{root};
  std::uint64_t pages = 0, pss_kib = 0;
  while (!pending.empty())
  {
    if (pss && (interrupted || (deadline && now() >= deadline)))
      break;
    auto pid = pending.back();
    pending.pop_back();
    std::ifstream stat("/proc/" + std::to_string(pid) + "/statm");
    std::uint64_t total = 0, rss = 0;
    if (stat >> total >> rss)
      pages += rss;
    std::uint64_t r = 0, p = 0;
    if (pss && memory_rollup(pid, r, p))
      pss_kib += p;
    std::ifstream children("/proc/" + std::to_string(pid) + "/task/" +
                           std::to_string(pid) + "/children");
    pid_t child;
    while (children >> child)
      pending.push_back(child);
  }
  if (pss)
    *pss = pss_kib * 1024;
  return pages * static_cast<std::uint64_t>(sysconf(_SC_PAGESIZE));
}
// --stats-json, opened before anything runs: a path that cannot be written
// is a usage error at once, never a found answer lost at the end.
struct StatsFile
{
  int fd = -1;
  explicit StatsFile(const std::string& path)
  {
    if (path.empty())
      return;
    fd = open(path.c_str(), O_WRONLY | O_CREAT | O_NONBLOCK | O_CLOEXEC, 0666);
    if (fd < 0)
      throw std::runtime_error("cannot open stats output: " + path);
    struct stat st{};
    if (fstat(fd, &st) || !S_ISREG(st.st_mode) || ftruncate(fd, 0))
    {
      close(fd);
      throw std::runtime_error("stats output must be a writable regular file");
    }
  }
  ~StatsFile()
  {
    if (fd >= 0)
      close(fd);
  }
  StatsFile(const StatsFile&) = delete;
  StatsFile& operator=(const StatsFile&) = delete;
};
// The report: to --stats-json, then the answer to stdout. Returns the exit
// status: sat 10, unsat 20, unknown 0; an error report is the invocation's
// error (exit 2), written to the stats first so that its evidence survives.
// A found answer is always the exit status: a stats write that fails or runs
// late is reported on stderr instead, and so is an answer line that stdout
// cannot take by the deadline (or a second after it).
int publish(Json report, const Options& o, double began, const StatsFile& stats)
{
  report["schema"] = "stp-p-0.3";
  report["elapsed_s"] = now() - began;
  if (report.value("decision_at", 0.0) > 0)
    report["first_answer_s"] = report["decision_at"].get<double>() - began;
  const bool error = report.contains("error");
  const std::string answer =
      error ? "" : report.value("answer", std::string("unknown"));
  // Past the deadline the writes still get a second: an answer found at the
  // deadline is published, not lost to it. With no deadline they wait.
  const double bound = o.deadline ? std::max(o.deadline, now() + 1) : 0;
  if (stats.fd >= 0)
  {
    try
    {
      write_bounded(stats.fd, dump(report, 2) + "\n", bound);
    }
    catch (const std::exception& e)
    {
      std::cerr << "stp-p: --stats-json not written: " << e.what() << '\n';
    }
  }
  if (error)
    throw std::runtime_error(report["error"].is_string()
                                 ? report["error"].get<std::string>()
                                 : "error");
  if (answer != "sat" && answer != "unsat" && answer != "unknown")
    throw std::runtime_error("invalid owner verdict");
  // stdout's flags are shared with whoever else holds it (a shell): it is
  // never switched to non-blocking. The answer is shorter than PIPE_BUF, so
  // once poll says stdout takes output, one write takes all of it.
  const int status = answer == "sat" ? 10 : answer == "unsat" ? 20 : 0;
  const std::string line = answer + "\n";
  std::string lost;
  while (lost.empty())
  {
    if (bound && now() >= bound)
    {
      lost = "standard output took nothing by the deadline";
      break;
    }
    pollfd p{1, POLLOUT, 0};
    const int ready = poll(&p, 1, 10);
    if (ready < 0 && errno != EINTR)
      lost = std::string("standard output: ") + strerror(errno);
    else if (ready > 0 && (p.revents & (POLLERR | POLLNVAL)))
      lost = "standard output is closed";
    else if (ready > 0)
    {
      const auto n = write(1, line.data(), line.size());
      if (n == ssize_t(line.size()))
        break;
      if (!(n < 0 && (errno == EINTR || errno == EAGAIN)))
        lost = std::string("standard output: ") +
               (n < 0 ? strerror(errno) : "a partial write");
    }
  }
  if (!lost.empty())
    std::cerr << "stp-p: the answer line (" << answer << ") was lost: " << lost
              << "; the exit status is the answer's\n";
  return status;
}
// Two complete answers that disagree, among the evidence and the report.
bool contradicts(const std::vector<Json>& evidence, const Json& report)
{
  std::string seen = evidence_answer(report);
  for (const auto& e : evidence)
  {
    const auto a = evidence_answer(e);
    if (a.empty())
      continue;
    if (!seen.empty() && a != seen)
      return true;
    seen = a;
  }
  return false;
}
} // namespace
Json execute(Options o)
{
  // The owner's peak resident size counts from here (a test bounds it, after
  // the parse, against the source).
  if (FILE* f = fopen("/proc/self/clear_refs", "w"))
  {
    fputs("5", f);
    fclose(f);
  }
  memory_limit(o.worker_mib);
  if (!o.source)
    throw std::runtime_error("no input");
  Source& input = *o.source;
  const std::size_t bytes = input.text().size();
  auto sized = [&](Json result)
  {
    if (result.is_object())
      result["source_bytes"] = bytes;
    return result;
  };
  // The group is the whole invocation: it parses the query once and forks
  // the hedge itself (on QF_BV) and its roots. A race is the test driver's
  // portfolio.
  if (o.roots && o.portfolio.empty())
    return sized(batch_group(input, o));
  if (!o.portfolio.empty())
    return sized(race(input, o));
  if (config(o.config).route == Config::Route::Retained)
  {
    auto result = retained(input, o);
    result["config"] = o.config;
    return sized(result);
  }
  return sized(ordinary(input, o));
}
Json ordinary(Source& input, const Options& o)
{
  stp::TermManager tm;
  stp::Solver solver(tm, solver_options(o));
  const double parse_started = now();
  // -j1 and the group's own route take the theory logics; a portfolio's
  // side takes QF_BV.
  const std::string logic = parse_query(solver, input);
  admit_logic(logic, !o.strict_logic);
  release_memory();
  const double parsed = now();
  // The owner's resident size once the query is parsed and its source
  // released, and its peak during the parse (regression tests bound both).
  const std::uint64_t parse_rss = own_rss(), parse_peak = peak_rss();
  Stop stop(o.deadline);
  solver.set_terminator(&stop);
  const auto r = solver.check_sat();
  solver.set_terminator(nullptr);
  return {{"answer", r.is_sat()     ? "sat"
                     : r.is_unsat() ? "unsat"
                                    : "unknown"},
          {"engine", "ordinary"},
          {"logic", logic},
          {"parse_s", parsed - parse_started},
          {"parse_rss_bytes", parse_rss},
          {"parse_peak_rss_bytes", parse_peak},
          {"config", o.config},
          {"requested_jobs", o.jobs},
          {"reason", r.reason_message()},
          {"decision_at", now()}};
}
// The test driver's `retained` configuration (alone, or a portfolio's
// side): the hedge's check on a query it parses itself. QF_BV only.
Json retained(Source& input, const Options& o)
{
  if (injected(o, "hold-hedge"))
  {
    // A test fault: the hedge starts 30 s late.
    const double until = now() + 30;
    while (now() < until && !(o.deadline && now() >= o.deadline))
      poll(nullptr, 0, 10);
  }
  stp::TermManager tm;
  stp::Solver solver(tm, solver_options(o, true));
  const double parse_started = now();
  const std::string logic = parse_query(solver, input);
  admit_logic(logic, false);
  release_memory();
  Json report = hedge_check(solver, o, logic);
  report["parse_s"] = now() - parse_started;
  return report;
}
Json hedge_check(stp::Solver& solver, const Options& o, const std::string& logic)
{
  const double started = now();
  Stop stop(o.deadline);
  solver.set_terminator(&stop);
  const auto r = solver.check_sat();
  solver.set_terminator(nullptr);
  return {{"answer", r.is_sat()     ? "sat"
                     : r.is_unsat() ? "unsat"
                                    : "unknown"},
          {"engine", "retained"},
          {"logic", logic},
          {"check_s", now() - started},
          {"requested_jobs", o.jobs},
          {"reason", r.reason_message()},
          {"decision_at", r.is_unknown() ? 0.0 : now()}};
}
int supervise(const Options& options)
{
  const double began = now();
  interrupted = 0;
  struct sigaction action{};
  action.sa_handler = on_signal;
  sigemptyset(&action.sa_mask);
  sigaction(SIGINT, &action, nullptr);
  sigaction(SIGTERM, &action, nullptr);
  signal(SIGPIPE, SIG_IGN);
  Options o = options;
  // A closed standard input would be the first descriptor the next open
  // takes (the stats file's), and the input read from it.
  if (o.input == "-" && fcntl(STDIN_FILENO, F_GETFD) < 0)
    throw std::runtime_error("standard input is closed: give a file, or pipe "
                             "the query in");
  const StatsFile stats(o.stats);
  // The query is read here, before anything is forked: the supervisor is
  // still in the terminal's foreground process group, and a read that stalls
  // is bounded by the deadline and by a signal, its size by input_limit.
  o.source = std::make_shared<Source>();
  try
  {
    if (!read_source(o.input, *o.source, input_limit(o), o.deadline, interrupted))
    {
      if (interrupted)
      {
        std::cerr << "stp-p: interrupted while reading the input\n";
        return 128 + interrupted;
      }
      return publish({{"answer", "unknown"},
                      {"reason", "wall timeout while reading the input"}},
                     o, began, stats);
    }
  }
  catch (const std::exception& e)
  {
    return publish({{"error", e.what()}}, o, began, stats);
  }
  if (prctl(PR_SET_CHILD_SUBREAPER, 1))
    throw std::runtime_error("cannot establish child ownership");
  int channel[2];
  if (pipe2(channel, O_CLOEXEC | O_NONBLOCK))
    throw std::runtime_error("supervisor pipe");
  const pid_t parent = getpid(), owner = fork();
  if (owner < 0)
  {
    const int error = errno;
    close(channel[0]);
    close(channel[1]);
    throw std::runtime_error(std::string("owner fork: ") + strerror(error));
  }
  if (!owner)
  {
    close(channel[0]);
    setpgid(0, 0);
    parent_death(parent);
    signal(SIGINT, SIG_DFL);
    signal(SIGTERM, SIG_DFL);
    const int to_supervisor = channel[1];
    const bool linger = injected(o, "linger");
    o.note = [to_supervisor](const Json& e)
    {
      try
      {
        write_bounded(to_supervisor, dump(Json{{"note", e}}) + "\n",
                      now() + 1);
      }
      catch (...)
      {
      }
    };
    const bool contradict = injected(o, "contradict"),
               cut = injected(o, "cut-report");
    const auto note = o.note;
    Json result;
    try
    {
      result = execute(std::move(o));
    }
    catch (const Failure& e)
    {
      result = {{"error", e.what()}, {"fatal", true}, {"evidence", e.evidence}};
    }
    catch (const std::exception& e)
    {
      result = {{"error", e.what()}};
    }
    if (contradict && !evidence_answer(result).empty())
      // A test fault: a root's answer that contradicts the report, passed
      // on ahead of it.
      note({{"root", 0},
            {"answer", evidence_answer(result) == "sat" ? "unsat" : "sat"}});
    // Unbounded: the supervisor's deadline and its cleanup bound the
    // invocation, and a report it stops reading (a stopped terminal job)
    // still arrives whole once it reads again.
    try
    {
      const std::string line = dump(result) + "\n";
      if (cut)
      {
        // A test fault: half a report, and the owner killed while it writes.
        write_bounded(to_supervisor, line.substr(0, line.size() / 2), 0);
        for (;;)
          pause();
      }
      write_bounded(to_supervisor, line, 0);
    }
    catch (...)
    {
      _exit(2);
    }
    // A test fault: the owner stays alive after its report, so that the
    // supervisor stops it at the deadline with the report in hand.
    for (const double until = now() + 30; linger && now() < until;)
      poll(nullptr, 0, 10);
    _exit(result.contains("error") ? 2 : 0);
  }
  close(channel[1]);
  // The owner has its copy; the supervisor's goes.
  o.source.reset();
  release_memory();
  const std::uint64_t supervisor_rss = own_rss();
  setpgid(owner, owner);
  Channel from_owner;
  std::string limit_reason;
  bool eof = false, owner_done = false, cleaned = false;
  int status = 0;
  std::uint64_t peak_rss = 0, peak_pss = 0;
  double next_memory = 0, next_pss = 0, child_cpu = 0;
  auto drain = [&]
  {
    char raw[16384];
    for (;;)
    {
      auto n = read(channel[0], raw, sizeof raw);
      if (n > 0)
        from_owner.take(raw, static_cast<std::size_t>(n));
      else if (!n)
      {
        eof = true;
        from_owner.end();
        break;
      }
      else if (errno != EINTR)
        break;
    }
  };
  // Kills and reaps every process of the invocation; false when one is
  // still not reaped five seconds on.
  auto cleanup = [&]
  {
    if (cleaned)
      return true;
    // This group is created by this invocation; no name-based process killing.
    // Keep the owner unreaped until here, so its PID/PGID cannot be recycled.
    kill(-owner, SIGKILL);
    kill(owner, SIGKILL);
    const double until = now() + 5;
    for (;;)
    {
      int st;
      rusage ru{};
      pid_t p = wait4(-1, &st, WNOHANG, &ru);
      if (p > 0)
      {
        child_cpu += ru.ru_utime.tv_sec + ru.ru_utime.tv_usec / 1e6 +
                     ru.ru_stime.tv_sec + ru.ru_stime.tv_usec / 1e6;
        if (p == owner)
        {
          status = st;
          owner_done = true;
        }
        continue;
      }
      if (p < 0 && errno == ECHILD)
      {
        cleaned = true;
        return true;
      }
      if (now() >= until)
        return false;
      poll(nullptr, 0, 2);
    }
  };
  try
  {
    while (!eof || !owner_done)
    {
      if (interrupted)
      {
        limit_reason = "interrupted";
        break;
      }
      if (o.deadline && now() >= o.deadline)
      {
        limit_reason = "wall timeout";
        break;
      }
      // The aggregate memory guard, only when asked for: the RSS sum every
      // 50 ms, and over the limit the PSS sum at most every 0.5 s, counted
      // from the end of the last walk.
      if (o.memory_mib && now() >= next_memory)
      {
        next_memory = now() + .05;
        const std::uint64_t limit = o.memory_mib * 1024 * 1024;
        const std::uint64_t rss = resident_tree(getpid(), o.deadline);
        peak_rss = std::max(peak_rss, rss);
        if (rss > limit && now() >= next_pss)
        {
          std::uint64_t pss = 0;
          resident_tree(getpid(), o.deadline, &pss);
          next_pss = now() + .5;
          peak_pss = std::max(peak_pss, pss);
          if (pss > limit)
          {
            limit_reason = "aggregate sampled memory limit";
            break;
          }
        }
      }
      drain();
      if (!owner_done)
      {
        siginfo_t info{};
        if (waitid(P_PID, owner, &info, WEXITED | WNOHANG | WNOWAIT) < 0)
          throw std::runtime_error("owner wait failed");
        owner_done = info.si_pid == owner;
      }
      if (!eof || !owner_done)
      {
        pollfd p{channel[0], POLLIN, 0};
        poll(&p, 1, 5);
      }
    }
    const bool stopped = !limit_reason.empty();
    // What the owner wrote before the stop is read before the kill.
    drain();
    const bool reaped = cleanup();
    drain();
    from_owner.end();
    close(channel[0]);
    channel[0] = -1;
    if (interrupted)
    {
      std::cerr << "stp-p: interrupted; owned processes reaped\n";
      return 128 + interrupted;
    }
    if (!reaped)
      std::cerr << "stp-p: owned processes not reaped within 5 s\n";
    // The owner's report, if it wrote one whole: an answer it found stands,
    // whatever stopped the run after it was written. One the stop cut short
    // is no report.
    Json report;
    const bool cut = stopped && from_owner.cut;
    if (from_owner.overflow)
      report = {{"error", "owner report exceeds protocol limit"}};
    else if (!from_owner.report.empty() && !cut)
    {
      try
      {
        report = Json::parse(from_owner.report);
      }
      catch (...)
      {
        report = nullptr;
      }
      if (!report.is_object())
        report = {{"error", "malformed owner report"}};
    }
    const bool reported = report.is_object();
    if (!reported)
    {
      if (stopped)
      {
        report = {{"answer", "unknown"}, {"reason", limit_reason}};
        // A decision the group had made before the stop, passed on as it was
        // made: the answer it is, whatever stopped the group's report.
        for (const auto& e : from_owner.evidence)
          if (e.is_object() && e.contains("decided") && e["decided"].is_string() &&
              (e["decided"] == "sat" || e["decided"] == "unsat"))
          {
            report = {{"answer", e["decided"]},
                      {"decided_by", e.value("by", Json())},
                      {"published_from", "the group's decision record"},
                      {"stopped_by", limit_reason}};
            break;
          }
      }
      else
        report = {{"error", "owner exited without a result (wait status " +
                                std::to_string(status) + ")"}};
      if (cut)
        report["owner_report_cut"] = true;
      if (!from_owner.evidence.empty())
        report["evidence"] = from_owner.evidence;
    }
    else if (!stopped && owner_done &&
             (!WIFEXITED(status) || WEXITSTATUS(status)) &&
             !report.contains("error"))
      // The owner failed after its report, which stands: recorded only.
      report["owner_wait_status_after_report"] = status;
    if (!report.contains("error") && contradicts(from_owner.evidence, report))
      report = {{"error", "complete answers disagree"},
                {"fatal", true},
                {"evidence", {{"records", from_owner.evidence}, {"report", report}}}};
    if (stopped && !report.contains("error") && evidence_answer(report).empty())
      report["stopped_by"] = limit_reason;
    // What the owner passed on, when a limit stopped the run: each answer and
    // each death, also those its report (written as the limit came) could
    // not include.
    if (stopped && !report.contains("evidence") && !from_owner.evidence.empty())
      report["evidence"] = from_owner.evidence;
    report["child_cpu_s"] = child_cpu;
    report["supervisor_rss_bytes"] = supervisor_rss;
    if (o.memory_mib)
    {
      report["peak_sampled_rss_bytes"] = peak_rss;
      // Zero unless the RSS sum went over --memory-mib and PSS was read.
      report["peak_sampled_pss_bytes"] = peak_pss;
    }
    report["cleanup_complete"] = reaped;
    if (o.roots)
      report["base_config"] = o.config;
    return publish(std::move(report), o, began, stats);
  }
  catch (...)
  {
    cleanup();
    if (channel[0] >= 0)
      close(channel[0]);
    throw;
  }
}
} // namespace stpp

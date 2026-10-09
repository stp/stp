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
#include <chrono>
#include <cstdint>
#include <functional>
#include <memory>
#include <stdexcept>
#include <nlohmann/json.hpp>
#include <optional>
#include <stp/stp.hpp>
#include <string>
#include <vector>

namespace stpp
{
using Json = nlohmann::ordered_json;
// A report as text. Strings may hold the input's bytes (a parse error quotes
// its token), which need not be UTF-8: those bytes are replaced (U+FFFD)
// rather than failing the report.
inline std::string dump(const Json& j, int indent = -1)
{
  return j.dump(indent, ' ', false, Json::error_handler_t::replace);
}
class Source;
double now();
struct Options
{
  // -j; absent, the allowed CPUs up to eight (default_jobs).
  unsigned jobs = 1;
  std::optional<std::uint64_t> seed;
  double timeout = 0, deadline = 0;
  // Per-process address space (MiB; 0 inherits). 16 GiB by default: the
  // largest competition inputs need more than 2 GiB of address space.
  std::uint64_t worker_mib = 16384, memory_mib = 0;
  std::string input = "-", stats;
  // The query, read by the supervisor before it forks anything.
  std::shared_ptr<Source> source;
  // Where this process sends evidence as it arrives, ahead of its own report:
  // a complete answer from a process that may be killed before it exits, or
  // a process that died without one. The supervisor and the race set it to
  // the channel to their parent; not an option.
  std::function<void(const Json&)> note;
  // A portfolio's ordinary side takes QF_BV only (not an option).
  bool strict_logic = false;
  std::string config = "default"; // see Portfolio.cpp
  std::vector<std::string> portfolio; // race sides; empty: no race
  // The group (-jN, N > 1): `roots` batch roots forked at ordinary STP's
  // before-search point (root 0 ordinary STP on CaDiCaL, the rest
  // diversified), beside the hedge unless `hedge` is "none". Not an option:
  // the command line sets it to -j minus the hedge, and the group takes the
  // hedge's CPU too when it does not fork the hedge (a query that is not
  // QF_BV). 0: no group.
  unsigned roots = 0;
  std::string hedge = "retained";
  // Import: at most `import_budget` clauses of two or more literals per own
  // conflict, the shortest first; a poll scans at most `import_window` of
  // each ring's newest literals. Without `root0_import` root 0 exports only,
  // so its search is ordinary STP's on CaDiCaL.
  std::uint32_t import_budget = 1;
  bool root0_import = false;
  // The transport settings stp-p runs with; only the test driver changes
  // them.
  bool sharing = true;
  std::uint32_t exchange_interval = 256, exchange_size = 8;
  double exchange_rate = 2000;
  std::size_t ring_literals = std::size_t(1) << 20;
  std::size_t import_window = std::size_t(1) << 16;
  // Set only from the test driver's command line (stpp-drive): the code is
  // in stp-p's library too, but no stp-p option reaches it. `pin` binds each
  // root and side to one CPU of the allowed set; stp-p leaves placement to
  // the scheduler.
  // `control` "batch-handoff" forks no root, so the owner's own check is
  // published; "batch-all" lets every root run to its own answer. `inject`
  // names faults the tests need, comma-separated: "wrong-root=SLOT:ANSWER"
  // makes that root report ANSWER as soon as it is forked and then wait to
  // be killed; "hold-root=SLOT" makes that root wait 30 s before it
  // searches, and "hold-hedge" the hedge before it starts; "fail-root-setup"
  // makes every root's setup fail; "fork-fails" makes every root's fork
  // fail; "linger" keeps the owner alive for 30 s after its report;
  // "contradict" makes the owner pass on, ahead of its report, a root's
  // answer that contradicts it (the supervisor's own comparison must catch
  // it); "cut-report" makes the owner write half its report and wait to be
  // killed.
  bool pin = false;
  std::string control, inject;
};
// Whether `inject` names the fault `kind` ("hold-hedge"), or for
// "wrong-root" the answer a slot is to report ("" when none).
bool injected(const Options&, const std::string& kind);
std::string injected_answer(const Options&, unsigned slot);
bool injected_hold(const Options&, unsigned slot); // hold-root=SLOT
// The CPUs this process may run on, however many the system has.
std::vector<int> allowed_cpus();
// -j when it is absent: the allowed CPUs, at most eight, where the group can
// run; 1 on a build without the clause-import extension.
unsigned default_jobs();
// An error that ends the whole invocation, whatever another side answers
// (two complete answers that disagree), with the evidence for the stats.
struct Failure : std::runtime_error
{
  Json evidence;
  Failure(const std::string& what, Json e)
      : std::runtime_error(what), evidence(std::move(e))
  {
  }
};
struct Stop final : stp::Terminator
{
  double end;
  explicit Stop(double value) : end(value) {}
  bool terminate() override { return end && now() >= end; }
};
stp::Options solver_options(const Options&, bool retained = false);
void memory_limit(std::uint64_t mib);
void parent_death(int expected_parent);
void write_bounded(int fd, const std::string&, double deadline);
// A process's channel to its parent carries one JSON object per line:
// evidence records, each {"note": ...} and nothing else, then its report.
// `Channel` collects them as they arrive (at most `limit` bytes in all).
struct Channel
{
  std::string pending;
  std::vector<Json> evidence;
  std::string report; // the last line that is not evidence, unparsed
  std::size_t bytes = 0;
  // `cut`: the report is a last line its writer never ended (it died, or
  // was killed, while writing it).
  bool overflow = false, malformed = false, cut = false;
  // Takes what was read; returns the evidence records completed by it.
  std::vector<Json> take(const char* data, std::size_t size,
                         std::size_t limit = 2 * 1024 * 1024);
  void end(); // the writer is gone: an unterminated last line is its report
};
// The answer a complete report or evidence record gives ("sat", "unsat"),
// whatever became of the process after it wrote it; "" otherwise.
std::string evidence_answer(const Json&);
// Returns this process's freed memory to the system where the allocator
// keeps it (mimalloc, or glibc's malloc).
void release_memory();
// RSS and PSS of a live process in KiB (smaps_rollup); false once it is gone.
bool memory_rollup(int pid, std::uint64_t& rss_kib, std::uint64_t& pss_kib);
// This process's resident size in bytes (statm), and its peak (VmHWM).
std::uint64_t own_rss();
std::uint64_t peak_rss();
// The command line, parsed and run: stp-p's, or with `testing` the stpp-drive
// driver's, which also takes the measurement options, the test controls and
// the transport settings.
int run(int argc, char** argv, bool testing);
// The owner's work: runs the route on the query (it takes the source from
// the options). Each route parses the source with STP's single-query mode
// and releases it (parse_query), then decides on the logic it read; the race
// releases its copy once its sides are forked.
Json execute(Options);
Json ordinary(Source&, const Options&);
Json retained(Source&, const Options&);
// The hedge's check of a solver that holds the query (the incremental
// driver from the first check, one plain check, no assumptions), as a
// report.
Json hedge_check(stp::Solver&, const Options&, const std::string& logic);
Json race(Source&, const Options&);
Json batch_group(Source&, const Options&);
int supervise(const Options&);
} // namespace stpp

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
// The command line of stp-p, and of the test driver (stpp-drive), which
// accepts the same options plus the measurement options, test controls and
// transport settings that stp-p does not offer. One CLI11 app: the options'
// ranges are its validators, and a parse error is exit 2 with its message.
#include "Common.h"
#include "Portfolio.h"
#include <CLI/CLI.hpp>
#include <cmath>
#include <cstdint>
#include <algorithm>
#include <iostream>
#include <stdexcept>

namespace stpp
{
namespace
{
// A whole number in decimal digits and nothing else (no sign, no exponent,
// no prefix), read in base 10: leading zeros go before CLI11 converts it,
// which would otherwise read 010 as octal.
const CLI::Validator digits(
    [](std::string& value)
    {
      if (value.empty() ||
          value.find_first_not_of("0123456789") != std::string::npos)
        return std::string("must be a whole number written in decimal digits");
      value.erase(0, std::min(value.find_first_not_of('0'), value.size() - 1));
      return std::string();
    },
    "DIGITS", "digits");
const CLI::Validator finite_seconds(
    [](std::string& value)
    {
      try
      {
        std::size_t used = 0;
        const double t = std::stod(value, &used);
        if (used == value.size() && std::isfinite(t) && t >= 0 && t <= 1e9)
          return std::string();
      }
      catch (const std::exception&)
      {
      }
      return std::string("must be a number of seconds in 0..1e9");
    },
    "SECONDS", "seconds");
const CLI::Validator mebibytes(
    [](std::string& value)
    {
      try
      {
        if (std::stoull(value) <= UINT64_MAX / (1024 * 1024))
          return std::string();
      }
      catch (const std::exception&)
      {
      }
      return std::string("is too large: the limit in bytes overflows");
    },
    "MIB", "mebibytes");
const CLI::Validator not_empty(
    [](std::string& value)
    { return value.empty() ? std::string("must not be empty") : std::string(); },
    "PATH", "path");
// The driver's faults (Options::inject), comma-separated.
const CLI::Validator faults(
    [](std::string& value)
    {
      for (std::size_t at = 0; at <= value.size();)
      {
        auto comma = value.find(',', at);
        if (comma == std::string::npos)
          comma = value.size();
        const auto item = value.substr(at, comma - at);
        const auto colon = item.find(':');
        auto slot = [](const std::string& s)
        { return !s.empty() && s.find_first_not_of("0123456789") == std::string::npos; };
        const bool known =
            item == "hold-hedge" || item == "fail-root-setup" ||
            item == "fork-fails" || item == "linger" || item == "contradict" ||
            item == "cut-report" ||
            (item.rfind("hold-root=", 0) == 0 && slot(item.substr(10))) ||
            (item.rfind("wrong-root=", 0) == 0 && colon != std::string::npos &&
             slot(item.substr(11, colon - 11)) &&
             (item.substr(colon + 1) == "sat" || item.substr(colon + 1) == "unsat"));
        if (!known)
          return std::string("takes wrong-root=SLOT:sat|unsat, hold-root=SLOT, "
                             "hold-hedge, fail-root-setup, fork-fails, linger, "
                             "contradict and cut-report");
        at = comma + 1;
      }
      return std::string();
    },
    "FAULT,...", "faults");
std::vector<std::string> config_names(bool testing)
{
  std::vector<std::string> names;
  for (const auto& c : configs())
    if (testing || c.product)
      names.push_back(c.name);
  return names;
}
void list_configs()
{
  for (const auto& c : configs())
  {
    std::cout << c.name << '\t'
              << (c.route == Config::Route::Retained ? "retained" : "batch");
    for (const auto& [name, value] : c.options)
      std::cout << ' ' << name << '=' << value;
    if (c.seed_offset)
      std::cout << " random-seed+=" << c.seed_offset;
    std::cout << '\t' << c.summary << (c.product ? "" : " (driver only)") << '\n';
  }
}
} // namespace

int run(int argc, char** argv, bool testing)
{
  const double started = now();
  Options o;
  CLI::App app("stp-p: STP's parallel decision solver", "stp-p");
  app.set_help_flag("--help", "Print this help and exit");
  app.set_version_flag("--version",
                       []
                       {
                         const auto v = stp::version();
                         return "stp-p (STP " + std::string(v.string) + "; " +
                                v.git_sha + ")";
                       });
  app.footer(
      "One decision-only nonincremental query: QF_BV, QF_ABV, QF_FP, QF_BVFP or\n"
      "QF_ABVFP, or one with no set-logic, which is admitted whatever it holds;\n"
      "read as one query by STP's parser. stdin is read when the input\n"
      "is absent or -, and must not be a terminal. The input may be at most\n"
      "--worker-memory-mib (16384 with 0).\n"
      "Exit: sat 10, unsat 20, unknown 0, errors 2, SIGINT 130, SIGTERM 143\n"
      "(stp's own are 0 and 255: these tell the answer apart without its line).");
  unsigned jobs = 1;
  std::uint64_t seed = 0;
  auto* jobs_option =
      app.add_option("-j,--jobs", jobs,
                     "N > 1: the clause-sharing group on N CPUs, holding N copies of "
                     "the loaded solver (--worker-memory-mib bounds each, "
                     "--memory-mib their sum); 1: ordinary STP's pipeline through "
                     "its API, without models. Default: the allowed CPUs, at most 8 "
                     "(1 on a build without the clause-import extension)")
          ->transform(digits)
          ->check(CLI::Range(1u, 4096u));
  auto* seed_option =
      app.add_option("--random-seed", seed,
                     "The native seed of ordinary STP, of the hedge and of root 0; "
                     "root i > 0 takes N + i (mod 2*10^9, CaDiCaL's seed range)")
          ->transform(digits)
          ->check(CLI::Range(std::uint64_t(0), std::uint64_t(UINT32_MAX)));
  app.add_option("--timeout", o.timeout,
                 "Whole invocation wall deadline in seconds; 0 unlimited")
      ->check(finite_seconds);
  app.add_option("--worker-memory-mib", o.worker_mib,
                 "Per-process address space; default 16384, 0 inherited")
      ->transform(digits)
      ->check(mebibytes);
  app.add_option("--memory-mib", o.memory_mib,
                 "Guard on the invocation's summed memory (PSS); default 0, none")
      ->transform(digits)
      ->check(mebibytes);
  app.add_option("--config", o.config,
                 testing ? "Any entry of --list-configs"
                         : "default (ordinary STP) or eager-arrays (eager array-read "
                           "axioms): the -j1 route, or the group's base (an equality "
                           "of floating-point or constant arrays still refines)")
      ->check(CLI::IsMember(config_names(testing)));
  app.add_option("--stats-json", o.stats, "Write bounded answer-support statistics")
      ->check(not_empty);
  app.add_option("input", o.input, "The query, a file or - for stdin")
      ->option_text("[input.smt2|-]");

  // The test driver's options (stpp-drive): never offered by stp-p.
  bool list = false;
  std::string portfolio, root0, sharing;
  CLI::Option* hedge = nullptr;
  CLI::Option* budget = nullptr;
  CLI::Option* root0_option = nullptr;
  if (testing)
  {
    const std::string driver = "Test driver only";
    app.add_flag("--list-configs", list, "Print the configuration table")->group(driver);
    app.add_option("--portfolio", portfolio,
                   "Race one single-CPU side per configuration (-j is their number)")
        ->group(driver);
    hedge = app.add_option("--hedge", o.hedge, "The group's hedge (default) or none")
                ->check(CLI::IsMember({"retained", "none"}))
                ->group(driver);
    budget = app.add_option("--import-budget", o.import_budget,
                            "Clauses of two or more literals imported per own "
                            "conflict, shortest first (default 1)")
                 ->transform(digits)
                 ->check(CLI::Range(1u, 4096u))
                 ->group(driver);
    root0_option = app.add_option("--root0-import", root0, "Root 0 imports (off)")
                       ->check(CLI::IsMember({"on", "off"}))
                       ->group(driver);
    app.add_option("--clause-sharing", sharing, "The group's rings (on)")
        ->check(CLI::IsMember({"on", "off"}))
        ->group(driver);
    const auto transport = CLI::Range(std::uint64_t(1), std::uint64_t(1) << 30);
    app.add_option("--exchange-interval", o.exchange_interval,
                   "Own conflicts between imports")
        ->transform(digits)
        ->check(transport)
        ->group(driver);
    app.add_option("--exchange-size", o.exchange_size, "Longest clause exported")
        ->transform(digits)
        ->check(CLI::Range(1u, 64u))
        ->group(driver);
    app.add_option("--exchange-ring", o.ring_literals, "Literals per ring")
        ->transform(digits)
        ->check(CLI::Range(std::uint64_t(64), std::uint64_t(1) << 30))
        ->group(driver);
    app.add_option("--import-window", o.import_window,
                   "Newest literals of each ring a poll scans")
        ->transform(digits)
        ->check(transport)
        ->group(driver);
    app.add_flag("--pin", o.pin, "Bind each root and side to one allowed CPU")
        ->group(driver);
    app.add_option("--control", o.control, "batch-handoff or batch-all")
        ->check(CLI::IsMember({"batch-handoff", "batch-all"}))
        ->group(driver);
    app.add_option("--inject", o.inject, "Faults the tests need")
        ->check(faults)
        ->group(driver);
  }
  try
  {
    app.parse(argc, argv);
  }
  catch (const CLI::ParseError& e)
  {
    if (e.get_exit_code() == 0) // --help, --version
      return app.exit(e, std::cout, std::cerr);
    // Some of CLI11's messages name the program already.
    const std::string what = e.what();
    std::cerr << (what.rfind("stp-p: ", 0) == 0 ? "" : "stp-p: ") << what << '\n';
    return 2;
  }
  try
  {
    if (list)
    {
      list_configs();
      return 0;
    }
    o.jobs = jobs_option->count() ? jobs : default_jobs();
    if (seed_option->count())
      o.seed = seed;
    if (!portfolio.empty())
      o.portfolio = portfolio_list(portfolio);
    if (!root0.empty())
      o.root0_import = root0 == "on";
    if (!sharing.empty())
      o.sharing = sharing == "on";
    const bool group_flags = (hedge && hedge->count()) ||
                             (budget && budget->count()) ||
                             (root0_option && root0_option->count());
    if (!o.portfolio.empty())
    {
      if (o.jobs != o.portfolio.size() || o.jobs < 2)
        throw std::runtime_error(
            "--portfolio needs at least two configurations and -j equal to "
            "their number");
      if (group_flags || !o.control.empty())
        throw std::runtime_error(
            "--hedge, --import-budget and --root0-import belong to the "
            "group, not to --portfolio");
      if (o.config != "default")
        throw std::runtime_error("--config and --portfolio are exclusive");
    }
    else if (o.jobs > 1 || !o.control.empty())
    {
      // The group. The hedge takes one CPU; every other is a batch root.
      const unsigned hedges = o.hedge == "none" ? 0 : 1;
      if (o.control.empty() && o.jobs <= hedges)
        throw std::runtime_error("the group needs -j greater than its hedge");
      o.roots = o.jobs - (o.control.empty() ? hedges : 0);
      if (!o.control.empty())
        o.hedge = "none";
      if (config(o.config).route != Config::Route::Batch)
        throw std::runtime_error(
            "the group's base must be an ordinary-route configuration");
      // The group needs CaDiCaL with STP's clause-import extension.
      if (stp::capabilities()["sat.clause-exchange"] != "true")
        throw std::runtime_error(
            "-j greater than 1 needs a CaDiCaL with STP's clause-import "
            "extension (this build's sat.clause-exchange capability is "
            "false); -j1 still works");
    }
    else if (group_flags)
      throw std::runtime_error(
          "--hedge, --import-budget and --root0-import need -j greater "
          "than 1");
    // A ring holds at least two of the longest clauses with their ends.
    if (o.ring_literals < 2 * (std::uint64_t(o.exchange_size) + 1))
      throw std::runtime_error("--exchange-ring must hold two clauses of "
                               "--exchange-size literals and their ends: at "
                               "least " +
                               std::to_string(2 * (o.exchange_size + 1)));
    // A poll's clauses are kept at 32-bit offsets: one poll scans at most a
    // window from every other root's ring.
    if (std::uint64_t(o.import_window) * (o.jobs ? o.jobs - 1 : 0) >=
        (std::uint64_t(1) << 32))
      throw std::runtime_error("--import-window times the other roots must "
                               "stay below 2^32 literals");
    if (o.jobs > allowed_cpus().size())
      throw std::runtime_error("requested jobs exceed allowed CPU slots");
    o.deadline = o.timeout ? started + o.timeout : 0;
    return supervise(o);
  }
  catch (const std::exception& e)
  {
    std::cerr << "stp-p: " << e.what() << '\n';
    return 2;
  }
}
} // namespace stpp

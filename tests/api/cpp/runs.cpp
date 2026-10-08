/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// runs.cpp -- an input run as the stp command line runs it: the parse
// modes that answer (EXECUTE, PARSE_ONLY), a stream as the input, the
// output, diagnostic and CNF sinks, the fatal error handler, an input
// printed back, the run that ends at its first CNF, and the refusals the
// solver makes of options once they are applied.

#include "api_common.hpp"

#include <algorithm>
#include <chrono>
#include <ios>
#include <sstream>
#include <stdexcept>
#include <streambuf>
#include <thread>
#include <utility>
#include <vector>

using namespace stp;
using namespace std::chrono_literals;

namespace
{

// Everything a solver says, by channel.
struct Heard
{
  std::string out, err, fatal;
  std::size_t flushes = 0;
  std::vector<std::pair<std::string, CnfScope>> cnfs;

  void attach(Solver& s)
  {
    s.set_output_sink([this](std::string_view c) {
      if (c.empty())
        ++flushes;
      out.append(c);
    });
    s.set_diagnostic_sink([this](std::string_view c) { err.append(c); });
    s.set_fatal_error_handler([this](std::string_view m) { fatal.append(m); });
    s.set_cnf_sink([this](std::string_view d, CnfScope scope) {
      cnfs.emplace_back(std::string(d), scope);
    });
  }
};

// A factoring query that preprocessing leaves to the SAT solver.
const char* const kNeedsCnf = "(declare-fun a () (_ BitVec 8))\n"
                              "(declare-fun b () (_ BitVec 8))\n"
                              "(assert (= (bvmul a b) #x0f))\n"
                              "(assert (bvugt a #x01))\n"
                              "(assert (bvugt b #x01))\n";

// api_test::add_hard_factoring's query as a script.
const char* const kHard = "(declare-fun hard_a () (_ BitVec 96))\n"
                          "(declare-fun hard_b () (_ BitVec 96))\n"
                          "(assert (= (bvmul hard_a hard_b) (_ bv486579698794948075013401 96)))\n"
                          "(assert (bvugt hard_a (_ bv1 96)))\n"
                          "(assert (bvugt hard_b (_ bv1 96)))\n"
                          "(assert (bvult hard_a (_ bv1099511627776 96)))\n"
                          "(assert (bvult hard_b (_ bv1099511627776 96)))\n"
                          "(assert (bvule hard_a hard_b))\n";

// A stream buffer that hands out one line per refill and records what the
// solver had said by the time each line was asked for.
class LineFeed final : public std::streambuf
{
public:
  LineFeed(std::vector<std::string> lines, const std::string& said)
      : lines_(std::move(lines)), said_(said)
  {
  }
  std::vector<std::string> said_before; // before line i was handed out

protected:
  int_type underflow() override
  {
    if (gptr() < egptr())
      return traits_type::to_int_type(*gptr());
    if (next_ == lines_.size())
      return traits_type::eof();
    said_before.push_back(said_);
    current_ = lines_[next_++];
    setg(&current_[0], &current_[0], &current_[0] + current_.size());
    return traits_type::to_int_type(*gptr());
  }

private:
  std::vector<std::string> lines_;
  const std::string& said_;
  std::string current_;
  std::size_t next_ = 0;
};

// A stream buffer that gives out `text` and then fails.
class FailingFeed final : public std::streambuf
{
public:
  explicit FailingFeed(std::string text) : text_(std::move(text)) {}

protected:
  int_type underflow() override
  {
    if (gptr() < egptr())
      return traits_type::to_int_type(*gptr());
    if (given_)
      throw std::ios_base::failure("the device went away");
    given_ = true;
    setg(&text_[0], &text_[0], &text_[0] + text_.size());
    return traits_type::to_int_type(*gptr());
  }

private:
  std::string text_;
  bool given_ = false;
};

} // namespace

TEST(Runs, execute_warns_when_an_answer_contradicts_the_status)
{
  const std::string script = "(set-logic QF_BV)\n(declare-fun x () (_ BitVec 8))\n"
                             "(assert (= x #x05))\n(assert (= x #x06))\n(check-sat)\n";
  TermManager tm;
  Solver s(tm);
  Heard h;
  h.attach(s);
  s.parse_smt2("(set-info :status unsat)\n" + script, ParseMode::EXECUTE);
  EXPECT_EQ(h.out, "unsat\n");
  EXPECT_EQ(h.err, "");
  // the input's check leaves no result or model behind; its assertions stay
  API_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
  EXPECT_FALSE(s.assertions().empty());
  EXPECT_TRUE(s.check_sat().is_unsat());
  // a :status the answer contradicts is a warning on the diagnostic channel
  TermManager t2;
  Solver s2(t2);
  Heard h2;
  h2.attach(s2);
  s2.parse_smt2("(set-info :status sat)\n" + script, ParseMode::EXECUTE);
  EXPECT_EQ(h2.out, "unsat\n");
  EXPECT_NE(h2.err.find("Warning. Expected satisfiable, FOUND unsatisfiable"), std::string::npos)
      << h2.err;
}

TEST(Runs, script_channels_preserve_and_restore_the_callers_sinks)
{
  TermManager tm;
  Solver s(tm);
  Heard h;
  h.attach(s);
  s.parse_smt2(R"(
    (set-option :regular-output-channel "stderr")
    (echo "diagnostic")
    (reset)
    (echo "regular")
  )", ParseMode::EXECUTE);
  EXPECT_EQ(h.out, "\"regular\"\n");
  EXPECT_EQ(h.err, "\"diagnostic\"\n");

  h.out.clear();
  h.err.clear();
  s.parse_smt2(R"(
    (set-option :diagnostic-output-channel "stdout")
    (set-logic QF_BV)
    (set-info :status unsat)
    (check-sat)
  )", ParseMode::EXECUTE);
  EXPECT_NE(h.out.find("Warning. Expected unsatisfiable"), std::string::npos);
  EXPECT_TRUE(h.err.empty());

  h.out.clear();
  s.parse_smt2("(echo \"next script\")", ParseMode::EXECUTE);
  EXPECT_EQ(h.out, "\"next script\"\n");
}

TEST(Runs, execute_runs_a_script_under_its_own_logic)
{
  // EXECUTE answers every command, and PARSE_ONLY every command but the
  // check; the process's stdout hears nothing of either
  for (const ParseMode mode : {ParseMode::EXECUTE, ParseMode::PARSE_ONLY})
  {
    TermManager tm;
    Solver s(tm);
    Heard h;
    h.attach(s);
    testing::internal::CaptureStdout();
    s.parse_smt2("(declare-fun a () (_ BitVec 8))\n(assert (= a #x2a))\n(check-sat)\n"
                 "(echo \"after\")\n",
                 mode);
    EXPECT_TRUE(testing::internal::GetCapturedStdout().empty());
    EXPECT_EQ(h.out, mode == ParseMode::EXECUTE ? "sat\n\"after\"\n" : "\"after\"\n");
    // an answer is flushed as it is given
    if (mode == ParseMode::EXECUTE)
    {
      EXPECT_GT(h.flushes, 0u);
    }
    EXPECT_EQ(s.assertions().size(), 1u);
  }
  // a function with arguments is refused under a logic without them, as the
  // command line reads the script; the API's own reading takes it whatever
  // the logic line says
  const std::string script = "(set-logic QF_BV)\n(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\n"
                             "(assert (= (f #x01) #x02))\n(check-sat)\n";
  TermManager tm;
  Solver s(tm);
  Heard h;
  h.attach(s);
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse_smt2(script, ParseMode::EXECUTE));
  EXPECT_EQ(h.out.rfind("(error \"syntax error", 0), 0u) << h.out;
  EXPECT_TRUE(s.assertions().empty());
  TermManager t2;
  Solver s2(t2);
  s2.parse_smt2(script);
  EXPECT_EQ(s2.assertions().size(), 1u);
}

TEST(Runs, a_stream_is_parsed_as_it_arrives)
{
  TermManager tm;
  Solver s(tm);
  Heard h;
  h.attach(s);
  LineFeed feed({"(declare-fun a () Bool)\n", "(assert a)\n", "(check-sat)\n",
                 "(assert (not a))\n", "(check-sat)\n"},
                h.out);
  std::istream in(&feed);
  s.parse(in, Format::AUTO, ParseMode::EXECUTE);
  EXPECT_EQ(h.out, "sat\nunsat\n");
  // the first check was answered before the fourth line was asked for
  ASSERT_EQ(feed.said_before.size(), 5u);
  EXPECT_EQ(feed.said_before[3], "sat\n");
}

TEST(Runs, a_stream_that_fails_fails_the_parse)
{
  TermManager tm;
  Solver s(tm);
  FailingFeed feed("(declare-fun a () Bool)\n(assert a)\n");
  std::istream in(&feed);
  API_EXPECT_ERROR(ErrorCode::IO, s.parse(in, Format::SMTLIB2, ParseMode::EXECUTE));
  // the parse ended there, with the stack as it was
  EXPECT_TRUE(s.assertions().empty());
  // not a language, or not a mode
  std::istringstream text("(check-sat)");
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s.parse(text, Format::DOT));
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT,
                   s.parse(text, Format::SMTLIB2, static_cast<ParseMode>(7)));
}

TEST(Runs, the_engine_prints_nowhere_but_the_sinks)
{
  TermManager tm;
  Options o;
  o.set("print-functionstat", "true");
  o.set("print-quickstat", "true");
  Solver s(tm, o);
  const Term a = tm.declare("a", tm.mk_bv_sort(8)), b = tm.declare("b", tm.mk_bv_sort(8));
  s.add(bvmul(a, b) == 15);
  s.add(bvugt(a, 1));
  s.add(bvugt(b, 1));
  // What STP prints reaches no stream without a sink. A SAT backend's own
  // report, which print-functionstat switches on, is the backend's:
  // CryptoMiniSat writes it with std::cout, which the sinks see, and CaDiCaL
  // and MiniSat to standard output themselves.
  const auto stdout_is_quiet = [&s](const std::string& out) {
    EXPECT_EQ(out.find("Node size is"), std::string::npos) << out;
    if (s.statistics().str("sat.backend") == "cryptominisat")
    {
      EXPECT_EQ(out, "");
    }
  };
  testing::internal::CaptureStdout();
  testing::internal::CaptureStderr();
  EXPECT_TRUE(s.check_sat().is_sat());
  stdout_is_quiet(testing::internal::GetCapturedStdout());
  EXPECT_EQ(testing::internal::GetCapturedStderr(), "");
  Heard h;
  h.attach(s);
  testing::internal::CaptureStdout();
  testing::internal::CaptureStderr();
  EXPECT_TRUE(s.check_sat().is_sat());
  stdout_is_quiet(testing::internal::GetCapturedStdout());
  EXPECT_EQ(testing::internal::GetCapturedStderr(), "");
  // The statistics the options asked for, on the diagnostic channel -- all of
  // them. The per-pass node sizes used to arrive on the regular channel, which
  // for the SMT-LIB frontend is the one that carries command responses, so a
  // (get-model) came back with them interleaved. They are diagnostics, so they
  // go where "Difficulty Initially" already went.
  EXPECT_NE(h.err.find("Difficulty Initially"), std::string::npos) << h.err;
  EXPECT_NE(h.err.find("Node size is"), std::string::npos) << h.err;
  EXPECT_EQ(h.out.find("Node size is"), std::string::npos) << h.out;
  // a sink that writes to the process's streams itself reaches them
  s.set_diagnostic_sink([](std::string_view c) { std::cerr << c; });
  testing::internal::CaptureStderr();
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_NE(testing::internal::GetCapturedStderr().find("Difficulty Initially"), std::string::npos);
}

// An application that redirects std::cout after the library first ran --
// a scoped redirection -- keeps its redirection for its own writes, and the
// engine's output still reaches the solver's sink: it used to reach the
// application's buffer instead.
TEST(Runs, the_sinks_survive_a_redirected_stdout)
{
  TermManager tm;
  Solver s(tm);
  std::string sink;
  s.set_output_sink([&](std::string_view text) { sink.append(text); });
  std::ostringstream captured;
  std::streambuf* const saved = std::cout.rdbuf(captured.rdbuf());
  s.parse_smt2("(set-logic QF_BV)(declare-fun x () (_ BitVec 8))(assert (= x #xc8))(check-sat)",
               ParseMode::EXECUTE);
  std::cout << "the application's own line\n";
  std::cout.rdbuf(saved);
  EXPECT_EQ(sink, "sat\n");
  EXPECT_EQ(captured.str(), "the application's own line\n");
}

// end-after-cnf ends a run at a check's first CNF. A check-sat-assuming's
// frame comes off even so: the assumptions used to stay asserted on a level
// of their own, and a later check against them answered unsat wrongly.
TEST(Runs, a_run_ended_in_check_sat_assuming_keeps_no_assumptions)
{
  TermManager tm;
  Options o;
  o.set_bool("end-after-cnf", true);
  Solver s(tm, o);
  s.parse_smt2("(set-logic QF_BV)(declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))"
               "(assert (= (bvmul x y) #x8f))(check-sat-assuming ((bvugt x #x05)))",
               ParseMode::EXECUTE);
  EXPECT_EQ(s.level(), 0u);
  EXPECT_EQ(s.assertions().size(), 1u);
  s.options().set_bool("end-after-cnf", false);
  s.add(bvule(*tm.symbol("x"), tm.mk_bv(8, 5))); // x = 1, y = #x8f
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST(Runs, every_cnf_reaches_the_cnf_sink)
{
  TermManager tm;
  Solver s(tm);
  Heard h;
  h.attach(s);
  s.parse_smt2(kNeedsCnf);
  EXPECT_TRUE(s.check_sat().is_sat());
  ASSERT_FALSE(h.cnfs.empty());
  EXPECT_NE(h.cnfs[0].first.find("\np cnf "), std::string::npos) << h.cnfs[0].first.substr(0, 80);
  EXPECT_EQ(h.cnfs[0].second, CnfScope::WHOLE);
  // none without a sink
  s.set_cnf_sink(nullptr);
  const std::size_t seen = h.cnfs.size();
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(h.cnfs.size(), seen);
}

TEST(Runs, end_after_cnf_ends_the_run_at_the_first_cnf)
{
  // a check stops there, unknown
  {
    TermManager tm;
    Options o;
    o.set_bool("end-after-cnf", true);
    Solver s(tm, o);
    Heard h;
    h.attach(s);
    s.parse_smt2(kNeedsCnf);
    const Result r = s.check_sat();
    EXPECT_TRUE(r.is_unknown());
    EXPECT_EQ(r.reason(), UnknownReason::STOPPED_AFTER_CNF);
    EXPECT_EQ(h.cnfs.size(), 1u);
    EXPECT_EQ(h.out, "");
    // the next check starts afresh, and stops at its own first CNF
    EXPECT_TRUE(s.check_sat().is_unknown());
    EXPECT_EQ(h.cnfs.size(), 2u);
    s.options().set_bool("end-after-cnf", false);
    EXPECT_TRUE(s.check_sat().is_sat());
  }
  // an executed script ends there, having said nothing more
  {
    TermManager tm;
    Options o;
    o.set_bool("end-after-cnf", true);
    Solver s(tm, o);
    Heard h;
    h.attach(s);
    s.parse_smt2(std::string(kNeedsCnf) + "(check-sat)\n(echo \"not reached\")\n",
                 ParseMode::EXECUTE);
    EXPECT_EQ(h.out, "");
    EXPECT_EQ(h.cnfs.size(), 1u);
  }
  // an input that never reaches a CNF runs to its end
  {
    TermManager tm;
    Options o;
    o.set_bool("end-after-cnf", true);
    Solver s(tm, o);
    Heard h;
    h.attach(s);
    s.parse_smt2("(declare-fun c () Bool)\n(assert c)\n(check-sat)\n(echo \"reached\")\n",
                 ParseMode::EXECUTE);
    EXPECT_EQ(h.out, "sat\n\"reached\"\n");
    EXPECT_TRUE(h.cnfs.empty());
  }
}

TEST(Runs, the_fatal_error_handler_hears_first)
{
  TermManager tm;
  Solver s(tm);
  Heard h;
  h.attach(s);
  std::istringstream in("(declare-fun x () (_ BitVec 0))\n");
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse(in, Format::SMTLIB2, ParseMode::EXECUTE));
  EXPECT_NE(h.fatal.find("bit-vectors must be of positive length"), std::string::npos) << h.fatal;
  EXPECT_NE(h.err.find("Fatal Error: " + h.fatal + "\n"), std::string::npos) << h.err;
  // the solver is as it was
  EXPECT_TRUE(s.assertions().empty());
  EXPECT_TRUE(s.check_sat().is_sat());
  // a syntax error is no fatal error
  Heard h2;
  h2.attach(s);
  std::istringstream unknown("(declare-fun a () Bool)\n(assert (foo a))\n");
  API_EXPECT_ERROR(ErrorCode::PARSE, s.parse(unknown, Format::SMTLIB2, ParseMode::EXECUTE));
  EXPECT_EQ(h2.fatal, "");
}

TEST(Runs, the_solver_refuses_what_the_applied_options_cannot_honour)
{
  TermManager tm;
  if (has_sat_backend("cadical") && has_sat_backend("cryptominisat"))
  {
    Options o;
    o.set("sat-backend", "cryptominisat");
    o.set_int("cadical-elim", 1);
    const std::optional<RecoverableError> e = API_ERROR_OF(Solver(tm, o));
    ASSERT_TRUE(e.has_value());
    EXPECT_EQ(e->code(), ErrorCode::OPTION_CONFLICT) << e->what();
    EXPECT_EQ(e->option(), "cadical-elim");
    EXPECT_NE(std::string(e->what()).find("require the CaDiCaL backend"), std::string::npos)
        << e->what();
  }
  Options o;
  o.set_bool("lra-decision-polarity", true);
  o.set_bool("lra-theory-propagation", false);
  const std::optional<RecoverableError> e = API_ERROR_OF(Solver(tm, o));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::OPTION_CONFLICT) << e->what();
  EXPECT_EQ(e->option(), "lra-decision-polarity");
  // set on a live solver, the check is what refuses it, and changes nothing
  Solver s(tm);
  s.options().set_bool("lra-theory-propagation", false);
  s.options().set_bool("lra-decision-polarity", true);
  API_EXPECT_ERROR(ErrorCode::OPTION_CONFLICT, s.check_sat());
  s.options().reset("lra-decision-polarity");
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST(Runs, the_sat_versions_are_listed_in_the_builds_order)
{
  const std::map<std::string, std::string> c = capabilities();
  ASSERT_TRUE(c.count("sat.versions"));
  const std::string versions = c.at("sat.versions");
  for (const char* backend : {"cadical", "cryptominisat"})
  {
    const auto it = c.find(std::string("sat.backend.") + backend + ".version");
    if (it != c.end())
    {
      EXPECT_NE(versions.find(backend + (" " + it->second)), std::string::npos) << versions;
    }
  }
}

// A check the input runs answers interrupt() as check_sat does: it stops, the
// run goes on (the script's answer is unknown), and the interrupt is consumed.
// Such a check ran on regardless and left the interrupt pending, so the next,
// unrelated check answered unknown at once.
TEST(Runs, interrupt_reaches_a_check_the_script_runs)
{
  const std::optional<std::string> backend = api_test::interruptible_backend();
  if (!backend)
    GTEST_SKIP() << "no backend of this build can be interrupted mid-search";
  TermManager tm;
  Options o;
  o.set_str("sat-backend", *backend);
  Solver s(tm, o);
  Heard heard;
  heard.attach(s);
  std::thread stopper([&s] {
    std::this_thread::sleep_for(300ms);
    s.interrupt();
  });
  const auto start = std::chrono::steady_clock::now();
  s.parse_smt2(std::string(kHard) + "(check-sat)\n", ParseMode::EXECUTE);
  const auto elapsed = std::chrono::steady_clock::now() - start;
  stopper.join();
  EXPECT_LT(elapsed, 10s);
  EXPECT_EQ(heard.out, "unknown\n");
  EXPECT_FALSE(s.interrupt_pending());
  // the next check is not interrupted (its budget is what stops it)
  EXPECT_EQ(s.check_sat({}, CheckBudget{0ms, std::nullopt}).reason(), UnknownReason::TIMEOUT);

  // pending before the run: its first check answers unknown, the rest are
  // answered; a run with no check leaves it for the next check
  TermManager t2;
  Solver quick(t2);
  Heard said;
  said.attach(quick);
  quick.interrupt();
  quick.parse_smt2("(declare-fun x () (_ BitVec 8)) (assert (= x #x01)) (check-sat) (check-sat)",
                   ParseMode::EXECUTE);
  EXPECT_EQ(said.out, "unknown\nsat\n");
  EXPECT_FALSE(quick.interrupt_pending());
  quick.interrupt();
  quick.parse_smt2("(declare-fun y () (_ BitVec 8))", ParseMode::EXECUTE);
  EXPECT_TRUE(quick.interrupt_pending());
  EXPECT_EQ(quick.check_sat().reason(), UnknownReason::INTERRUPTED);
  EXPECT_FALSE(quick.interrupt_pending());
}

// An interrupt requested while an answer is written -- from the output sink,
// which may call interrupt() -- is the next check's, and a check that begins
// with one pending answers at once, solving nothing: so a sink can end a run
// of many checks by interrupting at every answer.
TEST(Runs, an_interrupt_from_the_output_sink_is_the_next_checks)
{
  TermManager tm;
  Solver s(tm);
  std::string out;
  s.set_output_sink([&](std::string_view text) {
    out += text;
    if (std::count(out.begin(), out.end(), '\n') >= 2) // two answers out
      s.interrupt();
  });
  std::string script = "(declare-fun a () (_ BitVec 16))(declare-fun b () (_ BitVec 16))\n";
  for (int i = 0; i < 200; ++i)
    script += "(push 1)(assert (= (bvmul ((_ zero_extend 16) a) ((_ zero_extend 16) b)) (_ bv" +
              std::to_string(1000003 + 2 * i) +
              " 32)))(assert (bvugt a #x0001))(assert (bvugt b #x0001))(check-sat)(pop 1)\n";
  const auto start = std::chrono::steady_clock::now();
  s.parse_smt2(script, ParseMode::EXECUTE);
  EXPECT_LT(std::chrono::steady_clock::now() - start, 20s);
  // two answered, then the interrupt each answer requests is the next check's
  ASSERT_EQ(std::count(out.begin(), out.end(), '\n'), 200) << out;
  const std::size_t third = out.find('\n', out.find('\n') + 1) + 1;
  EXPECT_EQ(out.find("unknown"), third) << out;
  std::string rest;
  for (int i = 2; i < 200; ++i)
    rest += "unknown\n";
  EXPECT_EQ(out.substr(third), rest);
  EXPECT_TRUE(s.interrupt_pending()); // the last answer's request, for the next check
  s.clear_interrupt();
}

// An exception out of a check the input runs -- here the terminator's, which
// that check now polls -- is an engine failure like any other: INTERNAL, the
// manager poisoned. The parse's timer bracket had already been closed by the
// check, and closing it again crashed.
TEST(Runs, an_exception_in_a_check_the_script_runs_is_internal)
{
  struct Thrower : Terminator
  {
    bool terminate() override { throw std::runtime_error("the terminator threw"); }
  } thrower;
  TermManager tm;
  Solver s(tm);
  s.set_terminator(&thrower);
  try
  {
    s.parse_smt2(std::string(kNeedsCnf) + "(check-sat)\n", ParseMode::EXECUTE);
    ADD_FAILURE() << "the parse returned";
  }
  catch (const UnsafeError& failure)
  {
    EXPECT_EQ(failure.code(), ErrorCode::INTERNAL);
    EXPECT_NE(std::string(failure.what()).find("the terminator threw"), std::string::npos)
        << failure.what();
  }
  API_EXPECT_ERROR(ErrorCode::STATE, s.check_sat());
}

// A callback must not call the library. A sink that pushed tripped an assertion
// in the frontend part way through its check-sat, and one that parsed
// deadlocked on the parser lock; every call from a callback is now refused with
// STATE, but interrupt(), clear_interrupt() and interrupt_pending().
TEST(Runs, a_callback_that_calls_the_library_is_refused)
{
  for (const std::string what : {"push", "parse", "check", "declare", "interrupt"})
  {
    TermManager tm;
    Solver s(tm);
    std::optional<ErrorCode> refused;
    bool called = false;
    s.set_output_sink([&](std::string_view text) {
      if (text.empty() || called)
        return;
      called = true;
      try
      {
        if (what == "push")
          s.push();
        else if (what == "parse")
          s.parse_smt2("(declare-fun z () (_ BitVec 8))");
        else if (what == "check")
          (void)s.check_sat();
        else if (what == "declare")
          (void)tm.declare("w", tm.mk_bv_sort(8));
        else
        {
          s.interrupt();
          s.clear_interrupt();
          (void)s.interrupt_pending();
        }
      }
      catch (const RecoverableError& e)
      {
        refused = e.code();
      }
    });
    s.parse_smt2("(declare-fun x () (_ BitVec 8)) (assert (= x #x01)) (check-sat)", ParseMode::EXECUTE);
    EXPECT_TRUE(called) << what;
    if (what == "interrupt")
      EXPECT_FALSE(refused.has_value());
    else
    {
      ASSERT_TRUE(refused.has_value()) << what;
      EXPECT_EQ(*refused, ErrorCode::STATE) << what;
    }
    // the solver goes on
    EXPECT_EQ(s.level(), 0u) << what;
    EXPECT_TRUE(s.check_sat().is_sat()) << what;
  }
}

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

// before-search.cpp -- Solver::set_before_search: a hook for the next check,
// which runs at most once, at the moment the check's SAT backend, with its
// CNF loaded, would start to search. It may let the check search, abandon
// it, connect a clause exchange or diversify the search through its
// SearchPoint, and a process may fork there: every copy holds the loaded
// backend.

#include "api_common.hpp"

#include <climits>
#include <cstdlib>
#include <sstream>
#include <string>
#include <vector>

#ifdef __linux__
#include <sys/wait.h>
#include <unistd.h>
#endif

using namespace stp;

namespace
{

const bool exchange_available = capabilities()["sat.clause-exchange"] == "true";

Options batch_options()
{
  Options o;
  if (has_sat_backend("cadical"))
    o.set("sat-backend", "cadical");
  return o;
}

// x * y = n with 1 < x, y < 2^16 over 40 bits: sat for n = 46337 * 46327,
// unsat for the prime 2^31 - 1, both after a second of search.
const unsigned long long sat_n = 2146654199ULL, unsat_n = 2147483647ULL;
std::string factoring(unsigned long long n)
{
  return "(declare-const x (_ BitVec 40))(declare-const y (_ BitVec 40))"
         "(assert (= (bvmul x y) (_ bv" +
         std::to_string(n) +
         " 40)))"
         "(assert (bvugt x (_ bv1 40)))(assert (bvugt y (_ bv1 40)))"
         "(assert (bvult x (_ bv65536 40)))(assert (bvult y (_ bv65536 40)))";
}

struct Counting final : ClauseExchange
{
  std::size_t learned_clauses = 0;
  void learned(const int*, std::size_t) noexcept override { ++learned_clauses; }
  bool next(std::vector<int>&) noexcept override { return false; }
};

// Records the budget each import poll announces.
struct Polls final : ClauseExchange
{
  std::vector<std::size_t> budgets;
  void learned(const int*, std::size_t) noexcept override {}
  bool next(std::vector<int>&) noexcept override { return false; }
  void begin_import(std::size_t budget) noexcept override { budgets.push_back(budget); }
};

std::string answer(const Result& r)
{
  return r.is_sat() ? "sat" : r.is_unsat() ? "unsat" : "unknown";
}

} // namespace

TEST(BeforeSearch, AHookThatProceedsLetsTheCheckDecide)
{
  for (unsigned long long n : {sat_n, unsat_n})
  {
    TermManager tm;
    Solver s(tm, batch_options());
    s.parse_smt2(factoring(n));
    unsigned calls = 0;
    std::uint64_t variables = 0;
    s.set_before_search(
        [&](SearchPoint& point)
        {
          ++calls;
          variables = point.variables();
          return true;
        },
        "test hook");
    const Result r = s.check_sat();
    EXPECT_EQ(calls, 1u);
    EXPECT_GT(variables, 0u);
    EXPECT_EQ(r.is_sat(), n == sat_n);
    EXPECT_EQ(r.is_unsat(), n == unsat_n);
    // The hook belonged to that check alone.
    EXPECT_EQ(s.check_sat().is_sat(), n == sat_n);
    EXPECT_EQ(calls, 1u);
  }
}

TEST(BeforeSearch, AHookThatDeclinesAbandonsTheCheckUnsearched)
{
  TermManager tm;
  Solver s(tm, batch_options());
  s.parse_smt2(factoring(unsat_n));
  bool connected = false;
  Counting counting;
  s.set_before_search(
      [&](SearchPoint& point)
      {
        ClauseExchangeSettings settings;
        settings.import_interval = 1;
        connected = point.connect_clause_exchange(&counting, settings);
        return false;
      },
      "declined by the test");
  const Result r = s.check_sat();
  ASSERT_TRUE(r.is_unknown());
  EXPECT_EQ(r.reason(), UnknownReason::INCOMPLETE);
  EXPECT_NE(r.reason_message().find("declined by the test"), std::string::npos)
      << r.reason_message();
  EXPECT_EQ(connected, exchange_available);
  // Nothing searched: no clause learned, no poll made; the backend's closing
  // counters are the solver's statistics.
  EXPECT_EQ(counting.learned_clauses, 0u);
  const Statistics st = s.statistics();
  EXPECT_EQ(st.uint64("sat.exchange.connected"), exchange_available ? 1u : 0u);
  EXPECT_EQ(st.uint64("sat.exchange.exported"), 0u);
  EXPECT_EQ(st.uint64("sat.exchange.polls"), 0u);
  if (exchange_available)
  {
    EXPECT_GT(st.uint64("sat.exchange.variables"), 0u);
  }
  // The next check, with no hook, decides.
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(BeforeSearch, AThrowingHookAbandonsTheCheck)
{
  TermManager tm;
  Solver s(tm, batch_options());
  s.parse_smt2(factoring(sat_n));
  s.set_before_search([](SearchPoint&) -> bool { throw std::runtime_error("boom"); },
                      "the thrower");
  const Result r = s.check_sat();
  ASSERT_TRUE(r.is_unknown());
  EXPECT_EQ(r.reason(), UnknownReason::INCOMPLETE);
  EXPECT_NE(r.reason_message().find("the before-search hook failed: the thrower"),
            std::string::npos)
      << r.reason_message();
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST(BeforeSearch, ACheckWithRefinementAheadIsNeverOffered)
{
  // The floating-point and bit-vector abstractions, Real arithmetic, lazy
  // array axioms and uninterpreted functions: each may need another solve
  // after the first. The hook is never called; the check is abandoned, or
  // searched in place on the batch pipeline (NoSearchPoint::search).
  struct Case
  {
    const char* option;
    const char* value;
    const char* script;
  };
  const Case cases[] = {
      {"fp-abstraction", "true",
       "(declare-const x (_ FloatingPoint 8 24))(declare-const y (_ FloatingPoint 8 24))"
       "(assert (fp.eq (fp.mul RNE x y) ((_ to_fp 8 24) RNE 6.0)))"
       "(assert (fp.gt x ((_ to_fp 8 24) RNE 1.0)))"},
      {"bv-term-abstraction", "true",
       "(declare-const x (_ BitVec 32))(declare-const y (_ BitVec 32))"
       "(assert (= (bvmul x y) #x0000008f))(assert (bvugt x #x00000001))"
       "(assert (bvugt y #x00000001))(assert (bvult x #x00000100))"
       "(assert (bvult y #x00000100))"},
      {"incremental", "off",
       "(declare-const r Real)(declare-const s Real)(assert (> (+ r s) 1))"
       "(assert (< r 1))(assert (< s 1))"},
      {"bv-eq-abstraction", "true",
       "(declare-const x (_ BitVec 32))(declare-const y (_ BitVec 32))"
       "(assert (= (bvmul x y) #x0000008f))(assert (= (bvadd x y) #x00000018))"},
      // Lazy array axioms: sixteen reads that survive simplification.
      {"incremental", "auto",
       "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))"
       "(declare-const i0 (_ BitVec 8))(declare-const i1 (_ BitVec 8))"
       "(declare-const i2 (_ BitVec 8))(declare-const i3 (_ BitVec 8))"
       "(declare-const i4 (_ BitVec 8))(declare-const i5 (_ BitVec 8))"
       "(declare-const i6 (_ BitVec 8))(declare-const i7 (_ BitVec 8))"
       "(declare-const i8 (_ BitVec 8))(declare-const i9 (_ BitVec 8))"
       "(declare-const i10 (_ BitVec 8))(declare-const i11 (_ BitVec 8))"
       "(declare-const i12 (_ BitVec 8))(declare-const i13 (_ BitVec 8))"
       "(declare-const i14 (_ BitVec 8))(declare-const i15 (_ BitVec 8))"
       "(assert (bvugt (bvadd (select a i0) (select a i1) (select a i2) (select a i3)"
       " (select a i4) (select a i5) (select a i6) (select a i7) (select a i8)"
       " (select a i9) (select a i10) (select a i11) (select a i12) (select a i13)"
       " (select a i14) (select a i15)) #x80))"},
      // An uninterpreted function.
      {"incremental", "auto",
       "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))(declare-const x (_ BitVec 8))"
       "(assert (= (f x) #x03))(assert (= (f (bvadd x #x01)) #x04))"}};
  for (const Case& c : cases)
    for (NoSearchPoint otherwise : {NoSearchPoint::abandon, NoSearchPoint::search})
    {
      const bool search = otherwise == NoSearchPoint::search;
      SCOPED_TRACE(std::string(c.option) + "=" + c.value + (search ? " search: " : " abandon: ") +
                   std::string(c.script).substr(0, 120));
      TermManager tm;
      Options o = batch_options();
      o.set(c.option, c.value);
      Solver s(tm, o);
      s.parse_smt2(c.script);
      unsigned calls = 0;
      s.set_before_search(
          [&](SearchPoint&)
          {
            ++calls;
            return true;
          },
          "the group", otherwise);
      const Result r = s.check_sat();
      EXPECT_EQ(calls, 0u);
      const Statistics st = s.statistics();
      EXPECT_EQ(st.str("before-search.outcome"), "refused");
      EXPECT_NE(st.str("before-search.refusal").find("may refine after its first solve"),
                std::string::npos)
          << st.str("before-search.refusal");
      if (search)
        EXPECT_TRUE(r.is_sat()) << r.reason_message();
      else
      {
        ASSERT_TRUE(r.is_unknown()) << r.reason_message();
        EXPECT_EQ(r.reason(), UnknownReason::INCOMPLETE);
        EXPECT_NE(r.reason_message().find("exactly one solve"), std::string::npos)
            << r.reason_message();
      }
      EXPECT_TRUE(s.check_sat().is_sat());
      EXPECT_EQ(s.statistics().str("before-search.outcome"), "none");
    }
}

// The value of "first_search_connections" in the arithmetic coordinator's
// metrics line, or -1 when there is none.
static long first_search_connections(const std::string& text)
{
  const std::string key = "\"first_search_connections\":";
  const std::size_t at = text.find(key);
  if (at == std::string::npos)
    return -1;
  return std::strtol(text.c_str() + at + key.size(), nullptr, 10);
}

TEST(BeforeSearch, AnArithmeticCheckSearchedInPlaceKeepsItsCoordinatorsCallback)
{
  // With lra-first-search the coordinator binds its atoms and joins the
  // search from a callback at the before-search point. A refused point
  // searched in place keeps that callback: the coordinator connects to the
  // first search exactly as it does with no hook.
  const char* script = "(declare-const r Real)(declare-const s Real)"
                       "(assert (> (+ r s) 1))(assert (< r 1))(assert (< s 1))";
  auto run = [&](bool hooked, unsigned& calls, std::string& outcome)
  {
    std::string diagnostics;
    {
      TermManager tm;
      Options o = batch_options();
      o.set("lra-first-search", "true");
      o.set("print-functionstat", "true");
      Solver s(tm, o);
      s.set_diagnostic_sink([&](std::string_view text) { diagnostics += text; });
      s.parse_smt2(script);
      if (hooked)
        s.set_before_search(
            [&](SearchPoint&)
            {
              ++calls;
              return true;
            },
            "the group", NoSearchPoint::search);
      EXPECT_TRUE(s.check_sat().is_sat());
      outcome = s.statistics().str("before-search.outcome");
    }
    return first_search_connections(diagnostics);
  };
  unsigned calls = 0;
  std::string outcome;
  const long plain = run(false, calls, outcome);
  EXPECT_EQ(outcome, "none");
  const long hooked = run(true, calls, outcome);
  EXPECT_EQ(outcome, "refused");
  EXPECT_EQ(calls, 0u);
  EXPECT_GE(plain, 1);
  EXPECT_EQ(hooked, plain);
}

TEST(BeforeSearch, AClearedHookIsGoneAndAHookNeedsAReason)
{
  TermManager tm;
  Solver s(tm, batch_options());
  s.parse_smt2(factoring(sat_n));
  // Without a reason an abandoned check would carry none.
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT,
                   s.set_before_search([](SearchPoint&) { return false; }, ""));
  s.set_before_search([](SearchPoint&) { return false; }, "never");
  s.set_before_search(nullptr, "");
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST(BeforeSearch, ACheckDecidedBeforeTheSearchAnswersWithoutTheHook)
{
  // Sixteen reads in a cycle of bvuge keep the array axioms lazy, so the
  // main solve may refine and could not offer the point. But x * 2 is even
  // and the read's double plus one is odd: the solve's own shortcut decides
  // the formula once it is encoded, before any search starts, and the check
  // answers without reaching the point, whichever NoSearchPoint it asked for.
  std::string script = "(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))"
                       "(declare-const x (_ BitVec 8))";
  for (int i = 0; i < 16; ++i)
    script += "(declare-const i" + std::to_string(i) + " (_ BitVec 8))";
  for (int i = 0; i < 16; ++i)
    script += "(assert (bvuge (select a i" + std::to_string(i) + ") (select a i" +
              std::to_string((i + 1) % 16) + ")))";
  script += "(assert (= (bvmul x #x02) (bvor (bvmul (select a i3) #x02) #x01)))";
  for (NoSearchPoint otherwise : {NoSearchPoint::abandon, NoSearchPoint::search})
  {
    TermManager tm;
    Solver s(tm, batch_options());
    s.parse_smt2(script);
    unsigned calls = 0;
    s.set_before_search(
        [&](SearchPoint&)
        {
          ++calls;
          return false;
        },
        "the group", otherwise);
    const Result r = s.check_sat();
    EXPECT_TRUE(r.is_unsat()) << r.reason_message();
    EXPECT_EQ(calls, 0u);
    EXPECT_EQ(s.statistics().str("before-search.outcome"), "not reached");
  }
}

TEST(BeforeSearch, ASideSolveNeverTakesTheHook)
{
  // congruence-candidates proves candidate equalities with solves of their
  // own before the main one; the hook belongs to the main solve alone.
  const std::string script =
      "(declare-const x (_ BitVec 40))(declare-const y (_ BitVec 40))"
      "(declare-const w (_ BitVec 40))(declare-const z (_ BitVec 40))"
      "(declare-const p (_ BitVec 40))(declare-const q (_ BitVec 40))"
      "(assert (= (bvmul p q) (_ bv2146654199 40)))"
      "(assert (bvugt p (_ bv1 40)))(assert (bvugt q (_ bv1 40)))"
      "(assert (bvult p (_ bv65536 40)))(assert (bvult q (_ bv65536 40)))"
      "(assert (= (bvmul (bvadd x y) z) (bvadd p (_ bv7 40))))"
      "(assert (= (bvmul (bvadd x w) z) (bvadd q (_ bv9 40))))";
  std::uint64_t plain_variables = 0;
  for (bool congruence : {false, true})
  {
    TermManager tm;
    Options o = batch_options();
    o.set("congruence-candidates", congruence ? "true" : "false");
    Solver s(tm, o);
    s.parse_smt2(script);
    unsigned calls = 0;
    std::uint64_t variables = 0;
    s.set_before_search(
        [&](SearchPoint& point)
        {
          ++calls;
          variables = point.variables();
          return true;
        },
        "test hook");
    EXPECT_TRUE(s.check_sat().is_sat());
    EXPECT_EQ(calls, 1u) << congruence;
    if (!congruence)
      plain_variables = variables;
    // The main solve's backend, not a side solve's (about a hundred
    // variables): within a fifth of the plain check's.
    EXPECT_GT(variables * 5, plain_variables * 4) << variables << " " << plain_variables;
  }
}

TEST(BeforeSearch, AnInterruptedCheckConsumesTheHook)
{
  TermManager tm;
  Solver s(tm, batch_options());
  s.parse_smt2(factoring(sat_n));
  unsigned calls = 0;
  s.set_before_search(
      [&](SearchPoint&)
      {
        ++calls;
        return false;
      },
      "never");
  s.interrupt();
  const Result interrupted = s.check_sat();
  ASSERT_TRUE(interrupted.is_unknown());
  EXPECT_EQ(interrupted.reason(), UnknownReason::INTERRUPTED);
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(calls, 0u);
}

TEST(BeforeSearch, WriteCnfRefusesAPendingHookAndLeavesIt)
{
  TermManager tm;
  Solver s(tm, batch_options());
  s.parse_smt2(factoring(sat_n));
  unsigned calls = 0;
  s.set_before_search(
      [&](SearchPoint&)
      {
        ++calls;
        return true;
      },
      "test hook");
  std::ostringstream cnf;
  API_EXPECT_ERROR(ErrorCode::STATE, s.write_cnf(cnf));
  EXPECT_EQ(calls, 0u);
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(calls, 1u);
  s.write_cnf(cnf);
  EXPECT_FALSE(cnf.str().empty());
}

TEST(BeforeSearch, WriteCnfKeepsWhatTheLastCheckDidWithItsHook)
{
  // The export is not a check: before-search.outcome and
  // before-search.refusal still describe the last check afterwards, as the
  // other last-check records do -- an offered point, and a refused one.
  const std::string uf =
      "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))(declare-const x (_ BitVec 8))"
      "(assert (= (f x) #x03))(assert (= (f (bvadd x #x01)) #x04))";
  for (const std::string& script : {factoring(sat_n), uf})
  {
    SCOPED_TRACE(script.substr(0, 60));
    TermManager tm;
    Solver s(tm, batch_options());
    s.parse_smt2(script);
    s.set_before_search([](SearchPoint&) { return true; }, "test hook",
                        NoSearchPoint::search);
    EXPECT_TRUE(s.check_sat().is_sat());
    const std::string outcome = s.statistics().str("before-search.outcome");
    const std::string refusal = s.statistics().str("before-search.refusal");
    EXPECT_EQ(outcome, script == uf ? "refused" : "offered");
    std::ostringstream cnf;
    s.write_cnf(cnf);
    EXPECT_FALSE(cnf.str().empty());
    EXPECT_EQ(s.statistics().str("before-search.outcome"), outcome);
    EXPECT_EQ(s.statistics().str("before-search.refusal"), refusal);
  }
}

TEST(BeforeSearch, ResetsClearAPendingHook)
{
  for (const bool everything : {true, false})
  {
    SCOPED_TRACE(everything ? "reset" : "reset_assertions");
    TermManager tm;
    Solver s(tm, batch_options());
    unsigned calls = 0;
    s.set_before_search(
        [&](SearchPoint&)
        {
          ++calls;
          return true;
        },
        "test hook");
    if (everything)
      s.reset();
    else
      s.reset_assertions();
    s.parse_smt2(factoring(sat_n));
    EXPECT_TRUE(s.check_sat().is_sat());
    EXPECT_EQ(calls, 0u);
    EXPECT_EQ(s.statistics().str("before-search.outcome"), "none");
  }
}

TEST(BeforeSearch, AnExchangeReplacedOrDisconnectedInTheHookCountsNothing)
{
  // A hook may connect one exchange and then another, or none: the one
  // connected when the search starts is the only one the backend uses.
  if (!exchange_available)
    GTEST_SKIP() << "no clause-import extension in this build's CaDiCaL";
  TermManager tm;
  Solver s(tm, batch_options());
  s.parse_smt2(factoring(unsat_n));
  Counting first, second;
  s.set_before_search(
      [&](SearchPoint& point)
      { return point.connect_clause_exchange(&first) && point.connect_clause_exchange(nullptr); },
      "test hook");
  EXPECT_TRUE(s.check_sat().is_unsat());
  EXPECT_EQ(s.statistics().uint64("sat.exchange.connected"), 0u);
  EXPECT_EQ(s.statistics().uint64("sat.exchange.exported"), 0u);
  EXPECT_EQ(first.learned_clauses, 0u);
  s.set_before_search(
      [&](SearchPoint& point)
      { return point.connect_clause_exchange(&first) && point.connect_clause_exchange(&second); },
      "test hook");
  EXPECT_TRUE(s.check_sat().is_unsat());
  EXPECT_EQ(s.statistics().uint64("sat.exchange.connected"), 1u);
  EXPECT_EQ(first.learned_clauses, 0u);
  EXPECT_GT(second.learned_clauses, 0u);
  EXPECT_GT(s.statistics().uint64("sat.exchange.exported"), 0u);
}

TEST(BeforeSearch, ClausesThatCannotBeImportedAreDroppedAndTheAnswerStands)
{
  // An empty clause, a zero literal, INT_MIN and literals beyond the
  // exchange's variables are dropped and counted; next() appends to what it
  // is handed, so each clause starts from an empty vector.
  if (!exchange_available)
    GTEST_SKIP() << "no clause-import extension in this build's CaDiCaL";
  struct Junk final : ClauseExchange
  {
    std::vector<std::vector<int>> clauses{
        {}, {1, 0, 2}, {INT_MIN}, {1, 2000000000}, {-2000000000}};
    std::size_t at = 0;
    void learned(const int*, std::size_t) noexcept override {}
    bool next(std::vector<int>& literals) noexcept override
    {
      if (at == clauses.size())
        return false;
      literals.insert(literals.end(), clauses[at].begin(), clauses[at].end());
      ++at;
      return true;
    }
  };
  for (const unsigned long long n : {sat_n, unsat_n})
  {
    TermManager tm;
    Solver s(tm, batch_options());
    s.parse_smt2(factoring(n));
    Junk junk;
    s.set_before_search(
        [&](SearchPoint& point)
        {
          ClauseExchangeSettings settings;
          settings.import_interval = 1;
          return point.connect_clause_exchange(&junk, settings);
        },
        "test hook");
    const Result r = s.check_sat();
    EXPECT_EQ(answer(r), n == sat_n ? "sat" : "unsat");
    EXPECT_EQ(s.statistics().uint64("sat.exchange.import-dropped"), 5u);
    EXPECT_EQ(s.statistics().uint64("sat.exchange.imported"), 0u);
  }
}

TEST(BeforeSearch, AScriptsChecksRefuseAPendingHookAndLeaveIt)
{
  // A script's (check-sat) runs through the frontend, which would neither use
  // nor consume a hook set for the next check: EXECUTE refuses while one is
  // set, and the declarations a plain parse adds still go in.
  TermManager tm;
  Solver s(tm, batch_options());
  unsigned calls = 0;
  s.set_before_search(
      [&](SearchPoint&)
      {
        ++calls;
        return true;
      },
      "test hook");
  API_EXPECT_ERROR(ErrorCode::STATE,
                   s.parse_smt2(factoring(sat_n) + "(check-sat)", ParseMode::EXECUTE));
  s.parse_smt2(factoring(sat_n));
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(calls, 1u);
  EXPECT_EQ(s.statistics().str("before-search.outcome"), "offered");
  s.parse_smt2("(check-sat)", ParseMode::EXECUTE);
}

TEST(BeforeSearch, ExchangeCountersDescribeTheLastCheck)
{
  if (!exchange_available)
    GTEST_SKIP() << "no clause-import extension in this build's CaDiCaL";
  TermManager tm;
  Solver s(tm, batch_options());
  s.parse_smt2(factoring(unsat_n));
  Counting counting;
  s.set_before_search(
      [&](SearchPoint& point) { return point.connect_clause_exchange(&counting); },
      "test hook");
  EXPECT_TRUE(s.check_sat().is_unsat());
  EXPECT_EQ(s.statistics().uint64("sat.exchange.connected"), 1u);
  EXPECT_GT(s.statistics().uint64("sat.exchange.exported"), 0u);
  // The next check connected nothing.
  EXPECT_TRUE(s.check_sat().is_unsat());
  EXPECT_EQ(s.statistics().uint64("sat.exchange.connected"), 0u);
  EXPECT_EQ(s.statistics().uint64("sat.exchange.exported"), 0u);
}

TEST(BeforeSearch, AnImportPollAnnouncesTheBackendsCapWithoutABudget)
{
  if (!exchange_available)
    GTEST_SKIP() << "no clause-import extension in this build's CaDiCaL";
  TermManager tm;
  Solver s(tm, batch_options());
  s.parse_smt2(factoring(unsat_n));
  Polls polls;
  ClauseExchangeSettings settings;
  settings.import_interval = 1;
  settings.import_budget = 0;
  s.set_before_search(
      [&](SearchPoint& point) { return point.connect_clause_exchange(&polls, settings); },
      "test hook");
  EXPECT_TRUE(s.check_sat().is_unsat());
  ASSERT_FALSE(polls.budgets.empty());
  for (std::size_t budget : polls.budgets)
    EXPECT_EQ(budget, 16384u);
}

#ifdef __linux__
TEST(BeforeSearch, CopiesForkedInTheHookEachDecide)
{
  for (unsigned long long n : {sat_n, unsat_n})
  {
    TermManager tm;
    Solver s(tm, batch_options());
    s.parse_smt2(factoring(n));
    std::vector<int> readers;
    std::vector<pid_t> children;
    bool child = false;
    int report = -1;
    Counting counting;
    s.set_before_search(
        [&](SearchPoint& point)
        {
          // The owner's exchange: connected before the forks, so every copy
          // inherits it, and its closing counters stay with the owner.
          point.connect_clause_exchange(&counting);
          for (int copy = 0; copy < 2; ++copy)
          {
            int fds[2];
            if (pipe(fds) != 0)
              return false;
            const pid_t pid = fork();
            if (pid == 0)
            {
              close(fds[0]);
              child = true;
              report = fds[1];
              if (copy == 1)
              {
                SearchDiversification d;
                d.seed = 5;
                d.phase = 0;
                d.shuffle = true;
                point.diversify(d);
              }
              return true;
            }
            close(fds[1]);
            readers.push_back(fds[0]);
            children.push_back(pid);
          }
          return false; // the owner hands the search to its copies
        },
        "handed to the copies");
    const Result r = s.check_sat();
    if (child)
    {
      const std::string text = r.is_sat() ? "sat" : r.is_unsat() ? "unsat" : "unknown";
      _exit(write(report, text.data(), text.size()) == ssize_t(text.size()) ? 0 : 3);
    }
    ASSERT_TRUE(r.is_unknown());
    EXPECT_NE(r.reason_message().find("handed to the copies"), std::string::npos);
    const std::string expected = n == sat_n ? "sat" : "unsat";
    for (std::size_t i = 0; i < children.size(); ++i)
    {
      std::string text;
      char buffer[64];
      for (ssize_t got; (got = read(readers[i], buffer, sizeof buffer)) > 0;)
        text.append(buffer, std::size_t(got));
      close(readers[i]);
      int status = 0;
      waitpid(children[i], &status, 0);
      EXPECT_TRUE(WIFEXITED(status) && WEXITSTATUS(status) == 0);
      EXPECT_EQ(text, expected) << "copy " << i;
    }
    const Statistics st = s.statistics();
    EXPECT_EQ(st.uint64("sat.exchange.connected"), exchange_available ? 1u : 0u);
    EXPECT_EQ(st.uint64("sat.exchange.polls"), 0u); // the owner never searched
  }
}

namespace
{
// Everything a forked copy writes to its pipe, then its exit.
std::string drain(int fd, pid_t pid)
{
  std::string text;
  char buffer[4096];
  for (ssize_t n; (n = read(fd, buffer, sizeof buffer)) > 0;)
    text.append(buffer, std::size_t(n));
  close(fd);
  int status = 0;
  waitpid(pid, &status, 0);
  if (!WIFEXITED(status) || WEXITSTATUS(status) != 0)
    return "copy failed";
  return text;
}

// Learned clauses as text: literals separated by spaces, one clause a line.
struct Recorder final : ClauseExchange
{
  std::string clauses;
  void learned(const int* literals, std::size_t size) noexcept override
  {
    for (std::size_t i = 0; i < size; ++i)
      clauses += std::to_string(literals[i]) + (i + 1 < size ? " " : "\n");
  }
  bool next(std::vector<int>&) noexcept override { return false; }
};
// Hands a recorded set over a few clauses a poll: at most the budget the poll
// announces, so the set goes in over many polls, during the search.
struct Replayer final : ClauseExchange
{
  std::vector<std::vector<int>> pending;
  std::size_t at = 0;
  std::size_t begun = 0;
  std::size_t allowance = 0;
  void learned(const int*, std::size_t) noexcept override {}
  bool next(std::vector<int>& literals) noexcept override
  {
    if (at == pending.size() || allowance == 0)
      return false;
    --allowance;
    literals = pending[at++];
    return true;
  }
  void begin_import(std::size_t budget) noexcept override
  {
    ++begun;
    allowance = budget;
  }
};

std::vector<std::vector<int>> parse_clauses(const std::string& text)
{
  std::vector<std::vector<int>> clauses(1);
  std::string number;
  for (char c : text)
  {
    if (c == ' ' || c == '\n')
    {
      clauses.back().push_back(std::stoi(number));
      number.clear();
      if (c == '\n')
        clauses.emplace_back();
    }
    else
      number += c;
  }
  clauses.pop_back();
  return clauses;
}
} // namespace

TEST(BeforeSearch, ClausesOneCopyLearnsImportIntoAnother)
{
  if (!exchange_available)
    GTEST_SKIP() << "no clause-import extension in this build's CaDiCaL";
  // Both copies are forked at the same point, so they share the backend's
  // numbering: the first exports only, and is waited for; the second then
  // imports what the first learned, two clauses every eight conflicts, so
  // most of it goes in mid-search, with literals already on the trail. On
  // the satisfiable instance a clause that is not implied could cut away
  // the only models; the importer must still find one, and it is checked.
  for (unsigned long long n : {sat_n, unsat_n})
  {
    SCOPED_TRACE(n == sat_n ? "sat" : "unsat");
    TermManager tm;
    Solver s(tm, batch_options());
    s.parse_smt2(factoring(n));
    Recorder recorder;
    Replayer replayer;
    char role = 'O';
    int report = -1;
    std::string exported, imported;
    s.set_before_search(
        [&](SearchPoint& point)
        {
          int fds[2];
          if (pipe(fds) != 0)
            return false;
          pid_t pid = fork();
          if (pid == 0)
          {
            close(fds[0]);
            role = 'A';
            report = fds[1];
            ClauseExchangeSettings settings;
            settings.import = false;
            settings.max_size = 16;
            return point.connect_clause_exchange(&recorder, settings);
          }
          close(fds[1]);
          exported = drain(fds[0], pid);
          const std::size_t end = exported.find('\n');
          if (end == std::string::npos)
            return false;
          replayer.pending = parse_clauses(exported.substr(end + 1));
          if (pipe(fds) != 0)
            return false;
          pid = fork();
          if (pid == 0)
          {
            close(fds[0]);
            role = 'B';
            report = fds[1];
            ClauseExchangeSettings settings;
            settings.import_interval = 8;
            settings.import_budget = 2;
            return point.connect_clause_exchange(&replayer, settings);
          }
          close(fds[1]);
          imported = drain(fds[0], pid);
          return false; // the owner searches nothing
        },
        "handed to the copies");
    const Result r = s.check_sat();
    if (role != 'O')
    {
      const Statistics st = s.statistics();
      std::string out = answer(r);
      for (const char* key :
           {"sat.exchange.connected", "sat.exchange.polls", "sat.exchange.exported",
            "sat.exchange.imported", "sat.exchange.import-backtracks"})
        out += " " + std::to_string(st.uint64(key));
      out += " " + std::to_string(replayer.begun);
      // A model, checked against the query itself: x * y = n, 1 < x, y < 2^16.
      std::string model = "none";
      if (r.is_sat())
      {
        const Model m = s.model();
        const std::uint64_t x = m.uint64_value(*s.symbol("x"));
        const std::uint64_t y = m.uint64_value(*s.symbol("y"));
        model = x > 1 && y > 1 && x < 65536 && y < 65536 && x * y == n ? "valid" : "invalid";
      }
      out += " " + model + "\n";
      if (role == 'A')
        out += recorder.clauses;
      std::size_t at = 0;
      while (at < out.size())
      {
        const ssize_t written = write(report, out.data() + at, out.size() - at);
        if (written <= 0)
          _exit(3);
        at += std::size_t(written);
      }
      _exit(0);
    }
    ASSERT_TRUE(r.is_unknown());
    const std::string expected = n == sat_n ? "sat" : "unsat";
    const std::string expected_model = n == sat_n ? "valid" : "none";
    // The exporter: the answer, connected, never polled, exported something.
    std::istringstream a(exported.substr(0, exported.find('\n')));
    std::string verdict, model;
    std::uint64_t connected = 0, polls = 0, out_clauses = 0, in_clauses = 0, backtracks = 0,
                  begun = 0;
    a >> verdict >> connected >> polls >> out_clauses >> in_clauses >> backtracks >> begun >>
        model;
    EXPECT_EQ(verdict, expected) << exported.substr(0, 200);
    EXPECT_EQ(model, expected_model);
    EXPECT_EQ(connected, 1u);
    EXPECT_EQ(polls, 0u);
    EXPECT_GT(out_clauses, 0u);
    ASSERT_GT(replayer.pending.size(), 16u);
    // The importer: the same answer, after taking those clauses over many
    // polls, some of them away from the root.
    std::istringstream b(imported);
    b >> verdict >> connected >> polls >> out_clauses >> in_clauses >> backtracks >> begun >>
        model;
    EXPECT_EQ(verdict, expected) << imported;
    EXPECT_EQ(model, expected_model);
    EXPECT_EQ(connected, 1u);
    EXPECT_GT(polls, 8u);
    EXPECT_GT(in_clauses, 8u);
    EXPECT_LE(in_clauses, replayer.pending.size());
    EXPECT_GT(backtracks, 0u);
    EXPECT_GT(begun, 8u);
  }
}
#endif

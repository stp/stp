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

// timeout-budget.cpp -- the budgets a check takes mean the same thing
// whichever SAT backend is underneath: "no limit" is the absence of a budget
// (an empty CheckBudget field per check; -1, or "none" for a duration, in the
// persistent max-num-confl and max-time options, the only negative value
// those take), and zero is a budget of zero rather than an absent one.
//
// The hard instance is api_test::add_hard_factoring, factoring a semiprime: hard
// enough that the SAT solver will not answer while a test is watching, so any
// answer we do get came from a budget running out rather than from the
// search finishing. Both factors are held below 2^40 so that the 96-bit
// multiply cannot wrap; without that the constraint is satisfied modulo 2^96
// by almost any operand, and the instance is trivial rather than a factoring
// problem.

#include "api_common.hpp"

#include <chrono>
#include <cstdint>
#include <string>
#include <vector>

using namespace stp;
using namespace std::chrono_literals;

namespace
{

struct Backend
{
  const char* name;

  // true if a time budget stops a search that is already running. The others
  // only notice a time budget between calls into the SAT solver, so asking
  // one of them to give up part way through a hard query would mean waiting
  // for that query to finish. (MiniSat notices one mid-search only where its
  // build has a terminator, so it is counted with the others.)
  bool interruptible;
};

// Every backend this build has.
std::vector<Backend> backends()
{
  const Backend all[] = {{"minisat", false},
                         {"simplifying-minisat", false},
                         {"cryptominisat", true},
                         {"cadical", true}};
  std::vector<Backend> result;
  for (const Backend& b : all)
    if (has_sat_backend(b.name))
      result.push_back(b);
  return result;
}

// A solver's backend is chosen when it is built. Every solver here that
// checks satisfiability also runs the engine's model self-check
// (check-sanity), as every 2.x checker did.
Options backend_options(const char* name)
{
  Options o;
  o.set_str("sat-backend", name);
  o.set_bool("check-sanity", true);
  return o;
}

std::string backend_in_use(const Solver& s)
{
  return s.statistics().str("sat.backend");
}

double seconds_since(const std::chrono::steady_clock::time_point& start)
{
  const std::chrono::duration<double> elapsed = std::chrono::steady_clock::now() - start;
  return elapsed.count();
}
} // namespace

// -1 is the only negative budget with a meaning, and 3.x spells it only in
// the persistent options; a per-check budget says "no limit" by leaving its
// field empty, and its conflict count is unsigned. Anything else is a mistake
// on the caller's part and is reported rather than being run as unlimited.
TEST(timeout_budget, negative_budgets_are_rejected)
{
  TermManager tm;
  Solver s(tm);
  SolverOptions& o = s.options();
  o.set_bool("check-sanity", true);

  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("max-num-confl", -2));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_duration("max-time", -2ms));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("max-num-confl", "-100"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("max-time", "-100ms"));
  EXPECT_FALSE(o.is_set("max-num-confl"));
  EXPECT_FALSE(o.is_set("max-time"));
  EXPECT_EQ(-1, o.get_int("max-num-confl"));
  EXPECT_EQ(-1, o.get_duration("max-time").count());

  // -1 itself is accepted, and is no limit.
  o.set_int("max-num-confl", -1);
  o.set_duration("max-time", -1ms);
  EXPECT_TRUE(s.check_sat().is_sat());

  // A negative per-check time is refused before the check starts, and the
  // solver is as it was: never run as unlimited, nor as a budget of zero.
  api_test::add_hard_factoring(tm, s);
  const std::chrono::steady_clock::time_point start = std::chrono::steady_clock::now();
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s.check_sat({}, CheckBudget{-2ms, std::nullopt}));
  EXPECT_LT(seconds_since(start), 30.0);
  const Result r = s.check_sat({}, CheckBudget{0ms, std::nullopt});
  EXPECT_TRUE(r.is_unknown()) << r;
  EXPECT_EQ(UnknownReason::TIMEOUT, r.reason());
}

// A budget of zero is a budget, not the absence of one.
TEST(timeout_budget, zero_time_budget_gives_up_immediately)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    TermManager tm;
    Solver s(tm, backend_options(backend.name));
    api_test::add_hard_factoring(tm, s);

    const std::chrono::steady_clock::time_point start = std::chrono::steady_clock::now();

    EXPECT_TRUE(s.check_sat({}, CheckBudget{0ms, std::nullopt}).is_unknown());
    EXPECT_LT(seconds_since(start), 30.0);
  }
}

TEST(timeout_budget, zero_conflict_budget_gives_up_immediately)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    TermManager tm;
    Solver s(tm, backend_options(backend.name));
    api_test::add_hard_factoring(tm, s);

    EXPECT_TRUE(s.check_sat({}, CheckBudget{std::nullopt, std::uint64_t(0)}).is_unknown());
  }
}

// The budget is for the check rather than for each call into the SAT solver,
// of which a check makes one per refinement iteration. Allow generously more
// than the budget before failing: the point is that the check stops in some
// multiple of the budget that does not grow with the number of iterations.
TEST(timeout_budget, time_budget_covers_the_whole_query)
{
  for (const Backend& backend : backends())
  {
    if (!backend.interruptible)
    {
      continue;
    }

    SCOPED_TRACE(backend.name);

    TermManager tm;
    Solver s(tm, backend_options(backend.name));
    api_test::add_hard_factoring(tm, s);

    const std::chrono::steady_clock::time_point start = std::chrono::steady_clock::now();

    EXPECT_TRUE(s.check_sat({}, CheckBudget{2s, std::nullopt}).is_unknown());
    EXPECT_LT(seconds_since(start), 30.0);
  }
}

// An unlimited check must still reach the SAT solver and come back with an
// answer. The trivial case below is decided before the solver is called, so
// it would not notice a backend that mistook "no budget configured" for a
// budget of zero.
TEST(timeout_budget, no_limit_reaches_the_solver)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    TermManager tm;
    Solver s(tm, backend_options(backend.name));

    // 60491 == 251 * 241, factored in milliseconds, but still an answer
    // that has to come out of the SAT solver: give this same instance a
    // budget of zero conflicts and every backend reports unknown.
    const std::uint32_t width = 32;
    const Term a = tm.declare("a", tm.mk_bv_sort(width));
    const Term b = tm.declare("b", tm.mk_bv_sort(width));
    const Term one = tm.mk_bv(width, 1);
    const Term limit = tm.mk_bv(width, 1ULL << 16);
    const Term product = tm.mk_bv(width, 60491);

    s.add(bvmul(a, b) == product);
    s.add(bvugt(a, one));
    s.add(bvugt(b, one));
    s.add(bvult(a, limit));
    s.add(bvult(b, limit));
    s.add(bvule(a, b));

    // The assertions are satisfiable; a budget with neither field set is no
    // limit at all.
    EXPECT_TRUE(s.check_sat({}, CheckBudget{}).is_sat());
  }
}

// An unlimited check is unaffected by any of the above.
TEST(timeout_budget, no_limit_still_answers)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    TermManager tm;
    Solver s(tm, backend_options(backend.name));

    const Term a = tm.declare("a", tm.mk_bv_sort(32));
    const Term value = tm.mk_bv(32, 42);
    s.add(a == value);

    EXPECT_TRUE(s.entails(a == value, CheckBudget{}).is_valid());
  }
}

// A budget past what the clock counts (about 292 years, up to the largest a
// caller can spell) is no limit in all but name, not a deadline that wraps
// into the past; the trivial query is decided before the SAT solver is
// called, the factoring one by it.
TEST(timeout_budget, a_budget_past_the_clocks_range_is_no_limit)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    TermManager tm;
    Solver s(tm, backend_options(backend.name));
    const Term x = tm.declare("x", tm.mk_bv_sort(8));
    const Term a = tm.declare("a", tm.mk_bv_sort(32));
    const Term b = tm.declare("b", tm.mk_bv_sort(32));
    const Term trivial = x == tm.mk_bv(8, 3);
    const Term factoring = and_({bvmul(a, b) == tm.mk_bv(32, 60491), bvugt(a, tm.mk_bv(32, 1)),
                                 bvugt(b, tm.mk_bv(32, 1)), bvult(a, tm.mk_bv(32, 1ULL << 16)),
                                 bvult(b, tm.mk_bv(32, 1ULL << 16)), bvule(a, b)});
    for (const Term& query : {trivial, factoring})
    {
      for (const std::int64_t ms : {std::int64_t(9223372036854), std::int64_t(9223372036854775),
                                    std::int64_t(INT64_MAX)})
        EXPECT_TRUE(s.check_sat({query}, CheckBudget{std::chrono::milliseconds(ms), std::nullopt}).is_sat())
            << ms << " ms";
      for (const char* text : {"9223372036854ms", "9223372036854775807ms", "1000000000h"})
      {
        s.options().set("max-time", text);
        EXPECT_TRUE(s.check_sat({query}).is_sat()) << text;
      }
      s.options().reset("max-time");
    }
  }
}

// Without a budget argument and with the budget options at their defaults,
// a check has no limit.
TEST(timeout_budget, vc_query_is_unlimited)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool("check-sanity", true);

  const Term a = tm.declare("a", tm.mk_bv_sort(32));
  const Term value = tm.mk_bv(32, 42);
  s.add(a == value);

  EXPECT_TRUE(s.entails(a == value).is_valid());
  EXPECT_TRUE(s.entails(tm.mk_false()).is_invalid());
}

// Every backend that is compiled in can be selected and reports itself.
TEST(timeout_budget, backends_are_selectable)
{
  for (const Backend& backend : backends())
  {
    SCOPED_TRACE(backend.name);

    TermManager tm;
    Solver s(tm, backend_options(backend.name));
    EXPECT_EQ(backend.name, backend_in_use(s));
  }
}

#ifdef USE_CADICAL
TEST(timeout_budget, cadical_is_selectable)
{
  EXPECT_TRUE(has_sat_backend("cadical"));
  TermManager tm;
  Solver s(tm, backend_options("cadical"));
  EXPECT_EQ("cadical", backend_in_use(s));

  // 2.x then moved the same checker to MiniSat. 3.x fixes a solver's backend
  // when it is built: a live solver refuses to switch, and a solver built for
  // MiniSat runs it.
  API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, s.options().set_str("sat-backend", "minisat"));
  EXPECT_EQ("cadical", backend_in_use(s));
#ifdef USE_MINISAT
  Solver m(tm, backend_options("minisat"));
  EXPECT_EQ("minisat", backend_in_use(m));
#endif
}
#else
TEST(timeout_budget, cadical_is_absent)
{
  EXPECT_FALSE(has_sat_backend("cadical"));
  TermManager tm;
  API_EXPECT_ERROR(ErrorCode::OPTION_UNAVAILABLE, Solver s(tm, backend_options("cadical")));
  Solver s(tm);
  EXPECT_NE("cadical", backend_in_use(s));
}
#endif

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

// reason-unknown.cpp -- why a check had no answer.
//
// A check that could not be decided answers unknown whatever stopped it, and
// that is the one verdict every way of giving up carries: a caller that only
// wants to know whether there is an answer has one test to make. Which cause
// it was is a separate question, and the answer rides on the Result (and the
// Entailment) itself: Result::reason() for the cause, reason_message() for
// the sentence behind it -- the record SMT-LIB2 reads through
// (get-info :reason-unknown). A budget no clock was involved in is told apart
// from one that was.

#include "api_common.hpp"

#include <chrono>
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

using namespace stp;
using namespace std::chrono_literals;

namespace
{
// Options with the engine's model self-check on (check-sanity), as every 2.x
// checker had it: a sat answer whose model does not satisfy the assertions is
// an INTERNAL error rather than a silent pass. Every solver here is built
// from these.
Options checked()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

// A solver pinned to CaDiCaL, or nullopt on a build without it (the caller
// skips).
//
// The factorisation below is decided in under a second and costs a few
// thousand conflicts -- CaDiCaL's timings, which is why the backend is pinned
// rather than left to the build's default: CryptoMiniSat, the default
// wherever it is compiled in, takes minutes over this same square.
std::optional<Options> cadical()
{
  if (!has_sat_backend("cadical"))
    return std::nullopt;
  Options o = checked();
  o.set_str("sat-backend", "cadical");
  return o;
}

// A real factorisation, zero-extended so the product cannot wrap: modular
// multiplication would make it trivially satisfiable and no budget would bind.
// The number is (2^31 - 69)^2. It has to be chosen with care: products with a
// Mersenne factor -- the previous constant had 2^31 - 1 in it -- fell to the
// solver's preprocessing with zero conflicts once the multiplier circuit
// shrank, and a conflict budget that is never consulted never binds, while a
// generic semiprime takes minutes. This square costs a few thousand
// conflicts, so every budget here has something to stop.
void assert_factoring(TermManager& tm, Solver& s)
{
  const Sort bv = tm.mk_bv_sort(32);
  const Term x = tm.declare("x", bv);
  const Term y = tm.declare("y", bv);
  const Term wide_x = concat(tm.mk_bv(32, 0), x);
  const Term wide_y = concat(tm.mk_bv(32, 0), y);
  s.add(bvmul(wide_x, wide_y) == tm.mk_bv(64, 0x3fffffbb00001299ULL));
  s.add(bvugt(x, 1));
  s.add(bvugt(y, 1));
}
} // namespace

// Nothing to explain while there is an answer, and the reason describes the
// check it came with rather than the session. 3.x has no per-solver register
// to read before any check: the reason belongs to each Result, so the one to
// read after an earlier unknown is the new result's.
TEST(reason_unknown, AnAnsweredQueryHasNoReason)
{
  const std::optional<Options> o = cadical();
  if (!o)
    GTEST_SKIP() << "CaDiCaL backend not compiled in";
  TermManager tm;
  Solver s(tm, *o);
  assert_factoring(tm, s);

  const Result stopped = s.check_sat({}, CheckBudget{std::nullopt, std::uint64_t(0)});
  ASSERT_TRUE(stopped.is_unknown());
  EXPECT_NE(UnknownReason::NONE, stopped.reason());

  const Result r = s.check_sat({}, CheckBudget{});
  ASSERT_TRUE(r.is_sat()) << r;
  EXPECT_EQ(UnknownReason::NONE, r.reason());
  EXPECT_EQ("", r.reason_message());
}

// ... and a later check that gives up for another reason reports that one.
// Within a check the engine keeps the first reason it records (a solve may
// note a spent budget on every refinement round), so the solver clears the
// record at the start of every check; without that, the conflict budget of
// the first check below would also answer for the second one's clock, as it
// did in the 2.x C API (issue #1144).
TEST(reason_unknown, ALaterUnknownReportsItsOwnReason)
{
  const std::optional<Options> o = cadical();
  if (!o)
    GTEST_SKIP() << "CaDiCaL backend not compiled in";
  TermManager tm;
  Solver s(tm, *o);
  assert_factoring(tm, s);

  const Result counted = s.check_sat({}, CheckBudget{std::nullopt, std::uint64_t(0)});
  ASSERT_TRUE(counted.is_unknown());
  ASSERT_EQ(UnknownReason::CONFLICT_LIMIT, counted.reason());

  const Result timed = s.check_sat({}, CheckBudget{0ms, std::nullopt});
  EXPECT_TRUE(timed.is_unknown());
  EXPECT_EQ(UnknownReason::TIMEOUT, timed.reason());
  EXPECT_NE(std::string::npos, timed.reason_message().find("time budget")) << timed.reason_message();
}

// The two the SAT solver enforces keep the verdict they had. They share it, so
// the verdict alone cannot separate them -- which is what the reason is for:
// the clock may pass with more time on the same machine, the conflict budget
// is deterministic and will not.
TEST(reason_unknown, TheClockAndTheConflictBudgetAreToldApartByTheReason)
{
  const std::optional<Options> o = cadical();
  if (!o)
    GTEST_SKIP() << "CaDiCaL backend not compiled in";

  TermManager clock_tm;
  Solver clock(clock_tm, *o);
  assert_factoring(clock_tm, clock);
  const Result timed = clock.check_sat({}, CheckBudget{0ms, std::nullopt});
  EXPECT_TRUE(timed.is_unknown());
  EXPECT_EQ(UnknownReason::TIMEOUT, timed.reason());

  TermManager conflicts_tm;
  Solver conflicts(conflicts_tm, *o);
  assert_factoring(conflicts_tm, conflicts);
  const Result counted = conflicts.check_sat({}, CheckBudget{std::nullopt, std::uint64_t(0)});
  EXPECT_TRUE(counted.is_unknown());
  EXPECT_EQ(UnknownReason::CONFLICT_LIMIT, counted.reason());
}

// The AIG budget is neither of those two and has a reason of its own,
// RESOURCE_LIMIT, rather than a catch-all. A caller sets this budget in order
// to act on it firing; the sentence still supplies the count the value
// cannot.
TEST(reason_unknown, TheAigBudgetIsNotReportedAsAClock)
{
  std::optional<Options> o = cadical();
  if (!o)
    GTEST_SKIP() << "CaDiCaL backend not compiled in";
  o->set_int("aig-node-budget", 50);
  TermManager tm;
  Solver s(tm, *o);
  assert_factoring(tm, s);

  const Result r = s.check_sat({}, CheckBudget{});
  EXPECT_TRUE(r.is_unknown()) << r;
  EXPECT_EQ(UnknownReason::RESOURCE_LIMIT, r.reason());

  const std::string why = r.reason_message();
  EXPECT_NE(std::string::npos, why.find("--aig-node-budget")) << why;
  EXPECT_NE(std::string::npos, why.find("50")) << why;
}

// Same query, no limit: decided. So the no-answer above is the budget
// speaking and not the query being hard.
TEST(reason_unknown, WithoutTheBudgetTheSameQueryIsDecided)
{
  std::optional<Options> o = cadical();
  if (!o)
    GTEST_SKIP() << "CaDiCaL backend not compiled in";
  o->set_int("aig-node-budget", -1);
  TermManager tm;
  Solver s(tm, *o);
  assert_factoring(tm, s);

  const Result r = s.check_sat({}, CheckBudget{});
  EXPECT_TRUE(r.is_sat()) << r;
  EXPECT_EQ(UnknownReason::NONE, r.reason());
}

// The one cause on this list that names an option of its own, and the one a
// caller should never see. uf-inject-args asserts that equality-only
// uninterpreted functions are injective, which the query did not say and
// which can only remove models. An `unsat` over it therefore refutes the
// query with an assumption on top of it -- not the query -- and there was a
// time when STP reported exactly that as an answer.
//
// It does not any more, and not by withholding the answer either: the
// assumption is installed behind an activation literal the search holds, so
// STP can ask whether the refutation used it and take it back when it did.
// The query below is satisfiable, plainly -- three pairwise-distinct two-bit
// arguments to a function into one bit, asserting that two of the three
// results collide, which three values into two must. So the answer is sat
// with the option and sat without it, and ASSUMED_INJECTIVITY stays a reason
// the header explains rather than one a check returns.
namespace
{
void assert_pigeonhole(TermManager& tm, Solver& s)
{
  s.options().set_str("uninterpreted-functions", "on");
  const Sort bv2 = tm.mk_bv_sort(2);
  const Sort bv1 = tm.mk_bv_sort(1);
  const Term f = tm.declare("f", tm.mk_fun_sort({bv2}, bv1));

  const Term a = tm.declare("a", bv2);
  const Term b = tm.declare("b", bv2);
  const Term c = tm.declare("c", bv2);
  s.add(!(a == b));
  s.add(!(b == c));
  s.add(!(a == c));

  const Term fa = f(a), fb = f(b), fc = f(c);
  s.add(fa == fb || (fb == fc || fa == fc));
}
} // namespace

// A declared sort is unbounded and its carrier is not: five distinct
// elements over a two-bit carrier are unsatisfiable in the encoding and
// satisfiable in the theory, so the unsat is withheld, as the command line
// withholds it, with the width to raise. A sat over a narrow carrier is a
// genuine model and is kept, and a wider carrier decides the query.
TEST(reason_unknown, ANarrowCarrierWithholdsAnUnsat)
{
  for (std::uint32_t width : {2u, 3u})
  {
    TermManager::Config config;
    config.uf_sort_width = width;
    TermManager tm(config);
    const Sort S = tm.declare_sort("S");
    std::vector<Term> elements;
    for (int i = 0; i < 5; ++i)
      elements.push_back(tm.declare("e" + std::to_string(i), S));
    Solver s(tm, checked());
    s.add(tm.mk_term(Kind::DISTINCT, elements));
    const Result r = s.check_sat();
    if (width == 2)
    {
      EXPECT_TRUE(r.is_unknown()) << r;
      EXPECT_EQ(UnknownReason::CARRIER_EXHAUSTED, r.reason());
      EXPECT_NE(std::string::npos, r.reason_message().find("raise uf-sort-width to at least 3"))
          << r.reason_message();
    }
    else
      EXPECT_TRUE(r.is_sat()) << r;
  }
  // a query that fits the carrier keeps its refutation
  TermManager::Config config;
  config.uf_sort_width = 2;
  TermManager tm(config);
  const Sort S = tm.declare_sort("S");
  const Term u = tm.declare("u", S);
  Solver s(tm, checked());
  s.add(u != u);
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST(reason_unknown, AnAssumedInjectivityIsRetractedRatherThanReported)
{
  TermManager tm;
  Solver s(tm, checked());
  s.options().set_bool("uf-inject-args", true);
  assert_pigeonhole(tm, s);

  const Result r = s.check_sat({}, CheckBudget{});
  EXPECT_TRUE(r.is_sat()) << r;
  EXPECT_EQ(UnknownReason::NONE, r.reason());
  EXPECT_EQ("", r.reason_message());
}

// Same query, option clear. Equal to the above is the entire point: the
// option is a search hint, and a hint that changed the answer would not be
// one.
TEST(reason_unknown, TheSameQueryAnswersTheSameWithoutTheAssumption)
{
  TermManager tm;
  Solver s(tm, checked());
  s.options().set_bool("uf-inject-args", false);
  assert_pigeonhole(tm, s);

  const Result r = s.check_sat({}, CheckBudget{});
  EXPECT_TRUE(r.is_sat()) << r;
  EXPECT_EQ(UnknownReason::NONE, r.reason());
}

// And an unsatisfiable query with the assumption installed over it keeps its
// refutation. Taking an answer back on the assumption's account is the cost of
// the rule; taking one back that the assumption had nothing to do with would
// be the rule quietly failing to be a search hint.
TEST(reason_unknown, AnUnsatisfiableQueryKeepsItsRefutationUnderTheAssumption)
{
  TermManager tm;
  Solver s(tm, checked());
  s.options().set_bool("uf-inject-args", true);
  s.options().set_str("uninterpreted-functions", "on");
  const Sort bv4 = tm.mk_bv_sort(4);
  const Term g = tm.declare("g", tm.mk_fun_sort({bv4}, bv4));

  const Term p = tm.declare("p", bv4);
  const Term q = tm.declare("q", bv4);
  s.add(!(g(p) == g(q)));
  s.add(p == q);

  const Result r = s.check_sat({}, CheckBudget{});
  EXPECT_TRUE(r.is_unsat()) << r;
  EXPECT_EQ(UnknownReason::NONE, r.reason());
}

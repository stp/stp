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

// api3-solver.cpp -- the solver: the assertion stack, resets, checks with
// assumptions, entailment, incremental sessions, budgets, interrupts,
// terminators, candidate models, statistics, CNF output and moved-from
// solvers (several live solvers per manager: api3-solvers.cpp).

#include "api3_common.hpp"

#include <atomic>
#include <chrono>
#include <sstream>
#include <thread>

using namespace stp;
using namespace std::chrono_literals;

namespace
{

class SolverTest : public ::testing::Test
{
protected:
  TermManager tm;
  Solver s{tm};
  Sort bv8 = tm.mk_bv_sort(8);
  Term x = tm.declare("x", bv8), y = tm.declare("y", bv8);
  Term a = tm.declare("a", tm.mk_bool_sort()), b = tm.declare("b", tm.mk_bool_sort());
};

TEST_F(SolverTest, assertion_stack)
{
  EXPECT_EQ(s.level(), 0u);
  EXPECT_TRUE(s.assertions().empty());
  const Term f1 = x == 1, f2 = y == 2, f3 = bvult(x, y);
  s.add(f1);
  s.push();
  EXPECT_EQ(s.level(), 1u);
  s.assert_formula(f2);
  s.push();
  s.add(f3);
  EXPECT_EQ(s.level(), 2u);
  std::vector<Term> all = s.assertions();
  ASSERT_EQ(all.size(), 3u);
  EXPECT_TRUE(all[0].same_as(f1)); // outermost first
  EXPECT_TRUE(all[1].same_as(f2));
  EXPECT_TRUE(all[2].same_as(f3));
  s.pop();
  EXPECT_EQ(s.level(), 1u);
  all = s.assertions();
  ASSERT_EQ(all.size(), 2u);
  EXPECT_TRUE(all[1].same_as(f2));
  s.pop(1);
  EXPECT_EQ(s.level(), 0u);
  ASSERT_EQ(s.assertions().size(), 1u);
  EXPECT_TRUE(s.assertions()[0].same_as(f1));
  // pop below zero: refused, nothing removed
  auto e = API3_ERROR_OF(s.pop());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::INVALID_ARGUMENT);
  EXPECT_EQ(e->function(), "Solver::pop");
  EXPECT_EQ(s.level(), 0u);
  EXPECT_EQ(s.assertions().size(), 1u);
  s.push(3);
  EXPECT_EQ(s.level(), 3u);
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, s.pop(4));
  EXPECT_EQ(s.level(), 3u);
  s.pop(3);
  EXPECT_EQ(s.level(), 0u);
  s.pop(0);
  EXPECT_EQ(s.level(), 0u);
  // what may be asserted
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.add(x));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.add(tm.mk_bv(1, 1)));
  API3_EXPECT_ERROR(ErrorCode::NULL_HANDLE, s.add(Term()));
  TermManager other;
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, s.add(other.mk_true()));
  API3_EXPECT_ERROR(ErrorCode::FOREIGN_MANAGER, s.check_sat({other.mk_true()}));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.check_sat({x}));
  API3_EXPECT_ERROR(ErrorCode::SORT_MISMATCH, s.entails(x));
  EXPECT_EQ(s.assertions().size(), 1u);
  s.add(tm.mk_true());
  s.add(tm.mk_false());
  EXPECT_EQ(s.assertions().size(), 3u);
  EXPECT_TRUE(s.check_sat().is_unsat());
  EXPECT_TRUE(s.manager() == tm);
  EXPECT_TRUE(s.symbol("x")->same_as(x));
}

TEST_F(SolverTest, resets)
{
  s.options().set_duration("max-time", 5s);
  s.options().set_bool("flattening", false);
  s.add(x == 1);
  s.push();
  s.add(y == 2);
  ASSERT_TRUE(s.check_sat().is_sat());
  s.reset_assertions();
  EXPECT_EQ(s.level(), 0u);
  EXPECT_TRUE(s.assertions().empty());
  EXPECT_EQ(s.options().get_duration("max-time").count(), 5000); // options kept
  EXPECT_FALSE(s.options().get_bool("flattening"));
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model()); // the last answer is gone
  s.add(x == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(x), 3u);
  s.reset();
  EXPECT_EQ(s.level(), 0u);
  EXPECT_TRUE(s.assertions().empty());
  EXPECT_EQ(s.options().get_duration("max-time").count(), -1); // options back to defaults
  EXPECT_TRUE(s.options().get_bool("flattening"));
  EXPECT_FALSE(s.options().is_set("max-time"));
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
  // before-first-check entries open again after a reset
  s.options().set_uint("random-seed", 11);
  EXPECT_EQ(s.options().get_uint("random-seed"), 11u);
  s.add(x == 4);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(x), 4u);
  // the manager's symbols survive both resets
  EXPECT_TRUE(tm.symbol("x")->same_as(x));
}

TEST_F(SolverTest, assumptions_and_unsat_assumptions)
{
  API3_EXPECT_ERROR(ErrorCode::STATE, s.unsat_assumptions()); // nothing checked yet
  s.add(implies(a, x == 0));
  const Result r = s.check_sat({a, !(x == 0)});
  EXPECT_TRUE(r.is_unsat());
  EXPECT_EQ(r.verdict(), Verdict::UNSAT);
  EXPECT_EQ(r.reason(), UnknownReason::NONE);
  EXPECT_TRUE(r.reason_message().empty());
  EXPECT_EQ(r.str(), "unsat");
  const std::vector<Term> failed = s.unsat_assumptions();
  EXPECT_FALSE(failed.empty());
  EXPECT_LE(failed.size(), 2u);
  for (const Term& t : failed)
    EXPECT_TRUE(t.same_as(a) || t.same_as(!(x == 0)));
  EXPECT_EQ(s.level(), 0u); // the assumptions were not asserted
  EXPECT_EQ(s.assertions().size(), 1u);
  // sat with assumptions: a model, and unsat_assumptions is STATE
  const Result r2 = s.check_sat({a});
  EXPECT_TRUE(r2.is_sat());
  EXPECT_EQ(s.model().uint64_value(x), 0u);
  EXPECT_TRUE(s.model().bool_value(a));
  auto e = API3_ERROR_OF(s.unsat_assumptions());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::STATE);
  // without assumptions the failed set of an unsat check is empty
  s.add(!a);
  s.add(a);
  EXPECT_TRUE(s.check_sat().is_unsat());
  EXPECT_TRUE(s.unsat_assumptions().empty());
  EXPECT_TRUE(s.check_sat({}).is_unsat());
}

TEST_F(SolverTest, unsat_assumptions_subset_under_the_incremental_driver)
{
  TermManager t2;
  Options o;
  o.set_str("incremental", "on");
  Solver inc(t2, o);
  const Term p = t2.declare("p", t2.mk_bool_sort()), q = t2.declare("q", t2.mk_bool_sort());
  const Term z = t2.declare("z", t2.mk_bv_sort(8));
  inc.add(implies(p, z == 0));
  const Result r = inc.check_sat({p, !(z == 0), q});
  ASSERT_TRUE(r.is_unsat());
  const std::vector<Term> failed = inc.unsat_assumptions();
  ASSERT_EQ(failed.size(), 2u);
  EXPECT_TRUE(failed[0].same_as(p) || failed[1].same_as(p));
  for (const Term& t : failed)
    EXPECT_FALSE(t.same_as(q)); // q played no part
  EXPECT_EQ(inc.statistics().uint64("incremental.engaged"), 1u);
  EXPECT_TRUE(inc.check_sat({q}).is_sat());
  EXPECT_TRUE(inc.model().bool_value(q));
}

TEST_F(SolverTest, entails)
{
  s.add(bvult(x, 10));
  EXPECT_TRUE(s.entails(bvult(x, 11)).is_valid());
  EXPECT_EQ(s.entails(bvult(x, 11)).validity(), Validity::VALID);
  EXPECT_EQ(s.entails(bvult(x, 11)).str(), "valid");
  const Entailment inv = s.entails(bvult(x, 3));
  EXPECT_TRUE(inv.is_invalid());
  EXPECT_EQ(inv.str(), "invalid");
  EXPECT_EQ(inv.reason(), UnknownReason::NONE);
  // the countermodel of an invalid entailment is the model
  const Model m = s.model();
  EXPECT_GE(m.uint64_value(x), 3u);
  EXPECT_LT(m.uint64_value(x), 10u);
  EXPECT_EQ(s.assertions().size(), 1u); // entails asserts nothing
  EXPECT_EQ(s.level(), 0u);
  // an entailment the budget cuts short is unknown with the budget's reason
  TermManager t2;
  Solver hard(t2);
  api3::add_hard_factoring(t2, hard);
  const Entailment unk = hard.entails(t2.mk_false(), CheckBudget{0ms, std::nullopt});
  EXPECT_TRUE(unk.is_unknown());
  EXPECT_EQ(unk.reason(), UnknownReason::TIMEOUT);
  EXPECT_FALSE(unk.reason_message().empty());
  EXPECT_EQ(unk.str(), "unknown (timeout)");
  std::ostringstream os;
  os << unk << " " << inv;
  EXPECT_EQ(os.str(), "unknown (timeout) invalid");
  EXPECT_TRUE(Entailment(Result(Verdict::UNSAT, UnknownReason::NONE, "")).is_valid());
  EXPECT_TRUE(Entailment(Result(Verdict::SAT, UnknownReason::NONE, "")).is_invalid());
  EXPECT_TRUE(Entailment().is_unknown());
  EXPECT_EQ(Entailment().reason(), UnknownReason::OTHER);
}

TEST_F(SolverTest, incremental_session)
{
  TermManager t2;
  Options o;
  o.set_str("incremental", "on");
  Solver inc(t2, o);
  const Term v = t2.declare("v", t2.mk_bv_sort(16)), w = t2.declare("w", t2.mk_bv_sort(16));
  inc.add(bvmul(v, w) == 91);
  inc.add(bvugt(v, 1));
  inc.add(bvugt(w, 1));
  inc.push();
  inc.add(bvult(v, w));
  ASSERT_TRUE(inc.check_sat().is_sat());
  const std::uint64_t v1 = inc.model().uint64_value(v);
  inc.add(v != inc.model().value(v));
  const Result r2 = inc.check_sat();
  if (r2.is_sat())
  {
    EXPECT_NE(inc.model().uint64_value(v), v1);
  }
  inc.add(v == 200);
  EXPECT_TRUE(inc.check_sat().is_unsat());
  inc.pop();
  EXPECT_TRUE(inc.check_sat().is_sat());
  EXPECT_EQ((inc.model().uint64_value(v) * inc.model().uint64_value(w)) & 0xffff, 91u);
  EXPECT_GE(inc.statistics().uint64("checks.total"), 4u);
  EXPECT_EQ(inc.statistics().uint64("incremental.engaged"), 1u);
  // the auto mode engages after pushes as well
  s.add(bvmul(x, y) == 6);
  s.add(bvult(x, 16));
  s.add(bvult(y, 16));
  s.push();
  s.add(x == 2);
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(y), 3u);
  s.pop();
  s.push();
  s.add(x == 3);
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(y), 2u);
  s.pop();
  s.add(bvugt(x, 6));
  s.add(bvugt(y, 6));
  s.add(bvult(x, 20));
  s.add(bvult(y, 20));
  EXPECT_TRUE(s.check_sat().is_unsat());
}

TEST_F(SolverTest, budgets)
{
  api3::add_hard_factoring(tm, s);
  // a zero time budget gives up at once
  const auto start = std::chrono::steady_clock::now();
  const Result r = s.check_sat({}, CheckBudget{0ms, std::nullopt});
  EXPECT_TRUE(r.is_unknown());
  EXPECT_EQ(r.reason(), UnknownReason::TIMEOUT);
  EXPECT_FALSE(r.reason_message().empty());
  EXPECT_EQ(r.str(), "unknown (timeout)");
  EXPECT_LT(std::chrono::steady_clock::now() - start, 5s);
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
  API3_EXPECT_ERROR(ErrorCode::STATE, s.unsat_assumptions()); // unknown: no failed set
  // a small time budget is honoured mid-search
  const auto t0 = std::chrono::steady_clock::now();
  const Result rt = s.check_sat({}, CheckBudget{300ms, std::nullopt});
  EXPECT_TRUE(rt.is_unknown());
  EXPECT_EQ(rt.reason(), UnknownReason::TIMEOUT);
  EXPECT_LT(std::chrono::steady_clock::now() - t0, 10s);
  // a conflict budget
  const Result rc = s.check_sat({}, CheckBudget{std::nullopt, std::uint64_t(50)});
  EXPECT_TRUE(rc.is_unknown());
  EXPECT_EQ(rc.reason(), UnknownReason::CONFLICT_LIMIT);
  EXPECT_FALSE(rc.reason_message().empty());
  EXPECT_EQ(rc.str(), "unknown (conflict-limit)");
  // both: the time budget is the one that reports when it fires first
  const Result rb = s.check_sat({}, CheckBudget{0ms, std::uint64_t(1000000)});
  EXPECT_EQ(rb.reason(), UnknownReason::TIMEOUT);
  // the persistent options
  s.options().set_duration("max-time", 200ms);
  const Result rp = s.check_sat();
  EXPECT_TRUE(rp.is_unknown());
  EXPECT_EQ(rp.reason(), UnknownReason::TIMEOUT);
  s.options().reset("max-time");
  s.options().set_int("max-num-confl", 20);
  const Result rq = s.check_sat();
  EXPECT_EQ(rq.reason(), UnknownReason::CONFLICT_LIMIT);
  // a per-check budget overrides the option for that call only
  s.options().set_duration("max-time", 0ms);
  // (a generous time budget: the conflict limit must be the one that fires,
  // however slow the build -- sanitizers, 32-bit)
  EXPECT_EQ(s.check_sat({}, CheckBudget{60s, std::uint64_t(10)}).reason(), UnknownReason::CONFLICT_LIMIT);
  EXPECT_EQ(s.check_sat().reason(), UnknownReason::TIMEOUT);
  EXPECT_EQ(s.options().get_duration("max-time").count(), 0);
  // an easy problem answers under any budget
  TermManager t2;
  Solver easy(t2);
  const Term z = t2.declare("z", t2.mk_bv_sort(8));
  easy.add(z == 5);
  EXPECT_TRUE(easy.check_sat({}, CheckBudget{1000ms, std::uint64_t(1000)}).is_sat());
  EXPECT_EQ(easy.model().uint64_value(z), 5u);
}

TEST_F(SolverTest, interrupt_from_another_thread)
{
  const std::optional<std::string> backend = api3::interruptible_backend();
  if (!backend)
    GTEST_SKIP() << "no backend of this build can be interrupted mid-search";
  TermManager t2;
  Options o;
  o.set_str("sat-backend", *backend);
  Solver hard(t2, o);
  api3::add_hard_factoring(t2, hard);
  EXPECT_FALSE(hard.interrupt_pending());
  std::thread stopper([&hard] {
    std::this_thread::sleep_for(300ms);
    hard.interrupt(); // the one call allowed from another thread
  });
  const auto start = std::chrono::steady_clock::now();
  const Result r = hard.check_sat();
  const auto elapsed = std::chrono::steady_clock::now() - start;
  stopper.join();
  EXPECT_TRUE(r.is_unknown()) << r;
  EXPECT_EQ(r.reason(), UnknownReason::INTERRUPTED);
  EXPECT_EQ(r.reason_message(), "the check was interrupted");
  EXPECT_LT(elapsed, 10s);
  EXPECT_GE(elapsed, 250ms);
  EXPECT_FALSE(hard.interrupt_pending()); // consumed by the check that reported it
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, hard.model());
  // the solver is usable afterwards
  EXPECT_EQ(hard.check_sat({}, CheckBudget{0ms, std::nullopt}).reason(), UnknownReason::TIMEOUT);
  // a stop request inside a time budget: INTERRUPTED wins
  std::thread stopper2([&hard] {
    std::this_thread::sleep_for(200ms);
    hard.interrupt();
  });
  const Result r2 = hard.check_sat({}, CheckBudget{5s, std::nullopt});
  stopper2.join();
  EXPECT_EQ(r2.reason(), UnknownReason::INTERRUPTED);
}

TEST_F(SolverTest, interrupt_pending_and_clear)
{
  s.add(x == 1);
  // a pending interrupt is consumed by the next check
  s.interrupt();
  EXPECT_TRUE(s.interrupt_pending());
  const Result r = s.check_sat();
  EXPECT_TRUE(r.is_unknown());
  EXPECT_EQ(r.reason(), UnknownReason::INTERRUPTED);
  EXPECT_FALSE(s.interrupt_pending());
  EXPECT_TRUE(s.check_sat().is_sat()); // and only that one
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, [&] {
    s.interrupt();
    s.check_sat();
    s.model();
  }());
  // clear_interrupt discards it
  s.interrupt();
  s.interrupt(); // idempotent
  EXPECT_TRUE(s.interrupt_pending());
  s.clear_interrupt();
  EXPECT_FALSE(s.interrupt_pending());
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.model().uint64_value(x), 1u);
  // entails is interrupted the same way
  s.interrupt();
  EXPECT_EQ(s.entails(x == 1).reason(), UnknownReason::INTERRUPTED);
  EXPECT_TRUE(s.entails(x == 1).is_valid());
}

TEST_F(SolverTest, terminator)
{
  struct Counting : Terminator
  {
    std::atomic<int> polls{0};
    std::chrono::steady_clock::time_point start = std::chrono::steady_clock::now();
    std::chrono::milliseconds after{300};
    bool terminate() override
    {
      ++polls;
      return std::chrono::steady_clock::now() - start >= after;
    }
  };
  const std::optional<std::string> backend = api3::interruptible_backend();
  if (!backend)
    GTEST_SKIP() << "no backend of this build can be interrupted mid-search";
  TermManager t2;
  Options o;
  o.set_str("sat-backend", *backend);
  Solver hard(t2, o);
  api3::add_hard_factoring(t2, hard);
  Counting term;
  hard.set_terminator(&term);
  const auto start = std::chrono::steady_clock::now();
  const Result r = hard.check_sat();
  EXPECT_TRUE(r.is_unknown()) << r;
  EXPECT_EQ(r.reason(), UnknownReason::INTERRUPTED);
  EXPECT_LT(std::chrono::steady_clock::now() - start, 10s);
  EXPECT_GT(term.polls.load(), 1);
  EXPECT_FALSE(hard.interrupt_pending()); // a terminator leaves no pending flag
  // a terminator that never fires lets the budget report
  struct Never : Terminator
  {
    bool terminate() override { return false; }
  } never;
  hard.set_terminator(&never);
  EXPECT_EQ(hard.check_sat({}, CheckBudget{200ms, std::nullopt}).reason(), UnknownReason::TIMEOUT);
  // nullptr clears it
  hard.set_terminator(nullptr);
  EXPECT_EQ(hard.check_sat({}, CheckBudget{0ms, std::nullopt}).reason(), UnknownReason::TIMEOUT);
  // one that fires at once on an easy problem
  struct Always : Terminator
  {
    bool terminate() override { return true; }
  } always;
  s.add(bvmul(x, y) == 6);
  s.set_terminator(&always);
  const Result r2 = s.check_sat();
  EXPECT_TRUE(r2.is_unknown() && r2.reason() == UnknownReason::INTERRUPTED) << r2;
  s.set_terminator(nullptr);
  EXPECT_TRUE(s.check_sat().is_sat());
}

TEST_F(SolverTest, candidate_model_is_optional)
{
  s.add(x == 1);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_FALSE(s.candidate_model().has_value()); // sat has a model, no candidate
  api3::add_hard_factoring(tm, s);
  const Result r = s.check_sat({}, CheckBudget{std::nullopt, std::uint64_t(20)});
  ASSERT_TRUE(r.is_unknown());
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, s.model());
  const std::optional<Model> cand = s.candidate_model();
  if (cand.has_value())
  {
    // when the engine left one, its values are readable
    const Term v = cand->value(x);
    EXPECT_TRUE(v.is_value());
    EXPECT_TRUE(v.sort() == bv8);
  }
  s.add(tm.mk_false());
  EXPECT_TRUE(s.check_sat().is_unsat());
  EXPECT_FALSE(s.candidate_model().has_value());
}

TEST_F(SolverTest, statistics)
{
  const Statistics before = s.statistics();
  EXPECT_EQ(before.uint64("checks.total"), 0u);
  s.add(bvmul(x, y) == 6);
  s.add(bvugt(x, 1));
  s.add(bvugt(y, 1));
  ASSERT_TRUE(s.check_sat().is_sat());
  const Statistics st = s.statistics();
  EXPECT_EQ(st.uint64("checks.total"), 1u);
  EXPECT_GE(st.real("time.total_ms"), 0.0);
  EXPECT_TRUE(has_sat_backend(st.str("sat.backend")));
  EXPECT_EQ(st.str("checks.total"), "1");
  EXPECT_FALSE(st.entries().empty());
  EXPECT_EQ(st.entries().count("sat.backend"), 1u);
  EXPECT_EQ(st.tier("checks.total"), Tier::STABLE);
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, st.get("no.such.statistic"));
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, st.tier("no.such.statistic"));
  API3_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, st.uint64("sat.backend"));
  std::ostringstream os;
  os << st;
  EXPECT_NE(os.str().find("checks.total = 1"), std::string::npos);
  EXPECT_TRUE(s.check_sat().is_sat());
  EXPECT_EQ(s.statistics().uint64("checks.total"), 2u);
  // a statistic the registry knows but this check did not produce reads as zero
  const Statistics empty;
  EXPECT_TRUE(empty.entries().empty());
  EXPECT_EQ(empty.uint64("checks.total"), 0u);
  EXPECT_EQ(empty.str("sat.backend"), "");
}

TEST_F(SolverTest, write_cnf)
{
  // trivial forms
  std::ostringstream none;
  s.write_cnf(none);
  EXPECT_EQ(none.str(), "c decided before CNF generation: sat\np cnf 0 0\n");
  s.push();
  s.add(tm.mk_false());
  std::ostringstream contradiction;
  s.write_cnf(contradiction);
  EXPECT_EQ(contradiction.str(), "c decided before CNF generation: unsat\np cnf 1 2\n1 0\n-1 0\n");
  s.pop();
  // a real DIMACS body for a problem that reaches the bit-blaster
  s.add(bvmul(x, y) == 6);
  s.add(bvugt(x, 1));
  s.add(bvugt(y, 1));
  ASSERT_TRUE(s.check_sat().is_sat());
  const std::uint64_t xv = s.model().uint64_value(x);
  const std::uint64_t checks = s.statistics().uint64("checks.total");
  std::ostringstream cnf;
  s.write_cnf(cnf);
  const std::string text = cnf.str();
  const std::size_t header = text.find("p cnf ");
  ASSERT_NE(header, std::string::npos) << text.substr(0, 200);
  std::istringstream head(text.substr(header + 6));
  std::size_t vars = 0, clauses = 0;
  head >> vars >> clauses;
  EXPECT_GT(vars, 0u);
  EXPECT_GT(clauses, 0u);
  // every clause line ends in 0 and the count matches
  std::size_t counted = 0;
  std::istringstream lines(text.substr(text.find('\n', header) + 1));
  std::string line;
  while (std::getline(lines, line))
    if (!line.empty() && line[0] != 'c')
    {
      ++counted;
      EXPECT_EQ(line.substr(line.size() - 2), " 0") << line;
    }
  EXPECT_EQ(counted, clauses);
  // writing the CNF left the solver where it was
  EXPECT_EQ(s.model().uint64_value(x), xv);
  EXPECT_EQ(s.statistics().uint64("checks.total"), checks);
  EXPECT_EQ(s.assertions().size(), 3u);
  EXPECT_EQ(s.level(), 0u);
  EXPECT_TRUE(s.check_sat().is_sat());
  // stop-after-cnf as an option answers unknown(STOPPED_AFTER_CNF) on the
  // batch pipeline (a session the pushes made incremental is not stopped:
  // FINDINGS.md, design points)
  TermManager t2;
  Solver fresh(t2);
  const Term p = t2.declare("p", t2.mk_bv_sort(8)), q = t2.declare("q", t2.mk_bv_sort(8));
  fresh.add(bvmul(p, q) == 6);
  fresh.add(bvugt(p, 1));
  fresh.add(bvugt(q, 1));
  fresh.options().set_bool("stop-after-cnf", true);
  const Result r = fresh.check_sat();
  EXPECT_TRUE(r.is_unknown());
  EXPECT_EQ(r.reason(), UnknownReason::STOPPED_AFTER_CNF);
  EXPECT_EQ(r.str(), "unknown (stopped-after-cnf)");
  EXPECT_FALSE(r.reason_message().empty());
  API3_EXPECT_ERROR(ErrorCode::NO_MODEL, fresh.model());
  fresh.options().set_bool("stop-after-cnf", false);
  EXPECT_TRUE(fresh.check_sat().is_sat());
  EXPECT_EQ(fresh.assertions().size(), 3u);
}

TEST_F(SolverTest, moved_from_solvers)
{
  EXPECT_EQ(capabilities()["solvers-per-manager"], "unbounded");
  s.add(x == 1);
  EXPECT_TRUE(s.check_sat().is_sat()); // the first is untouched
  // a moved-from solver is empty; the target owns the state
  Solver moved = std::move(s);
  EXPECT_TRUE(moved.check_sat().is_sat());
  EXPECT_EQ(moved.model().uint64_value(x), 1u);
  EXPECT_EQ(moved.assertions().size(), 1u);
  API3_EXPECT_ERROR(ErrorCode::STATE, s.check_sat());
  API3_EXPECT_ERROR(ErrorCode::STATE, s.assertions());
  API3_EXPECT_ERROR(ErrorCode::STATE, s.push());
  API3_EXPECT_ERROR(ErrorCode::STATE, s.add(x == 1));
  API3_EXPECT_ERROR(ErrorCode::STATE, s.model());
  API3_EXPECT_ERROR(ErrorCode::STATE, s.options());
  API3_EXPECT_ERROR(ErrorCode::STATE, s.statistics());
  API3_EXPECT_ERROR(ErrorCode::STATE, s.manager());
  API3_EXPECT_ERROR(ErrorCode::STATE, s.parse_smt2("(check-sat)"));
  API3_EXPECT_ERROR(ErrorCode::STATE, s.to_smt2());
  EXPECT_EQ(s.level(), 0u);
  EXPECT_FALSE(s.interrupt_pending());
  s.interrupt(); // a no-op, not a crash
  s.clear_interrupt();
  Solver third(tm); // any number of solvers over the manager
  EXPECT_TRUE(third.check_sat().is_sat());
  EXPECT_TRUE(third.assertions().empty());
  // move-assignment releases the target's engine
  {
    TermManager t2;
    Solver other(t2);
    other.add(t2.mk_true());
    other = std::move(moved);
    EXPECT_TRUE(other.manager() == tm);
    EXPECT_EQ(other.model().uint64_value(x), 1u);
    Solver again(t2); // t2's solver was released by the assignment
    EXPECT_TRUE(again.check_sat().is_sat());
  }
  // and after the live solver is gone a new one is admitted
  Solver fresh(tm);
  EXPECT_TRUE(fresh.assertions().empty());
  fresh.add(x == 2);
  EXPECT_TRUE(fresh.check_sat().is_sat());
  EXPECT_EQ(fresh.model().uint64_value(x), 2u);
}

TEST_F(SolverTest, produce_models_off_and_array_fill)
{
  TermManager t2;
  Options o;
  o.set_bool(Option::PRODUCE_MODELS, false);
  Solver quiet(t2, o);
  const Term z = t2.declare("z", t2.mk_bv_sort(8));
  quiet.add(z == 3);
  ASSERT_TRUE(quiet.check_sat().is_sat());
  auto e = API3_ERROR_OF(quiet.model());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::NO_MODEL);
  EXPECT_NE(std::string(e->what()).find("produce-models"), std::string::npos);
  quiet.options().set_bool("produce-models", true); // anytime
  ASSERT_TRUE(quiet.check_sat().is_sat());
  EXPECT_EQ(quiet.model().uint64_value(z), 3u);
  // model-array-fill decides the unobserved cells
  const Sort A = t2.mk_array_sort(t2.mk_bv_sort(8), t2.mk_bv_sort(8));
  const Term arr = t2.declare("arr", A);
  quiet.add(arr[t2.mk_bv(8, 1)] == 9);
  ASSERT_TRUE(quiet.check_sat().is_sat());
  EXPECT_EQ(quiet.model().uint64_value(arr[t2.mk_bv(8, 2)]), 0u);
  EXPECT_EQ(quiet.model().array_value(arr).default_value().to_uint64(), 0u);
  quiet.options().set_str("model-array-fill", "ones");
  ASSERT_TRUE(quiet.check_sat().is_sat());
  EXPECT_EQ(quiet.model().uint64_value(arr[t2.mk_bv(8, 2)]), 0xffu);
  EXPECT_EQ(quiet.model().uint64_value(arr[t2.mk_bv(8, 1)]), 9u);
  EXPECT_EQ(quiet.model().array_value(arr).default_value().to_uint64(), 0xffu);
  std::uint8_t bytes[3] = {0, 0, 0};
  quiet.model().array_bytes(arr, 0, 3, bytes);
  EXPECT_EQ(bytes[0], 0xffu);
  EXPECT_EQ(bytes[1], 9u);
  EXPECT_EQ(bytes[2], 0xffu);
  // a Bool-valued diagnostic sink is accepted
  std::string sink;
  quiet.set_diagnostic_sink([&sink](std::string_view s) { sink.append(s); });
  EXPECT_TRUE(quiet.check_sat().is_sat());
  quiet.set_diagnostic_sink(nullptr);
}

TEST_F(SolverTest, content_a_switched_off_theory_cannot_decide)
{
  // uninterpreted-functions = off with an application asserted: refused at
  // the check, which therefore was no check, so the mode can still change
  {
    TermManager t;
    Options o;
    o.set("uninterpreted-functions", "off");
    Solver u(t, o);
    const Sort w8 = t.mk_bv_sort(8);
    const Term p = t.declare("p", w8), q = t.declare("q", w8), r = t.declare("r", w8);
    const Term f = t.declare("f", t.mk_fun_sort({w8}, w8));
    u.add(bvult(p, q));
    u.add(f(p) == bvadd(q, 1));
    u.push();
    u.add(p == r);
    API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, u.check_sat());
    API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, u.entails(f(p) == f(r)));
    EXPECT_EQ(u.level(), 1u);
    EXPECT_EQ(u.assertions().size(), 3u);
    u.options().set("uninterpreted-functions", "auto");
    EXPECT_TRUE(u.check_sat().is_sat());
    EXPECT_TRUE(u.entails(f(p) == f(r)).is_valid());
  }
  // array-equality switched off after an array equality was asserted
  {
    TermManager t;
    Solver u(t);
    const Sort as = t.mk_array_sort(t.mk_bv_sort(4), t.mk_bv_sort(4));
    const Term c = t.declare("c", as), d = t.declare("d", as);
    u.add(c == d);
    u.add(c[t.mk_bv(4, 1)] != d[t.mk_bv(4, 1)]);
    u.options().set("array-equality", "off");
    API3_EXPECT_ERROR(ErrorCode::UNSUPPORTED, u.check_sat());
    u.options().set("array-equality", "auto");
    EXPECT_TRUE(u.check_sat().is_unsat());
  }
}

TEST(Results, value_type)
{
  const Result d;
  EXPECT_TRUE(d.is_unknown());
  EXPECT_EQ(d.reason(), UnknownReason::OTHER);
  EXPECT_EQ(d.str(), "unknown (other)");
  const Result sat(Verdict::SAT, UnknownReason::TIMEOUT, "ignored");
  EXPECT_TRUE(sat.is_sat());
  EXPECT_EQ(sat.reason(), UnknownReason::NONE); // reasons belong to unknown
  EXPECT_TRUE(sat.reason_message().empty());
  const Result unk(Verdict::UNKNOWN, UnknownReason::CONFLICT_LIMIT, "budget");
  EXPECT_EQ(unk.reason_message(), "budget");
  std::ostringstream os;
  os << sat << " " << unk << " " << Verdict::UNSAT << " " << UnknownReason::INTERRUPTED;
  EXPECT_EQ(os.str(), "sat unknown (conflict-limit) unsat interrupted");
  EXPECT_EQ(static_cast<int>(Verdict::SAT), 1);
  EXPECT_EQ(static_cast<int>(Verdict::UNSAT), 2);
  EXPECT_EQ(static_cast<int>(Verdict::UNKNOWN), 3);
  EXPECT_STREQ(to_string(UnknownReason::STOPPED_AFTER_CNF), "stopped-after-cnf");
  EXPECT_STREQ(to_string(UnknownReason::CARRIER_EXHAUSTED), "carrier-exhausted");
  EXPECT_STREQ(to_string(Validity::INVALID), "invalid");
}

} // namespace

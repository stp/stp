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

// stp_solver_interrupt from another thread while a check runs, and a
// terminator callback: both must end the check with unknown(INTERRUPTED).

#include <stp/stp.h>

#include <gtest/gtest.h>

#include <atomic>
#include <chrono>
#include <cstring>
#include <thread>

namespace
{
// A backend that polls the interrupt during its search: CaDiCaL or MiniSat.
// CryptoMiniSat is interrupted between its calls only (capabilities
// "interrupt.cryptominisat"), so a build with no other backend cannot stop a
// long search from another thread.
const char* mid_search_backend()
{
  if (stp_has_sat_backend("cadical"))
    return "cadical";
  if (stp_has_sat_backend("minisat"))
    return "minisat";
  return nullptr;
}

// zext(x) * zext(y) == a 64-bit prime at 128 bits (no wrap-around) with neither
// factor 1: unsat, and hard enough for a bit-blasted multiplier that no backend
// finishes in the interrupt's window.
struct Hard
{
  stp_tm tm;
  stp_solver s;
  Hard()
  {
    tm = stp_tm_new(nullptr);
    stp_tm_scope_push(tm);
    stp_options o = stp_options_new();
    if (const char* backend = mid_search_backend())
      stp_options_set_str(o, "sat-backend", backend);
    stp_options_set_duration_ms(o, "max-time", 120000); // a broken interrupt fails, it does not hang
    s = stp_solver_new(tm, o);
    stp_options_delete(o);
    stp_sort bv64 = stp_mk_bv_sort(tm, 64);
    stp_term x = stp_declare(tm, "x", bv64);
    stp_term y = stp_declare(tm, "y", bv64);
    stp_term one = stp_mk_bv_uint64(tm, 64, 1);
    stp_term product = stp_bvmul(tm, stp_zero_extend(tm, 64, x), stp_zero_extend(tm, 64, y));
    stp_solver_assert(s, stp_eq(tm, product, stp_mk_bv_uint64(tm, 128, 18446744073709551557ull)));
    stp_solver_assert(s, stp_not(tm, stp_eq(tm, x, one)));
    stp_solver_assert(s, stp_not(tm, stp_eq(tm, y, one)));
    stp_solver_assert(s, stp_bvult(tm, x, y));
  }
  ~Hard()
  {
    stp_solver_delete(s);
    stp_tm_scope_pop(tm);
    stp_tm_release(tm);
  }
};
} // namespace

TEST(c3_interrupt, from_another_thread)
{
  if (mid_search_backend() == nullptr)
    GTEST_SKIP() << "no backend in this build stops mid-search";
  Hard h;
  ASSERT_NE(nullptr, h.s);
  ASSERT_EQ(nullptr, stp_solver_failed(h.s));
  std::atomic<bool> fired{false};
  std::thread other([&] {
    std::this_thread::sleep_for(std::chrono::milliseconds(400));
    stp_solver_interrupt(h.s); // the one call allowed from another thread
    fired.store(true);
  });
  const auto started = std::chrono::steady_clock::now();
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat(h.s, &r));
  other.join();
  const auto elapsed = std::chrono::steady_clock::now() - started;
  EXPECT_TRUE(fired.load());
  EXPECT_EQ(STP_UNKNOWN, r.kind);
  EXPECT_EQ(STP_REASON_INTERRUPTED, r.reason);
  EXPECT_LT(elapsed, std::chrono::seconds(60));
  char* why = stp_solver_last_reason_message(h.s);
  ASSERT_NE(nullptr, why);
  EXPECT_NE(nullptr, strstr(why, "interrupt"));
  stp_free(why);
  EXPECT_FALSE(stp_solver_interrupt_pending(h.s)); // consumed by the check that reported it
  // after unknown there may or may not be a candidate; either way no error
  stp_model candidate = stp_solver_candidate_model(h.s);
  EXPECT_EQ(nullptr, stp_tm_error(h.tm));
  stp_model_release(candidate);
}

TEST(c3_interrupt, pending_interrupt_is_consumed_by_the_next_check_and_can_be_cleared)
{
  Hard h;
  stp_solver_interrupt(h.s);
  EXPECT_TRUE(stp_solver_interrupt_pending(h.s));
  stp_solver_clear_interrupt(h.s);
  EXPECT_FALSE(stp_solver_interrupt_pending(h.s));
  stp_solver_interrupt(h.s);
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat(h.s, &r));
  EXPECT_EQ(STP_UNKNOWN, r.kind);
  EXPECT_EQ(STP_REASON_INTERRUPTED, r.reason);
  EXPECT_FALSE(stp_solver_interrupt_pending(h.s));
}

namespace
{
bool stop_after_some_polls(void* user)
{
  int* polls = static_cast<int*>(user);
  return ++*polls >= 3;
}
} // namespace

TEST(c3_interrupt, terminator_callback)
{
  Hard h;
  int polls = 0;
  ASSERT_EQ(STP_OK, stp_solver_set_terminator(h.s, stop_after_some_polls, &polls));
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat(h.s, &r));
  EXPECT_EQ(STP_UNKNOWN, r.kind);
  EXPECT_EQ(STP_REASON_INTERRUPTED, r.reason);
  EXPECT_GE(polls, 3);
  // cleared: a zero budget is what stops the next check
  ASSERT_EQ(STP_OK, stp_solver_set_terminator(h.s, nullptr, nullptr));
  stp_budget b;
  b.has_time = true;
  b.time_ms = 0;
  b.has_conflicts = false;
  b.conflicts = 0;
  ASSERT_EQ(STP_OK, stp_solver_check_sat_budget(h.s, 0, nullptr, &b, &r));
  EXPECT_EQ(STP_UNKNOWN, r.kind);
  EXPECT_EQ(STP_REASON_TIMEOUT, r.reason);
  EXPECT_EQ(nullptr, stp_solver_model(h.s));
  EXPECT_EQ(STP_ERR_NO_MODEL, stp_tm_error(h.tm)->code);
  stp_tm_clear_error(h.tm);
}

TEST(c3_interrupt, conflict_budget_and_assumptions)
{
  Hard h;
  stp_budget b;
  b.has_time = false;
  b.time_ms = 0;
  b.has_conflicts = true;
  b.conflicts = 1;
  stp_result r;
  ASSERT_EQ(STP_OK, stp_solver_check_sat_budget(h.s, 0, nullptr, &b, &r));
  EXPECT_EQ(STP_UNKNOWN, r.kind);
  EXPECT_EQ(STP_REASON_CONFLICT_LIMIT, r.reason);
  // an assumption that contradicts the assertions comes back as the failed subset
  stp_term x = stp_tm_symbol(h.tm, "x");
  stp_term assumption = stp_eq(h.tm, x, stp_mk_bv_uint64(h.tm, 64, 1));
  ASSERT_EQ(STP_OK, stp_solver_check_sat_assuming(h.s, 1, &assumption, &r));
  EXPECT_EQ(STP_UNSAT, r.kind);
  ASSERT_EQ(1u, stp_solver_num_unsat_assumptions(h.s));
  EXPECT_EQ(assumption, stp_solver_unsat_assumption(h.s, 0));
}

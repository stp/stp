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

// api3-fp-multi-checker.cpp -- independent floating-point problems side by
// side: two term managers, and several solvers over one, interleaved; the
// floating-point backend's binding to a manager, per thread; two threads
// solving at once; printing one model after another solver's check.
//
// This used to corrupt the second problem: floating-point blasting bound a
// process-global symfpu backend to the first manager to use it. Each manager
// now blasts into itself, so both give correct results.
//
// The backend binding is engine state with no API form, so that one case
// reaches the engine managers through api3_engine.hpp.

#include "api3_engine.hpp"

#include <stp/FloatBlaster/symbolic_fp.h>

#include <condition_variable>
#include <cstdint>
#include <mutex>
#include <string>
#include <thread>

using namespace stp::api;

namespace
{

// Every solver here runs with the engine's counterexample self-check on
// (check-sanity), as every 2.x validity checker did.
Options sanity_checked()
{
  Options o;
  o.set_bool("check-sanity", true);
  return o;
}

// The packed IEEE bits of a float in the model of the solver's last check.
std::uint64_t ieee_bits(const Solver& s, const Term& f)
{
  return std::stoull(s.model().fp_value(f).bits(), nullptr, 2);
}

// Two independent problems are two term managers, or two solvers over one
// manager (copies of a TermManager share it); the interleaved cases run both
// ways.
const char* describe(bool one_manager)
{
  return one_manager ? "two solvers over one manager" : "two term managers";
}

} // namespace

TEST(fp_multi_checker, two_live_checkers)
{
  for (const bool one_manager : {false, true})
  {
    SCOPED_TRACE(describe(one_manager));
    TermManager tm1;
    TermManager tm2 = one_manager ? tm1 : TermManager();
    Solver v1(tm1, sanity_checked()), v2(tm2, sanity_checked());

    // v1: a is 2.0 (half); a*a is 4.0.
    const Sort f16 = tm1.mk_fp16_sort();
    const Term a = tm1.declare("a", f16);
    v1.add(fp_eq(a, tm1.mk_fp_from_bits(f16, tm1.mk_bv(16, 0x4000))));
    const Term prod = fp_mul(RoundingMode::RNE, a, a);

    // v2: b is 3.0 (double).
    const Sort f64 = tm2.mk_fp64_sort();
    const Term b = tm2.declare("b", f64);
    v2.add(fp_eq(b, tm2.mk_fp_from_bits(f64, tm2.mk_bv(64, 0x4008000000000000ULL))));

    ASSERT_TRUE(v1.check_sat().is_sat());
    ASSERT_TRUE(v2.check_sat().is_sat());

    // Read from both, interleaved.
    EXPECT_EQ(ieee_bits(v1, a), 0x4000u);
    EXPECT_EQ(ieee_bits(v2, b), 0x4008000000000000ULL);
    EXPECT_EQ(ieee_bits(v1, prod), 0x4400u); // 2.0 * 2.0 = 4.0
    EXPECT_EQ(ieee_bits(v1, a), 0x4000u);    // v1 still intact after reading v2
  }
}

// The symfpu traits API has no context parameter, so STP binds its backend to
// a manager through symbolic_fp::init. The binding must be per-thread: with a
// process-global binding, the deliberately ordered init of the second manager
// below redirects the first thread's subsequent backend operation into the
// second manager.
TEST(fp_multi_checker, concurrent_backend_contexts_are_thread_local)
{
  struct Coordination
  {
    std::mutex mutex;
    std::condition_variable changed;
    bool first_initialised = false;
    bool second_initialised = false;
    bool first_checked = false;
  } coordination;

  bool first_uses_own_manager = false;
  bool second_uses_own_manager = false;

  // Everything the threads use is made here, through the API, on the thread
  // that owns both managers; the threads themselves only drive the backend.
  TermManager first_tm, second_tm;
  stp::STPMgr& first_bm = api3::engine_manager(first_tm);
  stp::STPMgr& second_bm = api3::engine_manager(second_tm);

  const Term first_lhs = first_tm.declare("first_rm_lhs", first_tm.mk_rm_sort());
  const Term first_rhs = first_tm.declare("first_rm_rhs", first_tm.mk_rm_sort());
  const stp::ASTNode first_lhs_node = api3::engine_node(first_lhs);
  const stp::ASTNode first_rhs_node = api3::engine_node(first_rhs);
  const stp::ASTNode first_expected = api3::engine_node(first_lhs == first_rhs);

  const Term second_lhs = second_tm.declare("second_rm_lhs", second_tm.mk_rm_sort());
  const Term second_rhs = second_tm.declare("second_rm_rhs", second_tm.mk_rm_sort());
  const stp::ASTNode second_lhs_node = api3::engine_node(second_lhs);
  const stp::ASTNode second_rhs_node = api3::engine_node(second_rhs);
  const stp::ASTNode second_expected = api3::engine_node(second_lhs == second_rhs);

  std::thread first([&]() {
    stp::symbolic_fp::init(&first_bm);
    {
      std::lock_guard<std::mutex> lock(coordination.mutex);
      coordination.first_initialised = true;
    }
    coordination.changed.notify_all();

    {
      std::unique_lock<std::mutex> lock(coordination.mutex);
      coordination.changed.wait(lock, [&]() { return coordination.second_initialised; });
    }

    const stp::ASTNode n = stp::symbolic_fp::roundingMode(first_lhs_node) ==
                           stp::symbolic_fp::roundingMode(first_rhs_node);
    first_uses_own_manager = n == first_expected;

    {
      std::lock_guard<std::mutex> lock(coordination.mutex);
      coordination.first_checked = true;
    }
    coordination.changed.notify_all();
  });

  std::thread second([&]() {
    {
      std::unique_lock<std::mutex> lock(coordination.mutex);
      coordination.changed.wait(lock, [&]() { return coordination.first_initialised; });
    }

    stp::symbolic_fp::init(&second_bm);
    {
      std::lock_guard<std::mutex> lock(coordination.mutex);
      coordination.second_initialised = true;
    }
    coordination.changed.notify_all();

    {
      std::unique_lock<std::mutex> lock(coordination.mutex);
      coordination.changed.wait(lock, [&]() { return coordination.first_checked; });
    }

    const stp::ASTNode n = stp::symbolic_fp::roundingMode(second_lhs_node) ==
                           stp::symbolic_fp::roundingMode(second_rhs_node);
    second_uses_own_manager = n == second_expected;
  });

  first.join();
  second.join();

  EXPECT_TRUE(first_uses_own_manager);
  EXPECT_TRUE(second_uses_own_manager);
}

// Exercise the complete concurrent path too. In addition to the symfpu
// binding above, CNF derivation must not route two independent AIGs through
// ABC's process-global convenience manager. Each thread makes its own manager:
// a manager is used by one thread at a time.
TEST(fp_multi_checker, concurrent_floating_point_queries)
{
  struct StartGate
  {
    std::mutex mutex;
    std::condition_variable changed;
    unsigned ready = 0;
    bool go = false;
  } gate;

  bool solved[2] = {false, false};
  auto solve = [&](unsigned worker, std::uint32_t exponent_bits, std::uint32_t significand_bits) {
    TermManager tm;
    Solver s(tm, sanity_checked());
    const Sort type = tm.mk_fp_sort(exponent_bits, significand_bits);
    const Term rm = tm.mk_rm(RoundingMode::RNE);
    const Term x = tm.declare(worker == 0 ? "concurrent_x0" : "concurrent_x1", type);
    const Term root = fp_sqrt(rm, x);
    const Term result = fp_fma(rm, root, x, x);
    s.add(fp_is_normal(result));

    {
      std::unique_lock<std::mutex> lock(gate.mutex);
      ++gate.ready;
      if (gate.ready == 2)
      {
        gate.go = true;
        gate.changed.notify_all();
      }
      else
      {
        gate.changed.wait(lock, [&]() { return gate.go; });
      }
    }

    solved[worker] = s.check_sat().is_sat();
  };

  std::thread first(solve, 0, 5, 11);
  std::thread second(solve, 1, 8, 24);
  first.join();
  second.join();

  EXPECT_TRUE(solved[0]);
  EXPECT_TRUE(solved[1]);
}

// Printing the FIRST problem's model after the SECOND has been checked: the
// model-printing path must evaluate against its own manager. (The blaster
// takes the manager explicitly; this pins that no path still leans on
// whichever manager bound last.)
TEST(fp_multi_checker, print_counterexample_across_checkers)
{
  for (const bool one_manager : {false, true})
  {
    SCOPED_TRACE(describe(one_manager));
    TermManager tm1;
    TermManager tm2 = one_manager ? tm1 : TermManager();
    Solver v1(tm1, sanity_checked()), v2(tm2, sanity_checked());

    const Sort f16 = tm1.mk_fp16_sort();
    const Term a = tm1.declare("a", f16);
    v1.add(fp_eq(a, tm1.mk_fp_from_bits(f16, tm1.mk_bv(16, 0x4000))));
    EXPECT_TRUE(v1.check_sat().is_sat());

    const Term b = tm2.declare("b", tm2.mk_fp32_sort());
    v2.add(fp_is_normal(b));
    EXPECT_TRUE(v2.check_sat().is_sat()); // v2 checked last

    // Print v1's model; it must not touch v2's manager or solver.
    const std::string text = v1.model().to_smt2();
    EXPECT_FALSE(text.empty());
    EXPECT_NE(text.find("(define-fun a "), std::string::npos) << text;

    // And v1's values still read correctly.
    EXPECT_EQ(ieee_bits(v1, a), 0x4000u);
  }
}

// A checker built around an existing engine manager has no 3.x form: the term
// manager is what terms are shared through, and any number of solvers may be
// live over one. So the terms are built through the manager first, and a
// second solver joins one that is already using it: each answers over the
// shared terms, and destroying one leaves the manager and the other intact.
TEST(fp_multi_checker, checker_reuse_over_existing_manager)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_fp16_sort());

  Solver positive(tm, sanity_checked());
  positive.add(fp_is_zero(x));
  positive.add(fp_is_pos(x));
  ASSERT_TRUE(positive.check_sat().is_sat());
  {
    Solver reuse(tm, sanity_checked());
    reuse.add(fp_is_zero(x));
    reuse.add(fp_is_neg(x));
    EXPECT_TRUE(reuse.check_sat().is_sat());
    EXPECT_EQ(ieee_bits(reuse, x), 0x8000u);    // -0.0 in binary16
    EXPECT_EQ(ieee_bits(positive, x), 0x0000u); // its own model: +0.0
  }

  ASSERT_TRUE(positive.check_sat().is_sat());
  EXPECT_EQ(ieee_bits(positive, x), 0x0000u);
}

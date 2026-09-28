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

// solvers.cpp -- several live solvers over one manager: independent
// assertion stacks, options and models; interleaved checks; the incremental
// driver on one and the batch pipeline on the other; parsing into one while
// another holds assertions; destruction in either order; a solver created
// after checks; and the shelf round trip that keeps every level of a solver
// while another one owns the engine's stack.

#include "api_common.hpp"

#include <memory>
#include <optional>

using namespace stp;

namespace
{

class SolversTest : public ::testing::Test
{
protected:
  TermManager tm;
  Sort bv8 = tm.mk_bv_sort(8);
  Term x = tm.declare("x", bv8), y = tm.declare("y", bv8);
};

TEST_F(SolversTest, independent_stacks_and_models)
{
  EXPECT_EQ(capabilities()["solvers-per-manager"], "unbounded");
  Solver a(tm), b(tm);
  a.add(x == 1);
  b.add(x == 2);
  b.add(y == 3);
  EXPECT_EQ(a.assertions().size(), 1u);
  EXPECT_EQ(b.assertions().size(), 2u);
  EXPECT_TRUE(a.assertions()[0].same_as(x == 1));
  EXPECT_TRUE(b.assertions()[0].same_as(x == 2));
  ASSERT_TRUE(a.check_sat().is_sat());
  EXPECT_EQ(a.model().uint64_value(x), 1u);
  ASSERT_TRUE(b.check_sat().is_sat());
  EXPECT_EQ(b.model().uint64_value(x), 2u);
  EXPECT_EQ(b.model().uint64_value(y), 3u);
  // a's model is detached: it survives b's check and b's use of the engine
  EXPECT_EQ(a.model().uint64_value(x), 1u);
  a.add(x == 2);
  EXPECT_TRUE(a.check_sat().is_unsat());
  EXPECT_TRUE(b.check_sat().is_sat());
  EXPECT_EQ(b.model().uint64_value(x), 2u);
}

TEST_F(SolversTest, a_pending_model_is_kept_when_another_solver_runs)
{
  Solver a(tm), b(tm);
  a.add(x == 7);
  ASSERT_TRUE(a.check_sat().is_sat()); // the model is not read yet
  b.add(x == 9);
  ASSERT_TRUE(b.check_sat().is_sat());
  EXPECT_EQ(a.model().uint64_value(x), 7u); // snapshotted when a was shelved
  EXPECT_EQ(b.model().uint64_value(x), 9u);
}

TEST_F(SolversTest, levels_are_per_solver)
{
  Solver a(tm), b(tm);
  const Term f1 = x == 1, f2 = y == 2, f3 = bvult(x, y), g1 = y == 5;
  a.add(f1);
  a.push();
  a.add(f2);
  a.push();
  a.add(f3);
  EXPECT_EQ(a.level(), 2u);
  EXPECT_EQ(b.level(), 0u);
  b.push();
  b.add(g1);
  EXPECT_EQ(b.level(), 1u);
  EXPECT_EQ(a.level(), 2u); // read while a is shelved
  // the shelf round trip keeps every level in order
  std::vector<Term> all = a.assertions();
  ASSERT_EQ(all.size(), 3u);
  EXPECT_TRUE(all[0].same_as(f1));
  EXPECT_TRUE(all[1].same_as(f2));
  EXPECT_TRUE(all[2].same_as(f3));
  EXPECT_EQ(a.level(), 2u);
  a.pop();
  EXPECT_EQ(a.level(), 1u);
  EXPECT_EQ(a.assertions().size(), 2u);
  all = b.assertions();
  ASSERT_EQ(all.size(), 1u);
  EXPECT_TRUE(all[0].same_as(g1));
  EXPECT_EQ(b.level(), 1u);
  b.pop();
  EXPECT_EQ(b.level(), 0u);
  EXPECT_TRUE(b.assertions().empty());
  EXPECT_TRUE(b.check_sat().is_sat());
  ASSERT_TRUE(a.check_sat().is_sat());
  EXPECT_EQ(a.model().uint64_value(x), 1u);
  EXPECT_EQ(a.model().uint64_value(y), 2u);
  API_EXPECT_ERROR(ErrorCode::INVALID_ARGUMENT, b.pop());
}

TEST_F(SolversTest, options_are_per_solver)
{
  Options quiet;
  quiet.set_bool("produce-models", false);
  Solver a(tm, quiet), b(tm);
  a.add(x == 1);
  b.add(x == 2);
  ASSERT_TRUE(a.check_sat().is_sat());
  API_EXPECT_ERROR(ErrorCode::NO_MODEL, a.model());
  ASSERT_TRUE(b.check_sat().is_sat());
  EXPECT_EQ(b.model().uint64_value(x), 2u);
  EXPECT_FALSE(a.options().get_bool("produce-models"));
  EXPECT_TRUE(b.options().get_bool("produce-models"));
  // each solver's options are re-applied to the engine when it is used, so the
  // engine reports each one's own backend
  std::vector<std::string> backends;
  for (const char* name : {"cadical", "minisat", "cryptominisat", "simplifying-minisat"})
    if (has_sat_backend(name))
      backends.push_back(name);
  if (backends.size() >= 2)
  {
    Options oa, ob;
    oa.set_str("sat-backend", backends[0]);
    ob.set_str("sat-backend", backends[1]);
    Solver c(tm, oa), d(tm, ob);
    c.add(x == 3);
    d.add(x == 4);
    EXPECT_TRUE(c.check_sat().is_sat());
    EXPECT_TRUE(d.check_sat().is_sat());
    EXPECT_EQ(c.statistics().str("sat.backend"), backends[0]);
    EXPECT_EQ(d.statistics().str("sat.backend"), backends[1]);
    EXPECT_EQ(c.statistics().str("sat.backend"), backends[0]);
  }
}

TEST_F(SolversTest, incremental_and_batch_side_by_side)
{
  Options inc;
  inc.set("incremental", "on");
  Solver a(tm, inc), b(tm);
  a.add(bvult(x, 10));
  b.add(bvugt(x, 200));
  a.push();
  a.add(x == 3);
  ASSERT_TRUE(a.check_sat().is_sat());
  EXPECT_EQ(a.statistics().uint64("incremental.engaged"), 1u);
  ASSERT_TRUE(b.check_sat().is_sat());
  EXPECT_EQ(b.statistics().uint64("incremental.engaged"), 0u);
  EXPECT_GT(b.model().uint64_value(x), 200u);
  a.pop();
  a.push();
  a.add(x == 11);
  EXPECT_TRUE(a.check_sat().is_unsat());
  EXPECT_TRUE(b.check_sat().is_sat());
  a.pop();
  a.add(x == 4);
  ASSERT_TRUE(a.check_sat().is_sat());
  EXPECT_EQ(a.model().uint64_value(x), 4u);
  EXPECT_EQ(a.statistics().uint64("incremental.engaged"), 1u);
}

TEST_F(SolversTest, parsing_into_one_while_another_holds_assertions)
{
  Solver a(tm), b(tm);
  a.add(x == 1);
  b.parse_smt2("(declare-fun z () (_ BitVec 8))\n(assert (= z #x07))\n(assert (bvult x z))\n",
               ParseMode::DECLARE_AND_ASSERT);
  EXPECT_EQ(b.assertions().size(), 2u);
  EXPECT_EQ(a.assertions().size(), 1u);
  ASSERT_TRUE(tm.symbol("z").has_value()); // the script's declaration is the manager's
  const Term z = *tm.symbol("z");
  ASSERT_TRUE(b.check_sat().is_sat());
  EXPECT_EQ(b.model().uint64_value(z), 7u);
  EXPECT_LT(b.model().uint64_value(x), 7u);
  a.add(z == 200); // visible to the other solver too
  ASSERT_TRUE(a.check_sat().is_sat());
  EXPECT_EQ(a.model().uint64_value(z), 200u);
  EXPECT_EQ(a.model().uint64_value(x), 1u);
  // a parse that fails leaves both solvers as they were
  API_EXPECT_ERROR(ErrorCode::PARSE, a.parse_smt2("(assert (= x", ParseMode::DECLARE_AND_ASSERT));
  EXPECT_EQ(a.assertions().size(), 2u);
  EXPECT_EQ(b.assertions().size(), 2u);
  EXPECT_TRUE(b.check_sat().is_sat());
}

TEST_F(SolversTest, destruction_in_either_order)
{
  {
    auto a = std::make_unique<Solver>(tm);
    auto b = std::make_unique<Solver>(tm);
    a->add(x == 1);
    b->add(x == 2);
    ASSERT_TRUE(a->check_sat().is_sat());
    a.reset(); // the active solver goes first
    ASSERT_TRUE(b->check_sat().is_sat());
    EXPECT_EQ(b->model().uint64_value(x), 2u);
    EXPECT_EQ(b->assertions().size(), 1u);
  }
  {
    auto a = std::make_unique<Solver>(tm);
    auto b = std::make_unique<Solver>(tm);
    a->add(x == 1);
    b->add(x == 2);
    ASSERT_TRUE(b->check_sat().is_sat());
    a.reset(); // a shelved solver goes first
    EXPECT_EQ(b->model().uint64_value(x), 2u);
    ASSERT_TRUE(b->check_sat().is_sat());
    b.reset();
  }
  // the manager is clean afterwards
  Solver c(tm);
  EXPECT_TRUE(c.assertions().empty());
  EXPECT_TRUE(c.check_sat().is_sat());
}

TEST_F(SolversTest, a_third_solver_after_checks)
{
  Solver a(tm), b(tm);
  a.add(x == 1);
  b.add(x == 2);
  ASSERT_TRUE(a.check_sat().is_sat());
  ASSERT_TRUE(b.check_sat().is_sat());
  Solver c(tm);
  EXPECT_TRUE(c.assertions().empty());
  EXPECT_EQ(c.level(), 0u);
  c.add(x == 3);
  ASSERT_TRUE(c.check_sat().is_sat());
  EXPECT_EQ(c.model().uint64_value(x), 3u);
  EXPECT_EQ(a.model().uint64_value(x), 1u);
  EXPECT_EQ(b.model().uint64_value(x), 2u);
  EXPECT_TRUE(a.check_sat().is_sat());
}

TEST_F(SolversTest, reset_of_one_solver_leaves_the_other)
{
  Options o;
  o.set_bool("produce-models", false);
  Solver a(tm, o), b(tm);
  a.add(x == 1);
  b.add(x == 2);
  a.reset(); // assertions gone, options back to defaults
  EXPECT_TRUE(a.assertions().empty());
  EXPECT_TRUE(a.options().get_bool("produce-models"));
  EXPECT_EQ(b.assertions().size(), 1u);
  ASSERT_TRUE(b.check_sat().is_sat());
  EXPECT_EQ(b.model().uint64_value(x), 2u);
  a.add(x == 5);
  ASSERT_TRUE(a.check_sat().is_sat());
  EXPECT_EQ(a.model().uint64_value(x), 5u);
  b.reset_assertions();
  EXPECT_TRUE(b.assertions().empty());
  EXPECT_EQ(a.assertions().size(), 1u);
}

TEST_F(SolversTest, every_theory_survives_the_shelf)
{
  // Reals register with the engine's arithmetic frontend as they are asserted
  // and pushed; arrays and functions engage their machinery: all of it must
  // come back when a shelved solver is installed again.
  Solver a(tm), b(tm);
  const Term r = tm.declare("r", tm.mk_real_sort());
  const Sort f32 = tm.mk_fp32_sort();
  const Term fx = tm.declare("fx", f32);
  const Term f = tm.declare("f", tm.mk_fun_sort({bv8}, bv8));
  const Term arr = tm.declare("arr", tm.mk_array_sort(bv8, bv8));
  const Term arr2 = tm.declare("arr2", tm.mk_array_sort(bv8, bv8));
  a.add(real_lt(r + 1, tm.mk_real("3/2")));
  a.push();
  a.add(fx == tm.mk_fp(f32, RoundingMode::RNE, 1.5));
  b.add(f(x) == 7);
  b.add(arr[x] == 9);
  b.add(arr == store(arr2, y, tm.mk_bv(8, 1)));
  ASSERT_TRUE(b.check_sat().is_sat());
  ASSERT_TRUE(a.check_sat().is_sat());
  EXPECT_TRUE(a.model().value(fx).same_as(tm.mk_fp(f32, RoundingMode::RNE, 1.5)));
  const RationalValue q = a.model().real_value(r);
  EXPECT_FALSE(q.numerator.empty());
  ASSERT_TRUE(b.check_sat().is_sat());
  EXPECT_EQ(b.model().uint64_value(f(x)), 7u);
  EXPECT_EQ(b.model().uint64_value(arr[x]), 9u);
  a.pop();
  EXPECT_EQ(a.assertions().size(), 1u);
  a.add(real_lt(tm.mk_real(2), r)); // contradicts r + 1 < 3/2
  EXPECT_TRUE(a.check_sat().is_unsat());
  EXPECT_TRUE(b.check_sat().is_sat());
}

// Statistics are each solver's own: the engine's counters follow the active
// solver, so a new solver has counted nothing and one solver's checks do not
// show in another's.
TEST_F(SolversTest, statistics_are_each_solvers_own)
{
  Solver a(tm);
  a.add(bvmul(x, y) == tm.mk_bv(8, 35));
  a.add(bvugt(x, 1));
  a.add(bvugt(y, 1));
  ASSERT_TRUE(a.check_sat().is_sat());
  const std::uint64_t bitblasted = a.statistics().uint64("checks.bitblasted");
  EXPECT_GE(bitblasted, 1u);
  Solver b(tm);
  EXPECT_EQ(b.statistics().uint64("checks.bitblasted"), 0u);
  EXPECT_EQ(b.statistics().uint64("checks.total"), 0u);
  b.add(bvmul(x, x) == tm.mk_bv(8, 49));
  ASSERT_TRUE(b.check_sat().is_sat());
  EXPECT_EQ(a.statistics().uint64("checks.bitblasted"), bitblasted);
  EXPECT_EQ(a.statistics().uint64("checks.total"), 1u);
  EXPECT_EQ(b.statistics().uint64("checks.total"), 1u);
}

} // namespace

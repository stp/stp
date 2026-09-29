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

// option-effects.cpp -- what a check runs with after an option is set and
// then taken back (set to its default, reset, or given its default through
// set_args): the engine fields the entry and everything it implied wrote go
// back with it, for this solver and for every other solver of the manager.
// The flags are read as the check left them, without applying the options
// again first.

#include "api_engine.hpp"

#include <string>

using namespace stp::api;

namespace
{

// The manager's flags as the last check (of whichever solver) left them.
stp::UserDefinedFlags& flags_after(TermManager& tm)
{
  return api_test::engine_manager(tm).UserFlags;
}

enum class TakeBack
{
  FALSE,
  RESET,
  ARGS
};

void take_back(Solver& s, const std::string& name, TakeBack how)
{
  switch (how)
  {
    case TakeBack::FALSE: s.options().set_bool(name, false); break;
    case TakeBack::RESET: s.options().reset(name); break;
    case TakeBack::ARGS: s.options().set_args({"--" + name + "=false"}); break;
  }
}

} // namespace

TEST(OptionEffects, disable_simplifications_goes_back_with_everything_it_implied)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  for (TakeBack how : {TakeBack::FALSE, TakeBack::RESET, TakeBack::ARGS})
  {
    Solver s(tm);
    s.options().set_bool("disable-simplifications", true);
    take_back(s, "disable-simplifications", how);
    s.add(x == 3);
    ASSERT_TRUE(s.check_sat().is_sat());
    const stp::UserDefinedFlags& f = flags_after(tm);
    EXPECT_TRUE(f.bitConstantProp_flag);
    EXPECT_TRUE(f.optimize_flag);
    EXPECT_TRUE(f.wordlevel_solve_flag);
    EXPECT_TRUE(f.propagate_equalities);
    EXPECT_TRUE(f.enable_unconstrained);
    EXPECT_TRUE(f.enable_flatten);
  }
  // and while it is on, the check runs without them
  Solver s(tm);
  s.options().set_bool("disable-simplifications", true);
  s.add(x == 3);
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_FALSE(flags_after(tm).bitConstantProp_flag);
  EXPECT_FALSE(flags_after(tm).wordlevel_solve_flag);
}

TEST(OptionEffects, size_reducing_only_goes_back_with_everything_it_wrote)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  for (TakeBack how : {TakeBack::FALSE, TakeBack::RESET, TakeBack::ARGS})
  {
    Solver s(tm);
    s.options().set_bool("size-reducing-only", true);
    take_back(s, "size-reducing-only", how);
    s.add(x == 3);
    ASSERT_TRUE(s.check_sat().is_sat());
    const stp::UserDefinedFlags& f = flags_after(tm);
    EXPECT_FALSE(f.simplify_to_constants_only);
    EXPECT_TRUE(f.difficulty_reversion);
    EXPECT_TRUE(f.array_difficulty_reversion); // written by the switch, no entry of its own
  }
}

// One manager's flags serve every solver: one solver's switch must not stay
// behind for the next solver to check with.
TEST(OptionEffects, another_solver_does_not_inherit_a_composite_switch)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  Options size_reducing;
  size_reducing.set_bool("size-reducing-only", true);
  Solver a(tm, size_reducing), b(tm);
  a.add(x == 3);
  ASSERT_TRUE(a.check_sat().is_sat());
  EXPECT_FALSE(flags_after(tm).array_difficulty_reversion);
  b.add(x == 4);
  ASSERT_TRUE(b.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).array_difficulty_reversion);
  EXPECT_FALSE(flags_after(tm).simplify_to_constants_only);

  Options no_simplifications;
  no_simplifications.set_bool("disable-simplifications", true);
  Solver c(tm, no_simplifications), d(tm);
  c.add(x == 5);
  ASSERT_TRUE(c.check_sat().is_sat());
  d.add(x == 6);
  ASSERT_TRUE(d.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).bitConstantProp_flag);
  EXPECT_TRUE(flags_after(tm).optimize_flag);
}

// A logic switches the UF machinery and the extensional arrays on as the
// content would under `auto`; another logic, or none, takes that back.
TEST(OptionEffects, a_logic_goes_back_with_what_it_switched_on)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  Solver s(tm);
  s.options().set_str("logic", "QF_AUFBV");
  s.add(x == 3);
  {
    Solver probe(tm); // the logic applies to its own solver alone
    probe.add(x == 3);
    ASSERT_TRUE(probe.check_sat().is_sat());
    EXPECT_FALSE(flags_after(tm).enable_uninterpreted_functions);
  }
  ASSERT_TRUE(s.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).enable_uninterpreted_functions);
  EXPECT_TRUE(flags_after(tm).enable_array_equality);

  Solver t(tm);
  t.options().set_str("logic", "QF_AUFBV");
  t.options().reset("logic");
  t.add(x == 3);
  ASSERT_TRUE(t.check_sat().is_sat());
  EXPECT_FALSE(flags_after(tm).enable_uninterpreted_functions);
  EXPECT_FALSE(flags_after(tm).enable_array_equality);

  Solver u(tm);
  u.options().set_str("logic", "QF_AUFBV");
  u.options().set_str("logic", "QF_BV");
  u.add(x == 3);
  ASSERT_TRUE(u.check_sat().is_sat());
  EXPECT_FALSE(flags_after(tm).enable_uninterpreted_functions);
  EXPECT_FALSE(flags_after(tm).enable_array_equality);

  // an explicit `off` still wins over the logic
  Solver v(tm);
  v.options().set_str("uninterpreted-functions", "off");
  v.options().set_str("logic", "QF_UFBV");
  v.add(x == 3);
  ASSERT_TRUE(v.check_sat().is_sat());
  EXPECT_FALSE(flags_after(tm).enable_uninterpreted_functions);
}

// `incremental` can change until the first check, pushes or not, and the
// session follows it both ways: `off` is never.
TEST(OptionEffects, incremental_follows_its_last_value)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  {
    Solver s(tm);
    s.options().set("incremental", "on");
    s.options().set("incremental", "off");
    s.add(x == 3);
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_EQ(s.statistics().uint64("incremental.engaged"), 0u);
  }
  for (const bool push_first : {false, true})
  {
    SCOPED_TRACE(push_first ? "push, then off" : "off, then push");
    Solver s(tm);
    if (!push_first)
      s.options().set("incremental", "off");
    s.push();
    if (push_first)
      s.options().set("incremental", "off");
    for (int i = 0; i < 5; ++i)
    {
      s.push();
      s.add(x == i);
      ASSERT_TRUE(s.check_sat().is_sat());
      s.pop();
    }
    EXPECT_EQ(s.statistics().uint64("incremental.engaged"), 0u);
  }
  // and auto still engages on a push
  Solver s(tm);
  s.push();
  for (int i = 0; i < 5; ++i)
  {
    s.push();
    s.add(x == i);
    ASSERT_TRUE(s.check_sat().is_sat());
    s.pop();
  }
  EXPECT_EQ(s.statistics().uint64("incremental.engaged"), 1u);
}

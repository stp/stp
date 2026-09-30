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

#include <limits>
#include <string>
#include <vector>

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

TEST(OptionEffects, smtlib_random_seed_reaches_each_backend_and_retires_old_solvers)
{
  for (const char* backend : {"cadical", "cryptominisat", "minisat", "simplifying-minisat"})
  {
    if (!has_sat_backend(backend))
      continue;
    SCOPED_TRACE(backend);
    for (const char* incremental : {"on", "off"})
    {
      SCOPED_TRACE(incremental);
      TermManager tm;
      Options options;
      options.set_str("sat-backend", backend);
      options.set("incremental", incremental);
      options.set_uint("random-seed", 17);
      Solver s(tm, options);
      std::string output;
      // Observe the engine setting at solved responses, rather than just
      // checking get-option's echo of the requested value. In batch mode
      // also observe it at CNF emission, where the backend is configured.
      std::vector<uint64_t> seeds;
      s.set_output_sink([&](std::string_view text) {
        output += text;
        if (text.find("sat") != std::string_view::npos)
          seeds.push_back(flags_after(tm).random_seed);
      });
      std::vector<uint64_t> cnf_seeds;
      s.set_cnf_sink([&](std::string_view, CnfScope) {
        const uint64_t seed = flags_after(tm).random_seed;
        if (cnf_seeds.empty() || cnf_seeds.back() != seed)
          cnf_seeds.push_back(seed);
      });
      s.parse_smt2("(declare-const x (_ BitVec 8))(declare-const y (_ BitVec 8))"
                   "(assert (= (bvmul x y) #x8f))(assert (bvugt x #x01))"
                   "(assert (bvugt y #x01))");
      ASSERT_TRUE(s.check_sat().is_sat());
      // A persistent solver from the API must also be reseeded when the
      // script changes the option before its own first check.
      s.parse_smt2("(set-option :produce-models true)"
                   "(set-option :random-seed 42)(check-sat)"
                   "(set-option :random-seed 18446744073709551615)(check-sat)"
                   "(set-option :random-seed 0)(check-sat)"
                   "(set-option :random-seed 17)", ParseMode::EXECUTE);
      EXPECT_EQ(output, "sat\nsat\nsat\n");
      EXPECT_EQ(flags_after(tm).random_seed, 17u);
      // Restoring the option without another check must still retire the
      // backend constructed under 0 before native API solving resumes.
      EXPECT_FALSE(api_test::engine_solver(s).hasIncrementalSolver());
      EXPECT_EQ(s.options().get_uint("random-seed"), 17u);
      ASSERT_TRUE(s.check_sat().is_sat());
      const std::vector<uint64_t> expected{42, std::numeric_limits<uint64_t>::max(), 0};
      EXPECT_EQ(seeds, expected);
      if (std::string(incremental) == "off")
      {
        const std::vector<uint64_t> expected_cnf{
            17, 42, std::numeric_limits<uint64_t>::max(), 0, 17};
        EXPECT_EQ(cnf_seeds, expected_cnf);
      }
    }
  }
}

TEST(OptionEffects, smtlib_random_seed_is_local_even_when_parsing_fails)
{
  for (const char* script : {
       "(set-option :random-seed 42)",
       "(set-option :random-seed 42)(reset)",
       "(set-option :random-seed 42)(exit)",
       "(set-option :random-seed 42)(check-sat)",
       "(set-option :random-seed 42)(assert missing)",
       "(set-option :random-seed 42)(check-sat)(assert missing)",
       "(set-option :random-seed 18446744073709551616)"})
  {
    SCOPED_TRACE(script);
    for (ParseMode mode : {ParseMode::DECLARE_AND_ASSERT, ParseMode::EXECUTE,
                           ParseMode::PARSE_ONLY})
    {
      TermManager tm;
      Options options;
      options.set_uint("random-seed", 17);
      Solver s(tm, options);
      s.set_output_sink([](std::string_view) {});
      const auto error = API_ERROR_OF(s.parse_smt2(script, mode));
      const bool invalid = std::string(script).find("missing") != std::string::npos ||
                           std::string(script).find("51616") != std::string::npos;
      ASSERT_EQ(error.has_value(), invalid);
      if (error)
      {
        EXPECT_EQ(error->code(), ErrorCode::PARSE);
      }
      EXPECT_EQ(flags_after(tm).random_seed, 17u);
      EXPECT_EQ(s.options().get_uint("random-seed"), 17u);
      ASSERT_TRUE(s.check_sat().is_sat());
    }
  }
}

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

// The incremental driver under the floating-point abstraction expands arrays
// eagerly for its whole session; switching to another solver of the manager
// and back must not hand it the lazy strategy half way.
TEST(OptionEffects, the_fp_abstraction_driver_keeps_its_array_strategy)
{
  TermManager tm;
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  Options o;
  o.set_bool("fp-abstraction", true);
  o.set_bool("fp-abstraction-incremental", true);
  o.set("incremental", "on");
  Solver a(tm, o), b(tm);
  a.add(x == 1);
  ASSERT_TRUE(a.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).ackermannisation);
  b.add(x == 2);
  ASSERT_TRUE(b.check_sat().is_sat());
  EXPECT_FALSE(flags_after(tm).ackermannisation);
  ASSERT_TRUE(a.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).ackermannisation);
}

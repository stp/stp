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
#include "stp/Sat/SearchBias.h"

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

void add_tuning_array_problem(TermManager& tm, Solver& s)
{
  const Sort byte = tm.mk_bv_sort(8);
  const Term a = tm.declare("tuning_array", tm.mk_array_sort(byte, byte));
  const Term x = a[tm.mk_bv(8, 0)];
  const Term y = tm.declare("tuning_factor", byte);
  s.add(bvmul(x, y) == 143);
  s.add(bvugt(x, 1));
  s.add(bvugt(y, 1));
}

struct TuningSetting
{
  const char* name;
  const char* value;
};

std::vector<TuningSetting> bv_batch_settings(bool kissat)
{
  std::vector<TuningSetting> settings{{"sat-phase", "0"}};
  const TuningSetting extras[] = {
      {"cnf-generation-effort", "auto"}, {"kissat-adaptive-cnf", "true"},
      {"kissat-import-order", "2"},      {"kissat-incremental-greedy", "4"},
      {"kissat-batch-only", "true"},     {"bv-conditional-equality", "true"}};
  if (kissat)
    for (const auto& setting : extras)
      settings.push_back(setting);
  return settings;
}

void add_tuning_bv_problem(TermManager& tm, Solver& solver)
{
  const Sort word = tm.mk_bv_sort(8);
  const Term x = tm.declare("tuning_bv_x", word);
  const Term y = tm.declare("tuning_bv_y", word);
  solver.add(bvmul(x, y) == 143);
  solver.add(bvugt(x, 1));
  solver.add(bvugt(y, 1));
}

const TuningSetting kissat_abv_batch_settings[] = {
    {"cadical-factor", "off"},
    {"kissat-batch-only", "true"},
    {"kissat-one-shot-stable", "0"},
    {"cnf-auto-threshold", "0"},
    {"array-late-read-limit", "1024"},
    {"array-late-expansion-limit", "100000"},
    {"array-late-congruence-limit", "16000"},
    {"array-equality-gia-cnf", "true"},
    {"array-equality-gia-min-reads", "16"}};

const TuningSetting cadical_abv_batch_settings[] = {
    {"search-bias", "unsat"},
    {"cnf-generation-effort", "auto"},
    {"cadical-factor", "off"},
    {"array-late-read-limit", "1024"},
    {"array-late-expansion-limit", "100000"},
    {"array-late-congruence-limit", "16000"},
    {"array-equality-gia-cnf", "true"},
    {"array-equality-gia-min-reads", "16"}};

std::vector<TuningSetting> fp_batch_settings(bool kissat)
{
  if (!kissat)
    return {{"cadical-factor", "off"}};
  return {{"search-bias", "sat"},
          {"kissat-stable", "2"},
          {"sat-target", "0"},
          {"sat-rephase", "0"},
          {"cnf-generation-effort", "new-medium"},
          {"kissat-probe", "false"},
          {"cadical-factor", "off"},
          {"kissat-trail-reuse-mode", "2"},
          {"kissat-incremental-greedy", "2"},
          {"kissat-greedy-growth", "1"}};
}

void add_tuning_fp_problem(TermManager& tm, Solver& solver, bool arrays)
{
  const Sort half = tm.mk_fp_sort(5, 11);
  const Term x =
      arrays
          ? tm.declare("fp_tuning_array",
                       tm.mk_array_sort(tm.mk_bv_sort(8), half))[tm.mk_bv(8, 0)]
          : tm.declare("fp_tuning_x", half);
  const Term y = tm.declare("fp_tuning_y", half);
  const Term one = tm.mk_fp_from_bits(half, tm.mk_bv(16, 0x3c00));
  const Term three = tm.mk_fp_from_bits(half, tm.mk_bv(16, 0x4200));
  const Term four = tm.mk_fp_from_bits(half, tm.mk_bv(16, 0x4400));
  solver.add(fp_gt(x, one) && fp_lt(x, three));
  solver.add(fp_gt(y, one) && fp_lt(y, three));
  solver.add(fp_eq(fp_add(tm.mk_rm(RoundingMode::RNE), x, y), four));
}

std::string scalar_option_text(const OptionValue& value)
{
  if (const auto* v = std::get_if<bool>(&value))
    return *v ? "true" : "false";
  if (const auto* v = std::get_if<std::int64_t>(&value))
    return std::to_string(*v);
  if (const auto* v = std::get_if<std::uint64_t>(&value))
    return std::to_string(*v);
  return std::get<std::string>(value);
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

TEST(OptionEffects, cadical_abv_batch_tuning_reaches_the_first_encoding)
{
  if (!has_sat_backend("cadical"))
    GTEST_SKIP() << "CaDiCaL is not part of this build";
  using Flags = stp::UserDefinedFlags;
  const Options baseline;
  Options expected;
  for (const auto& setting : cadical_abv_batch_settings)
    expected.set(setting.name, setting.value);
  for (const bool parsed : {false, true})
  {
    SCOPED_TRACE(parsed);
    TermManager tm;
    Options options;
    options.set_str("sat-backend", "cadical");
    options.set_bool("check-sanity", true);
    if (!parsed)
      options.set_str("logic", "QF_ABV");
    Solver s(tm, options);
    if (parsed)
      s.parse_smt2("(set-logic QF_ABV)");
    add_tuning_array_problem(tm, s);
    bool emitted = false;
    s.set_cnf_sink(
        [&](std::string_view, CnfScope)
        {
          emitted = true;
          const auto& flags = flags_after(tm);
          EXPECT_EQ(flags.search_bias, stp::SearchBias::UNSAT);
          EXPECT_EQ(flags.cnf_effort, Flags::CNF_EFFORT_AUTO);
          EXPECT_EQ(flags.cadical_factor, Flags::BVAMode::OFF);
          EXPECT_EQ(flags.array_late_read_limit, 1024);
          EXPECT_EQ(flags.array_late_expansion_limit, 100000u);
          EXPECT_EQ(flags.array_late_congruence_limit, 16000u);
          EXPECT_TRUE(flags.array_equality_gia_cnf);
          EXPECT_EQ(flags.array_equality_gia_min_reads, 16);
        });
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_TRUE(emitted);
    for (const auto& setting : cadical_abv_batch_settings)
    {
      SCOPED_TRACE(setting.name);
      EXPECT_EQ(s.options().resolved(setting.name),
                expected.resolved(setting.name));
      EXPECT_EQ(s.options().get(setting.name), baseline.get(setting.name));
      EXPECT_FALSE(s.options().is_set(setting.name));
    }
  }
}

TEST(OptionEffects, cadical_abv_tuning_preserves_explicit_baseline_choices)
{
  if (!has_sat_backend("cadical"))
    GTEST_SKIP() << "CaDiCaL is not part of this build";
  using Flags = stp::UserDefinedFlags;
  struct Choice
  {
    const char* name;
    const char* value;
    stp::SearchBias bias;
    Flags::CNFEffort effort;
    Flags::BVAMode factor;
  };
  const Choice choices[] = {
      {"sat-tuning", "off", stp::SearchBias::NONE, Flags::CNF_EFFORT_AUTO,
       Flags::BVAMode::ON},
      {"search-bias", "none", stp::SearchBias::NONE, Flags::CNF_EFFORT_AUTO,
       Flags::BVAMode::OFF},
      {"cnf-generation-effort", "auto", stp::SearchBias::UNSAT,
       Flags::CNF_EFFORT_AUTO, Flags::BVAMode::OFF},
      {"cnf-generation-effort", "gia-low", stp::SearchBias::UNSAT,
       Flags::CNF_EFFORT_GIA_LOW, Flags::BVAMode::OFF},
      {"kissat-factor", "on", stp::SearchBias::UNSAT, Flags::CNF_EFFORT_AUTO,
       Flags::BVAMode::ON},
      {"incremental", "on", stp::SearchBias::SAT, Flags::CNF_EFFORT_NEW_MEDIUM,
       Flags::BVAMode::OFF},
  };
  for (const Choice& choice : choices)
  {
    SCOPED_TRACE(choice.name);
    TermManager tm;
    Options o;
    o.set_str("sat-backend", "cadical");
    o.set_str("logic", "QF_ABV");
    o.set(choice.name, choice.value);
    Solver s(tm, o);
    add_tuning_array_problem(tm, s);
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_TRUE(s.options().is_set(choice.name));
    EXPECT_EQ(flags_after(tm).search_bias, choice.bias);
    EXPECT_EQ(flags_after(tm).cnf_effort, choice.effort);
    EXPECT_EQ(flags_after(tm).cadical_factor, choice.factor);
  }
}

TEST(OptionEffects, cadical_abv_late_push_replaces_batch_tuning_before_engagement)
{
  if (!has_sat_backend("cadical"))
    GTEST_SKIP() << "CaDiCaL is not part of this build";
  using Flags = stp::UserDefinedFlags;
  const Options baseline;
  for (const bool parsed : {false, true})
  {
    SCOPED_TRACE(parsed);
    TermManager tm;
    Options options;
    options.set_str("sat-backend", "cadical");
    options.set("incremental-auto-engage-at", "1");
    if (!parsed)
      options.set_str("logic", "QF_ABV");
    Solver s(tm, options);
    if (parsed)
      s.parse_smt2("(set-logic QF_ABV)");
    add_tuning_array_problem(tm, s);
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_FALSE(api_test::engine_solver(s).hasIncrementalSolver());
    EXPECT_EQ(flags_after(tm).cnf_effort, Flags::CNF_EFFORT_AUTO);
    EXPECT_EQ(flags_after(tm).array_late_read_limit, 1024);
    if (parsed)
      s.parse_smt2("(push 1)");
    else
      s.push();
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_TRUE(api_test::engine_solver(s).hasIncrementalSolver());
    EXPECT_EQ(flags_after(tm).search_bias, stp::SearchBias::SAT);
    EXPECT_EQ(flags_after(tm).cnf_effort, Flags::CNF_EFFORT_NEW_MEDIUM);
    for (const char* name :
         {"array-late-read-limit", "array-late-expansion-limit",
          "array-late-congruence-limit", "array-equality-gia-cnf",
          "array-equality-gia-min-reads"})
      EXPECT_EQ(s.options().resolved(name), baseline.get(name)) << name;
    EXPECT_EQ(flags_after(tm).array_late_read_limit, 0);
    EXPECT_EQ(flags_after(tm).array_late_expansion_limit, 200u);
    EXPECT_EQ(flags_after(tm).array_late_congruence_limit, 4000u);
    EXPECT_FALSE(flags_after(tm).array_equality_gia_cnf);
    if (parsed)
      s.parse_smt2("(pop 1)");
    else
      s.pop();
    ASSERT_TRUE(s.check_sat().is_sat());
    EXPECT_EQ(flags_after(tm).cnf_effort, Flags::CNF_EFFORT_NEW_MEDIUM);
    EXPECT_EQ(flags_after(tm).array_late_read_limit, 0);
  }
}

TEST(OptionEffects,
     cadical_abv_batch_defaults_preserve_explicit_baseline_values)
{
  if (!has_sat_backend("cadical"))
    GTEST_SKIP() << "CaDiCaL is not part of this build";
  const Options baseline;
  for (const bool parsed : {false, true})
    for (const auto& setting : cadical_abv_batch_settings)
    {
      SCOPED_TRACE(parsed);
      SCOPED_TRACE(setting.name);
      TermManager tm;
      Options options;
      options.set_str("sat-backend", "cadical");
      if (!parsed)
      {
        options.set_str("logic", "QF_ABV");
        options.set(setting.name,
                    scalar_option_text(baseline.get(setting.name)));
      }
      Solver s(tm, options);
      if (parsed)
        s.parse_smt2(
            "(set-logic QF_ABV)(set-option :" + std::string(setting.name) +
            " " + scalar_option_text(baseline.get(setting.name)) + ")");
      const Term x = tm.declare("cadical_batch_explicit_x", tm.mk_bv_sort(8));
      s.add(x == 1);
      ASSERT_TRUE(s.check_sat().is_sat());
      EXPECT_TRUE(s.options().is_set(setting.name));
      EXPECT_EQ(s.options().resolved(setting.name), baseline.get(setting.name));
    }
}

TEST(OptionEffects,
     copying_cadical_batch_options_does_not_copy_automatic_values)
{
  if (!has_sat_backend("cadical"))
    GTEST_SKIP() << "CaDiCaL is not part of this build";
  const Options baseline;
  TermManager tm;
  Options options;
  options.set_str("sat-backend", "cadical");
  options.set_str("logic", "QF_ABV");
  Solver original(tm, options);
  const Term x = tm.declare("cadical_batch_copy_x", tm.mk_bv_sort(8));
  original.add(x == 1);
  ASSERT_TRUE(original.check_sat().is_sat());
  Options copied(original.options());
  for (const auto& setting : cadical_abv_batch_settings)
  {
    EXPECT_FALSE(copied.is_set(setting.name));
    EXPECT_EQ(copied.get(setting.name), baseline.get(setting.name));
  }
  copied.set_str("logic", "QF_BV");
  Solver other(tm, copied);
  other.add(x == 1);
  ASSERT_TRUE(other.check_sat().is_sat());
  EXPECT_EQ(flags_after(tm).array_late_read_limit, 0);
  EXPECT_FALSE(flags_after(tm).array_equality_gia_cnf);
  ASSERT_TRUE(original.check_sat().is_sat());
  EXPECT_EQ(flags_after(tm).array_late_read_limit, 1024);
  EXPECT_TRUE(flags_after(tm).array_equality_gia_cnf);
}

TEST(OptionEffects, forced_abvfp_tuning_reaches_the_incremental_solver)
{
  using Flags = stp::UserDefinedFlags;
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    const bool kissat = std::string(backend) == "kissat";
    for (const bool parsed : {false, true})
    {
      SCOPED_TRACE(std::string(backend) + (parsed ? "/SMT-LIB" : "/native"));
      TermManager tm;
      Options options;
      options.set_str("sat-backend", backend);
      options.set_bool("check-sanity", true);
      if (!parsed)
      {
        options.set_str("logic", "QF_ABVFP");
        options.set_str("incremental", "on");
      }
      Solver solver(tm, options);
      if (parsed)
        solver.parse_smt2("(set-logic QF_ABVFP)(set-option :incremental true)");
      add_tuning_array_problem(tm, solver);
      ASSERT_TRUE(solver.check_sat().is_sat());
      EXPECT_TRUE(api_test::engine_solver(solver).hasIncrementalSolver());
      const auto& flags = flags_after(tm);
      EXPECT_EQ(flags.search_bias, stp::SearchBias::SAT);
      EXPECT_EQ(flags.sat_search_options.phase, kissat ? -1 : 0);
      EXPECT_EQ(flags.sat_search_options.target, 0);
      EXPECT_EQ(flags.sat_search_options.rephase, kissat ? 0 : -1);
      EXPECT_EQ(flags.cnf_effort,
                kissat ? Flags::CNF_EFFORT_NEW_MEDIUM : Flags::CNF_EFFORT_AUTO);
      EXPECT_EQ(flags.cadical_factor, Flags::BVAMode::OFF);
      if (kissat)
      {
        EXPECT_FALSE(flags.kissat_probe);
        EXPECT_EQ(flags.kissat_stable, 2);
        EXPECT_EQ(flags.kissat_trail_reuse_mode, 2);
      }
      solver.push();
      solver.add(tm.mk_bool(false));
      ASSERT_TRUE(solver.check_sat().is_unsat());
      solver.pop();
      ASSERT_TRUE(solver.check_sat().is_sat());
    }
  }
}

TEST(OptionEffects, kissat_elimination_control_reaches_native_and_parsed_checks)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  for (const bool parsed : {false, true})
    for (const char* incremental : {"on", "off"})
      for (int elimination : {-1, 0, 1})
      {
        SCOPED_TRACE(std::string(parsed ? "SMT-LIB/" : "native/") +
                     incremental + "/" + std::to_string(elimination));
        TermManager tm;
        Options options;
        options.set_str("sat-backend", "kissat");
        options.set_str("incremental", incremental);
        options.set_bool("check-sanity", true);
        if (!parsed)
          options.set_int("kissat-eliminate", elimination);
        Solver solver(tm, options);
        if (parsed)
          solver.parse_smt2("(set-option :kissat-eliminate " +
                            std::to_string(elimination) + ")");
        add_tuning_array_problem(tm, solver);
        bool emitted = false;
        solver.set_cnf_sink(
            [&](std::string_view, CnfScope)
            {
              emitted = true;
              EXPECT_EQ(flags_after(tm).kissat_eliminate, elimination);
            });
        ASSERT_TRUE(solver.check_sat().is_sat());
        EXPECT_EQ(flags_after(tm).kissat_eliminate, elimination);
        if (std::string(incremental) == "off")
        {
          EXPECT_TRUE(emitted);
        }
        else
        {
          EXPECT_TRUE(api_test::engine_solver(solver).hasIncrementalSolver());
        }
        EXPECT_EQ(solver.options().resolved("kissat-eliminate"),
                  OptionValue(std::int64_t(elimination)));
        EXPECT_TRUE(solver.options().is_set("kissat-eliminate"));
        API_EXPECT_ERROR(ErrorCode::OPTION_TIMING,
                         solver.options().set_int("kissat-eliminate",
                                                  elimination == 0 ? 1 : 0));
      }
}

TEST(OptionEffects,
     kissat_import_and_cnf_controls_reach_native_and_parsed_checks)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  for (const bool parsed : {false, true})
    for (const char* incremental : {"on", "off"})
      for (int order : {0, 1, 2})
        for (const bool adaptive : {false, true})
        {
          SCOPED_TRACE(parsed);
          SCOPED_TRACE(incremental);
          SCOPED_TRACE(order);
          SCOPED_TRACE(adaptive);
          TermManager tm;
          Options options;
          options.set_str("sat-backend", "kissat");
          options.set_str("incremental", incremental);
          options.set_str("cnf-generation-effort", "auto");
          options.set_bool("check-sanity", true);
          if (!parsed)
          {
            options.set_int("kissat-import-order", order);
            options.set_bool("kissat-adaptive-cnf", adaptive);
          }
          Solver solver(tm, options);
          if (parsed)
            solver.parse_smt2("(set-option :kissat-import-order " +
                              std::to_string(order) +
                              ")(set-option :kissat-adaptive-cnf " +
                              (adaptive ? "true" : "false") + ")");
          add_tuning_array_problem(tm, solver);
          ASSERT_TRUE(solver.check_sat().is_sat());
          EXPECT_EQ(flags_after(tm).kissat_import_order, order);
          EXPECT_EQ(flags_after(tm).kissat_adaptive_cnf, adaptive);
          EXPECT_EQ(solver.options().resolved("kissat-import-order"),
                    OptionValue(std::int64_t(order)));
          EXPECT_EQ(solver.options().resolved("kissat-adaptive-cnf"),
                    OptionValue(adaptive));
          EXPECT_TRUE(solver.options().is_set("kissat-import-order"));
          EXPECT_TRUE(solver.options().is_set("kissat-adaptive-cnf"));
          API_EXPECT_ERROR(ErrorCode::OPTION_TIMING,
                           solver.options().set_int("kissat-import-order",
                                                    order == 0 ? 1 : 0));
          API_EXPECT_ERROR(
              ErrorCode::OPTION_TIMING,
              solver.options().set_bool("kissat-adaptive-cnf", !adaptive));
        }
}

TEST(OptionEffects, kissat_one_shot_mode_reaches_native_and_parsed_checks)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  for (const bool parsed : {false, true})
    for (const char* incremental : {"on", "off"})
      for (const bool batch : {false, true})
        for (int mode : {-1, 0, 1, 2})
        {
          SCOPED_TRACE(parsed);
          SCOPED_TRACE(incremental);
          SCOPED_TRACE(batch);
          SCOPED_TRACE(mode);
          TermManager tm;
          Options options;
          options.set_str("sat-backend", "kissat");
          options.set_str("incremental", incremental);
          options.set_bool("kissat-batch-only", batch);
          options.set_bool("check-sanity", true);
          if (!parsed)
            options.set_int("kissat-one-shot-stable", mode);
          Solver solver(tm, options);
          if (parsed)
            solver.parse_smt2("(set-option :kissat-one-shot-stable " +
                              std::to_string(mode) + ")");
          add_tuning_array_problem(tm, solver);
          ASSERT_TRUE(solver.check_sat().is_sat());
          EXPECT_EQ(flags_after(tm).kissat_one_shot_stable, mode);
          EXPECT_EQ(solver.options().resolved("kissat-one-shot-stable"),
                    OptionValue(std::int64_t(mode)));
          EXPECT_TRUE(solver.options().is_set("kissat-one-shot-stable"));
          API_EXPECT_ERROR(ErrorCode::OPTION_TIMING,
                           solver.options().set_int("kissat-one-shot-stable",
                                                    mode == 0 ? 1 : 0));
        }
}

TEST(OptionEffects, adjacent_bounds_option_reaches_native_and_parsed_checks)
{
  EXPECT_FALSE(Options().get_bool("bv-adjacent-bounds"));
  for (const bool parsed : {false, true})
  {
    SCOPED_TRACE(parsed);
    TermManager tm;
    Options options;
    if (!parsed)
      options.set_bool("bv-adjacent-bounds", true);
    Solver solver(tm, options);
    if (parsed)
      solver.parse_smt2("(set-option :bv-adjacent-bounds true)");
    const Term x = tm.declare("adjacent_option_x", tm.mk_bv_sort(8));
    solver.add(x == 1);
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_TRUE(flags_after(tm).enable_adjacent_bounds);
    EXPECT_TRUE(solver.options().is_set("bv-adjacent-bounds"));
    EXPECT_EQ(solver.options().resolved("bv-adjacent-bounds"),
              OptionValue(true));
    API_EXPECT_ERROR(ErrorCode::OPTION_TIMING,
                     solver.options().set_bool("bv-adjacent-bounds", false));
  }
}

TEST(OptionEffects, adjacent_bounds_option_is_restored_on_solver_activation)
{
  TermManager tm;
  Options enabled;
  enabled.set_bool("bv-adjacent-bounds", true);
  Solver on(tm, enabled), off(tm);
  const Term x = tm.declare("adjacent_switch_x", tm.mk_bv_sort(8));
  on.add(x == 1);
  off.add(x == 2);
  ASSERT_TRUE(on.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).enable_adjacent_bounds);
  ASSERT_TRUE(off.check_sat().is_sat());
  EXPECT_FALSE(flags_after(tm).enable_adjacent_bounds);
  ASSERT_TRUE(on.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).enable_adjacent_bounds);
}

TEST(OptionEffects, adjacent_bounds_option_handles_prebuilt_raw_terms)
{
  TermManager::Config config;
  config.simplify = false;
  TermManager tm(config);
  const Sort word = tm.mk_bv_sort(32);
  const Term x = tm.declare("adjacent_raw_x", word);
  const Term y = tm.declare("adjacent_raw_y", word);
  const Term lower = bvult(x, y);
  const Term upper = bvugt(bvadd(x, tm.mk_bv(32, 1)), y);
  Options options;
  options.set_bool("bv-adjacent-bounds", true);
  Solver solver(tm, options);
  solver.add(lower);
  solver.add(upper);
  bool emitted = false;
  solver.set_cnf_sink([&](std::string_view, CnfScope) { emitted = true; });
  ASSERT_TRUE(solver.check_sat().is_unsat());
  EXPECT_FALSE(emitted);
}

TEST(OptionEffects,
     conditional_equality_option_reaches_native_and_parsed_checks)
{
  EXPECT_FALSE(Options().get_bool("bv-conditional-equality"));
  for (const bool parsed : {false, true})
  {
    SCOPED_TRACE(parsed);
    TermManager tm;
    Options options;
    options.set_bool("check-sanity", true);
    if (!parsed)
      options.set_bool("bv-conditional-equality", true);
    Solver solver(tm, options);
    if (parsed)
      solver.parse_smt2("(set-option :bv-conditional-equality true)");
    solver.parse_smt2(
        "(set-logic QF_BV)(declare-const c Bool)"
        "(declare-const x (_ BitVec 8))(declare-const a (_ BitVec 8))"
        "(declare-const b (_ BitVec 8))"
        "(assert (ite c (= x a) (= x b)))"
        "(assert (= a #x09))(assert (= b #x0b))"
        "(assert (distinct x a))");
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_TRUE(flags_after(tm).enable_conditional_equality);
    EXPECT_TRUE(solver.options().is_set("bv-conditional-equality"));
    EXPECT_EQ(solver.options().resolved("bv-conditional-equality"),
              OptionValue(true));
    API_EXPECT_ERROR(
        ErrorCode::OPTION_TIMING,
        solver.options().set_bool("bv-conditional-equality", false));
    solver.push();
    solver.parse_smt2("(assert c)");
    ASSERT_TRUE(solver.check_sat().is_unsat());
    solver.pop();
    ASSERT_TRUE(solver.check_sat().is_sat());
  }
}

TEST(OptionEffects, conditional_equality_option_retires_on_solver_activation)
{
  TermManager tm;
  Options options;
  options.set_bool("bv-conditional-equality", true);
  Solver on(tm, options), off(tm);
  const Term x = tm.declare("conditional_switch_x", tm.mk_bv_sort(8));
  on.add(x == 1);
  off.add(x == 2);
  ASSERT_TRUE(on.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).enable_conditional_equality);
  ASSERT_TRUE(off.check_sat().is_sat());
  EXPECT_FALSE(flags_after(tm).enable_conditional_equality);
  ASSERT_TRUE(on.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).enable_conditional_equality);
}

TEST(OptionEffects, conditional_equality_option_handles_prebuilt_raw_terms)
{
  TermManager::Config config;
  config.simplify = false;
  TermManager tm(config);
  const Term condition = tm.declare("conditional_raw_c", tm.mk_bool_sort());
  const Sort word = tm.mk_bv_sort(8);
  const Term x = tm.declare("conditional_raw_x", word);
  const Term a = tm.declare("conditional_raw_a", word);
  const Term b = tm.declare("conditional_raw_b", word);
  const Term definition = ite(condition, x == a, x == b);
  const Term opposite = x != ite(condition, a, b);
  Options options;
  options.set_bool("bv-conditional-equality", true);
  Solver solver(tm, options);
  solver.add(definition && opposite);
  bool emitted = false;
  solver.set_cnf_sink([&](std::string_view, CnfScope) { emitted = true; });
  ASSERT_TRUE(solver.check_sat().is_unsat());
  EXPECT_TRUE(flags_after(tm).enable_conditional_equality);
  EXPECT_FALSE(emitted);
}

TEST(OptionEffects, double_equality_option_reaches_native_and_parsed_checks)
{
  EXPECT_FALSE(Options().get_bool("bv-double-equality"));
  for (const bool parsed : {false, true})
  {
    SCOPED_TRACE(parsed);
    TermManager tm;
    Options options;
    options.set_bool("check-sanity", true);
    if (!parsed)
      options.set_bool("bv-double-equality", true);
    Solver solver(tm, options);
    if (parsed)
      solver.parse_smt2("(set-option :bv-double-equality true)");
    solver.parse_smt2("(set-logic QF_BV)(declare-const x (_ BitVec 8))"
                      "(declare-const y (_ BitVec 8))"
                      "(assert (= (bvadd x y) (bvshl x #x01)))");
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_TRUE(flags_after(tm).enable_double_equality);
    EXPECT_TRUE(solver.options().is_set("bv-double-equality"));
    EXPECT_EQ(solver.options().resolved("bv-double-equality"),
              OptionValue(true));
    API_EXPECT_ERROR(ErrorCode::OPTION_TIMING,
                     solver.options().set_bool("bv-double-equality", false));
    solver.push();
    solver.parse_smt2("(assert (distinct x y))");
    ASSERT_TRUE(solver.check_sat().is_unsat());
    solver.pop();
    ASSERT_TRUE(solver.check_sat().is_sat());
  }
}

TEST(OptionEffects, double_equality_option_retires_on_solver_activation)
{
  TermManager tm;
  Options options;
  options.set_bool("bv-double-equality", true);
  Solver on(tm, options), off(tm);
  const Term x = tm.declare("double_switch_x", tm.mk_bv_sort(8));
  on.add(x == 1);
  off.add(x == 2);
  ASSERT_TRUE(on.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).enable_double_equality);
  ASSERT_TRUE(off.check_sat().is_sat());
  EXPECT_FALSE(flags_after(tm).enable_double_equality);
  ASSERT_TRUE(on.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).enable_double_equality);
}

TEST(OptionEffects, double_equality_option_handles_prebuilt_raw_terms)
{
  TermManager::Config config;
  config.simplify = false;
  TermManager tm(config);
  const Sort word = tm.mk_bv_sort(8);
  const Term x = tm.declare("double_raw_x", word);
  const Term y = tm.declare("double_raw_y", word);
  const Term identity = bvadd(x, y) == bvshl(x, tm.mk_bv(8, 1));
  Options options;
  options.set_bool("bv-double-equality", true);
  Solver solver(tm, options);
  solver.add(identity && x != y);
  bool emitted = false;
  solver.set_cnf_sink([&](std::string_view, CnfScope) { emitted = true; });
  ASSERT_TRUE(solver.check_sat().is_unsat());
  EXPECT_TRUE(flags_after(tm).enable_double_equality);
  EXPECT_FALSE(emitted);
}

TEST(OptionEffects, kissat_abv_batch_defaults_reach_native_and_parsed_encodings)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  const Options baseline;
  Options expected;
  for (const auto& setting : kissat_abv_batch_settings)
    expected.set(setting.name, setting.value);
  for (const bool parsed : {false, true})
  {
    SCOPED_TRACE(parsed);
    TermManager tm;
    Options options;
    options.set_str("sat-backend", "kissat");
    options.set_bool("check-sanity", true);
    if (!parsed)
      options.set_str("logic", "QF_ABV");
    Solver solver(tm, options);
    if (parsed)
      solver.parse_smt2("(set-logic QF_ABV)");
    add_tuning_array_problem(tm, solver);
    bool emitted = false;
    solver.set_cnf_sink(
        [&](std::string_view, CnfScope)
        {
          emitted = true;
          const auto& flags = flags_after(tm);
          EXPECT_TRUE(flags.kissat_batch_only);
          EXPECT_EQ(flags.kissat_one_shot_stable, 0);
          EXPECT_EQ(flags.cnf_auto_threshold, 0u);
          EXPECT_EQ(flags.array_late_read_limit, 1024);
          EXPECT_EQ(flags.array_late_expansion_limit, 100000u);
          EXPECT_EQ(flags.array_late_congruence_limit, 16000u);
          EXPECT_TRUE(flags.array_equality_gia_cnf);
          EXPECT_EQ(flags.array_equality_gia_min_reads, 16);
          EXPECT_EQ(flags.cadical_factor, stp::UserDefinedFlags::BVAMode::OFF);
        });
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_TRUE(emitted);
    for (const auto& setting : kissat_abv_batch_settings)
    {
      SCOPED_TRACE(setting.name);
      EXPECT_EQ(solver.options().resolved(setting.name),
                expected.resolved(setting.name));
      EXPECT_EQ(solver.options().get(setting.name), baseline.get(setting.name));
      EXPECT_FALSE(solver.options().is_set(setting.name));
    }
  }
}

TEST(OptionEffects, kissat_abv_batch_defaults_preserve_explicit_baseline_values)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  const Options baseline;
  for (const bool parsed : {false, true})
    for (const auto& setting : kissat_abv_batch_settings)
    {
      SCOPED_TRACE(parsed);
      SCOPED_TRACE(setting.name);
      TermManager tm;
      Options options;
      options.set_str("sat-backend", "kissat");
      if (!parsed)
      {
        options.set_str("logic", "QF_ABV");
        options.set(setting.name,
                    scalar_option_text(baseline.get(setting.name)));
      }
      Solver solver(tm, options);
      if (parsed)
        solver.parse_smt2(
            "(set-logic QF_ABV)(set-option :" + std::string(setting.name) +
            " " + scalar_option_text(baseline.get(setting.name)) + ")");
      const Term x = tm.declare("batch_explicit_x", tm.mk_bv_sort(8));
      solver.add(x == 1);
      ASSERT_TRUE(solver.check_sat().is_sat());
      EXPECT_TRUE(solver.options().is_set(setting.name));
      EXPECT_EQ(solver.options().resolved(setting.name),
                baseline.get(setting.name));
    }
}

TEST(OptionEffects, kissat_abv_batch_defaults_preserve_global_search_modes)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  for (const bool parsed : {false, true})
    for (int global : {-1, 0, 1, 2})
      for (int specific : {-2, -1, 0, 1, 2})
      {
        SCOPED_TRACE(parsed);
        SCOPED_TRACE(global);
        SCOPED_TRACE(specific);
        TermManager tm;
        Options options;
        options.set_str("sat-backend", "kissat");
        if (!parsed)
        {
          options.set_str("logic", "QF_ABV");
          options.set_int("kissat-stable", global);
          if (specific != -2)
            options.set_int("kissat-one-shot-stable", specific);
        }
        Solver solver(tm, options);
        if (parsed)
        {
          solver.parse_smt2("(set-logic QF_ABV)(set-option :kissat-stable " +
                            std::to_string(global) + ")");
          if (specific != -2)
            solver.parse_smt2("(set-option :kissat-one-shot-stable " +
                              std::to_string(specific) + ")");
        }
        const Term x = tm.declare("batch_mode_x", tm.mk_bv_sort(8));
        solver.add(x == 1);
        ASSERT_TRUE(solver.check_sat().is_sat());
        EXPECT_EQ(flags_after(tm).kissat_stable, global);
        EXPECT_EQ(flags_after(tm).kissat_one_shot_stable,
                  specific == -2 ? -1 : specific);
        EXPECT_EQ(solver.options().resolved("kissat-one-shot-stable"),
                  OptionValue(std::int64_t(specific == -2 ? -1 : specific)));
      }
}

TEST(OptionEffects, kissat_abv_batch_defaults_retire_before_a_late_push)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  const Options baseline;
  for (const bool parsed : {false, true})
  {
    SCOPED_TRACE(parsed);
    TermManager tm;
    Options options;
    options.set_str("sat-backend", "kissat");
    options.set_bool("check-sanity", true);
    options.set("incremental-auto-engage-at", "1");
    if (!parsed)
      options.set_str("logic", "QF_ABV");
    Solver solver(tm, options);
    if (parsed)
      solver.parse_smt2("(set-logic QF_ABV)");
    add_tuning_array_problem(tm, solver);
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_FALSE(api_test::engine_solver(solver).hasIncrementalSolver());
    EXPECT_TRUE(flags_after(tm).kissat_batch_only);
    if (parsed)
      solver.parse_smt2("(push 1)");
    else
      solver.push();
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_TRUE(api_test::engine_solver(solver).hasIncrementalSolver());
    EXPECT_EQ(flags_after(tm).search_bias, stp::SearchBias::SAT);
    EXPECT_EQ(flags_after(tm).kissat_stable, 2);
    for (const auto& setting : kissat_abv_batch_settings)
      if (std::string(setting.name) != "cadical-factor")
      {
        SCOPED_TRACE(setting.name);
        EXPECT_EQ(solver.options().resolved(setting.name),
                  baseline.get(setting.name));
      }
    EXPECT_FALSE(flags_after(tm).kissat_batch_only);
    EXPECT_EQ(flags_after(tm).kissat_one_shot_stable, -1);
    EXPECT_EQ(flags_after(tm).cnf_auto_threshold, 200000u);
    EXPECT_EQ(flags_after(tm).array_late_read_limit, 0);
    EXPECT_EQ(flags_after(tm).array_late_expansion_limit, 200u);
    EXPECT_EQ(flags_after(tm).array_late_congruence_limit, 4000u);
    EXPECT_FALSE(flags_after(tm).array_equality_gia_cnf);
    if (parsed)
      solver.parse_smt2("(pop 1)");
    else
      solver.pop();
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_FALSE(flags_after(tm).kissat_batch_only);
  }
}

TEST(OptionEffects, kissat_abv_batch_defaults_respect_opt_out_and_named_search)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  const Options baseline;
  for (const char* policy : {"off", "none", "sat", "unsat"})
  {
    SCOPED_TRACE(policy);
    TermManager tm;
    Options options;
    options.set_str("sat-backend", "kissat");
    options.set_str("logic", "QF_ABV");
    const bool off = std::string(policy) == "off";
    options.set_str(off ? "sat-tuning" : "search-bias", policy);
    Solver solver(tm, options);
    const Term x = tm.declare("batch_optout_x", tm.mk_bv_sort(8));
    solver.add(x == 1);
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_EQ(solver.options().resolved("kissat-one-shot-stable"),
              baseline.get("kissat-one-shot-stable"));
    if (off)
      for (const auto& setting : kissat_abv_batch_settings)
      {
        SCOPED_TRACE(setting.name);
        EXPECT_EQ(solver.options().resolved(setting.name),
                  baseline.get(setting.name));
      }
  }
}

TEST(OptionEffects, kissat_abv_batch_defaults_leave_other_backends_unchanged)
{
  const Options baseline;
  for (const char* backend :
       {"cadical", "cryptominisat", "minisat", "simplifying-minisat", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    for (const char* incremental : {"on", "off", "auto"})
    {
      if (std::string(backend) == "kissat" && std::string(incremental) != "on")
        continue;
      SCOPED_TRACE(backend);
      SCOPED_TRACE(incremental);
      TermManager tm;
      Options options;
      options.set_str("sat-backend", backend);
      options.set_str("logic", "QF_ABV");
      options.set_str("incremental", incremental);
      Solver solver(tm, options);
      const Term x = tm.declare("batch_other_backend_x", tm.mk_bv_sort(8));
      solver.add(x == 1);
      ASSERT_TRUE(solver.check_sat().is_sat());
      for (const auto& setting : kissat_abv_batch_settings)
        if (std::string(setting.name) != "cadical-factor")
        {
          SCOPED_TRACE(setting.name);
          EXPECT_EQ(solver.options().resolved(setting.name),
                    baseline.get(setting.name));
        }
    }
  }
}

TEST(OptionEffects, kissat_abv_batch_defaults_preserve_closed_option_windows)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  for (const bool explicit_global : {false, true})
  {
    SCOPED_TRACE(explicit_global);
    TermManager tm;
    Options options;
    options.set_str("sat-backend", "kissat");
    options.set_str("logic", "QF_ABV");
    if (explicit_global)
      options.set_int("kissat-stable", -1);
    Solver solver(tm, options);
    const Term x = tm.declare("batch_closed_x", tm.mk_bv_sort(8));
    solver.add(x == 1);
    ASSERT_TRUE(solver.check_sat().is_sat());
    const OptionValue before =
        solver.options().resolved("kissat-one-shot-stable");
    EXPECT_EQ(before, OptionValue(std::int64_t(explicit_global ? -1 : 0)));
    API_EXPECT_ERROR(ErrorCode::OPTION_TIMING,
                     solver.options().set_int("kissat-stable", -1));
    API_EXPECT_ERROR(ErrorCode::OPTION_TIMING,
                     solver.options().reset("kissat-stable"));
    API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, solver.options().reset_all());
    EXPECT_EQ(solver.options().is_set("kissat-stable"), explicit_global);
    EXPECT_EQ(solver.options().resolved("kissat-one-shot-stable"), before);
    ASSERT_TRUE(solver.check_sat().is_sat());
  }
}

TEST(OptionEffects, copying_kissat_batch_options_does_not_copy_automatic_values)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  const Options baseline;
  TermManager tm;
  Options options;
  options.set_str("sat-backend", "kissat");
  options.set_str("logic", "QF_ABV");
  Solver solver(tm, options);
  const Term x = tm.declare("batch_copy_x", tm.mk_bv_sort(8));
  solver.add(x == 1);
  ASSERT_TRUE(solver.check_sat().is_sat());
  Options copied = solver.options().copy();
  for (const auto& setting : kissat_abv_batch_settings)
  {
    SCOPED_TRACE(setting.name);
    EXPECT_FALSE(copied.is_set(setting.name));
    EXPECT_EQ(copied.get(setting.name), baseline.get(setting.name));
  }
  copied.reset("logic");
  Solver other(tm, copied);
  other.add(x == 2);
  ASSERT_TRUE(other.check_sat().is_sat());
  for (const auto& setting : kissat_abv_batch_settings)
  {
    SCOPED_TRACE(setting.name);
    EXPECT_EQ(other.options().resolved(setting.name),
              baseline.get(setting.name));
  }
  EXPECT_FALSE(flags_after(tm).kissat_batch_only);
  ASSERT_TRUE(solver.check_sat().is_sat());
  EXPECT_TRUE(flags_after(tm).kissat_batch_only);
  EXPECT_EQ(solver.options().resolved("kissat-one-shot-stable"),
            OptionValue(std::int64_t(0)));
}

TEST(OptionEffects, kissat_batch_threshold_updates_remain_explicit_after_checks)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  const Options baseline;
  const auto threshold = baseline.get_uint("cnf-auto-threshold");
  for (const bool parsed : {false, true})
  {
    SCOPED_TRACE(parsed);
    TermManager tm;
    Options options;
    options.set_str("sat-backend", "kissat");
    options.set_bool("check-sanity", true);
    if (!parsed)
      options.set_str("logic", "QF_ABV");
    Solver solver(tm, options);
    if (parsed)
      solver.parse_smt2("(set-logic QF_ABV)");
    add_tuning_array_problem(tm, solver);
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_FALSE(solver.options().is_set("cnf-auto-threshold"));
    for (const auto value : {threshold + 1, threshold})
    {
      if (parsed)
        solver.parse_smt2("(set-option :cnf-auto-threshold " +
                          std::to_string(value) + ")");
      else
        solver.options().set_uint("cnf-auto-threshold", value);
      ASSERT_TRUE(solver.check_sat().is_sat());
      EXPECT_EQ(flags_after(tm).cnf_auto_threshold, value);
      EXPECT_TRUE(solver.options().is_set("cnf-auto-threshold"));
      EXPECT_EQ(solver.options().resolved("cnf-auto-threshold"),
                OptionValue(value));
    }
    solver.push();
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_EQ(flags_after(tm).cnf_auto_threshold, threshold);
    solver.pop();
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_EQ(flags_after(tm).cnf_auto_threshold, threshold);
    EXPECT_TRUE(solver.options().is_set("cnf-auto-threshold"));
  }
}

TEST(OptionEffects, bv_batch_defaults_reach_native_and_parsed_encodings)
{
  if (!has_sat_backend("cadical") && !has_sat_backend("kissat"))
  {
    GTEST_SKIP() << "No tuned BV batch backend is part of this build";
  }
  const Options baseline;
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    const bool kissat = std::string(backend) == "kissat";
    const auto settings = bv_batch_settings(kissat);
    Options expected;
    for (const auto& setting : settings)
      expected.set(setting.name, setting.value);
    for (const bool parsed : {false, true})
      for (const bool forced_batch : {false, true})
      {
        SCOPED_TRACE(backend);
        SCOPED_TRACE(parsed);
        SCOPED_TRACE(forced_batch);
        TermManager tm;
        Options options;
        options.set_str("sat-backend", backend);
        options.set_bool("check-sanity", true);
        if (!parsed)
        {
          options.set_str("logic", "QF_BV");
          if (forced_batch)
            options.set_str("incremental", "off");
        }
        Solver solver(tm, options);
        if (parsed)
        {
          solver.parse_smt2("(set-logic QF_BV)");
          if (forced_batch)
            solver.parse_smt2("(set-option :incremental false)");
        }
        add_tuning_bv_problem(tm, solver);
        bool emitted = false;
        solver.set_cnf_sink(
            [&](std::string_view, CnfScope)
            {
              emitted = true;
              const auto& flags = flags_after(tm);
              EXPECT_EQ(flags.sat_search_options.phase, 0);
              EXPECT_EQ(flags.kissat_batch_only, kissat);
              EXPECT_EQ(flags.kissat_adaptive_cnf, kissat);
              EXPECT_EQ(flags.kissat_import_order, kissat ? 2 : 0);
              EXPECT_EQ(flags.kissat_incremental_greedy, kissat ? 4 : 0);
              EXPECT_EQ(flags.kissat_one_shot_stable, -1);
              EXPECT_EQ(flags.enable_conditional_equality, kissat);
            });
        ASSERT_TRUE(solver.check_sat().is_sat());
        EXPECT_TRUE(emitted);
        for (const auto& setting : settings)
        {
          SCOPED_TRACE(setting.name);
          EXPECT_EQ(solver.options().resolved(setting.name),
                    expected.resolved(setting.name));
          EXPECT_EQ(solver.options().info(setting.name).resolved,
                    expected.resolved(setting.name));
          EXPECT_EQ(solver.options().get(setting.name),
                    baseline.get(setting.name));
          EXPECT_FALSE(solver.options().is_set(setting.name));
        }
      }
  }
}

TEST(OptionEffects, bv_batch_defaults_preserve_explicit_baseline_values)
{
  if (!has_sat_backend("cadical") && !has_sat_backend("kissat"))
  {
    GTEST_SKIP() << "No tuned BV batch backend is part of this build";
  }
  const Options baseline;
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    for (const bool parsed : {false, true})
      for (const auto& setting :
           bv_batch_settings(std::string(backend) == "kissat"))
      {
        SCOPED_TRACE(backend);
        SCOPED_TRACE(parsed);
        SCOPED_TRACE(setting.name);
        TermManager tm;
        Options options;
        options.set_str("sat-backend", backend);
        if (!parsed)
        {
          options.set_str("logic", "QF_BV");
          options.set(setting.name,
                      scalar_option_text(baseline.get(setting.name)));
        }
        Solver solver(tm, options);
        if (parsed)
          solver.parse_smt2(
              "(set-logic QF_BV)(set-option :" + std::string(setting.name) +
              " " + scalar_option_text(baseline.get(setting.name)) + ")");
        const Term x = tm.declare("bv_explicit_x", tm.mk_bv_sort(8));
        solver.add(x == 1);
        ASSERT_TRUE(solver.check_sat().is_sat());
        EXPECT_TRUE(solver.options().is_set(setting.name));
        EXPECT_EQ(solver.options().resolved(setting.name),
                  baseline.get(setting.name));
      }
  }
}

TEST(OptionEffects, bv_batch_defaults_retire_before_a_late_push)
{
  if (!has_sat_backend("cadical") && !has_sat_backend("kissat"))
  {
    GTEST_SKIP() << "No tuned BV batch backend is part of this build";
  }
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    const bool kissat = std::string(backend) == "kissat";
    const auto settings = bv_batch_settings(kissat);
    Options expected;
    if (kissat)
    {
      expected.set_str("search-bias", "unsat");
      expected.set_str("cnf-generation-effort", "new-medium");
    }
    else
      expected.set_int("sat-rephase", 0);
    for (const bool parsed : {false, true})
    {
      SCOPED_TRACE(backend);
      SCOPED_TRACE(parsed);
      TermManager tm;
      Options options;
      options.set_str("sat-backend", backend);
      options.set_bool("check-sanity", true);
      options.set("incremental-auto-engage-at", "1");
      if (!parsed)
        options.set_str("logic", "QF_BV");
      Solver solver(tm, options);
      if (parsed)
        solver.parse_smt2("(set-logic QF_BV)");
      add_tuning_bv_problem(tm, solver);
      ASSERT_TRUE(solver.check_sat().is_sat());
      EXPECT_FALSE(api_test::engine_solver(solver).hasIncrementalSolver());
      EXPECT_EQ(flags_after(tm).sat_search_options.phase, 0);
      EXPECT_EQ(flags_after(tm).kissat_batch_only, kissat);
      EXPECT_EQ(flags_after(tm).enable_conditional_equality, kissat);
      if (parsed)
        solver.parse_smt2("(push 1)");
      else
        solver.push();
      ASSERT_TRUE(solver.check_sat().is_sat());
      EXPECT_TRUE(api_test::engine_solver(solver).hasIncrementalSolver());
      for (const auto& setting : settings)
      {
        SCOPED_TRACE(setting.name);
        EXPECT_EQ(solver.options().resolved(setting.name),
                  expected.resolved(setting.name));
      }
      EXPECT_FALSE(flags_after(tm).kissat_batch_only);
      EXPECT_FALSE(flags_after(tm).kissat_adaptive_cnf);
      EXPECT_EQ(flags_after(tm).kissat_import_order, 0);
      EXPECT_EQ(flags_after(tm).kissat_incremental_greedy, 0);
      EXPECT_FALSE(flags_after(tm).enable_conditional_equality);
      if (parsed)
        solver.parse_smt2("(pop 1)");
      else
        solver.pop();
      ASSERT_TRUE(solver.check_sat().is_sat());
      EXPECT_FALSE(flags_after(tm).kissat_batch_only);
      EXPECT_EQ(solver.options().resolved("sat-phase"),
                expected.resolved("sat-phase"));
    }
  }
}

TEST(OptionEffects, bv_batch_defaults_respect_opt_out_and_named_search)
{
  if (!has_sat_backend("cadical") && !has_sat_backend("kissat"))
  {
    GTEST_SKIP() << "No tuned BV batch backend is part of this build";
  }
  const Options baseline;
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    for (const char* policy : {"off", "none", "sat", "unsat"})
    {
      SCOPED_TRACE(backend);
      SCOPED_TRACE(policy);
      const bool off = std::string(policy) == "off";
      TermManager tm;
      Options options;
      options.set_str("sat-backend", backend);
      options.set_str("logic", "QF_BV");
      options.set_str(off ? "sat-tuning" : "search-bias", policy);
      Solver solver(tm, options);
      const Term x = tm.declare("bv_policy_x", tm.mk_bv_sort(8));
      solver.add(x == 1);
      ASSERT_TRUE(solver.check_sat().is_sat());
      EXPECT_EQ(solver.options().resolved("sat-phase"),
                options.resolved("sat-phase"));
      for (const auto& setting :
           bv_batch_settings(std::string(backend) == "kissat"))
        if (off)
        {
          SCOPED_TRACE(setting.name);
          EXPECT_EQ(solver.options().resolved(setting.name),
                    baseline.get(setting.name));
        }
    }
  }
}

TEST(OptionEffects, copying_bv_batch_options_does_not_copy_automatic_values)
{
  if (!has_sat_backend("cadical") && !has_sat_backend("kissat"))
  {
    GTEST_SKIP() << "No tuned BV batch backend is part of this build";
  }
  const Options baseline;
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    SCOPED_TRACE(backend);
    const bool kissat = std::string(backend) == "kissat";
    const auto settings = bv_batch_settings(kissat);
    TermManager tm;
    Options options;
    options.set_str("sat-backend", backend);
    options.set_str("logic", "QF_BV");
    Solver solver(tm, options);
    const Term x = tm.declare("bv_copy_x", tm.mk_bv_sort(8));
    solver.add(x == 1);
    ASSERT_TRUE(solver.check_sat().is_sat());
    Options copied = solver.options().copy();
    for (const auto& setting : settings)
    {
      SCOPED_TRACE(setting.name);
      EXPECT_FALSE(copied.is_set(setting.name));
      EXPECT_EQ(copied.get(setting.name), baseline.get(setting.name));
    }
    copied.reset("logic");
    Solver other(tm, copied);
    other.add(x == 2);
    ASSERT_TRUE(other.check_sat().is_sat());
    for (const auto& setting : settings)
    {
      SCOPED_TRACE(setting.name);
      EXPECT_EQ(other.options().resolved(setting.name),
                baseline.get(setting.name));
    }
    EXPECT_FALSE(flags_after(tm).kissat_batch_only);
    EXPECT_FALSE(flags_after(tm).kissat_adaptive_cnf);
    ASSERT_TRUE(solver.check_sat().is_sat());
    EXPECT_EQ(flags_after(tm).sat_search_options.phase, 0);
    EXPECT_EQ(flags_after(tm).kissat_batch_only, kissat);
    EXPECT_EQ(flags_after(tm).kissat_import_order, kissat ? 2 : 0);
    EXPECT_EQ(flags_after(tm).kissat_adaptive_cnf, kissat);
  }
}

TEST(OptionEffects, kissat_bv_batch_defaults_preserve_closed_option_windows)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  const Options baseline;
  TermManager tm;
  Options options;
  options.set_str("sat-backend", "kissat");
  options.set_str("logic", "QF_BV");
  Solver solver(tm, options);
  const Term x = tm.declare("bv_window_x", tm.mk_bv_sort(8));
  solver.add(x == 1);
  ASSERT_TRUE(solver.check_sat().is_sat());
  for (const auto& setting : bv_batch_settings(true))
    if (std::string(setting.name) != "cnf-generation-effort")
    {
      SCOPED_TRACE(setting.name);
      const auto before = solver.options().resolved(setting.name);
      API_EXPECT_ERROR(
          ErrorCode::OPTION_TIMING,
          solver.options().set(setting.name,
                               scalar_option_text(baseline.get(setting.name))));
      EXPECT_EQ(solver.options().resolved(setting.name), before);
      EXPECT_FALSE(solver.options().is_set(setting.name));
    }
}

TEST(OptionEffects, bv_batch_conditional_default_rewrites_prebuilt_definitions)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  for (const bool parsed : {false, true})
  {
    SCOPED_TRACE(parsed);
    TermManager::Config config;
    config.simplify = false;
    TermManager tm(config);
    const Term condition = tm.declare("auto_conditional_c", tm.mk_bool_sort());
    const Sort word = tm.mk_bv_sort(8);
    const Term x = tm.declare("auto_conditional_x", word);
    const Term a = tm.declare("auto_conditional_a", word);
    const Term b = tm.declare("auto_conditional_b", word);
    const Term definition = ite(condition, x == a, x == b);
    const Term opposite = x != ite(condition, a, b);
    Options options;
    options.set_str("sat-backend", "kissat");
    options.set_bool("check-sanity", true);
    if (!parsed)
      options.set_str("logic", "QF_BV");
    Solver solver(tm, options);
    if (parsed)
      solver.parse_smt2("(set-logic QF_BV)");
    solver.add(definition && opposite);
    bool emitted = false;
    solver.set_cnf_sink([&](std::string_view, CnfScope) { emitted = true; });
    ASSERT_TRUE(solver.check_sat().is_unsat());
    EXPECT_FALSE(emitted);
    EXPECT_TRUE(flags_after(tm).enable_conditional_equality);
    EXPECT_FALSE(solver.options().is_set("bv-conditional-equality"));
    EXPECT_FALSE(solver.options().get_bool("bv-conditional-equality"));
    EXPECT_EQ(solver.options().resolved("bv-conditional-equality"),
              OptionValue(true));
  }
}

TEST(OptionEffects, bv_batch_defaults_preserve_explicit_composite_settings)
{
  if (!has_sat_backend("kissat"))
    GTEST_SKIP() << "Kissat is not part of this build";
  for (const bool parsed : {false, true})
    for (const bool disabled : {false, true})
    {
      SCOPED_TRACE(parsed);
      SCOPED_TRACE(disabled);
      TermManager tm;
      Options options;
      options.set_str("sat-backend", "kissat");
      options.set_bool("check-sanity", true);
      if (!parsed)
      {
        options.set_str("logic", "QF_BV");
        options.set_bool("disable-simplifications", disabled);
      }
      Solver solver(tm, options);
      if (parsed)
        solver.parse_smt2(
            std::string(
                "(set-logic QF_BV)(set-option :disable-simplifications ") +
            (disabled ? "true)" : "false)"));
      const Term x = tm.declare("auto_composite_x", tm.mk_bv_sort(8));
      solver.add(x == 1);
      ASSERT_TRUE(solver.check_sat().is_sat());
      EXPECT_EQ(flags_after(tm).enable_conditional_equality, !disabled);
      EXPECT_FALSE(solver.options().is_set("bv-conditional-equality"));
      EXPECT_EQ(solver.options().resolved("bv-conditional-equality"),
                OptionValue(!disabled));
      EXPECT_EQ(flags_after(tm).sat_search_options.phase, 0);
    }
}

TEST(OptionEffects, fp_batch_defaults_reach_native_and_parsed_encodings)
{
  if (!has_sat_backend("cadical") && !has_sat_backend("kissat"))
  {
    GTEST_SKIP() << "No tuned FP batch backend is part of this build";
  }
  const Options baseline;
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    const bool kissat = std::string(backend) == "kissat";
    const auto settings = fp_batch_settings(kissat);
    Options expected;
    for (const auto& setting : settings)
      expected.set(setting.name, setting.value);
    for (const char* logic : {"QF_BVFP", "QF_ABVFP"})
      for (const bool parsed : {false, true})
      {
        SCOPED_TRACE(backend);
        SCOPED_TRACE(logic);
        SCOPED_TRACE(parsed);
        TermManager tm;
        Options options;
        options.set_str("sat-backend", backend);
        options.set_bool("check-sanity", true);
        if (!parsed)
          options.set_str("logic", logic);
        Solver solver(tm, options);
        if (parsed)
          solver.parse_smt2("(set-logic " + std::string(logic) + ")");
        add_tuning_fp_problem(tm, solver, std::string(logic) == "QF_ABVFP");
        bool emitted = false;
        solver.set_cnf_sink(
            [&](std::string_view, CnfScope)
            {
              emitted = true;
              const auto& flags = flags_after(tm);
              EXPECT_EQ(flags.cadical_factor,
                        stp::UserDefinedFlags::BVAMode::OFF);
              if (kissat)
              {
                EXPECT_EQ(flags.search_bias, stp::SearchBias::SAT);
                EXPECT_EQ(flags.kissat_stable, 2);
                EXPECT_EQ(flags.sat_search_options.target, 0);
                EXPECT_EQ(flags.sat_search_options.rephase, 0);
                EXPECT_EQ(flags.cnf_effort,
                          stp::UserDefinedFlags::CNF_EFFORT_NEW_MEDIUM);
                EXPECT_FALSE(flags.kissat_probe);
                EXPECT_EQ(flags.kissat_trail_reuse_mode, 2);
                EXPECT_EQ(flags.kissat_incremental_greedy, 2);
                EXPECT_EQ(flags.kissat_greedy_growth, 1);
              }
            });
        ASSERT_TRUE(solver.check_sat().is_sat());
        EXPECT_TRUE(emitted);
        for (const auto& setting : settings)
        {
          SCOPED_TRACE(setting.name);
          EXPECT_EQ(solver.options().resolved(setting.name),
                    expected.resolved(setting.name));
          EXPECT_FALSE(solver.options().is_set(setting.name));
          EXPECT_EQ(solver.options().get(setting.name),
                    baseline.get(setting.name));
        }
      }
  }
}

TEST(OptionEffects, fp_batch_defaults_preserve_explicit_baseline_values)
{
  if (!has_sat_backend("cadical") && !has_sat_backend("kissat"))
  {
    GTEST_SKIP() << "No tuned FP batch backend is part of this build";
  }
  const Options baseline;
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    for (const char* logic : {"QF_BVFP", "QF_ABVFP"})
      for (const bool parsed : {false, true})
        for (const auto& setting :
             fp_batch_settings(std::string(backend) == "kissat"))
        {
          SCOPED_TRACE(backend);
          SCOPED_TRACE(logic);
          SCOPED_TRACE(parsed);
          SCOPED_TRACE(setting.name);
          TermManager tm;
          Options options;
          options.set_str("sat-backend", backend);
          if (!parsed)
          {
            options.set_str("logic", logic);
            options.set(setting.name,
                        scalar_option_text(baseline.get(setting.name)));
          }
          Solver solver(tm, options);
          if (parsed)
            solver.parse_smt2("(set-logic " + std::string(logic) +
                              ")(set-option :" + setting.name + " " +
                              scalar_option_text(baseline.get(setting.name)) +
                              ")");
          const Term x = tm.declare("fp_explicit_x", tm.mk_bv_sort(8));
          solver.add(x == 1);
          ASSERT_TRUE(solver.check_sat().is_sat());
          EXPECT_TRUE(solver.options().is_set(setting.name));
          EXPECT_EQ(solver.options().resolved(setting.name),
                    baseline.get(setting.name));
        }
  }
}

TEST(OptionEffects, fp_batch_defaults_retire_before_a_late_push)
{
  if (!has_sat_backend("cadical") && !has_sat_backend("kissat"))
  {
    GTEST_SKIP() << "No tuned FP batch backend is part of this build";
  }
  const Options baseline;
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    const auto settings = fp_batch_settings(std::string(backend) == "kissat");
    for (const char* logic : {"QF_BVFP", "QF_ABVFP"})
      for (const bool parsed : {false, true})
      {
        SCOPED_TRACE(backend);
        SCOPED_TRACE(logic);
        SCOPED_TRACE(parsed);
        TermManager tm;
        Options options;
        options.set_str("sat-backend", backend);
        options.set_bool("check-sanity", true);
        options.set("incremental-auto-engage-at", "1");
        if (!parsed)
          options.set_str("logic", logic);
        Solver solver(tm, options);
        if (parsed)
          solver.parse_smt2("(set-logic " + std::string(logic) + ")");
        add_tuning_fp_problem(tm, solver, std::string(logic) == "QF_ABVFP");
        ASSERT_TRUE(solver.check_sat().is_sat());
        EXPECT_FALSE(api_test::engine_solver(solver).hasIncrementalSolver());
        EXPECT_EQ(flags_after(tm).cadical_factor,
                  stp::UserDefinedFlags::BVAMode::OFF);
        if (parsed)
          solver.parse_smt2("(push 1)");
        else
          solver.push();
        ASSERT_TRUE(solver.check_sat().is_sat());
        EXPECT_TRUE(api_test::engine_solver(solver).hasIncrementalSolver());
        for (const auto& setting : settings)
        {
          SCOPED_TRACE(setting.name);
          EXPECT_EQ(solver.options().resolved(setting.name),
                    baseline.resolved(setting.name));
        }
        if (parsed)
          solver.parse_smt2("(pop 1)");
        else
          solver.pop();
        ASSERT_TRUE(solver.check_sat().is_sat());
        for (const auto& setting : settings)
          EXPECT_EQ(solver.options().resolved(setting.name),
                    baseline.resolved(setting.name));
      }
  }
}

TEST(OptionEffects, fp_batch_defaults_respect_opt_out_and_named_search)
{
  if (!has_sat_backend("cadical") && !has_sat_backend("kissat"))
  {
    GTEST_SKIP() << "No tuned FP batch backend is part of this build";
  }
  const Options baseline;
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    for (const char* logic : {"QF_BVFP", "QF_ABVFP"})
      for (const char* policy : {"off", "none", "sat", "unsat"})
      {
        SCOPED_TRACE(backend);
        SCOPED_TRACE(logic);
        SCOPED_TRACE(policy);
        const bool off = std::string(policy) == "off";
        TermManager tm;
        Options options;
        options.set_str("sat-backend", backend);
        options.set_str("logic", logic);
        options.set_str(off ? "sat-tuning" : "search-bias", policy);
        Solver solver(tm, options);
        const Term x = tm.declare("fp_policy_x", tm.mk_bv_sort(8));
        solver.add(x == 1);
        ASSERT_TRUE(solver.check_sat().is_sat());
        for (const char* name :
             {"sat-phase", "sat-rephase", "sat-target", "kissat-stable"})
          EXPECT_EQ(solver.options().resolved(name), options.resolved(name));
        if (off)
        {
          for (const auto& setting :
               fp_batch_settings(std::string(backend) == "kissat"))
          {
            SCOPED_TRACE(setting.name);
            EXPECT_EQ(solver.options().resolved(setting.name),
                      baseline.get(setting.name));
          }
        }
      }
  }
}

TEST(OptionEffects, batch_defaults_yield_to_first_assumptions_and_core_requests)
{
  if (!has_sat_backend("cadical") && !has_sat_backend("kissat"))
  {
    GTEST_SKIP() << "No tuned batch backend is part of this build";
  }
  const Options baseline;
  for (const char* backend : {"cadical", "kissat"})
  {
    if (!has_sat_backend(backend))
      continue;
    for (const char* logic : {"QF_BV", "QF_ABV", "QF_BVFP", "QF_ABVFP"})
      for (const std::string request : {"assuming", "assuming-empty", "cores"})
      {
        SCOPED_TRACE(backend);
        SCOPED_TRACE(logic);
        SCOPED_TRACE(request);
        TermManager tm;
        Options options;
        options.set_str("sat-backend", backend);
        options.set_bool("check-sanity", true);
        options.set_int("incremental-auto-engage-at", 1);
        std::string said;
        Solver solver(tm, options);
        solver.set_output_sink([&](std::string_view text)
                               { said.append(text); });
        std::string script = "(set-logic " + std::string(logic) + ")";
        if (request == "cores")
          script += "(set-option :produce-unsat-cores true)";
        script += "(declare-const x (_ BitVec 8))"
                  "(declare-const y (_ BitVec 8))"
                  "(declare-const gate Bool)"
                  "(assert (= (bvmul x y) #x8f))"
                  "(assert (bvugt x #x01))(assert (bvugt y #x01))";
        script += request == "cores"      ? "(check-sat)"
                  : request == "assuming" ? "(check-sat-assuming (gate))"
                                          : "(check-sat-assuming ())";
        solver.parse_smt2(script, ParseMode::EXECUTE);
        ASSERT_EQ(said, "sat\n");
        // Even the first empty assuming command creates a temporary frame.
        // Its AUTO incremental profile must precede encoding, and remain
        // selected when the temporary frame has gone away.
        for (const bool second_check : {false, true})
        {
          if (second_check)
          {
            ASSERT_TRUE(solver.check_sat().is_sat());
          }
          for (const char* name :
               {"kissat-batch-only", "kissat-one-shot-stable",
                "kissat-adaptive-cnf", "kissat-import-order",
                "bv-conditional-equality", "cnf-auto-threshold",
                "array-late-read-limit", "array-late-expansion-limit",
                "array-late-congruence-limit", "array-equality-gia-cnf",
                "array-equality-gia-min-reads"})
          {
            SCOPED_TRACE(name);
            EXPECT_EQ(solver.options().resolved(name), baseline.get(name));
            EXPECT_FALSE(solver.options().is_set(name));
          }
          const auto& flags = flags_after(tm);
          EXPECT_FALSE(flags.kissat_batch_only);
          EXPECT_FALSE(flags.kissat_adaptive_cnf);
          EXPECT_EQ(flags.kissat_import_order, 0);
          EXPECT_FALSE(flags.enable_conditional_equality);
          EXPECT_EQ(flags.array_late_read_limit, 0);
          EXPECT_EQ(flags.array_late_expansion_limit, 200u);
          EXPECT_EQ(flags.array_late_congruence_limit, 4000u);
          EXPECT_FALSE(flags.array_equality_gia_cnf);
          if (std::string(logic) == "QF_BVFP" ||
              std::string(logic) == "QF_ABVFP")
          {
            EXPECT_EQ(solver.options().resolved("cadical-factor"),
                      baseline.get("cadical-factor"));
            EXPECT_EQ(solver.options().resolved("kissat-stable"),
                      baseline.get("kissat-stable"));
          }
        }
      }
  }
}

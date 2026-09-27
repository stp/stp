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

// api3-registry.cpp -- the option registry against the engine and the
// command line it generates: every field-mapped entry's default is the
// engine's (a fresh UserDefinedFlags), and the CLI tables of options.toml
// are consistent with the entries. These read lib/Api/Internal.h, the
// in-tree view of the registry that tools/stp/main.cpp registers from.

#include "Api/Internal.h"

#include <gtest/gtest.h>

#include <cstring>
#include <set>
#include <string>

namespace reg = stp::api::detail;

// The registry's default of every entry that maps straight onto a
// UserDefinedFlags member is the member's initialiser. The CLI shows the
// registry's default in --help and the library applies only what differs
// from it, so a drift here would show a wrong default and skip a real one.
TEST(Registry, defaults_are_the_engines)
{
  const stp::UserDefinedFlags fresh;
  std::size_t n = 0;
  const reg::DefaultCheck* checks = reg::option_default_checks(n);
  ASSERT_GT(n, 100u);
  for (std::size_t i = 0; i < n; ++i)
  {
    const reg::OptionSpec* spec = reg::find_option(checks[i].name);
    ASSERT_NE(spec, nullptr) << checks[i].name;
    EXPECT_EQ(std::string(spec->default_text), checks[i].engine_default(fresh))
        << "--" << checks[i].name << ": options.toml says " << spec->default_text
        << ", UserDefinedFlags starts at " << checks[i].engine_default(fresh);
  }
}

// Every entry has a --help group, every alias sets an enum entry to one of
// its values and never shadows an entry, and every frontend row is one of
// the four kinds with a group (except the positional).
TEST(Registry, cli_tables_are_consistent)
{
  std::size_t ng = 0;
  const char* const* groups = reg::cli_groups(ng);
  std::set<std::string> group_set;
  for (std::size_t g = 0; g < ng; ++g)
    group_set.insert(groups[g]);
  EXPECT_EQ(group_set.size(), ng);

  std::size_t nc = 0;
  const reg::CliCategory* cats = reg::cli_categories(nc);
  std::set<std::string> categories;
  for (std::size_t c = 0; c < nc; ++c)
  {
    categories.insert(cats[c].category);
    EXPECT_TRUE(group_set.count(cats[c].group)) << cats[c].group;
  }
  std::size_t n = 0;
  const reg::OptionSpec* specs = reg::option_specs(n);
  for (std::size_t i = 0; i < n; ++i)
  {
    EXPECT_TRUE(categories.count(specs[i].category)) << specs[i].name;
    const std::string form = specs[i].cli_form;
    EXPECT_TRUE(form == "value" || form == "flag" || form == "none") << specs[i].name;
    if (form == "flag")
    {
      EXPECT_TRUE(specs[i].type == reg::OptType::BOOL || specs[i].type == reg::OptType::MODE)
          << specs[i].name;
    }
  }

  std::size_t na = 0;
  const reg::CliAlias* aliases = reg::cli_aliases(na);
  EXPECT_GE(na, 4u);
  for (std::size_t a = 0; a < na; ++a)
  {
    const reg::OptionSpec* of = reg::find_option(aliases[a].of);
    ASSERT_NE(of, nullptr) << aliases[a].name;
    EXPECT_EQ(of->type, reg::OptType::ENUM);
    bool member = false;
    for (std::size_t v = 0; v < of->num_values; ++v)
      member = member || std::strcmp(of->values[v], aliases[a].value) == 0;
    EXPECT_TRUE(member) << aliases[a].name;
    EXPECT_EQ(reg::find_option(aliases[a].name), nullptr) << aliases[a].name;
    EXPECT_NE(aliases[a].help, nullptr);
  }

  std::size_t nf = 0;
  const reg::CliFrontend* front = reg::cli_frontend(nf);
  EXPECT_GE(nf, 10u);
  std::set<std::string> keys;
  for (std::size_t r = 0; r < nf; ++r)
  {
    EXPECT_TRUE(keys.insert(front[r].key).second) << front[r].key;
    const std::string kind = front[r].kind;
    EXPECT_TRUE(kind == "positional" || kind == "help" || kind == "flag" || kind == "bool-option")
        << front[r].key;
    if (kind != "positional")
    {
      EXPECT_TRUE(front[r].group != nullptr && group_set.count(front[r].group)) << front[r].key;
    }
    EXPECT_NE(front[r].help, nullptr);
    EXPECT_NE(front[r].api, nullptr);
  }
}

// The stp binary applies the registry to a bare STPMgr: the appliers that
// consult the manager must do without one, and a manager-scoped entry
// reaches its flag there rather than being refused.
TEST(Registry, applies_without_a_manager)
{
  stp::UserDefinedFlags flags;
  reg::OptionsImpl o;
  o.set_text("test", "uf-sort-width", "24");
  o.set_text("test", "array-equality", "on");
  o.set_text("test", "uninterpreted-functions", "off");
  o.set_text("test", "max-time", "2s");
  o.set_text("test", "bv-term-abstraction-rounds", "5");
  o.set_text("test", "simplify", "false");
  reg::EngineTarget target{flags, nullptr, nullptr};
  reg::apply_all_options(target, o);
  EXPECT_EQ(flags.uf_sort_width, 24u);
  EXPECT_TRUE(flags.enable_array_equality);
  EXPECT_FALSE(flags.enable_uninterpreted_functions);
  EXPECT_EQ(flags.timeout_max_time_ms, 2000);
  EXPECT_EQ(flags.bv_term_abstraction_rounds, 5u);
  EXPECT_TRUE(flags.bv_term_abstraction_rounds_explicit);
  // auto leaves the frontend's set-logic to decide
  const bool before = flags.enable_uninterpreted_functions;
  reg::OptionsImpl o2;
  o2.set_text("test", "uninterpreted-functions", "auto");
  reg::apply_all_options(target, o2, true);
  EXPECT_EQ(flags.enable_uninterpreted_functions, before);
}

// A solver re-applies every registry default whenever it becomes the active
// one (apply_all_options with force_all). The engine's "the caller named it"
// markers must then stay clear: a named ceiling is what keeps a profile from
// overwriting it, so a default that counted as named would silently disable
// every profile.
TEST(Registry, reapplied_defaults_are_not_requests)
{
  stp::UserDefinedFlags flags;
  reg::OptionsImpl o;
  reg::EngineTarget target{flags, nullptr, nullptr};
  reg::apply_all_options(target, o, true);
  EXPECT_FALSE(flags.bv_term_abstraction_rounds_explicit);
  EXPECT_FALSE(flags.bv_term_abstraction_divmod_explicit);
  EXPECT_FALSE(flags.bv_term_abstraction_schema_groups_explicit);
  EXPECT_FALSE(flags.lra_decision_polarity_explicit);
  EXPECT_FALSE(flags.cadical_factor_explicit);
  // and a value the caller did set is a request, re-applied or not
  o.set_text("test", "bv-term-abstraction-rounds", "7");
  reg::apply_all_options(target, o, true);
  EXPECT_TRUE(flags.bv_term_abstraction_rounds_explicit);
  EXPECT_FALSE(flags.bv_term_abstraction_divmod_explicit);
}

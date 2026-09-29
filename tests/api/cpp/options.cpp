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

// options.cpp -- the option registry through Options and SolverOptions:
// every entry by text and by its typed setter, every enum/set member, every
// alias, short flag and negation through set_args, the five OPTION_* codes,
// the manager-scoped rows, resolution, info, names and help.

#include "api_common.hpp"

#include <algorithm>
#include <set>

using namespace stp;

namespace
{

// The CLI text of a value, as Options::set parses it.
std::string text_of(const OptionInfo& info, const OptionValue& v)
{
  switch (v.index())
  {
    case 0: return std::get<bool>(v) ? "true" : "false";
    case 1:
    {
      const std::int64_t i = std::get<std::int64_t>(v);
      if (info.type == "duration")
        return i < 0 ? "none" : std::to_string(i) + "ms";
      return std::to_string(i);
    }
    case 2: return std::to_string(std::get<std::uint64_t>(v));
    case 3: return std::get<std::string>(v);
    default:
    {
      std::string out;
      for (const std::string& s : std::get<std::vector<std::string>>(v))
        out += (out.empty() ? "" : ",") + s;
      return out;
    }
  }
}

TEST(Options, every_entry_accepts_its_default_by_text_and_by_type)
{
  Options probe;
  const std::vector<std::string> names = probe.names();
  EXPECT_GE(names.size(), 200u);
  std::set<std::string> seen;
  for (const std::string& name : names)
  {
    SCOPED_TRACE(name);
    EXPECT_TRUE(seen.insert(name).second);
    const OptionInfo info = probe.info(name);
    EXPECT_EQ(info.name, name);
    EXPECT_FALSE(info.type.empty());
    EXPECT_FALSE(info.help.empty());
    EXPECT_FALSE(info.category.empty());
    EXPECT_FALSE(info.is_set);
    EXPECT_TRUE(info.current == info.default_value);
    EXPECT_EQ(info.python_key.find('-'), std::string::npos);
    EXPECT_EQ(info.python_key.find('.'), std::string::npos);
    // by text
    Options o;
    o.set(name, text_of(info, info.default_value));
    EXPECT_TRUE(o.is_set(name));
    EXPECT_TRUE(o.get(name) == info.default_value) << text_of(info, o.get(name));
    EXPECT_TRUE(o.info(name).is_set);
    // by the typed setter of the entry's type, and a mismatched one refused
    Options t;
    if (info.type == "bool")
    {
      t.set_bool(name, std::get<bool>(info.default_value));
      EXPECT_EQ(t.get_bool(name), std::get<bool>(info.default_value));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.set_int(name, 1));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.set_str(name, "true"));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.get_int(name));
    }
    else if (info.type == "int")
    {
      t.set_int(name, std::get<std::int64_t>(info.default_value));
      EXPECT_EQ(t.get_int(name), std::get<std::int64_t>(info.default_value));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.set_bool(name, true));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.get_bool(name));
    }
    else if (info.type == "uint")
    {
      t.set_uint(name, std::get<std::uint64_t>(info.default_value));
      EXPECT_EQ(t.get_uint(name), std::get<std::uint64_t>(info.default_value));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.set_bool(name, true));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.set_names(name, {}));
    }
    else if (info.type == "mode" || info.type == "enum" || info.type == "string" ||
             info.type == "path")
    {
      t.set_str(name, std::get<std::string>(info.default_value));
      EXPECT_EQ(t.get_str(name), std::get<std::string>(info.default_value));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.set_bool(name, true));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.get_uint(name));
    }
    else if (info.type == "set")
    {
      t.set_names(name, std::get<std::vector<std::string>>(info.default_value));
      EXPECT_EQ(t.get_names(name), std::get<std::vector<std::string>>(info.default_value));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.set_str(name, "x"));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.get_str(name));
    }
    else if (info.type == "duration")
    {
      t.set_duration(name, std::chrono::milliseconds(std::get<std::int64_t>(info.default_value)));
      EXPECT_EQ(t.get_duration(name).count(), std::get<std::int64_t>(info.default_value));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.set_bool(name, true));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.set_str(name, "1s"));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, t.get_bool(name));
    }
    else
      ADD_FAILURE() << "unknown option type " << info.type;
    EXPECT_TRUE(t.is_set(name));
    EXPECT_TRUE(t.get(name) == info.default_value);
    // reset returns the entry to its default and clears is_set
    t.reset(name);
    EXPECT_FALSE(t.is_set(name));
    EXPECT_TRUE(t.get(name) == info.default_value);
  }
}

TEST(Options, every_enum_and_set_member)
{
  Options probe;
  for (const std::string& name : probe.names())
  {
    const OptionInfo info = probe.info(name);
    if (info.type == "enum")
    {
      EXPECT_FALSE(info.values.empty()) << name;
      for (const std::string& v : info.values)
      {
        SCOPED_TRACE(name + " = " + v);
        Options o;
        o.set_str(name, v);
        EXPECT_EQ(o.get_str(name), v);
        Options p;
        p.set(name, v);
        EXPECT_EQ(p.get_str(name), v);
        Options q;
        q.set_args({"--" + name + "=" + v});
        EXPECT_EQ(q.get_str(name), v);
      }
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, Options().set_str(name, "no-such-member"));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, Options().set(name, "no-such-member"));
    }
    else if (info.type == "set")
    {
      EXPECT_FALSE(info.values.empty()) << name;
      for (const std::string& v : info.values)
      {
        SCOPED_TRACE(name + " = " + v);
        Options o;
        o.set_names(name, {v});
        EXPECT_EQ(o.get_names(name), std::vector<std::string>{v});
        Options p;
        p.set(name, v);
        EXPECT_EQ(p.get_names(name), std::vector<std::string>{v});
      }
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, Options().set_names(name, {"no-such-member"}));
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, Options().set(name, "no-such-member"));
    }
    else if (info.type == "mode")
    {
      for (const char* v : {"auto", "on", "off"})
      {
        Options o;
        o.set_str(name, v);
        EXPECT_EQ(o.get_str(name), v);
      }
      Options o;
      API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_str(name, "maybe"));
      if (!info.values.empty())
      {
        // a mode that lists its spellings takes those alone, exactly
        EXPECT_EQ(info.values, (std::vector<std::string>{"on", "off", "auto"})) << name;
        API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set(name, "1"));
        API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set(name, "ON"));
        continue;
      }
      o.set(name, "1");
      EXPECT_EQ(o.get_str(name), "on");
      o.set(name, "false");
      EXPECT_EQ(o.get_str(name), "off");
      o.set(name, "Auto");
      EXPECT_EQ(o.get_str(name), "auto");
    }
  }
  // set members: comma lists and spaces; members, like enum values, match
  // exactly
  Options o;
  o.set("fp-abstraction-ops", "mul, fma");
  EXPECT_EQ(o.get_names("fp-abstraction-ops"), (std::vector<std::string>{"mul", "fma"}));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("fp-abstraction-ops", "mul, FMA"));
  EXPECT_EQ(o.get_names("fp-abstraction-ops"), (std::vector<std::string>{"mul", "fma"}));
  o.set("fp-abstraction-ops", "none");
  EXPECT_EQ(o.get_names("fp-abstraction-ops"), std::vector<std::string>{"none"});
  o.set_names("fp-abstraction-ops", {});
  EXPECT_TRUE(o.get_names("fp-abstraction-ops").empty());
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_str("sat-backend", "CADICAL"));
}

// A set the engine parses from text is held to that parser: what it accepts,
// the registry accepts, and its refusal is the registry's, in its words.
TEST(Options, sets_follow_the_engine_parser)
{
  Options o;
  // the operations list skips empty items and takes 'all' and 'none' beside others
  o.set("fp-abstraction-ops", "mul,,div");
  EXPECT_EQ(o.get_names("fp-abstraction-ops"), (std::vector<std::string>{"mul", "div"}));
  o.set_names("fp-abstraction-ops", {"all", "mul"});
  o.set("fp-abstraction-chain-ops", "none,mul");
  // the schema groups refuse an empty group and 'all' or 'none' beside another
  const char* groups = "bv-term-abstraction-schema-groups";
  for (const char* bad : {"", ",", "base,,urem", "base,", ",base", "all,base", "base,none", "BASE"})
  {
    SCOPED_TRACE(bad);
    auto e = API_ERROR_OF(o.set(groups, bad));
    ASSERT_TRUE(e.has_value());
    EXPECT_EQ(e->code(), ErrorCode::OPTION_VALUE);
    EXPECT_EQ(e->option(), groups);
  }
  auto empty = API_ERROR_OF(o.set(groups, "base,,urem"));
  ASSERT_TRUE(empty.has_value());
  EXPECT_NE(std::string(empty->what()).find("empty BV schema group; expected base"), std::string::npos)
      << empty->what();
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_names(groups, {"all", "base"}));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_names(groups, {}));
  o.set(groups, " base , urem ");
  EXPECT_EQ(o.get_names(groups), (std::vector<std::string>{"base", "urem"}));
  o.set(groups, "udiv");
  EXPECT_EQ(o.get_names(groups), std::vector<std::string>{"udiv"});
}

// The profile's "no profile" is the empty string: 'none' is not a profile.
TEST(Options, the_profile_is_unset_by_the_empty_string)
{
  Options o;
  EXPECT_EQ(o.get_str("bv-term-abstraction-profile"), "");
  EXPECT_EQ(o.info("bv-term-abstraction-profile").values,
            (std::vector<std::string>{"qualified", "broad", "aggressive"}));
  o.set("bv-term-abstraction-profile", "broad");
  o.set("bv-term-abstraction-profile", "");
  EXPECT_EQ(o.get_str("bv-term-abstraction-profile"), "");
  for (const char* bad : {"none", "NONE", "Qualified"})
    API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("bv-term-abstraction-profile", bad));
}

TEST(Options, aliases_shorts_and_negations_through_set_args)
{
  Options probe;
  for (const std::string& name : probe.names())
  {
    const OptionInfo info = probe.info(name);
    const std::string text = text_of(info, info.default_value);
    // --name=value and --name value
    {
      Options o;
      if (info.type == "bool")
        o.set_args({"--" + name});
      else
        o.set_args({"--" + name + "=" + text});
      EXPECT_TRUE(o.is_set(name)) << name;
      if (info.type == "bool")
        EXPECT_TRUE(o.get_bool(name)) << name;
      else
        EXPECT_TRUE(o.get(name) == info.default_value) << name;
      if (info.type != "bool" && info.type != "mode")
      {
        Options p;
        p.set_args({"--" + name, text});
        EXPECT_TRUE(p.get(name) == info.default_value) << name;
      }
    }
    for (const std::string& alias : info.aliases)
    {
      SCOPED_TRACE(name + " alias " + alias);
      Options o;
      if (info.type == "bool")
      {
        o.set_args({"--" + alias});
        EXPECT_TRUE(o.get_bool(name));
      }
      else
      {
        o.set_args({"--" + alias + "=" + text});
        EXPECT_TRUE(o.get(name) == info.default_value);
      }
      EXPECT_TRUE(o.is_set(name));
      // the alias works with the by-name setters too
      Options p;
      p.set(alias, text);
      EXPECT_TRUE(p.is_set(name));
      EXPECT_EQ(p.info(alias).name, name);
    }
    if (!info.short_flag.empty())
    {
      SCOPED_TRACE(name + " short -" + info.short_flag);
      Options o;
      if (info.type == "bool")
      {
        o.set_args({"-" + info.short_flag});
        EXPECT_TRUE(o.get_bool(name));
      }
      else
      {
        o.set_args({"-" + info.short_flag, text});
        EXPECT_TRUE(o.get(name) == info.default_value);
      }
      EXPECT_TRUE(o.is_set(name));
    }
    if (!info.negation.empty())
    {
      SCOPED_TRACE(name + " negation --" + info.negation);
      Options o;
      o.set_args({"--" + info.negation});
      EXPECT_TRUE(o.is_set(name));
      EXPECT_FALSE(o.get_bool(name));
    }
    if (info.type == "bool")
    {
      // --name=false and --no-name (set_args accepts --no- for every bool)
      Options o;
      o.set_args({"--" + name + "=false"});
      EXPECT_FALSE(o.get_bool(name)) << name;
      Options p;
      p.set_args({"--no-" + name});
      EXPECT_FALSE(p.get_bool(name)) << name;
      EXPECT_TRUE(p.is_set(name));
    }
  }
  // the registry's spellings for the documented cases
  Options o;
  o.set_args({"--stop-after-cnf"});
  EXPECT_TRUE(o.get_bool("stop-after-cnf"));
  o.set_args({"--max_time=2s", "--max_num_confl=5", "-w", "-d"});
  EXPECT_EQ(o.get_duration("max-time").count(), 2000);
  EXPECT_EQ(o.get_int("max-num-confl"), 5);
  EXPECT_TRUE(o.get_bool("switch-word"));
  EXPECT_TRUE(o.get_bool("check-sanity"));
  o.set_args({"-k", "500ms", "-g", "7"});
  EXPECT_EQ(o.get_duration("max-time").count(), 500);
  EXPECT_EQ(o.get_int("max-num-confl"), 7);
  o.set_args({"--no-incremental-promote-units"});
  EXPECT_FALSE(o.get_bool("incremental-promote-units"));
  o.set_args({"--incremental-promote-units"});
  EXPECT_TRUE(o.get_bool("incremental-promote-units"));
  o.set_args({"--simply_to_constants_only", "--difficulty_reversion=false"});
  EXPECT_TRUE(o.get_bool("simplify-to-constants-only"));
  EXPECT_FALSE(o.get_bool("difficulty-reversion"));
  // a bare mode flag means on; a value can follow with = or as the next word
  o.set_args({"--incremental"});
  EXPECT_EQ(o.get_str("incremental"), "on");
  o.set_args({"--incremental=off"});
  EXPECT_EQ(o.get_str("incremental"), "off");
  o.set_args({"--incremental", "auto"});
  EXPECT_EQ(o.get_str("incremental"), "auto");
  o.set_args({"--incremental", "--flattening=false"});
  EXPECT_EQ(o.get_str("incremental"), "on");
  EXPECT_FALSE(o.get_bool("flattening"));
  // the argc/argv form
  const char* argv[] = {"--random-seed=9", "--produce-models=false"};
  o.set_args(2, argv);
  EXPECT_EQ(o.get_uint("random-seed"), 9u);
  EXPECT_FALSE(o.get_bool("produce-models"));
  // the CLI's duration forms need a unit here
  o.set_args({"--max-time=0.5s"});
  EXPECT_EQ(o.get_duration("max-time").count(), 500);
  o.set_args({"--max-time=1m"});
  EXPECT_EQ(o.get_duration("max-time").count(), 60000);
  o.set_args({"--max-time=none"});
  EXPECT_EQ(o.get_duration("max-time").count(), -1);
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_args({"--max-time=2"}));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_args({"--max-time", "2"}));
}

TEST(Options, unknown_names)
{
  Options o;
  auto e = API_ERROR_OF(o.set("no-such-option", "1"));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::OPTION_UNKNOWN);
  EXPECT_EQ(e->option(), "no-such-option");
  EXPECT_TRUE(e->recoverable());
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.set_bool("no-such-option", true));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.get("no-such-option"));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.get_bool("no-such-option"));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.info("no-such-option"));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.resolved("no-such-option"));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.reset("no-such-option"));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.is_set("no-such-option"));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.set_args({"--no-such-option"}));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.set_args({"--no-such-option=1"}));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.set_args({"-Z"}));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.set_args({"file.smt2"}));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.set_args({"--no-max-time"}));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.set_args({"--"}));
  // a bad list changes nothing
  o.set_bool("flattening", false);
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, o.set_args({"--flattening=true", "--nope"}));
  EXPECT_FALSE(o.get_bool("flattening"));
  EXPECT_FALSE(Options::stable_option("no-such-option").has_value());
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, Options::name_of(Option::NUM_STABLE_OPTIONS));
}

TEST(Options, bad_values)
{
  Options o;
  auto e = API_ERROR_OF(o.set_bool("max-time", true));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::OPTION_VALUE);
  EXPECT_EQ(e->option(), "max-time");
  // type mismatches
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("produce-models", 1));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_str("produce-models", "true"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_names("logic", {"QF_BV"}));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_duration("random-seed", std::chrono::seconds(1)));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_uint("sat-backend", 1));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.get_str("produce-models"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.get_duration("random-seed"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.get_names("logic"));
  // ranges
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("cadical-elim", 2));  // max 1
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("cadical-elim", -2)); // min -1
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_uint("uf-sort-width", 0)); // min 1
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_uint("uf-sort-width", 1025)); // max 1024
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_uint("lra-presolve-rounds", 9)); // max 8
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("aig-node-budget", -2));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("aig-node-budget", 1ll << 40));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("max-num-confl", -2));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("random-seed", -1)); // uint
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_uint("cadical-elim", 1ull << 63));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("uf-sort-width", "0"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("uf-sort-width", "-3"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("threads", "x"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("threads", "1.5"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("produce-models", "maybe"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("incremental", "sometimes"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("sat-backend", "z3"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("max-time", "2"));      // a unit is needed
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("max-time", "-2ms"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("max-time", "2days"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("max-time", "ms"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_duration("max-time", std::chrono::milliseconds(-2)));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_args({"--random-seed"})); // needs a value
  // the accepted edges
  o.set_int("cadical-elim", 1);
  o.set_int("cadical-elim", -1);
  o.set_uint("uf-sort-width", 1024);
  o.set_int("aig-node-budget", 2147483647);
  o.set_duration("max-time", std::chrono::milliseconds(-1)); // none
  EXPECT_EQ(o.get_duration("max-time").count(), -1);
  o.set_duration("max-time", std::chrono::milliseconds(0));
  EXPECT_EQ(o.get_duration("max-time").count(), 0);
  o.set("max-time", "2h");
  EXPECT_EQ(o.get_duration("max-time").count(), 7200000);
  o.set("random-seed", "0x10");
  EXPECT_EQ(o.get_uint("random-seed"), 16u);
  o.set("produce-models", "off");
  EXPECT_FALSE(o.get_bool("produce-models"));
  o.set("produce-models", "YES");
  EXPECT_TRUE(o.get_bool("produce-models"));
  o.set_str("sat-backend", "cadical");
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_str("sat-backend", "CADICAL")); // exactly
  EXPECT_EQ(o.get_str("sat-backend"), "cadical");
  // a refused write leaves the entry alone
  o.set_int("cadical-elim", 0);
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("cadical-elim", 5));
  EXPECT_EQ(o.get_int("cadical-elim"), 0);
  // the typed setters by Option
  o.set_bool(Option::PRODUCE_MODELS, false);
  EXPECT_FALSE(o.get_bool("produce-models"));
  o.set_uint(Option::RANDOM_SEED, 4);
  EXPECT_EQ(o.get_uint("random-seed"), 4u);
  o.set_int(Option::MAX_NUM_CONFL, 10);
  EXPECT_EQ(o.get_int("max-num-confl"), 10);
  o.set_str(Option::LOGIC, "QF_BV");
  EXPECT_EQ(o.get_str("logic"), "QF_BV");
  o.set_duration(Option::MAX_TIME, std::chrono::seconds(3));
  EXPECT_EQ(o.get_duration("max-time").count(), 3000);
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_bool(Option::MAX_TIME, true));
  // uint/int readers cross over where the value fits
  EXPECT_EQ(o.get_int("random-seed"), 4);
  EXPECT_EQ(o.get_uint("max-num-confl"), 10u);
}

TEST(Options, timing_windows_on_a_live_solver)
{
  TermManager tm;
  Options o;
  o.set_str("sat-backend", "cadical");
  if (!has_sat_backend("cadical"))
    o.set_str("sat-backend", "auto");
  Solver s(tm, o);
  SolverOptions& live = s.options();
  // construction-only entries are refused on a live solver, even before a check
  auto e = API_ERROR_OF(live.set_str("sat-backend", "cryptominisat"));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::OPTION_TIMING);
  EXPECT_EQ(e->option(), "sat-backend");
  EXPECT_NE(std::string(e->what()).find("construction"), std::string::npos);
  API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, live.set_int("threads", 2));
  API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, live.set_bool("lra-verify-canonical", true));
  API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, live.set_args({"--threads=2"}));
  API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, live.reset("sat-backend"));
  EXPECT_EQ(live.get_str("sat-backend"), o.get_str("sat-backend"));
  // before-first-check entries are open until the first check
  live.set_uint("random-seed", 3);
  live.set_str("logic", "QF_BV");
  live.set_str("incremental", "off");
  EXPECT_EQ(live.get_uint("random-seed"), 3u);
  EXPECT_EQ(live.get_str("logic"), "QF_BV");
  const Term x = tm.declare("x", tm.mk_bv_sort(8));
  s.add(x == 1);
  ASSERT_TRUE(s.check_sat().is_sat());
  e = API_ERROR_OF(live.set_uint("random-seed", 4));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::OPTION_TIMING);
  EXPECT_NE(std::string(e->what()).find("before the first check"), std::string::npos);
  EXPECT_EQ(live.get_uint("random-seed"), 3u); // unchanged
  API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, live.set_str("logic", "QF_ABV"));
  EXPECT_EQ(live.get_str("logic"), "QF_BV");
  API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, live.set("array-equality", "on"));
  API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, live.reset("random-seed"));
  EXPECT_EQ(live.get_uint("random-seed"), 3u);
  // set_args is all or nothing
  API_EXPECT_ERROR(ErrorCode::OPTION_TIMING, live.set_args({"--max-time=1s", "--random-seed=5"}));
  EXPECT_EQ(live.get_duration("max-time").count(), -1);
  EXPECT_EQ(live.get_uint("random-seed"), 3u);
  // anytime entries keep working
  live.set_duration("max-time", std::chrono::seconds(30));
  EXPECT_EQ(live.get_duration("max-time").count(), 30000);
  live.set_bool("produce-models", false);
  live.set_args({"--max-num-confl=100", "--produce-models"});
  EXPECT_EQ(live.get_int("max-num-confl"), 100);
  EXPECT_TRUE(live.get_bool("produce-models"));
  live.reset("max-time");
  EXPECT_FALSE(live.is_set("max-time"));
  EXPECT_TRUE(s.check_sat().is_sat());
  // set_args with the value the entry already holds is not a change
  live.set_args({"--random-seed=3"});
  // a detached copy carries the live values
  const Options snapshot = live.copy();
  EXPECT_EQ(snapshot.get_uint("random-seed"), 3u);
  EXPECT_EQ(snapshot.get_int("max-num-confl"), 100);
  EXPECT_EQ(snapshot.get_str("logic"), "QF_BV");
  EXPECT_EQ(live.info("random-seed").settable, Settable::BEFORE_FIRST_CHECK);
  EXPECT_EQ(live.info("sat-backend").settable, Settable::CONSTRUCTION);
  EXPECT_EQ(live.info("max-time").settable, Settable::ANYTIME);
  EXPECT_EQ(live.names(Tier::STABLE).size(), static_cast<std::size_t>(Option::NUM_STABLE_OPTIONS));
  EXPECT_FALSE(live.help(Tier::STABLE).empty());
  live.resolve();
  EXPECT_TRUE(live.resolved("random-seed") == OptionValue(std::uint64_t(3)));
  API_EXPECT_ERROR(ErrorCode::OPTION_UNKNOWN, live.set("nope", "1"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, live.set_bool("max-time", true));
  // a moved-from solver's options refuse
  Solver moved = std::move(s);
  API_EXPECT_ERROR(ErrorCode::STATE, s.options());
  EXPECT_EQ(moved.options().get_uint("random-seed"), 3u);
}

TEST(Options, conflicts)
{
  Options o;
  o.set_bool("disable-simplifications", true);
  o.resolve(); // alone it is fine
  o.set_bool("switch-word", true);
  auto e = API_ERROR_OF(o.resolve());
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::OPTION_CONFLICT);
  EXPECT_TRUE(e->option() == "disable-simplifications" || e->option() == "switch-word");
  EXPECT_NE(std::string(e->what()).find("cannot be combined"), std::string::npos);
  TermManager tm;
  API_EXPECT_ERROR(ErrorCode::OPTION_CONFLICT, Solver s(tm, o));
  // the pair is symmetric and is checked only when both are set
  Options p;
  p.set_bool("switch-word", true);
  p.set_bool("disable-simplifications", false);
  API_EXPECT_ERROR(ErrorCode::OPTION_CONFLICT, p.resolve());
  p.reset("disable-simplifications");
  p.resolve();
  Options q;
  q.set_str("bv-term-abstraction-profile", "qualified");
  q.set_uint("bv-term-abstraction-rounds", 3);
  API_EXPECT_ERROR(ErrorCode::OPTION_CONFLICT, q.resolve());
  Options r;
  r.set_bool("size-reducing-only", true);
  r.set_bool("difficulty-reversion", false);
  API_EXPECT_ERROR(ErrorCode::OPTION_CONFLICT, r.resolve());
  // a value-level requirement: threads needs the cryptominisat backend
  if (has_sat_backend("cadical"))
  {
    Options t;
    t.set_int("threads", 2);
    t.set_str("sat-backend", "cadical");
    e = API_ERROR_OF(t.resolve());
    ASSERT_TRUE(e.has_value());
    // a build without CryptoMiniSat cannot honour threads at all
    EXPECT_EQ(e->code(), has_sat_backend("cryptominisat") ? ErrorCode::OPTION_CONFLICT
                                                          : ErrorCode::OPTION_UNAVAILABLE);
    EXPECT_EQ(e->option(), "threads");
    t.set_int("threads", 1); // the default never conflicts
    t.resolve();
  }
  if (has_sat_backend("cryptominisat"))
  {
    Options t;
    t.set_int("threads", 2);
    t.set_str("sat-backend", "cryptominisat");
    t.resolve();
    Solver s(tm, t);
    EXPECT_EQ(s.options().get_int("threads"), 2);
  }
  // a solver is usable after a refused construction
  Solver ok(tm);
  EXPECT_TRUE(ok.check_sat().is_sat());
}

TEST(Options, unavailable_in_this_build)
{
  TermManager tm;
  const std::vector<std::string> backends = sat_backends();
  EXPECT_FALSE(backends.empty());
  for (const std::string& b : backends)
    EXPECT_TRUE(has_sat_backend(b));
  EXPECT_FALSE(has_sat_backend("z3"));
  for (const char* b : {"cryptominisat", "cadical", "minisat", "simplifying-minisat"})
  {
    Options o;
    o.set_str("sat-backend", b); // every member is accepted here; one the build lacks is refused by Solver
    if (has_sat_backend(b))
    {
      Solver s(tm, o);
      EXPECT_EQ(s.options().get_str("sat-backend"), b);
      EXPECT_EQ(s.statistics().str("sat.backend"), b);
    }
    else
    {
      auto e = API_ERROR_OF(Solver(tm, o));
      ASSERT_TRUE(e.has_value()) << b;
      EXPECT_EQ(e->code(), ErrorCode::OPTION_UNAVAILABLE);
      EXPECT_EQ(e->option(), "sat-backend");
      EXPECT_NE(std::string(e->what()).find("not part of this build"), std::string::npos);
    }
  }
  // auto picks an available backend
  Solver s(tm);
  EXPECT_TRUE(has_sat_backend(s.statistics().str("sat.backend")));
  // requires.build rows: info().supported and OPTION_UNAVAILABLE when set
  const bool highs = capabilities()["highs"] == "true";
  Options probe;
  EXPECT_EQ(probe.info("lra-highs-mip").supported, highs);
  EXPECT_EQ(probe.info("cadical-elim").supported, has_sat_backend("cadical"));
  EXPECT_TRUE(probe.info("max-time").supported);
  {
    TermManager t2;
    Options o;
    o.set_bool("lra-highs-mip", true);
    if (highs)
      Solver ok(t2, o);
    else
    {
      auto e = API_ERROR_OF(o.resolve());
      ASSERT_TRUE(e.has_value());
      EXPECT_EQ(e->code(), ErrorCode::OPTION_UNAVAILABLE);
      EXPECT_EQ(e->option(), "lra-highs-mip");
      API_EXPECT_ERROR(ErrorCode::OPTION_UNAVAILABLE, Solver bad(t2, o));
    }
  }
  // what needs HiGHS is turning a search on; its tuning numbers are
  // accepted by every build
  for (const char* tuning : {"lra-highs-seconds", "lra-highs-replay-nodes", "lra-highs-cut-limit"})
  {
    SCOPED_TRACE(tuning);
    EXPECT_TRUE(probe.info(tuning).supported);
    TermManager t3;
    Options o;
    o.set_uint(tuning, 7);
    o.resolve();
    Solver ok(t3, o);
  }
  EXPECT_EQ(probe.info("lra-relu-branch").supported, highs);
}

// An entry over a 32-bit engine field takes what the field holds and no more;
// one over a 64-bit field takes all of it.
TEST(Options, ranges_are_the_engine_fields)
{
  Options o;
  o.set_uint("lra-float-reroute", 4294967295ull);
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_uint("lra-float-reroute", 4294967296ull));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("bv-term-abstraction-rounds", "4294967296"));
  EXPECT_EQ(o.get_uint("lra-float-reroute"), 4294967295ull);
  o.set("threads", "-2147483648");
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set("threads", "2147483648"));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_int("threads", -2147483649ll));
  o.set("lra-presolve-monotone-work", "18446744073709551615");
  EXPECT_EQ(o.get_uint("lra-presolve-monotone-work"), UINT64_MAX);
  o.set_uint("lra-presolve-subst-work", UINT64_MAX);
  EXPECT_EQ(o.get_uint("lra-presolve-subst-work"), UINT64_MAX);
}

TEST(Options, manager_scoped_rows)
{
  TermManager tm;
  for (const char* name : {"simplify", "default-rounding-mode", "uf-sort-width"})
  {
    SCOPED_TRACE(name);
    Options o;
    EXPECT_EQ(o.info(name).scope, OptionScope::MANAGER);
    if (std::string(name) == "simplify")
      o.set_bool(name, false);
    else if (std::string(name) == "default-rounding-mode")
      o.set_str(name, "RTZ");
    else
      o.set_uint(name, 8);
    auto e = API_ERROR_OF(Solver(tm, o));
    ASSERT_TRUE(e.has_value());
    EXPECT_EQ(e->code(), ErrorCode::OPTION_VALUE);
    EXPECT_EQ(e->option(), name);
    // a live solver refuses them too and keeps its value
    Solver s(tm);
    const OptionValue before = s.options().get(name);
    API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, s.options().set(name, o.info(name).type == "bool" ? "false" : o.info(name).type == "uint" ? "8" : "RTZ"));
    EXPECT_TRUE(s.options().get(name) == before);
  }
  EXPECT_EQ(Options().info("max-time").scope, OptionScope::SOLVER);
  // TermManager(const Options&) takes exactly those three
  Options mo;
  mo.set_bool("simplify", false);
  mo.set_str("default-rounding-mode", "RTZ");
  mo.set_uint("uf-sort-width", 8);
  TermManager configured(mo);
  EXPECT_FALSE(configured.simplify());
  EXPECT_EQ(configured.default_rounding_mode(), RoundingMode::RTZ);
  EXPECT_EQ(configured.uf_sort_width(), 8u);
  const Term rx = configured.declare("rx", configured.mk_bv_sort(8));
  EXPECT_EQ(bvadd(rx, configured.mk_bv(8, 0)).kind(), Kind::BV_ADD);
  const Term fx = configured.declare("fx", configured.mk_fp32_sort());
  EXPECT_TRUE((fx + fx).child(0).same_as(configured.mk_rm(RoundingMode::RTZ)));
  TermManager defaults{Options()};
  EXPECT_TRUE(defaults.simplify());
  EXPECT_EQ(defaults.default_rounding_mode(), RoundingMode::RNE);
  EXPECT_EQ(defaults.uf_sort_width(), 16u);
  // a solver-scoped entry that is set has no home in a manager
  Options bad;
  bad.set_bool("produce-models", false);
  auto e = API_ERROR_OF(TermManager(bad));
  ASSERT_TRUE(e.has_value());
  EXPECT_EQ(e->code(), ErrorCode::OPTION_VALUE);
  EXPECT_EQ(e->option(), "produce-models");
  for (const char* rm : {"RNE", "RNA", "RTP", "RTN", "RTZ"})
  {
    Options o;
    o.set_str("default-rounding-mode", rm);
    EXPECT_STREQ(to_string(TermManager(o).default_rounding_mode()), rm);
  }
}

TEST(Options, resolution)
{
  Options o;
  // follows: an unset entry takes the value given to the composite switch.
  // The nine per-operation circuits follow bb.fp-native-all; the predicate
  // switch (bb.fp-native-cmp) never did on the command line and does not here.
  EXPECT_TRUE(o.get_bool("bb.fp-native-arith"));
  o.set_bool("bb.fp-native-all", false);
  EXPECT_TRUE(o.get_bool("bb.fp-native-arith"));
  EXPECT_TRUE(o.resolved("bb.fp-native-arith") == OptionValue(false));
  EXPECT_TRUE(o.resolved("bb.fp-native-div") == OptionValue(false));
  EXPECT_TRUE(o.resolved("bb.fp-native-cmp") == OptionValue(true));
  EXPECT_TRUE(o.info("bb.fp-native-arith").current == OptionValue(true));
  EXPECT_TRUE(o.info("bb.fp-native-arith").resolved == OptionValue(false));
  o.set_bool("bb.fp-native-arith", true); // set explicitly: no longer follows
  EXPECT_TRUE(o.resolved("bb.fp-native-arith") == OptionValue(true));
  EXPECT_TRUE(o.resolved("bv-term-abstraction-divmod") == OptionValue(true));
  o.set_bool("bv-term-abstraction-mult", false);
  EXPECT_TRUE(o.resolved("bv-term-abstraction-divmod") == OptionValue(false));
  // implied_by: a value an unset entry takes when the other option is true
  EXPECT_EQ(o.get_uint("fp-abstraction-restart-width"), 0u);
  EXPECT_TRUE(o.resolved("fp-abstraction-restart-width") == OptionValue(std::uint64_t(0)));
  o.set_bool("bv-term-abstraction", true);
  EXPECT_TRUE(o.resolved("fp-abstraction-restart-width") == OptionValue(std::uint64_t(128)));
  EXPECT_EQ(o.get_uint("fp-abstraction-restart-width"), 0u);
  o.set_uint("fp-abstraction-restart-width", 32);
  EXPECT_TRUE(o.resolved("fp-abstraction-restart-width") == OptionValue(std::uint64_t(32)));
  // implies: a composite switch writes its dependents into the resolved view
  Options p;
  EXPECT_TRUE(p.resolved("switch-word") == OptionValue(false));
  EXPECT_TRUE(p.resolved("flattening") == OptionValue(true));
  p.set_bool("disable-simplifications", true);
  EXPECT_TRUE(p.resolved("switch-word") == OptionValue(true));
  EXPECT_TRUE(p.resolved("flattening") == OptionValue(false));
  EXPECT_TRUE(p.resolved("disable-opt-inc") == OptionValue(true));
  EXPECT_FALSE(p.get_bool("switch-word"));
  p.resolve();
  // an unset entry resolves to its default
  EXPECT_TRUE(Options().resolved("max-time") == OptionValue(std::int64_t(-1)));
  EXPECT_TRUE(Options().resolved("incremental") == OptionValue(std::string("auto")));
  // resolution runs at construction and the solver carries the resolved view
  TermManager tm;
  Solver s(tm, o);
  EXPECT_TRUE(s.options().resolved("fp-abstraction-restart-width") == OptionValue(std::uint64_t(32)));
  EXPECT_TRUE(s.options().resolved("bb.fp-native-div") == OptionValue(false));
}

TEST(Options, info_names_help_and_the_stable_tier)
{
  Options o;
  const OptionInfo mt = o.info("max-time");
  EXPECT_EQ(mt.name, "max-time");
  EXPECT_EQ(mt.python_key, "max_time");
  EXPECT_EQ(mt.type, "duration");
  EXPECT_TRUE(mt.default_value == OptionValue(std::int64_t(-1)));
  EXPECT_TRUE(mt.current == mt.default_value);
  EXPECT_EQ(mt.tier, Tier::STABLE);
  EXPECT_EQ(mt.settable, Settable::ANYTIME);
  EXPECT_EQ(mt.scope, OptionScope::SOLVER);
  EXPECT_EQ(mt.aliases, std::vector<std::string>{"max_time"});
  EXPECT_EQ(mt.short_flag, "k");
  EXPECT_TRUE(mt.negation.empty());
  EXPECT_TRUE(mt.supported);
  EXPECT_FALSE(mt.is_set);
  EXPECT_FALSE(mt.min.has_value());
  EXPECT_TRUE(mt.values.empty());
  const OptionInfo sb = o.info("sat-backend");
  EXPECT_EQ(sb.type, "enum");
  EXPECT_EQ(sb.values, (std::vector<std::string>{"auto", "cryptominisat", "cadical", "minisat", "simplifying-minisat"}));
  EXPECT_EQ(sb.settable, Settable::CONSTRUCTION);
  const OptionInfo ce = o.info("cadical-elim");
  EXPECT_EQ(ce.min, std::optional<std::int64_t>(-1));
  EXPECT_EQ(ce.max, std::optional<std::int64_t>(1));
  EXPECT_EQ(ce.tier, Tier::EXPERT);
  EXPECT_EQ(o.info("incremental-promote-units").negation, "no-incremental-promote-units");
  EXPECT_EQ(o.info("bb.div-v3").python_key, "bb_div_v3");
  EXPECT_EQ(o.info("print-counterex").tier, Tier::DIAGNOSTIC);
  EXPECT_EQ(o.info("print-counterex").short_flag, "p");
  EXPECT_EQ(o.info("merge-same").tier, Tier::EXPERIMENTAL);
  EXPECT_EQ(o.info("incremental").type, "mode");
  EXPECT_EQ(o.info("fp-abstraction-ops").type, "set");
  EXPECT_EQ(o.info("logic").type, "string");
  EXPECT_EQ(o.info("uf-sort-width").scope, OptionScope::MANAGER);
  o.set_duration("max-time", std::chrono::seconds(1));
  EXPECT_TRUE(o.info("max-time").is_set);
  EXPECT_TRUE(o.info("max-time").current == OptionValue(std::int64_t(1000)));
  EXPECT_TRUE(o.info("max-time").default_value == OptionValue(std::int64_t(-1)));

  // names by tier partition the registry; the stable tier is the enum
  const std::vector<std::string> all = o.names();
  std::size_t total = 0;
  for (Tier t : {Tier::STABLE, Tier::EXPERT, Tier::EXPERIMENTAL, Tier::DIAGNOSTIC})
  {
    const std::vector<std::string> tier = o.names(t);
    total += tier.size();
    for (const std::string& n : tier)
      EXPECT_EQ(o.info(n).tier, t) << n;
  }
  EXPECT_EQ(total, all.size());
  const std::vector<std::string> stable = o.names(Tier::STABLE);
  ASSERT_EQ(stable.size(), static_cast<std::size_t>(Option::NUM_STABLE_OPTIONS));
  for (std::size_t i = 0; i < stable.size(); ++i)
  {
    EXPECT_EQ(Options::name_of(static_cast<Option>(i)), stable[i]);
    EXPECT_EQ(Options::stable_option(stable[i]), std::optional<Option>(static_cast<Option>(i)));
  }
  EXPECT_EQ(Options::name_of(Option::MAX_TIME), "max-time");
  EXPECT_EQ(Options::name_of(Option::SAT_BACKEND), "sat-backend");
  EXPECT_EQ(Options::stable_option("flattening"), std::nullopt);
  EXPECT_EQ(Options::stable_option("max_time"), std::optional<Option>(Option::MAX_TIME));

  // help
  const std::string help = o.help();
  EXPECT_NE(help.find("--max-time"), std::string::npos);
  EXPECT_NE(help.find("-k"), std::string::npos);
  EXPECT_NE(help.find("[model]"), std::string::npos);
  EXPECT_NE(help.find("--print-counterex"), std::string::npos);
  const std::string diag = o.help(Tier::DIAGNOSTIC);
  EXPECT_NE(diag.find("--print-counterex"), std::string::npos);
  EXPECT_EQ(diag.find("--max-time"), std::string::npos);
  EXPECT_LT(o.help(Tier::STABLE).size(), help.size());
  EXPECT_STREQ(to_string(Tier::EXPERIMENTAL), "experimental");
  EXPECT_STREQ(to_string(Settable::BEFORE_FIRST_CHECK), "before-first-check");
}

TEST(Options, value_semantics)
{
  Options a;
  a.set_bool("flattening", false);
  a.set_names("fp-abstraction-ops", {"mul"});
  Options b = a;
  EXPECT_FALSE(b.get_bool("flattening"));
  EXPECT_EQ(b.get_names("fp-abstraction-ops"), std::vector<std::string>{"mul"});
  b.set_bool("flattening", true);
  EXPECT_FALSE(a.get_bool("flattening")); // independent
  Options c;
  c = a;
  EXPECT_FALSE(c.get_bool("flattening"));
  Options d = std::move(c);
  EXPECT_FALSE(d.get_bool("flattening"));
  d.reset_all();
  EXPECT_TRUE(d.get_bool("flattening"));
  EXPECT_FALSE(d.is_set("flattening"));
  EXPECT_FALSE(d.is_set("fp-abstraction-ops"));
  EXPECT_EQ(d.get_names("fp-abstraction-ops"), (std::vector<std::string>{"mul", "div", "sqrt", "fma"}));
  // the variant getter
  EXPECT_TRUE(a.get("flattening") == OptionValue(false));
  EXPECT_TRUE(a.get("max-time") == OptionValue(std::int64_t(-1)));
  EXPECT_TRUE(a.get("random-seed") == OptionValue(std::uint64_t(0)));
  EXPECT_TRUE(a.get("incremental") == OptionValue(std::string("auto")));
  EXPECT_TRUE(a.get("fp-abstraction-ops") == OptionValue(std::vector<std::string>{"mul"}));
  // a solver copies the options it is given
  TermManager tm;
  Solver s(tm, a);
  a.set_bool("flattening", true);
  EXPECT_FALSE(s.options().get_bool("flattening"));
  EXPECT_EQ(s.options().get_names("fp-abstraction-ops"), std::vector<std::string>{"mul"});
  s.options().set_bool("flattening", true);
  EXPECT_TRUE(s.options().get_bool("flattening"));
  const Options& ro = s.options().copy();
  EXPECT_TRUE(ro.get_bool("flattening"));
}

} // namespace

TEST(Options, none_is_minus_one_millisecond)
{
  Options o;
  EXPECT_EQ(o.get_duration("max-time"), std::chrono::milliseconds(-1));
  o.set_duration("max-time", std::chrono::milliseconds(2000));
  EXPECT_EQ(o.get_duration("max-time"), std::chrono::milliseconds(2000));
  o.set_duration("max-time", std::chrono::milliseconds(-1));
  EXPECT_TRUE(o.is_set("max-time"));
  EXPECT_EQ(o.get_duration("max-time"), std::chrono::milliseconds(-1));
  API_EXPECT_ERROR(ErrorCode::OPTION_VALUE, o.set_duration("max-time", std::chrono::milliseconds(-2)));
  EXPECT_EQ(o.get_duration("max-time"), std::chrono::milliseconds(-1));
}

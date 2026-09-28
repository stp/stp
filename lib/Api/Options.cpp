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

// Options.cpp -- the option registry (generated from options.toml), the
// Options value, the live SolverOptions view, and the table that carries a
// validated value into the engine's UserDefinedFlags.

#include "Internal.h"

#include "stp/UninterpretedFunctions/UFContext.h"

#include "stp/FloatBlaster/FpAbstraction.h"
#include "stp/Sat/SearchBias.h"
#include "stp/config.h"

#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <sstream>
#include <unordered_map>

namespace stp
{
namespace api
{
namespace detail
{

#include "gen/option_table.inc"
#include "gen/cli_table.inc"
#include "gen/option_defaults.inc"

const OptionSpec* option_specs(std::size_t& count)
{
  count = kNumOptionSpecs;
  return kOptionSpecs;
}
const char* const* cli_groups(std::size_t& count)
{
  count = kNumCliGroups;
  return kCliGroups;
}
const CliCategory* cli_categories(std::size_t& count)
{
  count = kNumCliCategories;
  return kCliCategories;
}
const CliAlias* cli_aliases(std::size_t& count)
{
  count = kNumCliAliases;
  return kCliAliases;
}
const CliFrontend* cli_frontend(std::size_t& count)
{
  count = kNumCliFrontend;
  return kCliFrontend;
}
const DefaultCheck* option_default_checks(std::size_t& count)
{
  count = kNumDefaultChecks;
  return kDefaultChecks;
}
const FieldRange* option_field_ranges(std::size_t& count)
{
  count = kNumFieldRanges;
  return kFieldRanges;
}

namespace
{
const std::unordered_map<std::string, std::size_t>& name_index()
{
  static const std::unordered_map<std::string, std::size_t> index = [] {
    std::unordered_map<std::string, std::size_t> out;
    for (std::size_t i = 0; i < kNumOptionSpecs; ++i)
    {
      out.emplace(kOptionSpecs[i].name, i);
      out.emplace(kOptionSpecs[i].python_key, i);
      for (std::size_t a = 0; a < kOptionSpecs[i].num_aliases; ++a)
        out.emplace(kOptionSpecs[i].aliases[a], i);
    }
    return out;
  }();
  return index;
}

const char* type_name(OptType t)
{
  switch (t)
  {
    case OptType::BOOL: return "bool";
    case OptType::INT: return "int";
    case OptType::UINT: return "uint";
    case OptType::MODE: return "mode";
    case OptType::ENUM: return "enum";
    case OptType::SET: return "set";
    case OptType::STRING: return "string";
    case OptType::PATH: return "path";
    case OptType::DURATION: return "duration";
  }
  return "?";
}

std::string lower(std::string_view s)
{
  std::string out(s);
  for (char& c : out)
    c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
  return out;
}

bool in_values(const OptionSpec& spec, const std::string& v)
{
  for (std::size_t i = 0; i < spec.num_values; ++i)
    if (v == spec.values[i])
      return true;
  return false;
}

std::string values_text(const OptionSpec& spec)
{
  std::string out;
  for (std::size_t i = 0; i < spec.num_values; ++i)
    out += (i ? ", " : "") + std::string(spec.values[i]);
  return out;
}

// An enum whose default is the empty string ("no choice made") also takes it.
bool enum_accepts(const OptionSpec& spec, const std::string& v)
{
  return in_values(spec, v) || (v.empty() && *spec.default_text == '\0');
}

// The set entries the engine parses from text: a set is accepted exactly when
// the engine's own parser accepts its comma list, so that the registry never
// holds a list the applier then refuses, and a refusal is worded by the
// parser that knows the syntax (an empty member, 'all' beside another).
bool engine_parses_set(const OptionSpec& spec, const std::string& text, std::string& error)
{
  const std::string engine = spec.engine != nullptr ? spec.engine : "";
  if (engine == "bv_term_abstraction_schema_groups")
  {
    std::uint32_t mask = 0;
    return parseBVSchemaGroups(text, mask, error);
  }
  if (engine == "fp_abstraction_ops" || engine == "fp_abstraction_chain_ops")
  {
    unsigned mask = 0;
    if (parseFpAbstractionOps(text, mask))
      return true;
    error = "invalid value '" + text + "'; expected a comma list of " + values_text(spec);
    return false;
  }
  return true;
}

std::string joined(const std::vector<std::string>& members)
{
  std::string out;
  for (std::size_t i = 0; i < members.size(); ++i)
    out += (i ? "," : "") + members[i];
  return out;
}
} // namespace

const OptionSpec* find_option(std::string_view name)
{
  const auto& index = name_index();
  auto it = index.find(std::string(name));
  if (it == index.end())
    return nullptr;
  return &kOptionSpecs[it->second];
}

std::size_t option_index(const OptionSpec* spec)
{
  return static_cast<std::size_t>(spec - kOptionSpecs);
}

OptionValue option_default(const OptionSpec& spec)
{
  return parse_option_text(spec, spec.default_text);
}

OptionValue parse_option_text(const OptionSpec& spec, std::string_view raw)
{
  const std::string text(raw);
  const std::string low = lower(text);
  switch (spec.type)
  {
    case OptType::BOOL:
      if (low == "true" || low == "1" || low == "on" || low == "yes")
        return true;
      if (low == "false" || low == "0" || low == "off" || low == "no")
        return false;
      fail_option(ErrorCode::OPTION_VALUE, spec.name,
                  "invalid value '" + text + "'; expected true or false");
    case OptType::INT:
    case OptType::UINT:
    {
      char* end = nullptr;
      errno = 0;
      if (spec.type == OptType::UINT && !text.empty() && text[0] != '-')
      {
        const unsigned long long v = std::strtoull(text.c_str(), &end, 0);
        if (end == text.c_str() || *end != '\0' || errno != 0)
          fail_option(ErrorCode::OPTION_VALUE, spec.name,
                      "invalid value '" + text + "'; expected a non-negative integer");
        OptionValue out = static_cast<std::uint64_t>(v);
        validate_option_value(spec, out);
        return out;
      }
      const long long v = std::strtoll(text.c_str(), &end, 0);
      if (end == text.c_str() || *end != '\0' || errno != 0)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    "invalid value '" + text + "'; expected an integer");
      OptionValue out = static_cast<std::int64_t>(v);
      validate_option_value(spec, out);
      return out;
    }
    case OptType::MODE:
      // A row that lists its spellings takes those alone, exactly as given.
      if (spec.num_values > 0)
      {
        if (!in_values(spec, text))
          fail_option(ErrorCode::OPTION_VALUE, spec.name,
                      "invalid value '" + text + "'; expected one of " + values_text(spec));
        return text;
      }
      if (low == "auto")
        return std::string("auto");
      if (low == "on" || low == "1" || low == "true")
        return std::string("on");
      if (low == "off" || low == "0" || low == "false")
        return std::string("off");
      fail_option(ErrorCode::OPTION_VALUE, spec.name,
                  "invalid value '" + text + "'; expected auto, on or off");
    case OptType::ENUM:
      // matched exactly, case included, as the engine's own spellings are
      if (!enum_accepts(spec, text))
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    "invalid value '" + text + "'; expected one of " + values_text(spec));
      return text;
    case OptType::SET:
    {
      std::string error;
      if (!engine_parses_set(spec, text, error))
        fail_option(ErrorCode::OPTION_VALUE, spec.name, error);
      std::vector<std::string> members;
      std::stringstream ss(text);
      std::string item;
      while (std::getline(ss, item, ','))
      {
        item.erase(0, item.find_first_not_of(" \t"));
        item.erase(item.find_last_not_of(" \t") + 1);
        if (item.empty())
          continue;
        if (!in_values(spec, item))
          fail_option(ErrorCode::OPTION_VALUE, spec.name,
                      "invalid member '" + item + "'; expected a comma list of " +
                          values_text(spec));
        members.push_back(item);
      }
      OptionValue out = members;
      validate_option_value(spec, out);
      return out;
    }
    case OptType::STRING:
    case OptType::PATH:
      return text;
    case OptType::DURATION:
    {
      if (low == "none" || low == "-1")
        return std::int64_t(-1);
      // number with a unit: ms, s, m, h; fractional allowed
      std::size_t i = 0;
      while (i < low.size() && (std::isdigit(static_cast<unsigned char>(low[i])) || low[i] == '.'))
        ++i;
      const std::string number = low.substr(0, i);
      const std::string unit = low.substr(i);
      if (number.empty() || unit.empty())
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    "invalid duration '" + text + "'; expected a number with a unit (500ms, 2s, 1m)");
      double scale;
      if (unit == "ms")
        scale = 1;
      else if (unit == "s")
        scale = 1000;
      else if (unit == "m" || unit == "min")
        scale = 60000;
      else if (unit == "h")
        scale = 3600000;
      else
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    "invalid duration unit in '" + text + "'; expected ms, s, m or h");
      double ms = 0;
      try
      {
        ms = std::stod(number) * scale;
      }
      catch (const std::exception&) // "." alone, say
      {
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    "invalid duration '" + text + "'; expected a number with a unit (500ms, 2s, 1m)");
      }
      // a budget past what milliseconds can count is no limit in all but name
      if (!(ms + 0.5 < 9223372036854775807.0))
        return std::int64_t(INT64_MAX);
      return static_cast<std::int64_t>(ms + 0.5);
    }
  }
  fail_option(ErrorCode::OPTION_VALUE, spec.name, "unknown option type");
}

std::string option_text(const OptionSpec& spec, const OptionValue& v)
{
  switch (v.index())
  {
    case 0: return std::get<bool>(v) ? "true" : "false";
    case 1:
    {
      const std::int64_t i = std::get<std::int64_t>(v);
      if (spec.type == OptType::DURATION)
        return i < 0 ? "none" : std::to_string(i) + "ms";
      return std::to_string(i);
    }
    case 2: return std::to_string(std::get<std::uint64_t>(v));
    case 3: return std::get<std::string>(v);
    case 4:
    {
      std::string out;
      for (const std::string& s : std::get<std::vector<std::string>>(v))
        out += (out.empty() ? "" : ",") + s;
      return out;
    }
  }
  return "";
}

void validate_option_value(const OptionSpec& spec, const OptionValue& v)
{
  switch (spec.type)
  {
    case OptType::INT:
    case OptType::UINT:
    {
      std::int64_t i;
      if (v.index() == 1)
        i = std::get<std::int64_t>(v);
      else if (v.index() == 2)
      {
        const std::uint64_t u = std::get<std::uint64_t>(v);
        if (u > static_cast<std::uint64_t>(INT64_MAX))
        {
          // Past every int64 bound: only an unsigned entry with no maximum
          // (a 64-bit engine field) takes it.
          if (spec.type != OptType::UINT)
            fail_option(ErrorCode::OPTION_VALUE, spec.name, "the value is too large");
          if (spec.has_max)
            fail_option(ErrorCode::OPTION_VALUE, spec.name,
                        "value " + std::to_string(u) + " is above the maximum " +
                            std::to_string(spec.max));
          return;
        }
        i = static_cast<std::int64_t>(u);
      }
      else
        fail_option(ErrorCode::OPTION_VALUE, spec.name, "expected an integer");
      if (spec.type == OptType::UINT && i < 0 && !(spec.has_min && spec.min < 0))
        fail_option(ErrorCode::OPTION_VALUE, spec.name, "expected a non-negative integer");
      if (spec.has_min && i < spec.min)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    "value " + std::to_string(i) + " is below the minimum " +
                        std::to_string(spec.min));
      if (spec.has_max && i > spec.max)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    "value " + std::to_string(i) + " is above the maximum " +
                        std::to_string(spec.max));
      return;
    }
    case OptType::ENUM:
    case OptType::MODE:
      if (v.index() != 3)
        fail_option(ErrorCode::OPTION_VALUE, spec.name, "expected a name");
      if (spec.type == OptType::ENUM && !enum_accepts(spec, std::get<std::string>(v)))
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    "invalid value '" + std::get<std::string>(v) + "'; expected one of " +
                        values_text(spec));
      if (spec.type == OptType::MODE)
      {
        const std::string& s = std::get<std::string>(v);
        if (s != "auto" && s != "on" && s != "off")
          fail_option(ErrorCode::OPTION_VALUE, spec.name, "expected auto, on or off");
        if (spec.num_values > 0 && !in_values(spec, s))
          fail_option(ErrorCode::OPTION_VALUE, spec.name,
                      "invalid value '" + s + "'; expected one of " + values_text(spec));
      }
      return;
    case OptType::SET:
    {
      if (v.index() != 4)
        fail_option(ErrorCode::OPTION_VALUE, spec.name, "expected a list of names");
      const auto& members = std::get<std::vector<std::string>>(v);
      for (const std::string& s : members)
        if (!in_values(spec, s))
          fail_option(ErrorCode::OPTION_VALUE, spec.name,
                      "invalid member '" + s + "'; expected " + values_text(spec));
      // what else a list may not say ('all' beside another group, say) is the
      // engine parser's to decide
      std::string error;
      if (!engine_parses_set(spec, joined(members), error))
        fail_option(ErrorCode::OPTION_VALUE, spec.name, error);
      return;
    }
    case OptType::BOOL:
      if (v.index() != 0)
        fail_option(ErrorCode::OPTION_VALUE, spec.name, "expected true or false");
      return;
    case OptType::STRING:
    case OptType::PATH:
      if (v.index() != 3)
        fail_option(ErrorCode::OPTION_VALUE, spec.name, "expected a string");
      return;
    case OptType::DURATION:
      if (v.index() != 1)
        fail_option(ErrorCode::OPTION_VALUE, spec.name, "expected a duration in milliseconds");
      if (std::get<std::int64_t>(v) < -1)
        fail_option(ErrorCode::OPTION_VALUE, spec.name, "a duration cannot be negative");
      return;
  }
}

bool option_build_supported(const OptionSpec& spec)
{
  if (spec.requires_build == nullptr)
    return true;
  const std::string b = spec.requires_build;
  if (b == "cadical")
    return STP_BUILD_WITH_CADICAL != 0;
  if (b == "cryptominisat")
    return STP_BUILD_WITH_CRYPTOMINISAT != 0;
  if (b == "minisat")
    return STP_BUILD_WITH_MINISAT != 0;
  if (b == "highs")
  {
#ifdef STP_HAVE_HIGHS
    return true;
#else
    return false;
#endif
  }
  if (b == "highs-cut-log")
  {
#ifdef STP_HAVE_HIGHS_CUT_LOG
    return true;
#else
    return false;
#endif
  }
  return true; // prose requirements (sat-backend) are checked by their applier
}

// ------------------------------------------------------------ OptionsImpl

OptionsImpl::OptionsImpl()
{
  values.reserve(kNumOptionSpecs);
  for (std::size_t i = 0; i < kNumOptionSpecs; ++i)
    values.push_back(option_default(kOptionSpecs[i]));
  is_set.assign(kNumOptionSpecs, false);
}

namespace
{
const OptionSpec& spec_of(std::string_view name)
{
  const OptionSpec* s = find_option(name);
  if (s == nullptr)
    fail_option(ErrorCode::OPTION_UNKNOWN, std::string(name), "unknown option");
  return *s;
}
} // namespace

void OptionsImpl::set(const char* /*fn*/, std::string_view name, const OptionValue& v, OptType via)
{
  const OptionSpec& spec = spec_of(name);
  OptionValue value = v;
  // the typed setter must match the entry's type
  switch (via)
  {
    case OptType::BOOL:
      if (spec.type != OptType::BOOL)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    std::string("set_bool on a ") + type_name(spec.type) + " option");
      break;
    case OptType::INT:
    case OptType::UINT:
      if (spec.type != OptType::INT && spec.type != OptType::UINT)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    std::string("set_int/set_uint on a ") + type_name(spec.type) + " option");
      if (value.index() == 2 && spec.type == OptType::INT)
      {
        const std::uint64_t u = std::get<std::uint64_t>(value);
        if (u > static_cast<std::uint64_t>(INT64_MAX))
          fail_option(ErrorCode::OPTION_VALUE, spec.name, "the value is too large");
        value = static_cast<std::int64_t>(u);
      }
      if (value.index() == 1 && spec.type == OptType::UINT)
      {
        const std::int64_t i = std::get<std::int64_t>(value);
        if (i < 0 && !(spec.has_min && spec.min < 0))
          fail_option(ErrorCode::OPTION_VALUE, spec.name, "expected a non-negative integer");
        value = static_cast<std::uint64_t>(i < 0 ? 0 : i);
        if (i < 0)
          value = static_cast<std::int64_t>(i);
      }
      break;
    case OptType::STRING:
      if (spec.type != OptType::STRING && spec.type != OptType::PATH && spec.type != OptType::ENUM &&
          spec.type != OptType::MODE)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    std::string("set_str on a ") + type_name(spec.type) + " option");
      if (spec.type == OptType::MODE || spec.type == OptType::ENUM)
        value = parse_option_text(spec, std::get<std::string>(value));
      break;
    case OptType::SET:
      if (spec.type != OptType::SET)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    std::string("set_names on a ") + type_name(spec.type) + " option");
      break;
    case OptType::DURATION:
      if (spec.type != OptType::DURATION)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    std::string("set_duration on a ") + type_name(spec.type) + " option");
      break;
    default:
      break;
  }
  // canonical storage: int options as int64, uint as uint64
  if (spec.type == OptType::UINT && value.index() == 1)
  {
    const std::int64_t i = std::get<std::int64_t>(value);
    if (i >= 0)
      value = static_cast<std::uint64_t>(i);
  }
  if (spec.type == OptType::INT && value.index() == 2)
    value = static_cast<std::int64_t>(std::get<std::uint64_t>(value));
  validate_option_value(spec, value);
  const std::size_t index = option_index(&spec);
  values[index] = value;
  is_set[index] = true;
}

void OptionsImpl::set_text(const char* fn, std::string_view name, std::string_view text)
{
  const OptionSpec& spec = spec_of(name);
  OptionValue v = parse_option_text(spec, text);
  set(fn, spec.name, v, spec.type == OptType::PATH ? OptType::STRING : spec.type);
}

void OptionsImpl::set_args(const char* fn, const std::vector<std::string>& argv)
{
  for (std::size_t i = 0; i < argv.size(); ++i)
  {
    const std::string& arg = argv[i];
    std::string name, value;
    bool has_value = false;
    if (arg.size() > 2 && arg[0] == '-' && arg[1] == '-')
    {
      const std::size_t eq = arg.find('=');
      name = arg.substr(2, eq == std::string::npos ? std::string::npos : eq - 2);
      if (eq != std::string::npos)
      {
        value = arg.substr(eq + 1);
        has_value = true;
      }
    }
    else if (arg.size() == 2 && arg[0] == '-')
    {
      const char c = arg[1];
      const OptionSpec* found = nullptr;
      for (std::size_t j = 0; j < kNumOptionSpecs; ++j)
        if (kOptionSpecs[j].short_flag != nullptr && kOptionSpecs[j].short_flag[0] == c)
          found = &kOptionSpecs[j];
      if (found == nullptr)
        fail_option(ErrorCode::OPTION_UNKNOWN, arg, "unknown short option");
      name = found->name;
    }
    else
      fail_option(ErrorCode::OPTION_UNKNOWN, arg, "expected an option (--name[=value] or -x)");
    // --no-<name> negation
    const OptionSpec* spec = find_option(name);
    bool negated = false;
    if (spec == nullptr && name.rfind("no-", 0) == 0)
    {
      spec = find_option(name.substr(3));
      negated = spec != nullptr && spec->type == OptType::BOOL;
      if (!negated)
        spec = nullptr;
    }
    if (spec == nullptr)
      fail_option(ErrorCode::OPTION_UNKNOWN, name, "unknown option");
    if (negated)
    {
      set(fn, spec->name, false, OptType::BOOL);
      continue;
    }
    if (!has_value)
    {
      if (spec->type == OptType::BOOL)
      {
        set(fn, spec->name, true, OptType::BOOL);
        continue;
      }
      if (spec->type == OptType::MODE)
      {
        // a bare mode flag means on, as the CLI reads --incremental
        if (i + 1 < argv.size() && argv[i + 1].rfind("-", 0) != 0)
        {
          value = argv[++i];
          has_value = true;
        }
        else
        {
          set(fn, spec->name, std::string("on"), OptType::STRING);
          continue;
        }
      }
      else
      {
        if (i + 1 >= argv.size())
          fail_option(ErrorCode::OPTION_VALUE, spec->name, "the option needs a value");
        value = argv[++i];
        has_value = true;
      }
    }
    set_text(fn, spec->name, value);
  }
}

const OptionValue& OptionsImpl::get(const char* /*fn*/, std::string_view name, OptType expect) const
{
  const OptionSpec& spec = spec_of(name);
  const OptionValue& v = values[option_index(&spec)];
  switch (expect)
  {
    case OptType::BOOL:
      if (spec.type != OptType::BOOL)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    std::string("get_bool on a ") + type_name(spec.type) + " option");
      break;
    case OptType::INT:
    case OptType::UINT:
      if (spec.type != OptType::INT && spec.type != OptType::UINT && spec.type != OptType::DURATION)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    std::string("get_int/get_uint on a ") + type_name(spec.type) + " option");
      break;
    case OptType::STRING:
      if (spec.type != OptType::STRING && spec.type != OptType::PATH && spec.type != OptType::ENUM &&
          spec.type != OptType::MODE)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    std::string("get_str on a ") + type_name(spec.type) + " option");
      break;
    case OptType::SET:
      if (spec.type != OptType::SET)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    std::string("get_names on a ") + type_name(spec.type) + " option");
      break;
    case OptType::DURATION:
      if (spec.type != OptType::DURATION)
        fail_option(ErrorCode::OPTION_VALUE, spec.name,
                    std::string("get_duration on a ") + type_name(spec.type) + " option");
      break;
    default:
      break;
  }
  return v;
}

OptionValue OptionsImpl::resolved(std::size_t index) const
{
  const OptionSpec& spec = kOptionSpecs[index];
  if (is_set[index])
    return values[index];
  if (spec.follows != nullptr)
  {
    const OptionSpec* other = find_option(spec.follows);
    if (other != nullptr && is_set[option_index(other)])
      return values[option_index(other)];
  }
  if (spec.implied_by_option != nullptr)
  {
    const OptionSpec* other = find_option(spec.implied_by_option);
    if (other != nullptr)
    {
      const OptionValue ov = resolved(option_index(other));
      if (ov.index() == 0 && std::get<bool>(ov))
        return parse_option_text(spec, spec.implied_by_value);
    }
  }
  // composite switches: an entry named in another set entry's `implies`
  for (std::size_t j = 0; j < kNumOptionSpecs; ++j)
  {
    if (!is_set[j] || kOptionSpecs[j].num_implies == 0)
      continue;
    const OptionValue& jv = values[j];
    if (jv.index() != 0 || !std::get<bool>(jv))
      continue;
    for (std::size_t p = 0; p < kOptionSpecs[j].num_implies; ++p)
      if (std::strcmp(kOptionSpecs[j].implies[2 * p], spec.name) == 0)
        return parse_option_text(spec, kOptionSpecs[j].implies[2 * p + 1]);
  }
  return values[index];
}

void OptionsImpl::resolve(const char* /*fn*/) const
{
  for (std::size_t i = 0; i < kNumOptionSpecs; ++i)
  {
    if (!is_set[i])
      continue;
    const OptionSpec& spec = kOptionSpecs[i];
    for (std::size_t e = 0; e < spec.num_excludes; ++e)
    {
      const OptionSpec* other = find_option(spec.excludes[e]);
      if (other != nullptr && is_set[option_index(other)])
        fail_option(ErrorCode::OPTION_CONFLICT, spec.name,
                    std::string("cannot be combined with '") + other->name + "'");
    }
    // An entry this build cannot honour is refused when it is set to anything
    // but its default: naming the default asks for nothing the build lacks.
    if (!option_build_supported(spec) && option_text(spec, values[i]) != spec.default_text)
      fail_option(ErrorCode::OPTION_UNAVAILABLE, spec.name,
                  std::string("needs a build with ") + spec.requires_build);
    if (spec.requires_option != nullptr && spec.requires_value != nullptr)
    {
      const OptionSpec* other = find_option(spec.requires_option);
      if (other != nullptr)
      {
        const OptionValue ov = resolved(option_index(other));
        std::string have = option_text(*other, ov);
        if (other->type == OptType::ENUM && have == "auto" &&
            std::string(other->name) == "sat-backend")
        {
#if STP_BUILD_WITH_CRYPTOMINISAT
          have = "cryptominisat";
#elif STP_BUILD_WITH_CADICAL
          have = "cadical";
#else
          have = "minisat";
#endif
        }
        // the default value never conflicts
        if (option_text(spec, values[i]) != spec.default_text && have != spec.requires_value)
          fail_option(ErrorCode::OPTION_CONFLICT, spec.name,
                      std::string("requires ") + spec.requires_option + " = " +
                          spec.requires_value + " (it is " + have + ")");
      }
    }
  }
}

OptionInfo OptionsImpl::info(std::string_view name) const
{
  const OptionSpec& spec = spec_of(name);
  const std::size_t index = option_index(&spec);
  OptionInfo o;
  o.name = spec.name;
  o.python_key = spec.python_key;
  o.type = type_name(spec.type);
  o.default_value = option_default(spec);
  o.current = values[index];
  o.resolved = resolved(index);
  if (spec.has_min)
    o.min = spec.min;
  if (spec.has_max)
    o.max = spec.max;
  for (std::size_t i = 0; i < spec.num_values; ++i)
    o.values.emplace_back(spec.values[i]);
  o.tier = spec.tier;
  o.settable = spec.settable;
  o.scope = spec.scope;
  o.category = spec.category;
  o.help = spec.help;
  o.supported = option_build_supported(spec);
  o.is_set = is_set[index];
  for (std::size_t i = 0; i < spec.num_aliases; ++i)
    o.aliases.emplace_back(spec.aliases[i]);
  o.short_flag = spec.short_flag ? spec.short_flag : "";
  o.negation = spec.negation ? spec.negation : "";
  return o;
}

std::vector<std::string> OptionsImpl::names(std::optional<Tier> tier) const
{
  std::vector<std::string> out;
  for (std::size_t i = 0; i < kNumOptionSpecs; ++i)
    if (!tier.has_value() || kOptionSpecs[i].tier == *tier)
      out.emplace_back(kOptionSpecs[i].name);
  return out;
}

std::string OptionsImpl::help(std::optional<Tier> tier) const
{
  std::ostringstream os;
  std::string category;
  for (std::size_t i = 0; i < kNumOptionSpecs; ++i)
  {
    const OptionSpec& s = kOptionSpecs[i];
    if (tier.has_value() && s.tier != *tier)
      continue;
    if (category != s.category)
    {
      category = s.category;
      os << "\n[" << category << "]\n";
    }
    os << "  --" << s.name;
    if (s.short_flag)
      os << ", -" << s.short_flag;
    os << " (" << type_name(s.type) << ", default " << s.default_text;
    if (s.num_values)
      os << ", one of " << values_text(s);
    os << ", " << to_string(s.tier) << ", " << to_string(s.settable) << ")\n      " << s.help
       << "\n";
  }
  return os.str();
}

void OptionsImpl::reset(std::string_view name)
{
  const OptionSpec& spec = spec_of(name);
  const std::size_t index = option_index(&spec);
  values[index] = option_default(spec);
  is_set[index] = false;
}

void OptionsImpl::reset_all()
{
  for (std::size_t i = 0; i < kNumOptionSpecs; ++i)
  {
    values[i] = option_default(kOptionSpecs[i]);
    is_set[i] = false;
  }
}

// ------------------------------------------------------------ the engine appliers

namespace
{
bool as_bool(const OptionValue& v)
{
  return v.index() == 0 ? std::get<bool>(v) : false;
}
std::int64_t as_int(const OptionValue& v)
{
  if (v.index() == 1)
    return std::get<std::int64_t>(v);
  if (v.index() == 2)
    return static_cast<std::int64_t>(std::get<std::uint64_t>(v));
  return 0;
}
const std::string& as_str(const OptionValue& v)
{
  static const std::string empty;
  return v.index() == 3 ? std::get<std::string>(v) : empty;
}
std::string as_list(const OptionValue& v)
{
  if (v.index() != 4)
    return "";
  std::string out;
  for (const std::string& s : std::get<std::vector<std::string>>(v))
    out += (out.empty() ? "" : ",") + s;
  return out;
}
template <class T> T as_mode(const OptionValue& v)
{
  const std::string& s = as_str(v);
  if (s == "on")
    return T::ON;
  if (s == "off")
    return T::OFF;
  return T::AUTO;
}
template <class F, class V> void assign_flag(F& field, V value)
{
  field = static_cast<F>(value);
}

using Flags = UserDefinedFlags;

bool custom_produce_models(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.request_counterexample = as_bool(v);
  if (t.solver != nullptr)
    t.solver->produce_models = as_bool(v);
  return true;
}
bool custom_sat_backend(EngineTarget& t, const OptionSpec& spec, const OptionValue& v)
{
  const std::string& s = as_str(v);
  if (s == "auto")
  {
#if STP_BUILD_WITH_CRYPTOMINISAT
    t.flags.solver_to_use = Flags::CRYPTOMINISAT5_SOLVER;
#elif STP_BUILD_WITH_CADICAL
    t.flags.solver_to_use = Flags::CADICAL_SOLVER;
#else
    t.flags.solver_to_use = Flags::MINISAT_SOLVER;
#endif
    return true;
  }
  const bool have_cms = STP_BUILD_WITH_CRYPTOMINISAT != 0;
  const bool have_cadical = STP_BUILD_WITH_CADICAL != 0;
  const bool have_minisat = STP_BUILD_WITH_MINISAT != 0;
  if (s == "cryptominisat" && have_cms)
    t.flags.solver_to_use = Flags::CRYPTOMINISAT5_SOLVER;
  else if (s == "cadical" && have_cadical)
    t.flags.solver_to_use = Flags::CADICAL_SOLVER;
  else if (s == "minisat" && have_minisat)
    t.flags.solver_to_use = Flags::MINISAT_SOLVER;
  else if (s == "simplifying-minisat" && have_minisat)
    t.flags.solver_to_use = Flags::SIMPLIFYING_MINISAT_SOLVER;
  else
    fail_option(ErrorCode::OPTION_UNAVAILABLE, spec.name,
                "the '" + s + "' backend is not part of this build (available: " +
                    [&] {
                      std::string out;
                      if (have_cms)
                        out += "cryptominisat ";
                      if (have_cadical)
                        out += "cadical ";
                      if (have_minisat)
                        out += "minisat simplifying-minisat";
                      return out;
                    }() +
                    ")");
  return true;
}
bool custom_random_seed(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.random_seed = static_cast<std::uint64_t>(as_int(v));
  return true;
}
bool custom_model_array_fill(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  if (t.solver != nullptr)
    t.solver->fill_ones = as_str(v) == "ones";
  return true;
}
bool custom_logic(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  // set-logic's side effects, visible through Options::resolved:
  // the UF logics switch the UF machinery on, QF_AX and the AUF logics the
  // extensional arrays.
  const std::string& logic = as_str(v);
  if (t.solver != nullptr)
    t.solver->logic = logic;
  if (logic.rfind("QF_UF", 0) == 0 || logic.rfind("QF_AUF", 0) == 0)
    t.flags.enable_uninterpreted_functions = true;
  if (logic == "QF_AX" || logic.rfind("QF_AUF", 0) == 0)
    t.flags.enable_array_equality = true;
  return true;
}
// The manager-scoped entries belong to TermManager's constructor when a
// manager exists; applied to a bare STPMgr (EngineTarget::mgr null),
// `simplify` is the frontend's to honour and the sort width is the engine
// flag.
bool custom_manager_simplify(EngineTarget& t, const OptionSpec& spec, const OptionValue&)
{
  if (t.mgr == nullptr)
    return true;
  fail_option(ErrorCode::OPTION_VALUE, spec.name,
              "manager-scoped: pass it to TermManager's constructor, not to a solver");
}
bool custom_manager_default_rounding_mode(EngineTarget& t, const OptionSpec& spec, const OptionValue&)
{
  if (t.mgr == nullptr)
    return true;
  fail_option(ErrorCode::OPTION_VALUE, spec.name,
              "manager-scoped: pass it to TermManager's constructor or set_default_rounding_mode");
}
bool custom_manager_uf_sort_width(EngineTarget& t, const OptionSpec& spec, const OptionValue& v)
{
  if (t.mgr == nullptr)
  {
    t.flags.uf_sort_width = static_cast<unsigned>(as_int(v));
    return true;
  }
  fail_option(ErrorCode::OPTION_VALUE, spec.name,
              "manager-scoped: pass it to TermManager's constructor, not to a solver");
}
// Three switches for which the engine also needs to know that the caller named
// them (the *_explicit flags it consults). A default re-applied by
// apply_all_options is not a request (EngineTarget::explicit_value).
bool custom_bv_term_abstraction_rounds(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.bv_term_abstraction_rounds = static_cast<unsigned>(as_int(v));
  t.flags.bv_term_abstraction_rounds_explicit = t.explicit_value;
  return true;
}
bool custom_bv_term_abstraction_divmod(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.bv_term_abstraction_divmod = as_bool(v);
  t.flags.bv_term_abstraction_divmod_explicit = t.explicit_value;
  return true;
}
bool custom_lra_decision_polarity(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.lra_decision_polarity = as_bool(v);
  t.flags.lra_decision_polarity_explicit = t.explicit_value;
  return true;
}
bool custom_lra_verify_canonical(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.lra_verify_canonical = as_bool(v);
  // The number layer's switch is process-wide and on unless told otherwise:
  // only an explicit setting moves it, and it has to be set before the
  // first exact value is built (hence settable at construction only).
  if (t.explicit_value && t.mgr != nullptr)
    t.mgr->bm->SetLraCanonicalVerification(t.flags.lra_verify_canonical);
  return true;
}
bool custom_incremental_mode(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.incremental_mode = as_mode<Flags::IncrementalMode>(v);
  if (t.solver != nullptr && t.solver->stp != nullptr &&
      t.flags.incremental_mode == Flags::IncrementalMode::ON)
  {
    t.solver->stp->incrementalFromStart = true;
    t.solver->stp->sessionIncremental = true;
  }
  return true;
}
bool custom_max_time(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.timeout_max_time_ms = as_int(v);
  return true;
}
bool custom_threads(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.num_solver_threads = static_cast<int>(as_int(v));
  return true;
}
bool custom_disable_simplifications(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  if (as_bool(v))
    t.flags.disableSimplifications();
  return true;
}
bool custom_switch_word(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.wordlevel_solve_flag = !as_bool(v);
  return true;
}
bool custom_disable_opt_inc(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.optimize_flag = !as_bool(v);
  return true;
}
bool custom_disable_cbitp(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.bitConstantProp_flag = !as_bool(v);
  return true;
}
bool custom_disable_equality(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.propagate_equalities = !as_bool(v);
  return true;
}
bool custom_size_reducing_only(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  if (as_bool(v))
    t.flags.disableSizeIncreasingSimplifications();
  return true;
}
bool custom_cadical_options_elim(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  const std::int64_t i = as_int(v);
  if (i < 0)
    t.flags.cadical_options.elim.reset();
  else
    t.flags.cadical_options.elim = static_cast<int>(i);
  return true;
}
bool custom_cadical_options_elimmineff(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  const std::int64_t i = as_int(v);
  if (i < 0)
    t.flags.cadical_options.elimmineff.reset();
  else
    t.flags.cadical_options.elimmineff = static_cast<int>(i);
  return true;
}
bool custom_cadical_options_elimmaxeff(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  const std::int64_t i = as_int(v);
  if (i < 0)
    t.flags.cadical_options.elimmaxeff.reset();
  else
    t.flags.cadical_options.elimmaxeff = static_cast<int>(i);
  return true;
}
bool custom_cadical_factor(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.cadical_factor = as_mode<Flags::BVAMode>(v);
  t.flags.cadical_factor_explicit = t.explicit_value;
  return true;
}
bool custom_incremental_inprobing(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.incremental_inprobing = as_mode<Flags::BVAMode>(v);
  return true;
}
bool custom_search_bias(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  const std::string& s = as_str(v);
  t.flags.search_bias = s == "sat" ? SearchBias::SAT : s == "unsat" ? SearchBias::UNSAT : SearchBias::NONE;
  return true;
}
bool custom_enable_array_equality(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  const std::string& s = as_str(v);
  if (t.mgr != nullptr)
    t.mgr->array_equality_off = s == "off";
  if (s == "on")
    t.flags.enable_array_equality = true;
  else if (s == "off")
    t.flags.enable_array_equality = false;
  else if (t.mgr != nullptr) // auto: engaged by the content, whatever an earlier off left behind
    t.flags.enable_array_equality = t.mgr->array_equality_seen;
  // auto without a manager (the stp binary): the frontend's set-logic decides
  return true;
}
bool custom_array_index_hints(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  const std::string& s = as_str(v);
  t.flags.array_index_hints = s == "phase"    ? Flags::ArrayIndexHints::PHASE
                              : s == "decide" ? Flags::ArrayIndexHints::DECIDE
                                              : Flags::ArrayIndexHints::OFF;
  return true;
}
bool custom_bv_term_abstraction_schema_groups(EngineTarget& t, const OptionSpec& spec,
                                              const OptionValue& v)
{
  std::string error;
  std::uint32_t mask = 0;
  if (!parseBVSchemaGroups(as_list(v), mask, error))
    fail_option(ErrorCode::OPTION_VALUE, spec.name, error);
  t.flags.bv_term_abstraction_schema_groups = mask;
  t.flags.bv_term_abstraction_schema_groups_explicit = t.explicit_value;
  return true;
}
bool custom_bv_term_abstraction_profile(EngineTarget& t, const OptionSpec& spec,
                                        const OptionValue& v)
{
  const std::string& s = as_str(v);
  if (s.empty()) // no profile: the schema-groups and rounds entries apply
    return true;
  std::string error;
  std::uint32_t mask = t.flags.bv_term_abstraction_schema_groups;
  unsigned rounds = t.flags.bv_term_abstraction_rounds;
  if (!parseBVTermAbstractionProfile(s, mask, rounds, error))
    fail_option(ErrorCode::OPTION_VALUE, spec.name, error);
  if (!t.flags.bv_term_abstraction_schema_groups_explicit)
    t.flags.bv_term_abstraction_schema_groups = mask;
  if (!t.flags.bv_term_abstraction_rounds_explicit)
    t.flags.bv_term_abstraction_rounds = rounds;
  return true;
}
bool custom_enable_uninterpreted_functions(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  const std::string& s = as_str(v);
  if (s == "on")
    t.flags.enable_uninterpreted_functions = true;
  else if (s == "off")
    t.flags.enable_uninterpreted_functions = false;
  else if (t.mgr != nullptr) // auto: engaged by a declaration, whatever an earlier off left behind
  {
    const UFContext* ctx = t.mgr->bm->getUFContextIfAny();
    t.flags.enable_uninterpreted_functions = ctx != nullptr && !ctx->activeDeclarations().empty();
  }
  // auto without a manager (the stp binary): the frontend's set-logic decides
  return true;
}
bool custom_uf_ackermann(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.uf_eager_mode = as_mode<Flags::UFEagerMode>(v);
  return true;
}
bool custom_uf_bv_term_abstraction(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.uf_bv_term_abstraction = as_mode<Flags::UFAbstractionMode>(v);
  return true;
}
bool custom_fp_abstraction_ops(EngineTarget& t, const OptionSpec& spec, const OptionValue& v)
{
  unsigned mask = 0;
  if (!parseFpAbstractionOps(as_list(v), mask))
    fail_option(ErrorCode::OPTION_VALUE, spec.name, "unknown operation in '" + as_list(v) + "'");
  t.flags.fp_abstraction_ops = mask;
  return true;
}
bool custom_fp_abstraction_chain_ops(EngineTarget& t, const OptionSpec& spec, const OptionValue& v)
{
  unsigned mask = 0;
  const std::string list = as_list(v);
  if (!list.empty() && !parseFpAbstractionOps(list, mask))
    fail_option(ErrorCode::OPTION_VALUE, spec.name, "unknown operation in '" + list + "'");
  t.flags.fp_abstraction_chain_ops = mask;
  return true;
}
bool custom_fp_abstraction_constant_operands(EngineTarget& t, const OptionSpec&, const OptionValue& v)
{
  t.flags.fp_abstraction_constant_operands = as_mode<Flags::FpConstantOperandMode>(v);
  return true;
}
bool custom_cnf_generation_effort(EngineTarget& t, const OptionSpec& spec, const OptionValue& v)
{
  static const std::pair<const char*, Flags::CNFEffort> table[] = {
      {"very-low", Flags::CNF_EFFORT_VERY_LOW},
      {"low", Flags::CNF_EFFORT_LOW},
      {"medium", Flags::CNF_EFFORT_MEDIUM},
      {"high", Flags::CNF_EFFORT_HIGH},
      {"very-high", Flags::CNF_EFFORT_VERY_HIGH},
      {"auto", Flags::CNF_EFFORT_AUTO},
      {"new-very-low", Flags::CNF_EFFORT_NEW_VERY_LOW},
      {"new-low", Flags::CNF_EFFORT_NEW_LOW},
      {"new-medium", Flags::CNF_EFFORT_NEW_MEDIUM},
      {"new-high", Flags::CNF_EFFORT_NEW_HIGH},
      {"gia-low", Flags::CNF_EFFORT_GIA_LOW},
      {"gia-high", Flags::CNF_EFFORT_GIA_HIGH},
      {"gia-very-high", Flags::CNF_EFFORT_GIA_VERY_HIGH},
  };
  const std::string& s = as_str(v);
  for (const auto& e : table)
    if (s == e.first)
    {
      t.flags.cnf_effort = e.second;
      return true;
    }
  fail_option(ErrorCode::OPTION_VALUE, spec.name, "unknown effort '" + s + "'");
}
} // namespace

bool apply_option_to_engine(EngineTarget& t, std::size_t index, const OptionSpec& spec,
                            const OptionValue& v)
{
#include "gen/option_apply.inc"
}

void apply_all_options(EngineTarget& t, const OptionsImpl& o, bool force_all)
{
  // What the engine holds for the solver, entry by entry: an unset entry at
  // its default is skipped unless the solver's last application left the
  // engine elsewhere (it followed another entry, or was set and reset).
  std::vector<bool>* off_default = t.solver != nullptr ? &t.solver->engine_off_default : nullptr;
  if (off_default != nullptr && off_default->size() != kNumOptionSpecs)
    off_default->assign(kNumOptionSpecs, false);
  for (std::size_t i = 0; i < kNumOptionSpecs; ++i)
  {
    const OptionSpec& spec = kOptionSpecs[i];
    if (spec.scope == OptionScope::MANAGER)
    {
      if (o.is_set[i])
        apply_option_to_engine(t, i, spec, o.values[i]); // refuses
      continue;
    }
    const OptionValue r = o.resolved(i);
    const bool at_default = !o.is_set[i] && option_text(spec, r) == spec.default_text;
    if (!force_all && at_default && !(off_default != nullptr && (*off_default)[i]))
      continue;
    // a default that the build cannot honour (a backend it lacks) stays unapplied
    if (force_all && !o.is_set[i] && !option_build_supported(spec))
      continue;
    t.explicit_value = o.is_set[i];
    apply_option_to_engine(t, i, spec, r);
    if (off_default != nullptr)
      (*off_default)[i] = !at_default;
  }
  t.explicit_value = true;
}

std::vector<std::string> unmapped_options()
{
  std::vector<std::string> out;
  for (std::size_t i = 0; i < kNumOptionSpecs; ++i)
    if (!kOptionSpecs[i].has_engine)
      out.emplace_back(kOptionSpecs[i].name);
  return out;
}

} // namespace detail

// ============================================================ Options

Options::Options() : impl_(new detail::OptionsImpl()) {}
Options::Options(const Options& o) : impl_(new detail::OptionsImpl(*o.impl_)) {}
Options::Options(Options&& o) noexcept : impl_(o.impl_)
{
  o.impl_ = nullptr;
}
Options& Options::operator=(const Options& o)
{
  if (this != &o)
    *impl_ = *o.impl_;
  return *this;
}
Options& Options::operator=(Options&& o) noexcept
{
  if (this != &o)
  {
    delete impl_;
    impl_ = o.impl_;
    o.impl_ = nullptr;
  }
  return *this;
}
Options::~Options()
{
  delete impl_;
}

void Options::set(std::string_view name, std::string_view value) { impl_->set_text("Options::set", name, value); }
void Options::set_bool(std::string_view name, bool v) { impl_->set("Options::set_bool", name, v, detail::OptType::BOOL); }
void Options::set_int(std::string_view name, std::int64_t v) { impl_->set("Options::set_int", name, v, detail::OptType::INT); }
void Options::set_uint(std::string_view name, std::uint64_t v) { impl_->set("Options::set_uint", name, v, detail::OptType::UINT); }
void Options::set_str(std::string_view name, std::string_view v) { impl_->set("Options::set_str", name, std::string(v), detail::OptType::STRING); }
void Options::set_names(std::string_view name, const std::vector<std::string>& v) { impl_->set("Options::set_names", name, v, detail::OptType::SET); }
void Options::set_duration(std::string_view name, std::chrono::milliseconds v) { impl_->set("Options::set_duration", name, static_cast<std::int64_t>(v.count()), detail::OptType::DURATION); }
void Options::set_bool(Option o, bool v) { set_bool(name_of(o), v); }
void Options::set_int(Option o, std::int64_t v) { set_int(name_of(o), v); }
void Options::set_uint(Option o, std::uint64_t v) { set_uint(name_of(o), v); }
void Options::set_str(Option o, std::string_view v) { set_str(name_of(o), v); }
void Options::set_duration(Option o, std::chrono::milliseconds v) { set_duration(name_of(o), v); }
void Options::set_args(const std::vector<std::string>& argv)
{
  // parsed into a copy first, so that a bad list changes nothing
  detail::OptionsImpl copy = *impl_;
  copy.set_args("Options::set_args", argv);
  *impl_ = std::move(copy);
}
void Options::set_args(int argc, const char* const* argv)
{
  std::vector<std::string> v;
  for (int i = 0; i < argc; ++i)
    v.emplace_back(argv[i]);
  set_args(v);
}

OptionValue Options::get(std::string_view name) const { return impl_->get("Options::get", name, detail::OptType::PATH); }
bool Options::get_bool(std::string_view name) const { return std::get<bool>(impl_->get("Options::get_bool", name, detail::OptType::BOOL)); }
std::int64_t Options::get_int(std::string_view name) const
{
  const OptionValue& v = impl_->get("Options::get_int", name, detail::OptType::INT);
  return v.index() == 2 ? static_cast<std::int64_t>(std::get<std::uint64_t>(v)) : std::get<std::int64_t>(v);
}
std::uint64_t Options::get_uint(std::string_view name) const
{
  const OptionValue& v = impl_->get("Options::get_uint", name, detail::OptType::UINT);
  return v.index() == 1 ? static_cast<std::uint64_t>(std::get<std::int64_t>(v)) : std::get<std::uint64_t>(v);
}
std::string Options::get_str(std::string_view name) const { return std::get<std::string>(impl_->get("Options::get_str", name, detail::OptType::STRING)); }
std::vector<std::string> Options::get_names(std::string_view name) const { return std::get<std::vector<std::string>>(impl_->get("Options::get_names", name, detail::OptType::SET)); }
std::chrono::milliseconds Options::get_duration(std::string_view name) const { return std::chrono::milliseconds(std::get<std::int64_t>(impl_->get("Options::get_duration", name, detail::OptType::DURATION))); }
OptionValue Options::resolved(std::string_view name) const
{
  const detail::OptionSpec* s = detail::find_option(name);
  if (s == nullptr)
    detail::fail_option(ErrorCode::OPTION_UNKNOWN, std::string(name), "unknown option");
  return impl_->resolved(detail::option_index(s));
}
bool Options::is_set(std::string_view name) const { return impl_->info(name).is_set; }
void Options::reset(std::string_view name) { impl_->reset(name); }
void Options::reset_all() { impl_->reset_all(); }
OptionInfo Options::info(std::string_view name) const { return impl_->info(name); }
std::vector<std::string> Options::names(std::optional<Tier> tier) const { return impl_->names(tier); }
std::string Options::help(std::optional<Tier> tier) const { return impl_->help(tier); }
void Options::resolve() const { impl_->resolve("Options::resolve"); }

std::string Options::name_of(Option o)
{
  std::size_t n = 0;
  const detail::OptionSpec* specs = detail::option_specs(n);
  std::size_t stable = 0;
  for (std::size_t i = 0; i < n; ++i)
    if (specs[i].tier == Tier::STABLE)
    {
      if (stable == static_cast<std::size_t>(o))
        return specs[i].name;
      ++stable;
    }
  detail::fail_option(ErrorCode::OPTION_UNKNOWN, std::to_string(static_cast<int>(o)),
                      "not a stable option");
}

std::optional<Option> Options::stable_option(std::string_view name)
{
  const detail::OptionSpec* s = detail::find_option(name);
  if (s == nullptr || s->tier != Tier::STABLE)
    return std::nullopt;
  std::size_t n = 0;
  const detail::OptionSpec* specs = detail::option_specs(n);
  std::size_t stable = 0;
  for (std::size_t i = 0; i < n; ++i)
  {
    if (specs + i == s)
      return static_cast<Option>(stable);
    if (specs[i].tier == Tier::STABLE)
      ++stable;
  }
  return std::nullopt;
}

} // namespace api
} // namespace stp

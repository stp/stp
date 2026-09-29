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

// Registry.h -- the option registry's tables: one row per [[option]] entry of
// lib/Api/tables/options.toml, and the rows that make up the stp command line
// ([[cli_group]], [[category]], [[alias]] and [[frontend]]).
//
// The stp binary registers its command line from these rows and hands every
// value to stp::Options, so it reads this header and <stp/stp.hpp> and nothing
// of the engine's. Everything here is plain data over the public enums.

#ifndef STP_API_REGISTRY_H
#define STP_API_REGISTRY_H

#include "stp/stp.hpp"

#include <cstddef>
#include <cstdint>
#include <string_view>

namespace stp
{
namespace api
{
namespace detail
{

enum class OptType : std::uint8_t
{
  BOOL,
  INT,
  UINT,
  MODE,
  ENUM,
  SET,
  STRING,
  PATH,
  DURATION
};

struct OptionSpec
{
  const char* name;
  const char* python_key;
  OptType type;
  const char* default_text;
  bool has_min;
  std::int64_t min;
  bool has_max;
  std::int64_t max;
  const char* const* values;
  std::size_t num_values;
  Tier tier;
  Settable settable;
  OptionScope scope;
  const char* category;
  const char* help;
  const char* const* aliases;
  std::size_t num_aliases;
  const char* short_flag;
  const char* negation;
  const char* follows;
  const char* implied_by_option;
  const char* implied_by_value;
  const char* const* excludes;
  std::size_t num_excludes;
  const char* const* implies; // name, value pairs
  std::size_t num_implies;
  const char* implies_note;
  const char* requires_build;
  const char* requires_option;
  const char* requires_value;
  const char* latched_by;
  const char* sentinel;
  const char* engine;
  bool has_engine;
  const char* cli_form;      // "value" | "flag" | "none": how tools/stp registers the entry
  const char* cli_bad_value; // tools/stp's line for a refused value ({name} {value} {member} {expected}), or nullptr
  bool has_cli_range;        // a value window the command line checks itself, narrower than the range
  std::int64_t cli_min;
  std::int64_t cli_max;
  const char* cli_below_min; // tools/stp's line for a number below `min` ({name}), or nullptr
  const char* cli_above_max; // ... above `max`
  bool cli_take_last;        // a repeated spelling takes its last value (bool and lenient mode entries always do)
  bool cli_empty_unset;      // an empty value on the command line leaves the entry unset
  const char* cli_help;      // what --help says, where `help` speaks of the API; nullptr: `help`
  const char* cli_default;   // the value tools/stp gives an entry it is not given, where not `default`
  int stable_id;             // the pinned Option / stp_option value of a stable entry; -1 for the rest
};

STP_API_EXPORT const OptionSpec* option_specs(std::size_t& count);
// The row of a stable id (an Option / stp_option value), or nullptr.
STP_API_EXPORT const OptionSpec* stable_option_spec(std::size_t id);

// The command-line data of tools/stp that is not a per-entry column
// (lib/Api/gen/cli_table.inc, from the [[cli_group]], [[category]], [[alias]]
// and [[frontend]] sections of options.toml).
struct CliCategory
{
  const char* category; // an OptionSpec::category value
  const char* group;    // the --help group its entries join
};
struct CliAlias
{
  const char* name;  // the bare flag, without the leading --
  const char* of;    // the entry it sets
  const char* value; // to this value
  const char* help;
};
struct CliFrontend
{
  const char* key;       // what tools/stp binds the registration to
  const char* spellings; // CLI11's name list ("--SMTLIB1,-m")
  const char* kind;      // positional | help | flag | bool-option
  const char* group;     // nullptr for the positional
  const char* help;
  const char* api;       // the API call with the same effect
  const char* const* excludes; // spellings, nullptr-terminated
  std::size_t num_excludes;
};
STP_API_EXPORT const char* const* cli_groups(std::size_t& count); // in --help order
STP_API_EXPORT const CliCategory* cli_categories(std::size_t& count);
STP_API_EXPORT const CliAlias* cli_aliases(std::size_t& count);
STP_API_EXPORT const CliFrontend* cli_frontend(std::size_t& count);

// What the engine field of each numeric field-mapped entry can hold.
struct FieldRange
{
  const char* name;
  std::int64_t min;
  std::uint64_t max;
};
STP_API_EXPORT const FieldRange* option_field_ranges(std::size_t& count);

STP_API_EXPORT const OptionSpec* find_option(std::string_view name); // name or alias; nullptr if unknown
STP_API_EXPORT std::size_t option_index(const OptionSpec* spec);
// Whether this build can honour the entry's `requires.build` (a backend, HiGHS).
STP_API_EXPORT bool option_build_supported(const OptionSpec& spec);

} // namespace detail
} // namespace api
} // namespace stp

#endif

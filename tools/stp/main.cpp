/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Andrew Teylu
 *
 * BEGIN DATE: November, 2005
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

// The stp binary: a client of the 3.x API (<stp/stp.hpp>) and of the option
// registry's tables (lib/Api/Registry.h), and of nothing else of the library.
// This file is its command line; run.cpp reads and runs the input.

#include "run.h"

// The 3.x option registry's rows: the entries of lib/Api/tables/options.toml
// and the command line's own rows. The command line below is registered from
// them and every value goes to stp::Options, so the binary and the API
// accept the same options with the same meanings.
#include "Api/Registry.h"

#include <stp/stp.hpp>

#include <CLI/CLI.hpp>

#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <iterator>
#include <map>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>
#include <vector>

using std::cout;
using std::cerr;
using std::endl;

namespace api = stp::api;
namespace reg = stp::api::detail;

// The command line is the option registry plus the frontend rows.
//
// Every [[option]] entry of options.toml with a CLI form is registered with
// CLI11 from its row (name, aliases, short flag, negation, type, default,
// help, group), its value is handed to stp::Options as text, the options are
// resolved (excludes, requires, build) and the solver is made from them,
// which applies them to the engine through the appliers every library caller
// goes through. The [[alias]] rows are the bare backend flags (--cadical and
// friends) that set sat-backend to a value. The [[frontend]] rows are the
// CLI-only registrations, bound here by their key to the Invocation that
// run.cpp carries out.
//
// Hand-written and CLI-only, listed so that nothing else hides here:
//   - the frontend rows' actions: the positional input file, --help,
//     --version, the parser selection (--CVC, --SMTLIB1, --SMTLIB2, else the
//     file's extension), the print-back flags, --print-output, --output-CNF,
//     --exit-after-CNF (the solver's end-after-cnf), --parse-only and
//     --interactive;
//   - the reading of --max-time as a whole number of seconds (2.x
//     compatibility; the registry's duration type wants a unit);
//   - the wording of a refused value, kept to what the binary always said
//     ("--max-time must be -1 (no limit) or greater", "--search-bias must be
//     one of ..."), built from the row's range and values, or spelled out by
//     the row's cli_bad_value, cli_below_min or cli_above_max line where the
//     old wording was its own, and the order in which the refusals of a
//     command line with several mistakes are reported (kCheckedFirst ...);
//   - CLI11's own checks where the binary always had them: a 32-bit slot for
//     an entry over a 32-bit engine field (its range says so), the unsigned
//     entries with a range, the rows whose cli_range is narrower than the
//     API's (the CaDiCaL knobs, whose -1 means unset to the library), a
//     lenient mode's values, and a repeated option (refused unless the row
//     takes its last value);
//   - the exclusions of the backend flags among themselves and against the
//     entries that require a particular backend (from the rows' `of` and
//     `requires`), and CLI11's own exclusions for the frontend rows;
//   - the split-value diagnostic for --incremental (a flag whose value must be
//     attached with '=');
//   - the defaults the binary keeps where the library's differ: no model is
//     built unless asked for (produce-models) and exact rationals are not
//     re-derived (lra-verify-canonical), both set explicitly unless given;
//   - where the refusals the solver makes from the applied options (the
//     CaDiCaL knobs, --lra-decision-polarity) and the HiGHS-only searches are
//     reported;
//   - the LRA option combinations the coordinator would refuse only once a
//     Real query reached it (the extension controls with a Real session;
//     --lra-extension-restart-sat without CaDiCaL, with an explicit
//     --cadical-factor=on or with --array-index-hints=decide), refused by
//     value;
//   - the manager-scoped entries (simplify, uf-sort-width), which go to the
//     TermManager: an input printed back is read without folding, as it
//     always was.
class CommandLine
{
public:
  void create_options();
  int parse_options(int argc, char** argv);

  CLI::App app;

  // One slot per registry row. CLI11 keeps references to the storage, so
  // the vector is sized once, before the first registration. An entry that
  // reaches a 32-bit engine field is read into a 32-bit slot, so that CLI11
  // refuses what does not fit as it always did ("Could not convert").
  struct Entry
  {
    const reg::OptionSpec* spec = nullptr;
    CLI::Option* option = nullptr;
    bool b = false;
    std::int64_t i = 0;
    std::uint64_t u = 0;
    std::int32_t i32 = 0;
    std::uint32_t u32 = 0;
    std::string s;
  };
  std::vector<Entry> entries;

  // The backend flags of the [[alias]] rows.
  struct AliasFlag
  {
    const reg::CliAlias* alias = nullptr;
    CLI::Option* option = nullptr;
    bool given = false;
  };
  std::vector<AliasFlag> alias_flags;

  stp::Options options;

  // What the frontend rows set, carried out by run.cpp.
  stp_cli::Invocation invocation;
  // The frontend rows that are the command line's own.
  bool version = false;
  bool use_cvc = false;
  bool use_smtlib1 = false;
  bool use_smtlib2 = false;
  // Tri-state: --interactive is only honoured when it was given, so the
  // value needs its own presence check.
  bool interactive = false;
  CLI::Option* interactive_option = nullptr;

  // The manager and the solver the options made, for run.cpp.
  std::optional<stp::TermManager> manager;
  std::unique_ptr<stp::Solver> solver;

  std::string group_of(const reg::OptionSpec& spec) const;
  bool* frontend_target(const std::string& key);
  void register_frontend(const reg::CliFrontend& row);
  void register_entry(std::size_t index, const std::string& group);
  void register_alias(std::size_t k, const std::string& group);
  void register_exclusions();
  std::string entry_text(const Entry& e, std::string& refusal);
  std::string bad_value_line(const reg::OptionSpec& spec, const std::string& given,
                             const api::Error& error) const;
  [[noreturn]] void refuse(const std::string& line) const;
  const Entry* entry_named(const char* name) const;
  bool given(const char* name) const;
  void make_solver();
  void select_parser_by_extension();
};

// ---------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------

namespace
{
const char* kCliOnlyGroup = ""; // an empty group hides an option from --help

std::string quoted_list(const std::vector<std::string>& values)
{
  // 'a', 'b' or 'c'
  std::string out;
  for (std::size_t i = 0; i < values.size(); ++i)
  {
    if (i > 0)
      out += (i + 1 == values.size()) ? " or " : ", ";
    out += "'" + values[i] + "'";
  }
  return out;
}

bool backend_available(const std::string& value)
{
  if (value == "cadical" || value == "cryptominisat" || value == "minisat" ||
      value == "simplifying-minisat")
    return stp::has_sat_backend(value);
  return true;
}

// An entry whose range is exactly a 32-bit engine field's is read into a
// 32-bit slot: CLI11 then refuses a value the field cannot hold.
bool reads_int32(const reg::OptionSpec& spec)
{
  return spec.type == reg::OptType::INT && spec.has_min && spec.has_max && spec.min == INT32_MIN &&
         spec.max == INT32_MAX;
}
bool reads_uint32(const reg::OptionSpec& spec)
{
  return spec.type == reg::OptType::UINT && !spec.has_min && spec.has_max && spec.max == UINT32_MAX;
}
} // namespace

std::string CommandLine::group_of(const reg::OptionSpec& spec) const
{
  std::size_t n = 0;
  const reg::CliCategory* cats = reg::cli_categories(n);
  for (std::size_t i = 0; i < n; ++i)
    if (std::strcmp(cats[i].category, spec.category) == 0)
      return cats[i].group;
  // the generator refuses a category without a group, so this is unreachable
  throw std::logic_error(std::string("option category without a --help group: ") + spec.category);
}

const CommandLine::Entry* CommandLine::entry_named(const char* name) const
{
  const reg::OptionSpec* spec = reg::find_option(name);
  if (spec == nullptr)
    return nullptr;
  return &entries[reg::option_index(spec)];
}

bool* CommandLine::frontend_target(const std::string& key)
{
  if (key == "version")
    return &version;
  if (key == "cvc")
    return &use_cvc;
  if (key == "smtlib1")
    return &use_smtlib1;
  if (key == "smtlib2")
    return &use_smtlib2;
  if (key == "interactive")
    return &interactive;
  if (key == "parse-only")
    return &invocation.parse_only;
  if (key == "exit-after-cnf")
    return &invocation.exit_after_cnf;
  if (key == "print-stpinput")
    return &invocation.print_stpinput;
  if (key == "print-back-cvc")
    return &invocation.print_back_cvc;
  if (key == "print-back-smtlib2")
    return &invocation.print_back_smtlib2;
  if (key == "print-back-gdl")
    return &invocation.print_back_gdl;
  if (key == "print-back-dot")
    return &invocation.print_back_dot;
  if (key == "print-output")
    return &invocation.print_output;
  if (key == "output-cnf")
    return &invocation.output_cnf;
  // A frontend row this binary has no action for is a table/binary mismatch.
  throw std::logic_error("options.toml frontend row with no binding here: " + key);
}

void CommandLine::register_frontend(const reg::CliFrontend& row)
{
  const std::string kind = row.kind;
  if (kind == "positional")
  {
    // positional-only, hidden from --help
    app.add_option(row.spellings, invocation.infile, row.help)->group(kCliOnlyGroup);
    return;
  }
  if (kind == "help")
  {
    app.set_help_flag(row.spellings, row.help)->group(row.group);
    return;
  }
  bool* target = frontend_target(row.key);
  if (kind == "flag")
  {
    app.add_flag(row.spellings, *target, row.help)->group(row.group);
    return;
  }
  // bool-option: a value-taking Boolean (--interactive=true)
  CLI::Option* opt = app.add_option(row.spellings, *target, row.help)->group(row.group);
  if (std::string(row.key) == "interactive")
    interactive_option = opt;
}

void CommandLine::register_entry(std::size_t index, const std::string& group)
{
  std::size_t n = 0;
  const reg::OptionSpec& spec = reg::option_specs(n)[index];
  Entry& e = entries[index];
  e.spec = &spec;
  const std::string form = spec.cli_form;
  if (form == "none")
    return;
  // An entry of a SAT backend this build lacks is not registered, as it never
  // was; other build requirements (HiGHS) are accepted here and refused by
  // the registry with the build they need, so the spelling is still explained.
  if (spec.requires_build != nullptr && !reg::option_build_supported(spec) &&
      !backend_available(spec.requires_build))
    return;
  const bool flag = form == "flag";
  const bool mode_flag = flag && spec.type == reg::OptType::MODE;
  // A mode that lists its spellings takes those alone; one that does not also
  // reads 1/true and 0/false, in any case (the registry's `values`).
  const bool lenient_mode = spec.type == reg::OptType::MODE && spec.num_values == 0;

  // The spelling list: --name, its aliases, the short flag; a mode flag reads
  // bare as on, so each spelling carries CLI11's {on} default value; a
  // Boolean flag with a negation adds !--no-name.
  std::vector<std::string> spellings;
  spellings.push_back(std::string("--") + spec.name);
  for (std::size_t a = 0; a < spec.num_aliases; ++a)
    spellings.push_back(std::string("--") + spec.aliases[a]);
  if (spec.short_flag != nullptr)
    spellings.push_back(std::string("-") + spec.short_flag);
  std::string names;
  for (const std::string& s : spellings)
    names += (names.empty() ? "" : ",") + s + (mode_flag ? "{on}" : "");
  if (flag && spec.negation != nullptr && spec.type == reg::OptType::BOOL)
    names += std::string(",!--") + spec.negation;

  const std::string help = spec.help;
  const std::string dflt = spec.default_text;
  CLI::Option* opt = nullptr;
  switch (spec.type)
  {
    case reg::OptType::BOOL:
      if (flag)
        opt = app.add_flag(names, e.b, help);
      else
      {
        // A value-taking Boolean: accepts 1/0, true/false, on/off, as
        // '--flattening false' or '--flattening=false'. The captured default
        // is the registry's, which the api3 suite holds to the engine's.
        e.b = dflt == "true";
        opt = app.add_option(names, e.b, help)->capture_default_str();
      }
      break;
    case reg::OptType::INT:
      e.i = std::strtoll(dflt.c_str(), nullptr, 10);
      if (reads_int32(spec))
      {
        e.i32 = static_cast<std::int32_t>(e.i);
        opt = app.add_option(names, e.i32, help)->capture_default_str();
        break;
      }
      opt = app.add_option(names, e.i, help);
      // a default outside the window the command line checks is the API's
      // sentinel, not a value this option takes: not shown
      if (!(spec.has_cli_range && (e.i < spec.cli_min || e.i > spec.cli_max)))
        opt->capture_default_str();
      break;
    case reg::OptType::UINT:
      e.u = std::strtoull(dflt.c_str(), nullptr, 10);
      if (reads_uint32(spec))
      {
        e.u32 = static_cast<std::uint32_t>(e.u);
        opt = app.add_option(names, e.u32, help)->capture_default_str();
        break;
      }
      opt = app.add_option(names, e.u, help)->capture_default_str();
      break;
    case reg::OptType::MODE:
      if (flag && lenient_mode)
      {
        // A switch on or off, as a Boolean flag reads its value (bare: on).
        e.b = dflt == "on";
        opt = app.add_flag(names, e.b, help);
      }
      else if (flag)
        opt = app.add_flag(names, e.s, help);
      else
      {
        e.s = dflt;
        opt = app.add_option(names, e.s, help)->type_name("MODE")->default_str(dflt);
      }
      // CLI11 refuses a lenient mode's bad value itself, in the words the
      // command line always used for one
      if (lenient_mode && !flag)
        opt->check(CLI::Validator(
            [](std::string& value) -> std::string {
              std::string low = value;
              for (char& c : low)
                c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
              for (const char* ok : {"auto", "on", "1", "true", "off", "0", "false"})
                if (low == ok)
                  return std::string();
              return "expected auto, on/1/true, or off/0/false";
            },
            std::string(), std::string()));
      break;
    case reg::OptType::DURATION:
      // A whole number of seconds, as the binary always took (-1: no limit).
      e.i = -1;
      opt = app.add_option(names, e.i, help)
                ->type_name("INT")
                ->default_str(dflt == "none" ? "-1" : dflt);
      break;
    case reg::OptType::ENUM:
    case reg::OptType::SET:
    case reg::OptType::STRING:
    case reg::OptType::PATH:
      e.s = dflt;
      opt = app.add_option(names, e.s, help)->type_name("TEXT")->default_str(dflt);
      break;
  }
  // The window the command line checks itself, as it always did: the row's
  // cli_range, or the range of an unsigned entry. A signed entry with a -1
  // sentinel keeps the binary's own wording instead (bad_value_line).
  if (spec.has_cli_range)
    opt->check(CLI::Range(spec.cli_min, spec.cli_max));
  else if (spec.type == reg::OptType::UINT && spec.has_min && spec.has_max)
    opt->check(CLI::Range(static_cast<std::uint64_t>(spec.min), static_cast<std::uint64_t>(spec.max)));
  // A repeated flag, Boolean or lenient mode takes its last value, so a test
  // or a script that appends "--flag=1" to a command line that already says
  // "--flag=0" gets the appended value rather than a parse error; so does a
  // row that says so. Any other option given twice is CLI11's refusal.
  if (flag || spec.type == reg::OptType::BOOL || lenient_mode || spec.cli_take_last)
    opt->multi_option_policy(CLI::MultiOptionPolicy::TakeLast);
  opt->group(group);
  e.option = opt;
}

void CommandLine::register_alias(std::size_t k, const std::string& group)
{
  AliasFlag& af = alias_flags[k];
  // The flag of a backend this build lacks is not registered, as it never was.
  if (!backend_available(af.alias->value))
    return;
  af.option = app.add_flag(std::string("--") + af.alias->name, af.given, af.alias->help)
                  ->group(group);
}

// Combinations where one option discards another's effect. Each pair is one
// STP cannot honour both halves of; reporting that is more useful than
// obeying half a command line, most of all for the generated ones that option
// sweeps and build scripts produce, where a silently dropped flag reads as a
// measurement. CLI11 tests whether an option was given, not what it was set
// to, so '--disable-simplifications --flattening false' is refused as well,
// even though the two agree: the second option still had no bearing on the
// run. The pairs are the rows' `excludes`, `of` and `requires` columns.
void CommandLine::register_exclusions()
{
  for (const Entry& e : entries)
  {
    if (e.option == nullptr)
      continue;
    for (std::size_t x = 0; x < e.spec->num_excludes; ++x)
    {
      const Entry* other = entry_named(e.spec->excludes[x]);
      if (other != nullptr && other->option != nullptr)
        e.option->excludes(other->option);
    }
  }

  // The backend flags: only one of them can be meant, and none of them
  // alongside the entry they set.
  for (std::size_t k = 0; k < alias_flags.size(); ++k)
  {
    const AliasFlag& a = alias_flags[k];
    if (a.option == nullptr)
      continue;
    for (std::size_t j = k + 1; j < alias_flags.size(); ++j)
      if (alias_flags[j].option != nullptr &&
          std::strcmp(alias_flags[j].alias->of, a.alias->of) == 0)
        a.option->excludes(alias_flags[j].option);
    const Entry* of = entry_named(a.alias->of);
    if (of != nullptr && of->option != nullptr)
      a.option->excludes(of->option);
    // An entry that requires this backend flag's entry to hold another value
    // (--threads is read only by CryptoMiniSat) excludes the flag.
    for (const Entry& e : entries)
      if (e.option != nullptr && e.spec->requires_option != nullptr &&
          e.spec->requires_value != nullptr &&
          std::strcmp(e.spec->requires_option, a.alias->of) == 0 &&
          std::strcmp(e.spec->requires_value, a.alias->value) != 0)
        e.option->excludes(a.option);
  }

  // The frontend rows' exclusions, by spelling.
  std::size_t nf = 0;
  const reg::CliFrontend* front = reg::cli_frontend(nf);
  for (std::size_t r = 0; r < nf; ++r)
  {
    if (front[r].num_excludes == 0)
      continue;
    const std::string first = std::string(front[r].spellings).substr(
        0, std::string(front[r].spellings).find(','));
    CLI::Option* mine = app.get_option(first);
    for (std::size_t x = 0; x < front[r].num_excludes; ++x)
      mine->excludes(app.get_option(front[r].excludes[x]));
  }
}

void CommandLine::create_options()
{
  app.usage("USAGE: stp [options] <input-file>\n"
            " where input is SMTLIB1/2 or CVC depending on options and file "
            "extension");

  std::size_t n = 0;
  const reg::OptionSpec* specs = reg::option_specs(n);
  entries.resize(n);
  std::size_t na = 0;
  const reg::CliAlias* aliases = reg::cli_aliases(na);
  alias_flags.resize(na);
  for (std::size_t k = 0; k < na; ++k)
    alias_flags[k].alias = &aliases[k];
  std::size_t nf = 0;
  const reg::CliFrontend* front = reg::cli_frontend(nf);

  // The positional input file first, then every --help group in the table's
  // order: its frontend rows, its entries in registry order, then the backend
  // flags of an entry in the group.
  for (std::size_t r = 0; r < nf; ++r)
    if (std::string(front[r].kind) == "positional")
      register_frontend(front[r]);

  std::size_t ng = 0;
  const char* const* groups = reg::cli_groups(ng);
  for (std::size_t g = 0; g < ng; ++g)
  {
    const std::string group = groups[g];
    for (std::size_t r = 0; r < nf; ++r)
      if (front[r].group != nullptr && group == front[r].group)
        register_frontend(front[r]);
    for (std::size_t i = 0; i < n; ++i)
      if (std::string(specs[i].cli_form) != "none" && group_of(specs[i]) == group)
        register_entry(i, group);
    for (std::size_t k = 0; k < na; ++k)
    {
      const reg::OptionSpec* of = reg::find_option(aliases[k].of);
      if (of != nullptr && group_of(*of) == group)
        register_alias(k, group);
    }
  }
  register_exclusions();
}

// ---------------------------------------------------------------------
// Parsing
// ---------------------------------------------------------------------

void CommandLine::refuse(const std::string& line) const
{
  cerr << line << endl;
  std::exit(-1);
}

// The text the registry parses for an entry the command line gave, or the
// line refusing it.
std::string CommandLine::entry_text(const Entry& e, std::string& refusal)
{
  const reg::OptionSpec& spec = *e.spec;
  switch (spec.type)
  {
    case reg::OptType::BOOL: return e.b ? "true" : "false";
    case reg::OptType::INT:
      return std::to_string(reads_int32(spec) ? static_cast<std::int64_t>(e.i32) : e.i);
    case reg::OptType::UINT:
      return std::to_string(reads_uint32(spec) ? static_cast<std::uint64_t>(e.u32) : e.u);
    case reg::OptType::MODE:
      if (std::string(spec.cli_form) == "flag" && spec.num_values == 0)
        return e.b ? "on" : "off";
      return e.s;
    case reg::OptType::DURATION:
      // 2.x compatibility: a whole number of seconds, -1 no limit. -1 is the
      // only negative value with a meaning; anything more negative than that
      // is a mistake, and silently treating it as unlimited hides it.
      if (e.i == -1)
        return "none";
      if (e.i < -1)
        refusal = std::string("ERROR: --") + spec.name + " must be -1 (no limit) or greater";
      return std::to_string(e.i) + "s";
    default: return e.s;
  }
}

namespace
{
// The first quoted piece of a registry diagnostic after its "option 'name':"
// prefix: the member or value it refused ("invalid member 'x'; expected ...").
std::string quoted_piece(const std::string& what)
{
  const std::size_t prefix = what.find("': ");
  const std::size_t open = what.find('\'', prefix == std::string::npos ? 0 : prefix + 3);
  if (open == std::string::npos)
    return "";
  const std::size_t close = what.find('\'', open + 1);
  if (close == std::string::npos)
    return "";
  return what.substr(open + 1, close - open - 1);
}

// A registry diagnostic without its "option 'name': " prefix and " [CODE]"
// suffix: the refusal itself, in the words of whoever refused.
std::string detail_of(const std::string& what)
{
  std::string out = what;
  const std::size_t prefix = out.find("': ");
  if (out.rfind("option '", 0) == 0 && prefix != std::string::npos)
    out = out.substr(prefix + 3);
  const std::size_t code = out.rfind(" [");
  if (code != std::string::npos && !out.empty() && out.back() == ']')
    out = out.substr(0, code);
  return out;
}

// The row's values as the engine's own diagnostics list them: "a, b, or c".
std::string expected_values(const reg::OptionSpec& spec)
{
  std::string out;
  for (std::size_t i = 0; i < spec.num_values; ++i)
  {
    if (i > 0)
      out += (i + 1 == spec.num_values) ? ", or " : ", ";
    out += spec.values[i];
  }
  return out;
}

std::string fill_template(std::string text, const std::string& name, const std::string& value,
                          const std::string& member, const std::string& expected)
{
  for (const auto& hole : {std::make_pair("{name}", name), std::make_pair("{value}", value),
                           std::make_pair("{member}", member), std::make_pair("{expected}", expected)})
    for (std::size_t at = text.find(hole.first); at != std::string::npos;
         at = text.find(hole.first, at + hole.second.size()))
      text.replace(at, std::strlen(hole.first), hole.second);
  return text;
}
} // namespace

// The line the binary prints about a value the registry refused: the wording
// it has always used, spelled out by the row's template where it had one of
// its own and built from the row's range and values otherwise.
std::string CommandLine::bad_value_line(const reg::OptionSpec& spec, const std::string& given,
                                      const api::Error& error) const
{
  const std::string flag = std::string("--") + spec.name;
  const std::string detail = detail_of(error.what());
  const std::string plain = "ERROR: " + flag + ": " + detail;
  if (error.code() != api::ErrorCode::OPTION_VALUE)
    return plain;
  // The row's own wording is for the registry's refusal of a value or a
  // member; an applier or an engine parser that refuses in its own words (the
  // parser of a schema-group list, say) is quoted as it stands.
  if (spec.cli_bad_value != nullptr)
  {
    const bool registry_refusal =
        detail.rfind("invalid value", 0) == 0 || detail.rfind("invalid member", 0) == 0;
    if (registry_refusal)
      return fill_template(spec.cli_bad_value, spec.name, given, quoted_piece(error.what()),
                           expected_values(spec));
    return plain;
  }
  switch (spec.type)
  {
    case reg::OptType::INT:
    case reg::OptType::UINT:
    {
      errno = 0;
      const long long v = std::strtoll(given.c_str(), nullptr, 10);
      const bool converted = errno == 0;
      if (converted && spec.has_min && v < spec.min)
      {
        if (spec.cli_below_min != nullptr)
          return fill_template(spec.cli_below_min, spec.name, given, "", "");
        const bool no_limit = spec.min == -1 && spec.sentinel != nullptr &&
                              std::strncmp(spec.sentinel, "-1 = no limit", 13) == 0;
        return "ERROR: " + flag + " must be " + std::to_string(spec.min) +
               (no_limit ? " (no limit)" : "") + " or greater";
      }
      if (converted && spec.has_max && v > spec.max)
      {
        if (spec.cli_above_max != nullptr)
          return fill_template(spec.cli_above_max, spec.name, given, "", "");
        return "ERROR: " + flag + " must be at most " + std::to_string(spec.max);
      }
      return plain;
    }
    case reg::OptType::ENUM:
    case reg::OptType::MODE:
    {
      std::vector<std::string> values;
      for (std::size_t i = 0; i < spec.num_values; ++i)
        values.emplace_back(spec.values[i]);
      if (values.empty())
        values = {"on", "off", "auto"};
      std::string out = "ERROR: " + flag + " must be one of " + quoted_list(values);
      if (std::string(spec.cli_form) == "flag")
        out += ", attached with '=' (a bare " + flag + " means 'on')";
      return out;
    }
    default: return plain;
  }
}

namespace
{
// Where the command line reports a refused value. It has always checked the
// entries it validated itself in this order, interleaved with the checks
// that are not about one value (the parser selection, CaDiCaL's options, the
// polarity advice, the HiGHS searches, the LRA option combinations,
// --incremental's split value); a command line with several mistakes is told
// about the same one it always was. Every other refusal is CLI11's, while it
// parses.
const char* const kCheckedFirst[] = {"bv-term-abstraction-schema-groups", "bv-term-abstraction-profile",
                                     "fp-abstraction-ops", "fp-abstraction-chain-ops",
                                     "cnf-generation-effort"};
const char* const kCheckedAfterHighs[] = {"array-index-hints", "search-bias", "cadical-factor",
                                          "incremental-inprobing"};
const char* const kCheckedAfterLra[] = {"fp-abstraction-constant-operands", "uf-bv-term-abstraction",
                                        "uf-ackermann", "incremental"};
const char* const kCheckedLast[] = {"max-num-confl", "max-time", "aig-node-budget",
                                    "incremental-base-resimplify-limit", "incremental-cbp-feed-cap",
                                    "incremental-auto-engage-at"};

bool listed(const char* name, const char* const* list, std::size_t n)
{
  for (std::size_t i = 0; i < n; ++i)
    if (std::strcmp(name, list[i]) == 0)
      return true;
  return false;
}
} // namespace

int CommandLine::parse_options(int argc, char** argv)
{
  try
  {
    app.parse(argc, argv);
  }
  catch (const CLI::CallForHelp&)
  {
    cout << app.help();
    exit(0);
  }
  catch (const CLI::ParseError& e)
  {
    cerr << "Error: " << e.what() << endl;
    cerr << "Please give '--help' to get help" << endl;
    exit(-1);
  }

  // Every entry the command line gave goes to the registry as text, which
  // parses and validates it as the library would; a refusal is kept for its
  // place in the order above. An empty value of a row that says so leaves the
  // entry unset, as if it was not given.
  std::map<std::string, std::string> refused;
  for (const Entry& e : entries)
  {
    if (e.option == nullptr || e.option->count() == 0)
      continue;
    std::string refusal;
    const std::string text = entry_text(e, refusal);
    if (!refusal.empty())
    {
      refused.emplace(e.spec->name, refusal);
      continue;
    }
    if (text.empty() && e.spec->cli_empty_unset)
      continue;
    try
    {
      options.set(e.spec->name, text);
    }
    catch (const api::Error& error)
    {
      refused.emplace(e.spec->name, bad_value_line(*e.spec, text, error));
    }
  }
  for (const AliasFlag& a : alias_flags)
  {
    if (a.option == nullptr || !a.given)
      continue;
    try
    {
      options.set(a.alias->of, a.alias->value);
    }
    catch (const api::Error& error)
    {
      refuse(std::string("ERROR: --") + a.alias->name + ": " + detail_of(error.what()));
    }
  }
  const auto report = [&](const char* const* list, std::size_t n) {
    for (std::size_t i = 0; i < n; ++i)
    {
      const auto it = refused.find(list[i]);
      if (it != refused.end())
        refuse(it->second);
    }
  };
  report(kCheckedFirst, std::size(kCheckedFirst));
  // an entry with no place of its own (one the registry added) goes next
  for (const Entry& e : entries)
    if (e.spec != nullptr && refused.count(e.spec->name) &&
        !listed(e.spec->name, kCheckedAfterHighs, std::size(kCheckedAfterHighs)) &&
        !listed(e.spec->name, kCheckedAfterLra, std::size(kCheckedAfterLra)) &&
        !listed(e.spec->name, kCheckedLast, std::size(kCheckedLast)))
      refuse(refused[e.spec->name]);

  // A HiGHS search this build cannot run is reported where the command line
  // always checked for one, after the other build checks: set aside here, so
  // that the registry's own refusal of it does not come first.
  bool highs_cuts_requested = false, highs_search_requested = false;
  for (const Entry& e : entries)
  {
    // an entry the command line does not register has no spec here
    if (e.option == nullptr || e.option->count() == 0)
      continue;
    const reg::OptionSpec& spec = *e.spec;
    if (spec.requires_build == nullptr || std::strncmp(spec.requires_build, "highs", 5) != 0 ||
        reg::option_build_supported(spec))
      continue;
    const api::OptionInfo info = options.info(spec.name);
    if (info.current == info.default_value)
      continue;
    (std::string(spec.name) == "lra-highs-cuts" ? highs_cuts_requested : highs_search_requested) = true;
    options.reset(spec.name);
  }

  // The binary's own defaults where the library's differ, unless given: no
  // model is built unless asked for, and exact rationals are not re-derived.
  // --exit-after-CNF is the solver's end-after-cnf.
  if (!given("produce-models"))
    options.set_bool("produce-models", false);
  if (!given("lra-verify-canonical"))
    options.set_bool("lra-verify-canonical", false);
  if (invocation.exit_after_cnf)
    options.set_bool("end-after-cnf", true);

  // The cross-entry rules (excludes, requires, a build without the backend).
  try
  {
    options.resolve();
  }
  catch (const api::Error& error)
  {
    const std::string name(error.option());
    refuse("ERROR: " + (name.empty() ? std::string() : "--" + name + ": ") + detail_of(error.what()));
  }

  if (interactive_option != nullptr && interactive_option->count())
    invocation.interactive = interactive;

  int selected_type = 0;
  if (use_cvc)
  {
    selected_type++;
    invocation.format = stp::Format::CVC;
  }

  if (use_smtlib2)
  {
    selected_type++;
    invocation.format = stp::Format::SMTLIB2;
  }

  if (use_smtlib1)
  {
    selected_type++;
    invocation.format = stp::Format::SMTLIB1;
  }

  if (selected_type > 1)
  {
    cerr << "ERROR: You have selected more than one parsing option from "
            "CVC/SMTLIB1/SMTLIB2"
         << endl;
    std::exit(-1);
  }

  // The solver applies the options and refuses what the applied options
  // cannot honour (CaDiCaL's knobs, an explicit --lra-decision-polarity
  // without what it needs), in the engine's words.
  try
  {
    make_solver();
  }
  catch (const api::Error& error)
  {
    cerr << "ERROR: " << detail_of(error.what()) << endl;
    return -1;
  }

  if (highs_cuts_requested)
  {
    cerr << "ERROR: --lra-highs-cuts requires -DENABLE_HIGHS_CUT_LOG=ON and the HiGHS root-cut patch" << endl;
    return -1;
  }
  if (stp::capabilities()["highs"] != "true")
  {
    const api::OptionValue relu = options.resolved("lra-relu-lp");
    if (std::holds_alternative<std::string>(relu) && std::get<std::string>(relu) == "on")
      highs_search_requested = true;
  }
  if (highs_search_requested)
  {
    cerr << "ERROR: LRA LP/branch search requires a build with -DENABLE_HIGHS=ON" << endl;
    return -1;
  }

  report(kCheckedAfterHighs, std::size(kCheckedAfterHighs));

  // Checked by value, not presence: a control at 0 is the batch default and
  // combines with anything. LraCoordinator refuses the same combinations for
  // library callers, but only once a Real query reaches it.
  {
    std::vector<std::string> controls;
    if (options.get_uint("lra-extension-mode") != 0)
      controls.push_back("--lra-extension-mode=" + std::to_string(options.get_uint("lra-extension-mode")));
    if (options.get_uint("lra-row-order") != 0)
      controls.push_back("--lra-row-order=" + std::to_string(options.get_uint("lra-row-order")));
    if (options.get_bool("lra-extension-restart-float-basis"))
      controls.push_back("--lra-extension-restart-float-basis=1");
    const bool restart_sat = options.get_bool("lra-extension-restart-sat");
    if (restart_sat)
      controls.push_back("--lra-extension-restart-sat=1");
    std::vector<std::string> sessions;
    if (options.get_bool("lra-incremental-session"))
      sessions.push_back("--lra-incremental-session=1");
    if (options.get_bool("lra-persistent-state"))
      sessions.push_back("--lra-persistent-state=1");
    if (!controls.empty() && !sessions.empty())
    {
      auto join = [](const std::vector<std::string>& names) {
        std::string joined;
        for (const std::string& name : names)
          joined += (joined.empty() ? "" : ", ") + name;
        return joined;
      };
      cerr << "ERROR: " << join(controls) << " cannot be combined with " << join(sessions)
           << ": the LRA extension controls apply to batch solves only" << endl;
      std::exit(-1);
    }

    // 'auto' is the first backend the build has, in sat_backends()' order.
    std::string backend = options.get_str("sat-backend");
    if (backend == "auto")
    {
      const std::vector<std::string> built = stp::sat_backends();
      backend = built.empty() ? std::string() : built.front();
    }
    if (restart_sat && backend != "cadical")
    {
      if (stp::has_sat_backend("cadical"))
        cerr << "ERROR: --lra-extension-restart-sat=1 requires --cadical" << endl;
      else
        cerr << "ERROR: --lra-extension-restart-sat=1 requires a build with CaDiCaL" << endl;
      std::exit(-1);
    }

#ifdef STP_CADICAL_HAS_FACTOR
    // Only an explicit 'on': the unnamed default and 'auto' are turned off
    // for it (STP.cpp).
    if (restart_sat && options.is_set("cadical-factor") && options.get_str("cadical-factor") == "on")
    {
      cerr << "ERROR: --lra-extension-restart-sat=1 requires --cadical-factor=off" << endl;
      std::exit(-1);
    }
#endif

    // The decision hints hold CaDiCaL's propagator slot, which a search
    // reset cannot carry over.
    if (restart_sat && options.get_str("array-index-hints") == "decide")
    {
      cerr << "ERROR: --lra-extension-restart-sat=1 cannot be combined with --array-index-hints=decide" << endl;
      std::exit(-1);
    }
  }

  report(kCheckedAfterLra, std::size(kCheckedAfterLra));

  // A flag's value has to be attached, so 'stp --incremental off' parses as
  // --incremental (which means 'on') followed by an input file named 'off' --
  // the opposite of what was asked for, reported as "Cannot open off", which
  // names neither half of the mistake.
  const std::string& infile = invocation.infile;
  const Entry* incremental = entry_named("incremental");
  if (incremental != nullptr && incremental->option != nullptr && incremental->option->count() &&
      (infile == "on" || infile == "off" || infile == "auto"))
  {
    refuse("ERROR: --incremental takes its value attached with '=', as --incremental=" + infile +
           "; given as a separate argument it was read as the name of the input file");
  }

  report(kCheckedLast, std::size(kCheckedLast));

  if (selected_type == 0)
  {
    // No parser is explicity requested.
    select_parser_by_extension();
  }

  if (version)
  {
    stp_cli::print_version();
    exit(0);
  }

  return 0;
}

// Whether the command line gave the entry itself.
bool CommandLine::given(const char* name) const
{
  const Entry* e = entry_named(name);
  return e != nullptr && e->option != nullptr && e->option->count() > 0;
}

// The parser a file's extension picks when no flag picked one: .cvc and .smt
// their own, SMT-LIB 2 for .smt2 and anything else.
void CommandLine::select_parser_by_extension()
{
  const std::string& infile = invocation.infile;
  if (infile.size() >= 5)
  {
    if (!infile.compare(infile.length() - 4, 4, ".cvc"))
      invocation.format = stp::Format::CVC;
    if (!infile.compare(infile.length() - 4, 4, ".smt"))
      invocation.format = stp::Format::SMTLIB1;
    if (!infile.compare(infile.length() - 5, 5, ".smt2"))
      invocation.format = stp::Format::SMTLIB2;
  }
}

namespace
{
std::uint64_t as_uint(const api::OptionValue& v)
{
  if (std::holds_alternative<std::uint64_t>(v))
    return std::get<std::uint64_t>(v);
  return static_cast<std::uint64_t>(std::get<std::int64_t>(v));
}
} // namespace

// The manager and the solver, from the options. The manager-scoped entries
// are the manager's: `simplify` (always off for an input printed back, which
// is read as written) and the uninterpreted sorts' width. The solver copies
// the rest, resolves and applies them.
void CommandLine::make_solver()
{
  stp::TermManager::Config config;
  const api::OptionValue simplify = options.resolved("simplify");
  config.simplify = (!std::holds_alternative<bool>(simplify) || std::get<bool>(simplify)) &&
                    !invocation.print_back();
  config.uf_sort_width = static_cast<std::uint32_t>(as_uint(options.resolved("uf-sort-width")));
  options.reset("simplify");
  options.reset("uf-sort-width");
  // An input printed back reports no run times; it never did (the read that
  // prints it back would).
  if (invocation.print_back() && !invocation.parse_only)
    options.reset("print-quickstat");
  manager.emplace(config);
  solver = std::make_unique<stp::Solver>(*manager, options);
}

int main(int argc, char** argv)
{
  CommandLine command_line;
  command_line.create_options();
  const int ret = command_line.parse_options(argc, argv);
  if (ret != 0)
    return ret;
  return stp_cli::run(command_line.invocation, std::move(command_line.solver));
}

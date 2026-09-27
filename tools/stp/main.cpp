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

#include "main_common.h"
#include "stp/Sat/SATSolverFactory.h"

// The 3.x option registry: the rows of lib/Api/tables/options.toml, their
// parsing and validation, and the table that carries a validated value into
// UserDefinedFlags. The command line below is registered from it, so the
// binary and the API accept the same options with the same meanings.
#include "Api/Internal.h"

#include <CLI/CLI.hpp>

#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <stdexcept>
#include <string>
#include <variant>
#include <vector>

using namespace stp;
using std::cout;
using std::cerr;
using std::endl;

namespace reg = stp::api::detail;

/********************************************************************
 * MAIN FUNCTION:
 *
 * step 0. Parse the input into an ASTVec.
 * step 1. Do BV Rewrites
 * step 2. Bitblasts the ASTNode.
 * step 3. Convert to CNF
 * step 4. Convert to SAT
 * step 5. Call SAT to determine if input is SAT or UNSAT
 ********************************************************************/

// The command line is the option registry plus the frontend rows.
//
// Every [[option]] entry of options.toml with a CLI form is registered with
// CLI11 from its row (name, aliases, short flag, negation, type, default,
// help, group), its value is handed to the registry as text, and after the
// parse the registry validates the whole set (excludes, requires, build) and
// applies it to bm->UserFlags through the same appliers the library uses.
// The [[alias]] rows are the bare backend flags (--cadical and friends) that
// set sat-backend to a value. The [[frontend]] rows are the CLI-only
// registrations, bound here by their key.
//
// Hand-written and CLI-only, listed so that nothing else hides here:
//   - the frontend rows' actions: the positional input file, --help,
//     --version, the parser selection (--CVC, --SMTLIB1, --SMTLIB2), the
//     print-back flags, --print-output, --output-CNF, --exit-after-CNF,
//     --parse-only and --interactive, whose state is the binary's own;
//   - the reading of --max-time's bare number as seconds (2.x compatibility;
//     the registry's duration type wants a unit);
//   - the wording of a refused value, kept to what the binary always said
//     ("--max-time must be -1 (no limit) or greater", "--search-bias must be
//     one of ..."), built from the row's range and values, or spelled out by
//     the row's cli_bad_value template where the old wording was its own;
//   - CLI11's own range check where the binary always had one: the unsigned
//     entries with a range, and the rows whose cli_range is narrower than the
//     API's (the CaDiCaL knobs, whose -1 means unset to the library);
//   - the exclusions of the backend flags among themselves and against the
//     entries that require a particular backend (from the rows' `of` and
//     `requires`), and CLI11's own exclusions for the frontend rows;
//   - the split-value diagnostic for --incremental (a flag whose value must be
//     attached with '=');
//   - the checks that need this build's macros and must run after the flags
//     are applied: CaDiCaL option consistency, --lra-decision-polarity's
//     backend prerequisites and the HiGHS-only searches;
//   - the manager-scoped `simplify` entry, honoured by the parser's choice of
//     node factory (main_common.cpp).
class ExtraMain : public Main
{
public:
  int create_and_parse_options(int argc, char** argv) override;
  void create_options();
  int parse_options(int argc, char** argv);

  CLI::App app;

  // One slot per registry row. CLI11 keeps references to the storage, so
  // the vector is sized once, before the first registration.
  struct Entry
  {
    const reg::OptionSpec* spec = nullptr;
    CLI::Option* option = nullptr;
    bool b = false;
    std::int64_t i = 0;
    std::uint64_t u = 0;
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

  reg::OptionsImpl options;

  // The frontend rows' state. Rows bound to a UserFlags member bind it
  // directly; these are the binary's own.
  bool version = false;
  bool use_cvc = false;
  bool use_smtlib1 = false;
  bool use_smtlib2 = false;
  // Tri-state: UserFlags.interactive_read is only overridden when the
  // option was given, so the value needs its own presence check.
  bool interactive = false;
  CLI::Option* interactive_option = nullptr;

  std::string group_of(const reg::OptionSpec& spec) const;
  bool* frontend_target(const std::string& key);
  void register_frontend(const reg::CliFrontend& row);
  void register_entry(std::size_t index, const std::string& group);
  void register_alias(std::size_t k, const std::string& group);
  void register_exclusions();
  std::string entry_text(const Entry& e);
  std::string bad_value_message(const reg::OptionSpec& spec, const std::string& given,
                                const api::Error& error) const;
  [[noreturn]] void refuse(const std::string& message) const;
  const Entry* entry_named(const char* name) const;
};

int ExtraMain::create_and_parse_options(int argc, char** argv)
{
  create_options();
  int ret = parse_options(argc, argv);
  if (ret != 0)
  {
    return ret;
  }
  return 0;
}

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
  if (value == "cadical")
    return STP_BUILD_WITH_CADICAL != 0;
  if (value == "cryptominisat")
    return STP_BUILD_WITH_CRYPTOMINISAT != 0;
  if (value == "minisat" || value == "simplifying-minisat")
    return STP_BUILD_WITH_MINISAT != 0;
  return true;
}

// The bare number of a legacy --max-time is seconds; -1 is no limit.
bool looks_numeric(const std::string& s)
{
  if (s.empty())
    return false;
  std::size_t i = (s[0] == '-' || s[0] == '+') ? 1 : 0;
  if (i == s.size())
    return false;
  bool dot = false;
  for (; i < s.size(); ++i)
  {
    if (s[i] == '.' && !dot)
      dot = true;
    else if (!std::isdigit(static_cast<unsigned char>(s[i])))
      return false;
  }
  return true;
}
} // namespace

std::string ExtraMain::group_of(const reg::OptionSpec& spec) const
{
  std::size_t n = 0;
  const reg::CliCategory* cats = reg::cli_categories(n);
  for (std::size_t i = 0; i < n; ++i)
    if (std::strcmp(cats[i].category, spec.category) == 0)
      return cats[i].group;
  // the generator refuses a category without a group, so this is unreachable
  throw std::logic_error(std::string("option category without a --help group: ") + spec.category);
}

const ExtraMain::Entry* ExtraMain::entry_named(const char* name) const
{
  const reg::OptionSpec* spec = reg::find_option(name);
  if (spec == nullptr)
    return nullptr;
  return &entries[reg::option_index(spec)];
}

bool* ExtraMain::frontend_target(const std::string& key)
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
    return &bm->UserFlags.parse_only;
  if (key == "exit-after-cnf")
    return &bm->UserFlags.exit_after_CNF;
  if (key == "print-stpinput")
    return &bm->UserFlags.print_STPinput_back_flag;
  if (key == "print-back-cvc")
    return &bm->UserFlags.print_STPinput_back_CVC_flag;
  if (key == "print-back-smtlib2")
    return &bm->UserFlags.print_STPinput_back_SMTLIB2_flag;
  if (key == "print-back-gdl")
    return &bm->UserFlags.print_STPinput_back_GDL_flag;
  if (key == "print-back-dot")
    return &bm->UserFlags.print_STPinput_back_dot_flag;
  if (key == "print-output")
    return &bm->UserFlags.print_output_flag;
  if (key == "output-cnf")
    return &bm->UserFlags.output_CNF_flag;
  // A frontend row this binary has no action for is a table/binary mismatch.
  throw std::logic_error("options.toml frontend row with no binding here: " + key);
}

void ExtraMain::register_frontend(const reg::CliFrontend& row)
{
  const std::string kind = row.kind;
  if (kind == "positional")
  {
    // positional-only, hidden from --help
    app.add_option(row.spellings, infile, row.help)->group(kCliOnlyGroup);
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

void ExtraMain::register_entry(std::size_t index, const std::string& group)
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
      opt = app.add_option(names, e.i, help);
      // a default outside the window the command line checks is the API's
      // sentinel, not a value this option takes: not shown
      if (!(spec.has_cli_range && (e.i < spec.cli_min || e.i > spec.cli_max)))
        opt->capture_default_str();
      break;
    case reg::OptType::UINT:
      e.u = std::strtoull(dflt.c_str(), nullptr, 10);
      opt = app.add_option(names, e.u, help)->capture_default_str();
      break;
    case reg::OptType::MODE:
      if (flag)
        opt = app.add_flag(names, e.s, help);
      else
      {
        e.s = dflt;
        opt = app.add_option(names, e.s, help)->type_name("MODE")->default_str(dflt);
      }
      break;
    case reg::OptType::DURATION:
      // Shown as the integer number of seconds the binary always took.
      opt = app.add_option(names, e.s, help)
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
  // sentinel keeps the binary's own wording instead (bad_value_message).
  if (spec.has_cli_range)
    opt->check(CLI::Range(spec.cli_min, spec.cli_max));
  else if (spec.type == reg::OptType::UINT && spec.has_min && spec.has_max)
    opt->check(CLI::Range(static_cast<std::uint64_t>(spec.min), static_cast<std::uint64_t>(spec.max)));
  // A repeated option takes its last value, so a test or a script that appends
  // "--flag=1" to a command line that already says "--flag=0" gets the
  // appended value rather than a parse error.
  opt->multi_option_policy(CLI::MultiOptionPolicy::TakeLast)->group(group);
  e.option = opt;
}

void ExtraMain::register_alias(std::size_t k, const std::string& group)
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
void ExtraMain::register_exclusions()
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

void ExtraMain::create_options()
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

void ExtraMain::refuse(const std::string& message) const
{
  cerr << "ERROR: " << message << endl;
  std::exit(-1);
}

// The text the registry parses for an entry the command line gave.
std::string ExtraMain::entry_text(const Entry& e)
{
  const reg::OptionSpec& spec = *e.spec;
  switch (spec.type)
  {
    case reg::OptType::BOOL: return e.b ? "true" : "false";
    case reg::OptType::INT: return std::to_string(e.i);
    case reg::OptType::UINT: return std::to_string(e.u);
    case reg::OptType::DURATION:
    {
      // 2.x compatibility: a bare number is seconds, -1 is no limit. -1 is
      // the only negative value with a meaning; anything more negative than
      // that is a mistake, and silently treating it as unlimited hides it.
      if (!looks_numeric(e.s))
        return e.s;
      if (e.s == "-1")
        return "none";
      if (e.s[0] == '-')
        refuse(std::string("--") + spec.name + " must be -1 (no limit) or greater");
      return e.s + "s";
    }
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

// What the binary says about a value the registry refused: the wording it has
// always used, spelled out by the row's template where it had one of its own
// and built from the row's range and values otherwise.
std::string ExtraMain::bad_value_message(const reg::OptionSpec& spec, const std::string& given,
                                         const api::Error& error) const
{
  const std::string flag = std::string("--") + spec.name;
  const std::string detail = detail_of(error.what());
  if (error.code() != api::ErrorCode::OPTION_VALUE)
    return flag + ": " + detail;
  // The row's own wording is for the registry's refusal of a value or a
  // member; an applier that refuses in its own words (the engine's parser of
  // a schema-group list, say) is quoted as it stands.
  if (spec.cli_bad_value != nullptr)
  {
    const bool registry_refusal =
        detail.rfind("invalid value", 0) == 0 || detail.rfind("invalid member", 0) == 0;
    if (registry_refusal)
      return fill_template(spec.cli_bad_value, spec.name, given, quoted_piece(error.what()),
                           expected_values(spec));
    return flag + ": " + detail;
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
        const bool no_limit = spec.min == -1 && spec.sentinel != nullptr &&
                              std::strncmp(spec.sentinel, "-1 = no limit", 13) == 0;
        return flag + " must be " + std::to_string(spec.min) + (no_limit ? " (no limit)" : "") +
               " or greater";
      }
      if (converted && spec.has_max && v > spec.max)
        return flag + " must be at most " + std::to_string(spec.max);
      return flag + ": " + detail;
    }
    case reg::OptType::ENUM:
    case reg::OptType::MODE:
    {
      std::vector<std::string> values;
      if (spec.type == reg::OptType::MODE)
        values = {"on", "off", "auto"};
      else
        for (std::size_t i = 0; i < spec.num_values; ++i)
          values.emplace_back(spec.values[i]);
      std::string out = "Unknown " + flag + " value '" + given + "': " + flag + " must be one of " +
                        quoted_list(values);
      if (std::string(spec.cli_form) == "flag")
        out += ", attached with '=' (a bare " + flag + " means 'on')";
      return out;
    }
    case reg::OptType::SET:
      return flag + ": " + detail;
    case reg::OptType::DURATION:
      return flag + ": expected a number of seconds, -1 for no limit, or a duration with a unit "
                    "(500ms, 2s, 1m); given '" +
             given + "'";
    default: return flag + ": " + detail;
  }
}

int ExtraMain::parse_options(int argc, char** argv)
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

  // A flag's value has to be attached, so 'stp --incremental off' parses as
  // --incremental (which means 'on') followed by an input file named 'off' --
  // the opposite of what was asked for, reported as "Cannot open off", which
  // names neither half of the mistake.
  const Entry* incremental = entry_named("incremental");
  if (incremental != nullptr && incremental->option != nullptr && incremental->option->count() &&
      (infile == "on" || infile == "off" || infile == "auto"))
  {
    refuse("--incremental takes its value attached with '=', as --incremental=" + infile +
           "; given as a separate argument it was read as the name of the input file");
  }

  // Every entry the command line gave goes to the registry as text, which
  // parses and validates it as the library would.
  for (const Entry& e : entries)
  {
    if (e.option == nullptr || e.option->count() == 0)
      continue;
    const std::string text = entry_text(e);
    try
    {
      options.set_text("stp", e.spec->name, text);
    }
    catch (const api::Error& error)
    {
      refuse(bad_value_message(*e.spec, text, error));
    }
  }
  for (const AliasFlag& a : alias_flags)
  {
    if (a.option == nullptr || !a.given)
      continue;
    try
    {
      options.set_text("stp", a.alias->of, a.alias->value);
    }
    catch (const api::Error& error)
    {
      refuse(std::string("--") + a.alias->name + ": " + error.what());
    }
  }

  // The cross-entry rules (excludes, requires, a build without the backend),
  // then the flags. The appliers are the library's: a value reaches
  // UserDefinedFlags the same way from here and from Solver's options.
  try
  {
    options.resolve("stp");
    reg::EngineTarget target{bm->UserFlags, nullptr, nullptr};
    reg::apply_all_options(target, options);
  }
  catch (const api::Error& error)
  {
    const std::string name(error.option());
    // The HiGHS entries in a build without HiGHS: the wording the binary has
    // always used for that build.
    const reg::OptionSpec* spec = name.empty() ? nullptr : reg::find_option(name);
    if (error.code() == api::ErrorCode::OPTION_UNAVAILABLE && spec != nullptr &&
        spec->requires_build != nullptr && std::strncmp(spec->requires_build, "highs", 5) == 0)
    {
      if (name == "lra-highs-cuts")
        refuse("--lra-highs-cuts requires -DENABLE_HIGHS_CUT_LOG=ON and the HiGHS root-cut patch");
      refuse("LRA LP/branch search requires a build with -DENABLE_HIGHS=ON (--" + name + ")");
    }
    refuse((name.empty() ? std::string() : "--" + name + ": ") + error.what());
  }

  // The manager-scoped `simplify` entry is honoured by the parser's choice of
  // node factory (main_common.cpp).
  {
    const Entry* simplify = entry_named("simplify");
    if (simplify != nullptr)
    {
      const api::OptionValue v = options.resolved(reg::option_index(simplify->spec));
      simplifyInput = v.index() == 0 ? std::get<bool>(v) : true;
    }
  }

  /* Before anything can build an exact rational, so that every budget this
   * run creates agrees about it. Left alone by every other entry point, which
   * therefore keeps the check. */
  bm->SetLraCanonicalVerification(bm->UserFlags.lra_verify_canonical);

  onePrintBack = bm->UserFlags.get_print_output_at_all();

  if (interactive_option != nullptr && interactive_option->count())
  {
    bm->UserFlags.interactive_read = interactive ? 1 : 0;
  }

  int selected_type = 0;
  if (use_cvc)
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = false;
    bm->UserFlags.smtlib2_parser_flag = false;
  }

  if (use_smtlib2)
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = false;
    bm->UserFlags.smtlib2_parser_flag = true;
  }

  if (use_smtlib1)
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = true;
    bm->UserFlags.smtlib2_parser_flag = false;
  }

  if (selected_type > 1)
  {
    cerr << "ERROR: You have selected more than one parsing option from "
            "CVC/SMTLIB1/SMTLIB2"
         << endl;
    std::exit(-1);
  }

  if (selected_type == 0)
  {
    bm->UserFlags.smtlib2_parser_flag = true;
  }

  try
  {
    validateCadicalOptions(bm->UserFlags);
  }
  catch (const std::invalid_argument& error)
  {
    cerr << "ERROR: " << error.what() << endl;
    return -1;
  }

  // The default polarity preference yields to backend capabilities; an
  // explicit request must still diagnose missing prerequisites.
  if (bm->UserFlags.lra_decision_polarity &&
      bm->UserFlags.lra_decision_polarity_explicit)
  {
    if (!bm->UserFlags.lra_theory_propagation)
    {
      cerr << "ERROR: --lra-decision-polarity requires "
              "--lra-theory-propagation=1" << endl;
      return -1;
    }
    bool supported = false;
#if defined(USE_CADICAL) && defined(STP_CADICAL_HAS_DECISION_POLARITY)
    supported = bm->UserFlags.solver_to_use == UserDefinedFlags::CADICAL_SOLVER;
#endif
    if (!supported)
    {
      cerr << "ERROR: --lra-decision-polarity requires CaDiCaL built with "
              "cmake/deps-utils/cadical-decision-polarity.patch" << endl;
      return -1;
    }
  }

#ifndef STP_HAVE_HIGHS_CUT_LOG
  if (bm->UserFlags.lra_highs_cuts)
  {
    cerr << "ERROR: --lra-highs-cuts requires -DENABLE_HIGHS_CUT_LOG=ON and the HiGHS root-cut patch" << endl;
    return -1;
  }
#endif
#ifndef STP_HAVE_HIGHS
  if (bm->UserFlags.lra_relu_lp == UserDefinedFlags::OptionMode::ON ||
      bm->UserFlags.lra_relu_branch ||
      bm->UserFlags.lra_highs_lp || bm->UserFlags.lra_highs_mip ||
      bm->UserFlags.lra_highs_replay)
  {
    cerr << "ERROR: LRA LP/branch search requires a build with -DENABLE_HIGHS=ON" << endl;
    return -1;
  }
#endif

  // Checked by value, not presence: a control at 0 is the batch default and
  // combines with anything. LraCoordinator refuses the same combinations for
  // library callers, but only once a Real query reaches it.
  {
    const UserDefinedFlags& uf = bm->UserFlags;
    std::vector<std::string> controls;
    if (uf.lra_extension_mode != 0)
      controls.push_back("--lra-extension-mode=" +
                         std::to_string(uf.lra_extension_mode));
    if (uf.lra_row_order != 0)
      controls.push_back("--lra-row-order=" +
                         std::to_string(uf.lra_row_order));
    if (uf.lra_extension_restart_float_basis)
      controls.push_back("--lra-extension-restart-float-basis=1");
    if (uf.lra_extension_restart_sat)
      controls.push_back("--lra-extension-restart-sat=1");
    std::vector<std::string> sessions;
    if (uf.lra_incremental_session)
      sessions.push_back("--lra-incremental-session=1");
    if (uf.lra_persistent_state)
      sessions.push_back("--lra-persistent-state=1");
    if (!controls.empty() && !sessions.empty())
    {
      auto join = [](const std::vector<std::string>& names) {
        std::string joined;
        for (const std::string& name : names)
          joined += (joined.empty() ? "" : ", ") + name;
        return joined;
      };
      cerr << "ERROR: " << join(controls) << " cannot be combined with "
           << join(sessions)
           << ": the LRA extension controls apply to batch solves only"
           << endl;
      std::exit(-1);
    }

    if (uf.lra_extension_restart_sat &&
        uf.solver_to_use != UserDefinedFlags::CADICAL_SOLVER)
    {
#ifdef USE_CADICAL
      cerr << "ERROR: --lra-extension-restart-sat=1 requires --cadical" << endl;
#else
      cerr << "ERROR: --lra-extension-restart-sat=1 requires a build with "
              "CaDiCaL"
           << endl;
#endif
      std::exit(-1);
    }

#ifdef STP_CADICAL_HAS_FACTOR
    // Only an explicit 'on': the unnamed default and 'auto' are turned off
    // for it (STP.cpp).
    if (uf.lra_extension_restart_sat && uf.cadical_factor_explicit &&
        uf.cadical_factor == UserDefinedFlags::BVAMode::ON)
    {
      cerr << "ERROR: --lra-extension-restart-sat=1 requires "
              "--cadical-factor=off"
           << endl;
      std::exit(-1);
    }
#endif

    // The decision hints hold CaDiCaL's propagator slot, which a search
    // reset cannot carry over.
    if (uf.lra_extension_restart_sat &&
        uf.array_index_hints == UserDefinedFlags::ArrayIndexHints::DECIDE)
    {
      cerr << "ERROR: --lra-extension-restart-sat=1 cannot be combined with "
              "--array-index-hints=decide"
           << endl;
      std::exit(-1);
    }
  }

  if (selected_type == 0)
  {
    // No parser is explicity requested.
    check_infile_type();
  }

  if (version)
  {
    printVersionInfo();
    exit(0);
  }

  return 0;
}

int main(int argc, char** argv)
{
  ExtraMain main;
  return main.main(argc, argv);
}

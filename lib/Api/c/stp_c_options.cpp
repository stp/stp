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

// stp_c_options.cpp -- the options side of <stp/stp.h>: standalone
// stp_options values (their own error record), the registry introspection
// (static strings straight from the option table) and the live options of a
// solver (the manager's record; a write is a mutating solver call).

#include "stp_c_internal.h"

#include <chrono>

namespace stp
{
namespace api
{
namespace capi
{

const detail::OptionSpec* spec_arg(const char* name, const char* fn, int arg)
{
  str_arg(name, fn, arg);
  const detail::OptionSpec* spec = detail::find_option(name);
  if (spec == nullptr)
    detail::fail_option(ErrorCode::OPTION_UNKNOWN, name, "unknown option");
  return spec;
}

const detail::OptionSpec* stable_spec(stp_option o, const char* fn, int arg)
{
  if (static_cast<unsigned>(o) >= static_cast<unsigned>(STP_NUM_STABLE_OPTIONS))
    detail::fail(ErrorCode::OPTION_UNKNOWN, fn, "not a stable option", arg);
  std::size_t n = 0;
  const detail::OptionSpec* specs = detail::option_specs(n);
  std::size_t stable = 0;
  for (std::size_t i = 0; i < n; ++i)
    if (specs[i].tier == Tier::STABLE)
    {
      if (stable == static_cast<std::size_t>(o))
        return &specs[i];
      ++stable;
    }
  detail::fail(ErrorCode::OPTION_UNKNOWN, fn, "not a stable option", arg);
}

std::string option_text_of(const detail::OptionSpec& spec, const OptionValue& v)
{
  return detail::option_text(spec, v);
}

} // namespace capi
} // namespace api
} // namespace stp

using namespace stp::api;
using namespace stp::api::capi;
using stp::api::detail::fail;

namespace
{
bool need(const void* p, const char* fn, int arg = 0) noexcept
{
  if (p != nullptr)
    return true;
  report_code(nullptr, nullptr, fn, ErrorCode::NULL_HANDLE, "the handle is null", arg);
  return false;
}

// A standalone options call: errors into the object's own record.
template <class R, class F>
R opts(stp_options o, const char* fn, R fail_value, F&& f) noexcept
{
  if (!need(o, fn))
    return fail_value;
  COptions* co = coptions(o);
  return guarded<R>(nullptr, &co->error, fn, fail_value, [&] { return f(co->options); });
}

template <class F>
stp_status opts_status(stp_options o, const char* fn, F&& f) noexcept
{
  return opts<stp_status>(o, fn, STP_ERROR, [&](Options& op) {
    f(op);
    return STP_OK;
  });
}

// A live-options call on a solver: reads report through the manager's record,
// writes are mutating solver calls.
template <class F>
stp_status solver_write(stp_solver s, const char* fn, F&& f) noexcept
{
  if (!need(s, fn))
    return STP_ERROR;
  CSolver* cs = csolver(s);
  return solver_mutate<stp_status>(cs, fn, STP_ERROR, [&] {
    f(cs->solver.options());
    return STP_OK;
  });
}

template <class R, class F>
R solver_read(stp_solver s, const char* fn, R fail_value, F&& f) noexcept
{
  if (!need(s, fn))
    return fail_value;
  CSolver* cs = csolver(s);
  return guarded<R>(cs->cm, nullptr, fn, fail_value, [&] { return f(cs->solver.options()); });
}

std::vector<std::string> names_arg(std::size_t n, const char* const* members, const char* fn, int arg)
{
  if (n > 0 && members == nullptr)
    fail(ErrorCode::NULL_HANDLE, fn, "the member array is null", arg);
  std::vector<std::string> out;
  out.reserve(n);
  for (std::size_t i = 0; i < n; ++i)
    out.emplace_back(str_arg(members[i], fn, arg));
  return out;
}

std::chrono::milliseconds ms_arg(std::uint64_t ms, const char* fn, int arg)
{
  if (ms > static_cast<std::uint64_t>(INT64_MAX))
    fail(ErrorCode::VALUE_OUT_OF_RANGE, fn, "the duration does not fit int64 milliseconds", arg);
  return std::chrono::milliseconds(static_cast<std::int64_t>(ms));
}

std::uint64_t ms_of(std::chrono::milliseconds d)
{
  return d.count() < 0 ? 0 : static_cast<std::uint64_t>(d.count());
}

// The registry rows of one tier (-1: every tier), in registry order.
const detail::OptionSpec* nth_spec(int tier, std::size_t index)
{
  if (tier != -1 && (tier < 0 || tier > STP_TIER_DIAGNOSTIC))
    return nullptr;
  std::size_t n = 0;
  const detail::OptionSpec* specs = detail::option_specs(n);
  std::size_t seen = 0;
  for (std::size_t i = 0; i < n; ++i)
  {
    if (tier != -1 && static_cast<int>(specs[i].tier) != tier)
      continue;
    if (seen == index)
      return &specs[i];
    ++seen;
  }
  return nullptr;
}

// The spec behind an introspection call: unknown names go to the thread-local
// record as OPTION_UNKNOWN.
const detail::OptionSpec* info_spec(const char* name, const char* fn) noexcept
{
  return guarded<const detail::OptionSpec*>(nullptr, nullptr, fn, nullptr,
                                            [&] { return spec_arg(name, fn, 0); });
}

const char* type_name(detail::OptType t) noexcept
{
  switch (t)
  {
    case detail::OptType::BOOL: return "bool";
    case detail::OptType::INT: return "int";
    case detail::OptType::UINT: return "uint";
    case detail::OptType::MODE: return "mode";
    case detail::OptType::ENUM: return "enum";
    case detail::OptType::SET: return "set";
    case detail::OptType::STRING: return "string";
    case detail::OptType::PATH: return "path";
    case detail::OptType::DURATION: return "duration";
  }
  return "?";
}
} // namespace

extern "C" {

// ============================================================ standalone options

stp_options stp_options_new(void)
{
  return guarded<stp_options>(nullptr, nullptr, "stp_options_new", nullptr,
                              [] { return reinterpret_cast<stp_options>(new COptions()); });
}

stp_options stp_options_copy(stp_options o)
{
  if (!need(o, "stp_options_copy"))
    return nullptr;
  return guarded<stp_options>(nullptr, nullptr, "stp_options_copy", nullptr, [&] {
    // the copy starts with a clean record of its own
    COptions* c = new COptions{coptions(o)->options, ErrorRecord()};
    return reinterpret_cast<stp_options>(c);
  });
}

void stp_options_delete(stp_options o)
{
  delete coptions(o);
}

const stp_error* stp_options_error(stp_options o)
{
  if (o == nullptr)
    return nullptr;
  COptions* co = coptions(o);
  return co->error.pending ? &co->error.view : nullptr;
}

void stp_options_clear_error(stp_options o)
{
  if (o != nullptr)
    coptions(o)->error.clear();
}

stp_status stp_options_set_str(stp_options o, const char* name, const char* value)
{
  return opts_status(o, "stp_options_set_str", [&](Options& op) {
    op.set(str_arg(name, "stp_options_set_str", 1), str_arg(value, "stp_options_set_str", 2));
  });
}

stp_status stp_options_set_bool(stp_options o, const char* name, bool v)
{
  return opts_status(o, "stp_options_set_bool",
                     [&](Options& op) { op.set_bool(str_arg(name, "stp_options_set_bool", 1), v); });
}

stp_status stp_options_set_int64(stp_options o, const char* name, int64_t v)
{
  return opts_status(o, "stp_options_set_int64",
                     [&](Options& op) { op.set_int(str_arg(name, "stp_options_set_int64", 1), v); });
}

stp_status stp_options_set_uint64(stp_options o, const char* name, uint64_t v)
{
  return opts_status(o, "stp_options_set_uint64", [&](Options& op) {
    op.set_uint(str_arg(name, "stp_options_set_uint64", 1), v);
  });
}

stp_status stp_options_set_duration_ms(stp_options o, const char* name, uint64_t ms)
{
  return opts_status(o, "stp_options_set_duration_ms", [&](Options& op) {
    op.set_duration(str_arg(name, "stp_options_set_duration_ms", 1),
                    ms_arg(ms, "stp_options_set_duration_ms", 2));
  });
}

stp_status stp_options_set_names(stp_options o, const char* name, size_t n,
                                 const char* const* members)
{
  return opts_status(o, "stp_options_set_names", [&](Options& op) {
    op.set_names(str_arg(name, "stp_options_set_names", 1),
                 names_arg(n, members, "stp_options_set_names", 3));
  });
}

stp_status stp_options_set_bool_e(stp_options o, stp_option e, bool v)
{
  return opts_status(o, "stp_options_set_bool_e", [&](Options& op) {
    op.set_bool(stable_spec(e, "stp_options_set_bool_e", 1)->name, v);
  });
}

stp_status stp_options_set_int64_e(stp_options o, stp_option e, int64_t v)
{
  return opts_status(o, "stp_options_set_int64_e", [&](Options& op) {
    op.set_int(stable_spec(e, "stp_options_set_int64_e", 1)->name, v);
  });
}

stp_status stp_options_set_uint64_e(stp_options o, stp_option e, uint64_t v)
{
  return opts_status(o, "stp_options_set_uint64_e", [&](Options& op) {
    op.set_uint(stable_spec(e, "stp_options_set_uint64_e", 1)->name, v);
  });
}

stp_status stp_options_set_str_e(stp_options o, stp_option e, const char* v)
{
  return opts_status(o, "stp_options_set_str_e", [&](Options& op) {
    op.set_str(stable_spec(e, "stp_options_set_str_e", 1)->name,
               str_arg(v, "stp_options_set_str_e", 2));
  });
}

stp_status stp_options_set_duration_ms_e(stp_options o, stp_option e, uint64_t ms)
{
  return opts_status(o, "stp_options_set_duration_ms_e", [&](Options& op) {
    op.set_duration(stable_spec(e, "stp_options_set_duration_ms_e", 1)->name,
                    ms_arg(ms, "stp_options_set_duration_ms_e", 2));
  });
}

stp_status stp_options_set_args(stp_options o, int argc, const char* const* argv)
{
  return opts_status(o, "stp_options_set_args", [&](Options& op) {
    if (argc < 0)
      fail(ErrorCode::INVALID_ARGUMENT, "stp_options_set_args", "argc is negative", 1);
    if (argc > 0 && argv == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_options_set_args", "argv is null", 2);
    for (int i = 0; i < argc; ++i)
      str_arg(argv[i], "stp_options_set_args", 2);
    op.set_args(argc, argv);
  });
}

char* stp_options_get_str(stp_options o, const char* name)
{
  return opts<char*>(o, "stp_options_get_str", nullptr, [&](Options& op) {
    const detail::OptionSpec* spec = spec_arg(name, "stp_options_get_str", 1);
    return dup_string(option_text_of(*spec, op.get(spec->name)));
  });
}

stp_status stp_options_get_bool(stp_options o, const char* name, bool* out)
{
  return opts_status(o, "stp_options_get_bool", [&](Options& op) {
    *out_arg(out, "stp_options_get_bool", 2) = op.get_bool(str_arg(name, "stp_options_get_bool", 1));
  });
}

stp_status stp_options_get_int64(stp_options o, const char* name, int64_t* out)
{
  return opts_status(o, "stp_options_get_int64", [&](Options& op) {
    *out_arg(out, "stp_options_get_int64", 2) = op.get_int(str_arg(name, "stp_options_get_int64", 1));
  });
}

stp_status stp_options_get_uint64(stp_options o, const char* name, uint64_t* out)
{
  return opts_status(o, "stp_options_get_uint64", [&](Options& op) {
    *out_arg(out, "stp_options_get_uint64", 2) =
        op.get_uint(str_arg(name, "stp_options_get_uint64", 1));
  });
}

stp_status stp_options_get_duration_ms(stp_options o, const char* name, uint64_t* out)
{
  return opts_status(o, "stp_options_get_duration_ms", [&](Options& op) {
    *out_arg(out, "stp_options_get_duration_ms", 2) =
        ms_of(op.get_duration(str_arg(name, "stp_options_get_duration_ms", 1)));
  });
}

char* stp_options_resolved_str(stp_options o, const char* name)
{
  return opts<char*>(o, "stp_options_resolved_str", nullptr, [&](Options& op) {
    const detail::OptionSpec* spec = spec_arg(name, "stp_options_resolved_str", 1);
    return dup_string(option_text_of(*spec, op.resolved(spec->name)));
  });
}

bool stp_options_is_set(stp_options o, const char* name)
{
  return opts<bool>(o, "stp_options_is_set", false,
                    [&](Options& op) { return op.is_set(str_arg(name, "stp_options_is_set", 1)); });
}

stp_status stp_options_reset(stp_options o, const char* name)
{
  return opts_status(o, "stp_options_reset",
                     [&](Options& op) { op.reset(str_arg(name, "stp_options_reset", 1)); });
}

void stp_options_reset_all(stp_options o)
{
  opts_status(o, "stp_options_reset_all", [](Options& op) { op.reset_all(); });
}

stp_status stp_options_resolve(stp_options o)
{
  return opts_status(o, "stp_options_resolve", [](Options& op) { op.resolve(); });
}

size_t stp_options_num_names(int tier)
{
  std::size_t count = 0;
  while (nth_spec(tier, count) != nullptr)
    ++count;
  return count;
}

const char* stp_options_name(int tier, size_t i)
{
  const detail::OptionSpec* spec = nth_spec(tier, i);
  return spec == nullptr ? nullptr : spec->name;
}

char* stp_options_help(int tier)
{
  return guarded<char*>(nullptr, nullptr, "stp_options_help", nullptr, [&] {
    if (tier != -1 && (tier < 0 || tier > STP_TIER_DIAGNOSTIC))
      fail(ErrorCode::INVALID_ARGUMENT, "stp_options_help", "not a tier", 0);
    Options op;
    return dup_string(op.help(tier == -1 ? std::nullopt : std::optional<Tier>(static_cast<Tier>(tier))));
  });
}

const char* stp_option_name(stp_option o)
{
  return guarded<const char*>(nullptr, nullptr, "stp_option_name", nullptr,
                              [&] { return stable_spec(o, "stp_option_name", 0)->name; });
}

stp_status stp_option_from_name(const char* name, stp_option* out)
{
  return guarded<stp_status>(nullptr, nullptr, "stp_option_from_name", STP_ERROR, [&] {
    out_arg(out, "stp_option_from_name", 1);
    const detail::OptionSpec* spec = spec_arg(name, "stp_option_from_name", 0);
    const std::optional<Option> o = Options::stable_option(spec->name);
    if (!o.has_value())
      detail::fail_option(ErrorCode::OPTION_UNKNOWN, spec->name, "not a stable-tier option");
    *out = static_cast<stp_option>(*o);
    return STP_OK;
  });
}

const char* stp_option_info_type(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_type");
  return spec == nullptr ? nullptr : type_name(spec->type);
}

const char* stp_option_info_python_key(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_python_key");
  return spec == nullptr ? nullptr : spec->python_key;
}

char* stp_option_info_default(const char* name)
{
  return guarded<char*>(nullptr, nullptr, "stp_option_info_default", nullptr, [&] {
    const detail::OptionSpec* spec = spec_arg(name, "stp_option_info_default", 0);
    return dup_string(option_text_of(*spec, detail::option_default(*spec)));
  });
}

stp_tier stp_option_info_tier(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_tier");
  return spec == nullptr ? STP_TIER_STABLE : static_cast<stp_tier>(spec->tier);
}

stp_settable stp_option_info_settable(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_settable");
  return spec == nullptr ? STP_SETTABLE_ANYTIME : static_cast<stp_settable>(spec->settable);
}

stp_option_scope stp_option_info_scope(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_scope");
  return spec == nullptr ? STP_SCOPE_SOLVER : static_cast<stp_option_scope>(spec->scope);
}

const char* stp_option_info_category(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_category");
  return spec == nullptr ? nullptr : spec->category;
}

const char* stp_option_info_help(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_help");
  return spec == nullptr ? nullptr : spec->help;
}

bool stp_option_info_supported(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_supported");
  return spec != nullptr && detail::option_build_supported(*spec);
}

stp_status stp_option_info_range(const char* name, bool* has_min, int64_t* min, bool* has_max,
                                 int64_t* max)
{
  return guarded<stp_status>(nullptr, nullptr, "stp_option_info_range", STP_ERROR, [&] {
    const detail::OptionSpec* spec = spec_arg(name, "stp_option_info_range", 0);
    out_arg(has_min, "stp_option_info_range", 1);
    out_arg(min, "stp_option_info_range", 2);
    out_arg(has_max, "stp_option_info_range", 3);
    out_arg(max, "stp_option_info_range", 4);
    *has_min = spec->has_min;
    *min = spec->has_min ? spec->min : 0;
    *has_max = spec->has_max;
    *max = spec->has_max ? spec->max : 0;
    return STP_OK;
  });
}

size_t stp_option_info_num_values(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_num_values");
  return spec == nullptr ? 0 : spec->num_values;
}

const char* stp_option_info_value(const char* name, size_t i)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_value");
  return (spec == nullptr || i >= spec->num_values) ? nullptr : spec->values[i];
}

size_t stp_option_info_num_aliases(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_num_aliases");
  return spec == nullptr ? 0 : spec->num_aliases;
}

const char* stp_option_info_alias(const char* name, size_t i)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_alias");
  return (spec == nullptr || i >= spec->num_aliases) ? nullptr : spec->aliases[i];
}

const char* stp_option_info_short(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_short");
  if (spec == nullptr)
    return nullptr;
  return spec->short_flag ? spec->short_flag : "";
}

const char* stp_option_info_negation(const char* name)
{
  const detail::OptionSpec* spec = info_spec(name, "stp_option_info_negation");
  if (spec == nullptr)
    return nullptr;
  return spec->negation ? spec->negation : "";
}

// ============================================================ the live options of a solver

stp_status stp_solver_set_str(stp_solver s, const char* name, const char* value)
{
  return solver_write(s, "stp_solver_set_str", [&](SolverOptions& op) {
    op.set(str_arg(name, "stp_solver_set_str", 1), str_arg(value, "stp_solver_set_str", 2));
  });
}

stp_status stp_solver_set_bool(stp_solver s, const char* name, bool v)
{
  return solver_write(s, "stp_solver_set_bool",
                      [&](SolverOptions& op) { op.set_bool(str_arg(name, "stp_solver_set_bool", 1), v); });
}

stp_status stp_solver_set_int64(stp_solver s, const char* name, int64_t v)
{
  return solver_write(s, "stp_solver_set_int64", [&](SolverOptions& op) {
    op.set_int(str_arg(name, "stp_solver_set_int64", 1), v);
  });
}

stp_status stp_solver_set_uint64(stp_solver s, const char* name, uint64_t v)
{
  return solver_write(s, "stp_solver_set_uint64", [&](SolverOptions& op) {
    op.set_uint(str_arg(name, "stp_solver_set_uint64", 1), v);
  });
}

stp_status stp_solver_set_duration_ms(stp_solver s, const char* name, uint64_t ms)
{
  return solver_write(s, "stp_solver_set_duration_ms", [&](SolverOptions& op) {
    op.set_duration(str_arg(name, "stp_solver_set_duration_ms", 1),
                    ms_arg(ms, "stp_solver_set_duration_ms", 2));
  });
}

stp_status stp_solver_set_names(stp_solver s, const char* name, size_t n, const char* const* members)
{
  return solver_write(s, "stp_solver_set_names", [&](SolverOptions& op) {
    op.set_names(str_arg(name, "stp_solver_set_names", 1),
                 names_arg(n, members, "stp_solver_set_names", 3));
  });
}

stp_status stp_solver_set_bool_e(stp_solver s, stp_option e, bool v)
{
  return solver_write(s, "stp_solver_set_bool_e", [&](SolverOptions& op) {
    op.set_bool(stable_spec(e, "stp_solver_set_bool_e", 1)->name, v);
  });
}

stp_status stp_solver_set_int64_e(stp_solver s, stp_option e, int64_t v)
{
  return solver_write(s, "stp_solver_set_int64_e", [&](SolverOptions& op) {
    op.set_int(stable_spec(e, "stp_solver_set_int64_e", 1)->name, v);
  });
}

stp_status stp_solver_set_uint64_e(stp_solver s, stp_option e, uint64_t v)
{
  return solver_write(s, "stp_solver_set_uint64_e", [&](SolverOptions& op) {
    op.set_uint(stable_spec(e, "stp_solver_set_uint64_e", 1)->name, v);
  });
}

stp_status stp_solver_set_str_e(stp_solver s, stp_option e, const char* v)
{
  return solver_write(s, "stp_solver_set_str_e", [&](SolverOptions& op) {
    op.set_str(stable_spec(e, "stp_solver_set_str_e", 1)->name, str_arg(v, "stp_solver_set_str_e", 2));
  });
}

stp_status stp_solver_set_duration_ms_e(stp_solver s, stp_option e, uint64_t ms)
{
  return solver_write(s, "stp_solver_set_duration_ms_e", [&](SolverOptions& op) {
    op.set_duration(stable_spec(e, "stp_solver_set_duration_ms_e", 1)->name,
                    ms_arg(ms, "stp_solver_set_duration_ms_e", 2));
  });
}

stp_status stp_solver_set_args(stp_solver s, int argc, const char* const* argv)
{
  return solver_write(s, "stp_solver_set_args", [&](SolverOptions& op) {
    if (argc < 0)
      fail(ErrorCode::INVALID_ARGUMENT, "stp_solver_set_args", "argc is negative", 1);
    if (argc > 0 && argv == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_solver_set_args", "argv is null", 2);
    for (int i = 0; i < argc; ++i)
      str_arg(argv[i], "stp_solver_set_args", 2);
    op.set_args(argc, argv);
  });
}

char* stp_solver_get_str(stp_solver s, const char* name)
{
  return solver_read<char*>(s, "stp_solver_get_str", nullptr, [&](const SolverOptions& op) {
    const detail::OptionSpec* spec = spec_arg(name, "stp_solver_get_str", 1);
    return dup_string(option_text_of(*spec, op.get(spec->name)));
  });
}

stp_status stp_solver_get_bool(stp_solver s, const char* name, bool* out)
{
  return solver_read<stp_status>(s, "stp_solver_get_bool", STP_ERROR, [&](const SolverOptions& op) {
    *out_arg(out, "stp_solver_get_bool", 2) = op.get_bool(str_arg(name, "stp_solver_get_bool", 1));
    return STP_OK;
  });
}

stp_status stp_solver_get_int64(stp_solver s, const char* name, int64_t* out)
{
  return solver_read<stp_status>(s, "stp_solver_get_int64", STP_ERROR, [&](const SolverOptions& op) {
    *out_arg(out, "stp_solver_get_int64", 2) = op.get_int(str_arg(name, "stp_solver_get_int64", 1));
    return STP_OK;
  });
}

stp_status stp_solver_get_uint64(stp_solver s, const char* name, uint64_t* out)
{
  return solver_read<stp_status>(s, "stp_solver_get_uint64", STP_ERROR, [&](const SolverOptions& op) {
    *out_arg(out, "stp_solver_get_uint64", 2) = op.get_uint(str_arg(name, "stp_solver_get_uint64", 1));
    return STP_OK;
  });
}

stp_status stp_solver_get_duration_ms(stp_solver s, const char* name, uint64_t* out)
{
  return solver_read<stp_status>(s, "stp_solver_get_duration_ms", STP_ERROR,
                                 [&](const SolverOptions& op) {
                                   *out_arg(out, "stp_solver_get_duration_ms", 2) = ms_of(
                                       op.get_duration(str_arg(name, "stp_solver_get_duration_ms", 1)));
                                   return STP_OK;
                                 });
}

char* stp_solver_resolved_str(stp_solver s, const char* name)
{
  return solver_read<char*>(s, "stp_solver_resolved_str", nullptr, [&](const SolverOptions& op) {
    const detail::OptionSpec* spec = spec_arg(name, "stp_solver_resolved_str", 1);
    return dup_string(option_text_of(*spec, op.resolved(spec->name)));
  });
}

bool stp_solver_option_is_set(stp_solver s, const char* name)
{
  return solver_read<bool>(s, "stp_solver_option_is_set", false, [&](const SolverOptions& op) {
    return op.is_set(str_arg(name, "stp_solver_option_is_set", 1));
  });
}

stp_status stp_solver_reset_option(stp_solver s, const char* name)
{
  return solver_write(s, "stp_solver_reset_option",
                      [&](SolverOptions& op) { op.reset(str_arg(name, "stp_solver_reset_option", 1)); });
}

stp_options stp_solver_options_copy(stp_solver s)
{
  return solver_read<stp_options>(s, "stp_solver_options_copy", nullptr, [&](const SolverOptions& op) {
    return reinterpret_cast<stp_options>(new COptions{op.copy(), ErrorRecord()});
  });
}

} // extern "C"

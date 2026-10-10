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

// Errors.cpp -- the exception classes, the throw helpers and the enum
// spellings of the 3.x API.

#include "Internal.h"

#include <atomic>
#include <cstdlib>
#include <cstring>
#include <new>
#include <ostream>

namespace stp
{
namespace api
{

// ------------------------------------------------------------ enum spellings

namespace
{
struct ErrorSpec
{
  ErrorCode code;
  const char* name;
  bool recoverable;
  const char* message;
  const char* python;
};
const ErrorSpec kErrorSpecs[] = {
#include "gen/error_table.inc"
};

const ErrorSpec* error_spec(ErrorCode code)
{
  for (const ErrorSpec& e : kErrorSpecs)
    if (e.code == code)
      return &e;
  return nullptr;
}
} // namespace

const char* to_string(Kind k)
{
  return detail::kind_spec(k).name;
}

const char* smtlib_name(Kind k)
{
  return detail::kind_spec(k).smtlib;
}

const char* to_string(SortKind k)
{
  switch (k)
  {
    case SortKind::BOOL: return "Bool";
    case SortKind::BV: return "BitVec";
    case SortKind::FP: return "FloatingPoint";
    case SortKind::RM: return "RoundingMode";
    case SortKind::REAL: return "Real";
    case SortKind::ARRAY: return "Array";
    case SortKind::FUN: return "Function";
    case SortKind::UNINTERPRETED: return "Uninterpreted";
  }
  return "?";
}

const char* to_string(RoundingMode rm)
{
  switch (rm)
  {
    case RoundingMode::RNE: return "RNE";
    case RoundingMode::RNA: return "RNA";
    case RoundingMode::RTP: return "RTP";
    case RoundingMode::RTN: return "RTN";
    case RoundingMode::RTZ: return "RTZ";
  }
  return "?";
}

const char* to_string(UnknownReason r)
{
  switch (r)
  {
    case UnknownReason::NONE: return "none";
    case UnknownReason::TIMEOUT: return "timeout";
    case UnknownReason::CONFLICT_LIMIT: return "conflict-limit";
    case UnknownReason::INTERRUPTED: return "interrupted";
    case UnknownReason::INCOMPLETE: return "incomplete";
    case UnknownReason::RESOURCE_LIMIT: return "resource-limit";
    case UnknownReason::CARRIER_EXHAUSTED: return "carrier-exhausted";
    case UnknownReason::ASSUMED_INJECTIVITY: return "assumed-injectivity";
    case UnknownReason::STOPPED_AFTER_CNF: return "stopped-after-cnf";
    case UnknownReason::OTHER: return "other";
  }
  return "?";
}

const char* to_string(ErrorCode c)
{
  const ErrorSpec* e = error_spec(c);
  return e ? e->name : "?";
}

const char* to_string(Verdict v)
{
  switch (v)
  {
    case Verdict::SAT: return "sat";
    case Verdict::UNSAT: return "unsat";
    case Verdict::UNKNOWN: return "unknown";
  }
  return "?";
}

const char* to_string(Validity v)
{
  switch (v)
  {
    case Validity::VALID: return "valid";
    case Validity::INVALID: return "invalid";
    case Validity::UNKNOWN: return "unknown";
  }
  return "?";
}

const char* to_string(Tier t)
{
  switch (t)
  {
    case Tier::STABLE: return "stable";
    case Tier::EXPERT: return "expert";
    case Tier::EXPERIMENTAL: return "experimental";
    case Tier::DIAGNOSTIC: return "diagnostic";
  }
  return "?";
}

const char* to_string(Settable s)
{
  switch (s)
  {
    case Settable::ANYTIME: return "anytime";
    case Settable::BEFORE_FIRST_CHECK: return "before-first-check";
    case Settable::CONSTRUCTION: return "construction";
  }
  return "?";
}

std::ostream& operator<<(std::ostream& os, Kind k) { return os << to_string(k); }
std::ostream& operator<<(std::ostream& os, RoundingMode r) { return os << to_string(r); }
std::ostream& operator<<(std::ostream& os, UnknownReason r) { return os << to_string(r); }
std::ostream& operator<<(std::ostream& os, Verdict v) { return os << to_string(v); }
std::ostream& operator<<(std::ostream& os, Validity v) { return os << to_string(v); }

// ------------------------------------------------------------ Error

Error::Error(std::shared_ptr<const detail::ErrorDetails> d) : d_(std::move(d)) {}
Error::Error(const Error&) noexcept = default;
Error& Error::operator=(const Error&) noexcept = default;
Error::~Error() = default;

ErrorCode Error::code() const noexcept
{
  return d_ ? d_->code : ErrorCode::RESOURCE;
}
bool Error::recoverable() const noexcept
{
  return detail::error_recoverable(code());
}
const char* Error::what() const noexcept
{
  return d_ ? d_->message.c_str() : "resource failure: out of memory [RESOURCE]";
}
std::string_view Error::function() const noexcept
{
  return d_ ? std::string_view(d_->function) : std::string_view();
}
std::optional<int> Error::argument_index() const noexcept
{
  return d_ ? d_->argument_index : std::nullopt;
}
const std::vector<Term>& Error::terms() const noexcept
{
  static const std::vector<Term> empty;
  return d_ ? d_->terms : empty;
}
const std::vector<Sort>& Error::sorts() const noexcept
{
  static const std::vector<Sort> empty;
  return d_ ? d_->sorts : empty;
}
std::string_view Error::option() const noexcept
{
  return d_ ? std::string_view(d_->option) : std::string_view();
}
int Error::line() const noexcept
{
  return d_ ? d_->line : 0;
}
int Error::column() const noexcept
{
  return d_ ? d_->column : 0;
}

// ------------------------------------------------------------ throw helpers

namespace detail
{

const char* error_template(ErrorCode code)
{
  const ErrorSpec* e = error_spec(code);
  return e ? e->message : "{what}";
}

bool error_recoverable(ErrorCode code)
{
  const ErrorSpec* e = error_spec(code);
  return e ? e->recoverable : false;
}

namespace
{
// The policy for the two unsafe codes, process-wide: written from any thread,
// read by every thread that throws.
std::atomic<InternalErrorPolicy> g_policy{[] {
  const char* env = std::getenv("STP_ABORT_ON_INTERNAL_ERROR");
  return (env != nullptr && std::strcmp(env, "1") == 0) ? InternalErrorPolicy::ABORT
                                                        : InternalErrorPolicy::POISON;
}()};

[[noreturn]] void throw_details(std::shared_ptr<ErrorDetails> d)
{
  if (d && error_recoverable(d->code))
    throw RecoverableError(std::move(d));
  if (g_policy == InternalErrorPolicy::ABORT)
  {
    std::fputs(UnsafeError(d).what(), stderr);
    std::fputc('\n', stderr);
    std::abort();
  }
  throw UnsafeError(std::move(d));
}
} // namespace

void fail(ErrorCode code, const char* fn, const std::string& what,
          std::optional<int> arg, std::vector<Term> terms, std::vector<Sort> sorts,
          const std::string& option)
{
  auto d = std::make_shared<ErrorDetails>();
  d->code = code;
  d->function = fn ? fn : "";
  d->argument_index = arg;
  d->terms = std::move(terms);
  d->sorts = std::move(sorts);
  d->option = option;
  d->message = std::string("invalid call to '") + d->function + "': " + what;
  if (arg.has_value())
    d->message += " (argument " + std::to_string(*arg) + ")";
  d->message += " [" + std::string(to_string(code)) + "]";
  throw_details(std::move(d));
}

void fail_option(ErrorCode code, const std::string& option, const std::string& what)
{
  auto d = std::make_shared<ErrorDetails>();
  d->code = code;
  d->function = "Options";
  d->option = option;
  d->message = "option '" + option + "': " + what + " [" + to_string(code) + "]";
  throw_details(std::move(d));
}

void fail_parse(const char* fn, int line, int column, const std::string& what)
{
  auto d = std::make_shared<ErrorDetails>();
  d->code = ErrorCode::PARSE;
  d->function = fn ? fn : "";
  d->line = line;
  d->column = column;
  d->message = "parse error";
  if (line > 0)
    d->message += " at " + std::to_string(line) + ":" + std::to_string(column);
  d->message += ": " + what + " [PARSE]";
  throw_details(std::move(d));
}

void fail_internal(const char* fn, const std::string& what)
{
  auto d = std::make_shared<ErrorDetails>();
  d->code = ErrorCode::INTERNAL;
  d->function = fn ? fn : "";
  d->message = std::string("internal error in '") + d->function + "': " + what +
               "; please report it [INTERNAL]";
  throw_details(std::move(d));
}

void fail_resource(const char* fn, const char* what)
{
  std::shared_ptr<ErrorDetails> d;
  try
  {
    d = std::make_shared<ErrorDetails>();
    d->code = ErrorCode::RESOURCE;
    d->function = fn ? fn : "";
    d->message = std::string("resource failure in '") + d->function + "': " + what +
                 " [RESOURCE]";
  }
  catch (const std::bad_alloc&)
  {
    // A null record is the allocation-free RESOURCE error. Reporting an
    // exhausted heap must not require another successful allocation.
    d.reset();
  }
  throw_details(std::move(d));
}

} // namespace detail

void set_internal_error_policy(InternalErrorPolicy p) noexcept
{
  detail::g_policy = p;
}

InternalErrorPolicy internal_error_policy() noexcept
{
  return detail::g_policy;
}

} // namespace api
} // namespace stp

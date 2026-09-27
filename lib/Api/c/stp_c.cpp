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

// stp_c.cpp -- the C layer's runtime (managers, reference counts, scopes,
// the error record), the library queries, and the term side of <stp/stp.h>:
// sorts, symbols, values, construction, introspection and the typed readers.
// The solver, model and statistics functions are in stp_c_solver.cpp, the
// options functions in stp_c_options.cpp.

#include "stp_c_internal.h"

#include <cstdlib>
#include <cstring>
#include <mutex>

namespace stp
{
namespace api
{
namespace capi
{

// ============================================================ errors

namespace
{
// The one message that must never allocate: the fallback of every record.
const char kOutOfMemory[] = "out of memory while recording an error [RESOURCE]";

std::string compose(ErrorCode code, const char* fn, const char* what, int arg)
{
  std::string m = std::string("invalid call to '") + (fn ? fn : "") + "': " + (what ? what : "");
  if (arg >= 0)
    m += " (argument " + std::to_string(arg) + ")";
  m += std::string(" [") + to_string(code) + "]";
  return m;
}
} // namespace

void ErrorRecord::clear() noexcept
{
  pending = false;
  terms.clear();
  message.clear();
  option.clear();
  view = stp_error{};
}

void ErrorRecord::set(ErrorCode code, const char* fn, const std::string& msg, int arg,
                      const std::string& opt, const std::vector<Term>& ts) noexcept
{
  // fn is always one of this layer's string literals, so the view can point
  // at it directly and the record holds copies of the message and option only
  pending = true;
  view.code = static_cast<stp_error_code>(code);
  view.recoverable = detail::error_recoverable(code);
  view.function = fn ? fn : "";
  view.argument_index = arg;
  try
  {
    message = msg;
    option = opt;
    terms = ts;
    view.message = message.c_str();
    view.option = option.empty() ? nullptr : option.c_str();
  }
  catch (...)
  {
    terms.clear();
    view.code = STP_ERR_RESOURCE;
    view.recoverable = false;
    view.message = kOutOfMemory;
    view.option = nullptr;
  }
}

void ErrorRecord::set(const char* fn, const Error& e) noexcept
{
  set(e.code(), fn, e.what(), e.argument_index().value_or(-1), std::string(e.option()),
      e.terms());
}

void ErrorRecord::assign(const ErrorRecord& o) noexcept
{
  // o.view.function is one of this layer's literals, so the pointer copies
  set(static_cast<ErrorCode>(o.view.code), o.view.function, o.message, o.view.argument_index,
      o.option, o.terms);
}

ErrorRecord& thread_error() noexcept
{
  static thread_local ErrorRecord record;
  return record;
}

namespace
{
ErrorRecord* target_of(CManager* cm, ErrorRecord* rec) noexcept
{
  if (rec != nullptr)
    return rec;
  if (cm != nullptr)
    return &cm->error;
  return &thread_error();
}

void deliver(CManager* cm, const ErrorRecord& cur) noexcept
{
  if (cm != nullptr && cm->callback != nullptr)
    cm->callback(&cur.view, cm->callback_user);
}
} // namespace

void report(CManager* cm, ErrorRecord* rec, const char* fn, const Error& e) noexcept
{
  ErrorRecord* target = target_of(cm, rec);
  // an object's record keeps the first error since its clear; the thread-local
  // record, which nothing clears, is the LAST error of an object-less call
  const bool last_wins = target == &thread_error();
  if (!target->pending || last_wins)
  {
    target->set(fn, e);
    // the thread-local record must never pin a manager through its terms
    if (last_wins)
      target->terms.clear();
  }
  if (cm != nullptr && cm->callback != nullptr)
  {
    ErrorRecord cur;
    cur.set(fn, e);
    deliver(cm, cur);
  }
}

void report_code(CManager* cm, ErrorRecord* rec, const char* fn, ErrorCode code, const char* what,
                 int arg) noexcept
{
  ErrorRecord* target = target_of(cm, rec);
  ErrorRecord cur;
  try
  {
    cur.set(code, fn, compose(code, fn, what, arg), arg, "", {});
  }
  catch (...)
  {
    cur.set(code, fn, "", arg, "", {}); // falls back to the static text inside
  }
  if (!target->pending || target == &thread_error())
    target->set(code, fn, cur.message, arg, "", {});
  deliver(cm, cur);
}

void poison_on_engine_failure(CManager* cm, const char* fn, const char* what) noexcept
{
  if (cm == nullptr || cm->impl == nullptr || cm->impl->poisoned)
    return;
  try
  {
    cm->impl->poison_message = std::string("an engine failure in ") + (fn ? fn : "") + " (" +
                               what + ") may have left its state inconsistent";
  }
  catch (...)
  {
    // out of memory: the flag alone still refuses every later call
  }
  cm->impl->poisoned = true;
}

// ============================================================ managers

namespace
{
// STPMgr* -> CManager*, for the calls that receive a term and nothing else.
// A live handle always resolves: a CManager dies only when no handle holds
// a reference on it, and its entry goes first.
struct Registry
{
  std::mutex mu;
  std::unordered_map<STPMgr*, CManager*> by_bm;
};
Registry& registry()
{
  static Registry r;
  return r;
}

void destroy(CManager* cm) noexcept
{
  {
    std::lock_guard<std::mutex> hold(registry().mu);
    registry().by_bm.erase(cm->bm);
  }
  // refs == 0 means no unscoped reference and no open scope survive, so the
  // journals and the count table are empty; the record's terms and the sort
  // pool go before the manager reference they depend on
  cm->error.clear();
  cm->sorts.clear();
  detail::ManagerImpl* impl = cm->impl;
  delete cm;
  impl->release();
}
} // namespace

CManager* cm_new(const TermManager& tm)
{
  std::unique_ptr<CManager> cm(new CManager());
  cm->impl = tm.impl();
  cm->bm = cm->impl->bm;
  cm->refs = 1;
  {
    std::lock_guard<std::mutex> hold(registry().mu);
    registry().by_bm[cm->bm] = cm.get();
  }
  cm->impl->retain();
  return cm.release();
}

CManager* cm_retain(CManager* cm) noexcept
{
  ++cm->refs;
  return cm;
}

void cm_release(CManager* cm) noexcept
{
  if (--cm->refs == 0)
    destroy(cm);
}

CManager* cm_of_node(ASTInternal* p) noexcept
{
  if (p == nullptr)
    return nullptr;
  STPMgr* bm = detail::NodeAccess::wrap(p).GetNodeManager();
  std::lock_guard<std::mutex> hold(registry().mu);
  auto it = registry().by_bm.find(bm);
  return it == registry().by_bm.end() ? nullptr : it->second;
}

// ============================================================ exports and arguments

stp_term export_term(CManager* cm, const Term& t)
{
  ASTInternal* p = detail::internal_of(t);
  if (p == nullptr)
    return nullptr;
  if (!cm->scopes.empty())
  {
    // the journal's ASTNode is the scoped reference
    cm->scopes.back().push_back(detail::node_of(t));
    return handle(p);
  }
  auto it = cm->unscoped.find(p);
  if (it == cm->unscoped.end())
    cm->unscoped.emplace(p, 1u); // the one operation that can throw, before any count moves
  else
    ++it->second;
  detail::NodeAccess::retain(p);
  ++cm->refs;
  return handle(p);
}

stp_sort export_sort(CManager* cm, const Sort& s)
{
  if (s.is_null())
    return nullptr;
  const std::uint32_t index = s.impl_index();
  if (index >= cm->sorts.size())
    cm->sorts.resize(index + 1);
  if (!cm->sorts[index])
    cm->sorts[index].reset(new CSort{cm, index});
  return reinterpret_cast<stp_sort>(cm->sorts[index].get());
}

stp_tm export_tm(CManager* cm) noexcept
{
  return tm_of(cm_retain(cm));
}

Term term_arg(CManager* cm, stp_term t, const char* fn, int arg)
{
  if (t == nullptr)
    throw NullArgument{};
  ASTInternal* p = raw(t);
  if (detail::NodeAccess::wrap(p).GetNodeManager() != cm->bm)
  {
    std::vector<Term> involved;
    if (CManager* other = cm_of_node(p))
      involved.emplace_back(other->impl, p);
    detail::fail(ErrorCode::FOREIGN_MANAGER, fn, "the term belongs to another term manager", arg,
                 involved);
  }
  return Term(cm->impl, p);
}

Sort sort_arg(CManager* cm, stp_sort s, const char* fn, int arg)
{
  if (s == nullptr)
    throw NullArgument{};
  CSort* cs = csort(s);
  if (cs->cm != cm)
    detail::fail(ErrorCode::FOREIGN_MANAGER, fn, "the sort belongs to another term manager", arg);
  return Sort(cm->impl, cs->index);
}

std::vector<Term> term_args(CManager* cm, std::size_t n, const stp_term* args, const char* fn, int arg)
{
  std::vector<Term> out;
  if (n == 0)
    return out;
  if (args == nullptr)
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the argument array is null", arg);
  out.reserve(n);
  for (std::size_t i = 0; i < n; ++i)
    out.push_back(term_arg(cm, args[i], fn, arg));
  return out;
}

const char* str_arg(const char* s, const char* fn, int arg)
{
  if (s == nullptr)
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the string is null", arg);
  return s;
}

bool term_ref(stp_term t, const char* fn, TermRef& out) noexcept
{
  if (t == nullptr)
    return false;
  ASTInternal* p = raw(t);
  CManager* cm = cm_of_node(p);
  if (cm == nullptr)
  {
    report_code(nullptr, nullptr, fn, ErrorCode::STATE,
                "the term's manager is not known to the C layer (was it released?)", 0);
    return false;
  }
  out.cm = cm;
  out.term = Term(cm->impl, p);
  return true;
}

char* dup_string(const std::string& s)
{
  char* out = static_cast<char*>(std::malloc(s.size() + 1));
  if (out == nullptr)
    throw std::bad_alloc();
  std::memcpy(out, s.c_str(), s.size() + 1);
  return out;
}

char* dup_string(const char* s)
{
  return dup_string(std::string(s ? s : ""));
}

RoundingMode rm_arg(stp_rm rm, const char* fn, int arg)
{
  if (static_cast<unsigned>(rm) > static_cast<unsigned>(STP_RM_RTZ))
    detail::fail(ErrorCode::INVALID_ARGUMENT, fn, "not a rounding mode", arg);
  return static_cast<RoundingMode>(rm);
}

Format format_arg(stp_format f, const char* fn, int arg)
{
  if (static_cast<unsigned>(f) > static_cast<unsigned>(STP_FORMAT_GDL))
    detail::fail(ErrorCode::INVALID_ARGUMENT, fn, "not a format", arg);
  return static_cast<Format>(f);
}

Kind kind_arg(stp_kind k, const char* fn, int arg)
{
  if (static_cast<unsigned>(k) >= static_cast<unsigned>(STP_NUM_KINDS))
    detail::fail(ErrorCode::INVALID_ARGUMENT, fn, "not a kind", arg);
  return static_cast<stp::api::Kind>(k);
}

void to_c(const FloatValue& v, stp_float_value* out) noexcept
{
  out->exp_size = v.exp_size;
  out->sig_size = v.sig_size;
  out->sign = v.sign;
  out->biased_exponent = v.biased_exponent;
  out->cls = static_cast<stp_fp_class>(v.cls);
}

std::optional<CheckBudget> budget_arg(const stp_budget* b)
{
  if (b == nullptr)
    return std::nullopt;
  CheckBudget out;
  if (b->has_time)
    out.time = std::chrono::milliseconds(static_cast<std::int64_t>(b->time_ms));
  if (b->has_conflicts)
    out.conflicts = b->conflicts;
  return out;
}

// The enums this layer declares by hand must agree with the C++ ones they mirror.
static_assert(static_cast<int>(SortKind::UNINTERPRETED) == STP_SORT_UNINTERPRETED, "sort kinds");
static_assert(static_cast<int>(RoundingMode::RTZ) == STP_RM_RTZ, "rounding modes");
static_assert(static_cast<int>(Verdict::UNKNOWN) == STP_UNKNOWN, "verdicts");
static_assert(static_cast<int>(Validity::UNKNOWN) == STP_UNKNOWN_VALIDITY, "validity");
static_assert(static_cast<int>(UnknownReason::OTHER) == STP_REASON_OTHER, "reasons");
static_assert(static_cast<int>(Format::GDL) == STP_FORMAT_GDL, "formats");
static_assert(static_cast<int>(ParseMode::EXECUTE) == STP_PARSE_EXECUTE, "parse modes");
static_assert(static_cast<int>(Tier::DIAGNOSTIC) == STP_TIER_DIAGNOSTIC, "tiers");
static_assert(static_cast<int>(Settable::CONSTRUCTION) == STP_SETTABLE_CONSTRUCTION, "settable");
static_assert(static_cast<int>(OptionScope::MANAGER) == STP_SCOPE_MANAGER, "scopes");
static_assert(static_cast<int>(FloatValue::Class::NOT_A_NUMBER) == STP_FP_NAN, "fp classes");
static_assert(static_cast<int>(InternalErrorPolicy::ABORT) == STP_ABORT, "policies");
static_assert(static_cast<int>(ErrorCode::INTERNAL) == STP_ERR_INTERNAL, "error codes");
static_assert(static_cast<int>(Kind::REAL_GE) + 1 == STP_NUM_KINDS, "kinds");

} // namespace capi
} // namespace api
} // namespace stp

using namespace stp::api;
using namespace stp::api::capi;
using stp::api::detail::fail;
using stp::ASTInternal;

// Every function below is one guarded body. The manager-taking ones name the
// manager first so that a NULL manager is NULL_HANDLE in the thread-local
// record; the term-only ones resolve their manager through term_ref.

namespace
{
// A NULL object handle: NULL_HANDLE into the thread-local record.
bool need(const void* p, const char* fn, int arg = 0) noexcept
{
  if (p != nullptr)
    return true;
  report_code(nullptr, nullptr, fn, ErrorCode::NULL_HANDLE, "the handle is null", arg);
  return false;
}

TermManager tmh(CManager* cm)
{
  return TermManager(cm->impl);
}

// The exported form of an indexed constructor's result.
template <class F>
stp_term make(stp_tm tm, const char* fn, F&& f) noexcept
{
  if (!need(tm, fn))
    return nullptr;
  CManager* cm = cm_of(tm);
  return guarded<stp_term>(cm, nullptr, fn, nullptr, [&] { return export_term(cm, f(cm)); });
}

template <class F>
stp_sort make_sort(stp_tm tm, const char* fn, F&& f) noexcept
{
  if (!need(tm, fn))
    return nullptr;
  CManager* cm = cm_of(tm);
  return guarded<stp_sort>(cm, nullptr, fn, nullptr, [&] { return export_sort(cm, f(cm)); });
}

// A term-only call returning a status through an out-pointer.
template <class F>
stp_status term_status(stp_term t, const char* fn, F&& f) noexcept
{
  TermRef r;
  if (!term_ref(t, fn, r))
    return STP_ERROR;
  return guarded<stp_status>(r.cm, nullptr, fn, STP_ERROR, [&] {
    f(r);
    return STP_OK;
  });
}

template <class F>
char* term_string(stp_term t, const char* fn, F&& f) noexcept
{
  TermRef r;
  if (!term_ref(t, fn, r))
    return nullptr;
  return guarded<char*>(r.cm, nullptr, fn, nullptr, [&] { return dup_string(f(r)); });
}

template <class F>
stp_term term_term(stp_term t, const char* fn, F&& f) noexcept
{
  TermRef r;
  if (!term_ref(t, fn, r))
    return nullptr;
  return guarded<stp_term>(r.cm, nullptr, fn, nullptr, [&] { return export_term(r.cm, f(r)); });
}

// The static spellings of the library-level tables.
const std::vector<std::string>& backend_names()
{
  static const std::vector<std::string> names = sat_backends();
  return names;
}

const Version& cached_version()
{
  static const Version v = version();
  return v;
}

void copy_limbs(const std::vector<std::uint64_t>& limbs, std::size_t n, std::uint64_t* out,
                const char* fn)
{
  out_arg(out, fn, 2);
  if (n < limbs.size())
    fail(ErrorCode::INVALID_ARGUMENT, fn,
         "the buffer holds " + std::to_string(n) + " limbs, " + std::to_string(limbs.size()) +
             " are needed",
         1);
  for (std::size_t i = 0; i < limbs.size(); ++i)
    out[i] = limbs[i];
}

void copy_bytes(const std::vector<std::uint8_t>& bytes, std::size_t n, std::uint8_t* out,
                const char* fn)
{
  out_arg(out, fn, 2);
  if (n < bytes.size())
    fail(ErrorCode::INVALID_ARGUMENT, fn,
         "the buffer holds " + std::to_string(n) + " bytes, " + std::to_string(bytes.size()) +
             " are needed",
         1);
  for (std::size_t i = 0; i < bytes.size(); ++i)
    out[i] = bytes[i];
}

double fp_double_of(const FloatValue& v, const char* fn)
{
  const std::optional<double> d = v.to_double();
  if (!d.has_value())
    fail(ErrorCode::DOES_NOT_FIT, fn, "the format is wider than binary64", 0);
  return *d;
}
} // namespace

namespace
{
template <class F>
stp_status sort_status(stp_sort s, const char* fn, F&& f) noexcept
{
  if (s == nullptr)
    return STP_ERROR;
  CSort* cs = csort(s);
  return guarded<stp_status>(cs->cm, nullptr, fn, STP_ERROR, [&] {
    f(Sort(cs->cm->impl, cs->index));
    return STP_OK;
  });
}

template <class F>
stp_sort sort_sort(stp_sort s, const char* fn, F&& f) noexcept
{
  if (s == nullptr)
    return nullptr;
  CSort* cs = csort(s);
  return guarded<stp_sort>(cs->cm, nullptr, fn, nullptr,
                           [&] { return export_sort(cs->cm, f(Sort(cs->cm->impl, cs->index))); });
}
} // namespace

extern "C" {

// ============================================================ library

stp_version stp_get_version(void)
{
  stp_version out;
  out.major = out.minor = out.patch = 0;
  out.string = out.git_sha = out.git_tag = out.build_info = "";
  try
  {
    const Version& v = cached_version();
    out.major = v.major;
    out.minor = v.minor;
    out.patch = v.patch;
    out.string = v.string.c_str();
    out.git_sha = v.git_sha.c_str();
    out.git_tag = v.git_tag.c_str();
    out.build_info = v.build_info.c_str();
  }
  catch (...)
  {
    // the empty strings stand
  }
  return out;
}

char* stp_capability(const char* key)
{
  return guarded<char*>(nullptr, nullptr, "stp_capability", nullptr, [&] {
    str_arg(key, "stp_capability", 0);
    const std::map<std::string, std::string> caps = capabilities();
    auto it = caps.find(key);
    return it == caps.end() ? nullptr : dup_string(it->second);
  });
}

char* stp_capabilities(void)
{
  return guarded<char*>(nullptr, nullptr, "stp_capabilities", nullptr, [&] {
    std::string out;
    for (const auto& kv : capabilities())
      out += kv.first + "=" + kv.second + "\n";
    return dup_string(out);
  });
}

bool stp_has_sat_backend(const char* name)
{
  return guarded<bool>(nullptr, nullptr, "stp_has_sat_backend", false, [&] {
    str_arg(name, "stp_has_sat_backend", 0);
    return has_sat_backend(name);
  });
}

size_t stp_num_sat_backends(void)
{
  return guarded<size_t>(nullptr, nullptr, "stp_num_sat_backends", 0,
                         [&] { return backend_names().size(); });
}

const char* stp_sat_backend_name(size_t i)
{
  return guarded<const char*>(nullptr, nullptr, "stp_sat_backend_name", nullptr, [&] {
    const std::vector<std::string>& names = backend_names();
    return i < names.size() ? names[i].c_str() : nullptr;
  });
}

void stp_free(void* p)
{
  std::free(p);
}

const stp_error* stp_last_error(void)
{
  ErrorRecord& r = thread_error();
  return r.pending ? &r.view : nullptr;
}

void stp_set_internal_error_policy(stp_internal_error_policy p)
{
  set_internal_error_policy(p == STP_ABORT ? InternalErrorPolicy::ABORT
                                            : InternalErrorPolicy::POISON);
}

stp_internal_error_policy stp_get_internal_error_policy(void)
{
  return internal_error_policy() == InternalErrorPolicy::ABORT ? STP_ABORT : STP_POISON;
}

const char* stp_kind_name(stp_kind k)
{
  if (static_cast<unsigned>(k) >= static_cast<unsigned>(STP_NUM_KINDS))
    return "?";
  return to_string(static_cast<stp::api::Kind>(k));
}

const char* stp_kind_smtlib(stp_kind k)
{
  if (static_cast<unsigned>(k) >= static_cast<unsigned>(STP_NUM_KINDS))
    return "?";
  return smtlib_name(static_cast<stp::api::Kind>(k));
}

const char* stp_rm_name(stp_rm rm)
{
  if (static_cast<unsigned>(rm) > static_cast<unsigned>(STP_RM_RTZ))
    return "?";
  return to_string(static_cast<RoundingMode>(rm));
}

const char* stp_unknown_reason_name(stp_unknown_reason r)
{
  if (static_cast<unsigned>(r) > static_cast<unsigned>(STP_REASON_OTHER))
    return "?";
  return to_string(static_cast<UnknownReason>(r));
}

const char* stp_error_code_name(stp_error_code c)
{
  return to_string(static_cast<ErrorCode>(c)); // "?" for an unknown code
}

const char* stp_result_kind_name(stp_result_kind k)
{
  if (k < STP_SAT || k > STP_UNKNOWN)
    return "?";
  return to_string(static_cast<Verdict>(k));
}

const char* stp_validity_name(stp_validity v)
{
  if (v < STP_VALID || v > STP_UNKNOWN_VALIDITY)
    return "?";
  return to_string(static_cast<Validity>(v));
}

// ============================================================ term manager

stp_tm stp_tm_new(stp_options manager_options)
{
  return guarded<stp_tm>(nullptr, nullptr, "stp_tm_new", nullptr, [&] {
    TermManager tm = manager_options == nullptr ? TermManager()
                                                : TermManager(coptions(manager_options)->options);
    return tm_of(cm_new(tm));
  });
}

stp_tm stp_tm_new_with(bool simplify, stp_rm default_rounding_mode, uint32_t uf_sort_width)
{
  return guarded<stp_tm>(nullptr, nullptr, "stp_tm_new_with", nullptr, [&] {
    TermManager::Config cfg;
    cfg.simplify = simplify;
    cfg.default_rounding_mode = rm_arg(default_rounding_mode, "stp_tm_new_with", 1);
    if (uf_sort_width == 0)
      fail(ErrorCode::INVALID_ARGUMENT, "stp_tm_new_with", "uf_sort_width must be positive", 2);
    cfg.uf_sort_width = uf_sort_width;
    TermManager tm(cfg);
    return tm_of(cm_new(tm));
  });
}

stp_tm stp_tm_copy(stp_tm tm)
{
  if (!need(tm, "stp_tm_copy"))
    return nullptr;
  return export_tm(cm_of(tm));
}

void stp_tm_release(stp_tm tm)
{
  if (tm != nullptr)
    cm_release(cm_of(tm));
}

uint64_t stp_tm_id(stp_tm tm)
{
  return tm == nullptr ? 0 : cm_of(tm)->impl->id;
}

bool stp_tm_simplify_enabled(stp_tm tm)
{
  return tm != nullptr && cm_of(tm)->impl->config.simplify;
}

stp_rm stp_tm_default_rounding_mode(stp_tm tm)
{
  if (tm == nullptr)
    return STP_RM_RNE;
  return static_cast<stp_rm>(cm_of(tm)->impl->config.default_rounding_mode);
}

stp_status stp_tm_set_default_rounding_mode(stp_tm tm, stp_rm rm)
{
  if (!need(tm, "stp_tm_set_default_rounding_mode"))
    return STP_ERROR;
  CManager* cm = cm_of(tm);
  return guarded<stp_status>(cm, nullptr, "stp_tm_set_default_rounding_mode", STP_ERROR, [&] {
    tmh(cm).set_default_rounding_mode(rm_arg(rm, "stp_tm_set_default_rounding_mode", 1));
    return STP_OK;
  });
}

uint32_t stp_tm_uf_sort_width(stp_tm tm)
{
  return tm == nullptr ? 0 : cm_of(tm)->impl->config.uf_sort_width;
}

// ---------------------------------------------------------- reclamation

void stp_tm_scope_push(stp_tm tm)
{
  if (tm == nullptr)
    return;
  CManager* cm = cm_of(tm);
  try
  {
    cm->scopes.emplace_back();
    ++cm->refs; // an open scope keeps the manager alive for its handles
  }
  catch (...)
  {
    report_code(cm, nullptr, "stp_tm_scope_push", ErrorCode::RESOURCE, "out of memory");
  }
}

void stp_tm_scope_pop(stp_tm tm)
{
  if (tm == nullptr)
    return;
  CManager* cm = cm_of(tm);
  if (cm->scopes.empty())
    return;
  cm->scopes.pop_back(); // the journal's ASTNodes release their engine references
  cm_release(cm);
}

size_t stp_tm_scope_depth(stp_tm tm)
{
  return tm == nullptr ? 0 : cm_of(tm)->scopes.size();
}

void stp_tm_release_all(stp_tm tm)
{
  if (tm == nullptr)
    return;
  CManager* cm = cm_of(tm);
  long released = 0;
  for (const auto& entry : cm->unscoped)
    for (std::uint32_t i = 0; i < entry.second; ++i)
    {
      stp::api::detail::NodeAccess::release(entry.first);
      ++released;
    }
  cm->unscoped.clear();
  for (std::vector<ASTNode>& journal : cm->scopes)
    journal.clear();
  // the caller's tm handle keeps refs above zero here
  cm->refs -= released;
}

// ---------------------------------------------------------- errors

const stp_error* stp_tm_error(stp_tm tm)
{
  if (tm == nullptr)
    return nullptr;
  CManager* cm = cm_of(tm);
  return cm->error.pending ? &cm->error.view : nullptr;
}

size_t stp_tm_error_num_terms(stp_tm tm)
{
  if (tm == nullptr)
    return 0;
  CManager* cm = cm_of(tm);
  return cm->error.pending ? cm->error.terms.size() : 0;
}

stp_term stp_tm_error_term(stp_tm tm, size_t i)
{
  if (!need(tm, "stp_tm_error_term"))
    return nullptr;
  CManager* cm = cm_of(tm);
  return guarded<stp_term>(cm, nullptr, "stp_tm_error_term", nullptr, [&] {
    if (!cm->error.pending || i >= cm->error.terms.size())
      fail(ErrorCode::INDEX_OUT_OF_RANGE, "stp_tm_error_term",
           "index " + std::to_string(i) + " out of range [0, " +
               std::to_string(cm->error.pending ? cm->error.terms.size() : 0) + ")",
           1);
    return export_term(cm, cm->error.terms[i]);
  });
}

void stp_tm_clear_error(stp_tm tm)
{
  if (tm != nullptr)
    cm_of(tm)->error.clear();
}

void stp_tm_set_error_callback(stp_tm tm, stp_error_callback cb, void* user)
{
  if (tm == nullptr)
    return;
  cm_of(tm)->callback = cb;
  cm_of(tm)->callback_user = user;
}

// ============================================================ sorts

stp_sort stp_mk_bool_sort(stp_tm tm)
{
  return make_sort(tm, "stp_mk_bool_sort", [](CManager* cm) { return tmh(cm).mk_bool_sort(); });
}

stp_sort stp_mk_bv_sort(stp_tm tm, uint32_t width)
{
  return make_sort(tm, "stp_mk_bv_sort", [&](CManager* cm) { return tmh(cm).mk_bv_sort(width); });
}

stp_sort stp_mk_fp_sort(stp_tm tm, uint32_t exp_size, uint32_t sig_size)
{
  return make_sort(tm, "stp_mk_fp_sort",
                   [&](CManager* cm) { return tmh(cm).mk_fp_sort(exp_size, sig_size); });
}

stp_sort stp_mk_fp16_sort(stp_tm tm)
{
  return make_sort(tm, "stp_mk_fp16_sort", [](CManager* cm) { return tmh(cm).mk_fp16_sort(); });
}

stp_sort stp_mk_fp32_sort(stp_tm tm)
{
  return make_sort(tm, "stp_mk_fp32_sort", [](CManager* cm) { return tmh(cm).mk_fp32_sort(); });
}

stp_sort stp_mk_fp64_sort(stp_tm tm)
{
  return make_sort(tm, "stp_mk_fp64_sort", [](CManager* cm) { return tmh(cm).mk_fp64_sort(); });
}

stp_sort stp_mk_fp128_sort(stp_tm tm)
{
  return make_sort(tm, "stp_mk_fp128_sort", [](CManager* cm) { return tmh(cm).mk_fp128_sort(); });
}

stp_sort stp_mk_rm_sort(stp_tm tm)
{
  return make_sort(tm, "stp_mk_rm_sort", [](CManager* cm) { return tmh(cm).mk_rm_sort(); });
}

stp_sort stp_mk_real_sort(stp_tm tm)
{
  return make_sort(tm, "stp_mk_real_sort", [](CManager* cm) { return tmh(cm).mk_real_sort(); });
}

stp_sort stp_mk_array_sort(stp_tm tm, stp_sort index, stp_sort element)
{
  return make_sort(tm, "stp_mk_array_sort", [&](CManager* cm) {
    return tmh(cm).mk_array_sort(sort_arg(cm, index, "stp_mk_array_sort", 1),
                                 sort_arg(cm, element, "stp_mk_array_sort", 2));
  });
}

stp_sort stp_mk_fun_sort(stp_tm tm, size_t arity, const stp_sort* domain, stp_sort codomain)
{
  return make_sort(tm, "stp_mk_fun_sort", [&](CManager* cm) {
    if (arity > 0 && domain == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_mk_fun_sort", "the domain array is null", 2);
    std::vector<Sort> dom;
    dom.reserve(arity);
    for (std::size_t i = 0; i < arity; ++i)
      dom.push_back(sort_arg(cm, domain[i], "stp_mk_fun_sort", 2));
    return tmh(cm).mk_fun_sort(dom, sort_arg(cm, codomain, "stp_mk_fun_sort", 3));
  });
}

stp_sort stp_tm_declare_sort(stp_tm tm, const char* name)
{
  return make_sort(tm, "stp_tm_declare_sort", [&](CManager* cm) {
    return tmh(cm).declare_sort(str_arg(name, "stp_tm_declare_sort", 1));
  });
}

stp_sort stp_mk_fresh_sort(stp_tm tm, const char* prefix)
{
  return make_sort(tm, "stp_mk_fresh_sort",
                   [&](CManager* cm) { return tmh(cm).mk_fresh_sort(prefix ? prefix : ""); });
}

stp_sort stp_sort_copy(stp_sort s)
{
  return s;
}

void stp_sort_release(stp_sort)
{
  // sorts are owned by their manager's pool
}


stp_status stp_sort_get_kind(stp_sort s, stp_sort_kind* out)
{
  return sort_status(s, "stp_sort_get_kind", [&](const Sort& so) {
    *out_arg(out, "stp_sort_get_kind", 1) = static_cast<stp_sort_kind>(so.kind());
  });
}

stp_status stp_sort_bv_size(stp_sort s, uint32_t* out)
{
  return sort_status(s, "stp_sort_bv_size",
                     [&](const Sort& so) { *out_arg(out, "stp_sort_bv_size", 1) = so.bv_size(); });
}

stp_status stp_sort_fp_exp_size(stp_sort s, uint32_t* out)
{
  return sort_status(s, "stp_sort_fp_exp_size", [&](const Sort& so) {
    *out_arg(out, "stp_sort_fp_exp_size", 1) = so.fp_exp_size();
  });
}

stp_status stp_sort_fp_sig_size(stp_sort s, uint32_t* out)
{
  return sort_status(s, "stp_sort_fp_sig_size", [&](const Sort& so) {
    *out_arg(out, "stp_sort_fp_sig_size", 1) = so.fp_sig_size();
  });
}

stp_sort stp_sort_array_index(stp_sort s)
{
  return sort_sort(s, "stp_sort_array_index", [](const Sort& so) { return so.array_index(); });
}

stp_sort stp_sort_array_element(stp_sort s)
{
  return sort_sort(s, "stp_sort_array_element", [](const Sort& so) { return so.array_element(); });
}

stp_status stp_sort_fun_arity(stp_sort s, uint32_t* out)
{
  return sort_status(s, "stp_sort_fun_arity", [&](const Sort& so) {
    *out_arg(out, "stp_sort_fun_arity", 1) = so.fun_arity();
  });
}

stp_sort stp_sort_fun_domain(stp_sort s, uint32_t i)
{
  return sort_sort(s, "stp_sort_fun_domain", [&](const Sort& so) {
    const std::vector<Sort> dom = so.fun_domain();
    if (i >= dom.size())
      fail(ErrorCode::INDEX_OUT_OF_RANGE, "stp_sort_fun_domain",
           "index " + std::to_string(i) + " out of range [0, " + std::to_string(dom.size()) + ")",
           1);
    return dom[i];
  });
}

stp_sort stp_sort_fun_codomain(stp_sort s)
{
  return sort_sort(s, "stp_sort_fun_codomain", [](const Sort& so) { return so.fun_codomain(); });
}

char* stp_sort_name(stp_sort s)
{
  if (s == nullptr)
    return nullptr;
  CSort* cs = csort(s);
  return guarded<char*>(cs->cm, nullptr, "stp_sort_name", nullptr,
                        [&] { return dup_string(Sort(cs->cm->impl, cs->index).name()); });
}

uint64_t stp_sort_id(stp_sort s)
{
  if (s == nullptr)
    return 0;
  CSort* cs = csort(s);
  return Sort(cs->cm->impl, cs->index).id();
}

char* stp_sort_str(stp_sort s)
{
  if (s == nullptr)
    return nullptr;
  CSort* cs = csort(s);
  return guarded<char*>(cs->cm, nullptr, "stp_sort_str", nullptr,
                        [&] { return dup_string(Sort(cs->cm->impl, cs->index).str()); });
}

stp_tm stp_sort_manager(stp_sort s)
{
  if (!need(s, "stp_sort_manager"))
    return nullptr;
  return export_tm(csort(s)->cm);
}

// ============================================================ symbols and values

stp_term stp_declare(stp_tm tm, const char* name, stp_sort sort)
{
  return make(tm, "stp_declare", [&](CManager* cm) {
    return tmh(cm).declare(str_arg(name, "stp_declare", 1), sort_arg(cm, sort, "stp_declare", 2));
  });
}

stp_term stp_mk_fresh(stp_tm tm, stp_sort sort, const char* prefix)
{
  return make(tm, "stp_mk_fresh", [&](CManager* cm) {
    return tmh(cm).mk_fresh(sort_arg(cm, sort, "stp_mk_fresh", 1), prefix ? prefix : "");
  });
}

stp_term stp_tm_symbol(stp_tm tm, const char* name)
{
  if (!need(tm, "stp_tm_symbol"))
    return nullptr;
  CManager* cm = cm_of(tm);
  return guarded<stp_term>(cm, nullptr, "stp_tm_symbol", nullptr, [&] {
    const std::optional<Term> t = tmh(cm).symbol(str_arg(name, "stp_tm_symbol", 1));
    return t.has_value() ? export_term(cm, *t) : nullptr;
  });
}

stp_status stp_tm_bind_symbol(stp_tm tm, const char* name, stp_term t)
{
  if (!need(tm, "stp_tm_bind_symbol"))
    return STP_ERROR;
  CManager* cm = cm_of(tm);
  return guarded<stp_status>(cm, nullptr, "stp_tm_bind_symbol", STP_ERROR, [&] {
    tmh(cm).bind_symbol(str_arg(name, "stp_tm_bind_symbol", 1),
                        term_arg(cm, t, "stp_tm_bind_symbol", 2));
    return STP_OK;
  });
}

size_t stp_tm_num_symbols(stp_tm tm)
{
  if (!need(tm, "stp_tm_num_symbols"))
    return 0;
  CManager* cm = cm_of(tm);
  return guarded<size_t>(cm, nullptr, "stp_tm_num_symbols", 0,
                         [&] { return tmh(cm).symbols().size(); });
}

stp_term stp_tm_symbol_at(stp_tm tm, size_t i)
{
  return make(tm, "stp_tm_symbol_at", [&](CManager* cm) {
    const std::vector<Term> all = tmh(cm).symbols();
    if (i >= all.size())
      fail(ErrorCode::INDEX_OUT_OF_RANGE, "stp_tm_symbol_at",
           "index " + std::to_string(i) + " out of range [0, " + std::to_string(all.size()) + ")",
           1);
    return all[i];
  });
}

size_t stp_tm_num_declared_sorts(stp_tm tm)
{
  if (!need(tm, "stp_tm_num_declared_sorts"))
    return 0;
  CManager* cm = cm_of(tm);
  return guarded<size_t>(cm, nullptr, "stp_tm_num_declared_sorts", 0,
                         [&] { return tmh(cm).declared_sorts().size(); });
}

stp_sort stp_tm_declared_sort_at(stp_tm tm, size_t i)
{
  return make_sort(tm, "stp_tm_declared_sort_at", [&](CManager* cm) {
    const std::vector<Sort> all = tmh(cm).declared_sorts();
    if (i >= all.size())
      fail(ErrorCode::INDEX_OUT_OF_RANGE, "stp_tm_declared_sort_at",
           "index " + std::to_string(i) + " out of range [0, " + std::to_string(all.size()) + ")",
           1);
    return all[i];
  });
}

stp_term stp_tm_term_from_id(stp_tm tm, uint64_t id)
{
  return make(tm, "stp_tm_term_from_id", [&](CManager* cm) { return tmh(cm).term_from_id(id); });
}

stp_term stp_mk_true(stp_tm tm)
{
  return make(tm, "stp_mk_true", [](CManager* cm) { return tmh(cm).mk_true(); });
}

stp_term stp_mk_false(stp_tm tm)
{
  return make(tm, "stp_mk_false", [](CManager* cm) { return tmh(cm).mk_false(); });
}

stp_term stp_mk_bool(stp_tm tm, bool b)
{
  return make(tm, "stp_mk_bool", [&](CManager* cm) { return tmh(cm).mk_bool(b); });
}

stp_term stp_mk_bv_uint64(stp_tm tm, uint32_t width, uint64_t value)
{
  return make(tm, "stp_mk_bv_uint64", [&](CManager* cm) { return tmh(cm).mk_bv(width, value); });
}

stp_term stp_mk_bv_int64(stp_tm tm, uint32_t width, int64_t value)
{
  return make(tm, "stp_mk_bv_int64",
              [&](CManager* cm) { return tmh(cm).mk_bv_signed(width, value); });
}

stp_term stp_mk_bv_str(stp_tm tm, uint32_t width, const char* digits, int base)
{
  return make(tm, "stp_mk_bv_str", [&](CManager* cm) {
    return tmh(cm).mk_bv(width, str_arg(digits, "stp_mk_bv_str", 2), base);
  });
}

stp_term stp_mk_bv_limbs(stp_tm tm, uint32_t width, size_t n, const uint64_t* lsb_first)
{
  return make(tm, "stp_mk_bv_limbs", [&](CManager* cm) {
    if (n > 0 && lsb_first == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_mk_bv_limbs", "the limb array is null", 3);
    return tmh(cm).mk_bv_limbs(width, std::vector<std::uint64_t>(lsb_first, lsb_first + n));
  });
}

stp_term stp_mk_bv_bytes(stp_tm tm, uint32_t width, size_t n, const uint8_t* bytes,
                         bool little_endian)
{
  return make(tm, "stp_mk_bv_bytes", [&](CManager* cm) {
    if (n > 0 && bytes == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_mk_bv_bytes", "the byte array is null", 3);
    return tmh(cm).mk_bv_bytes(width, std::vector<std::uint8_t>(bytes, bytes + n), little_endian);
  });
}

stp_term stp_mk_bv_wrapped(stp_tm tm, uint32_t width, uint64_t value)
{
  return make(tm, "stp_mk_bv_wrapped",
              [&](CManager* cm) { return tmh(cm).mk_bv_wrapped(width, value); });
}

stp_term stp_mk_bv_zero(stp_tm tm, uint32_t width)
{
  return make(tm, "stp_mk_bv_zero", [&](CManager* cm) { return tmh(cm).mk_bv_zero(width); });
}

stp_term stp_mk_bv_ones(stp_tm tm, uint32_t width)
{
  return make(tm, "stp_mk_bv_ones", [&](CManager* cm) { return tmh(cm).mk_bv_ones(width); });
}

stp_term stp_mk_bv_min_signed(stp_tm tm, uint32_t width)
{
  return make(tm, "stp_mk_bv_min_signed",
              [&](CManager* cm) { return tmh(cm).mk_bv_min_signed(width); });
}

stp_term stp_mk_bv_max_signed(stp_tm tm, uint32_t width)
{
  return make(tm, "stp_mk_bv_max_signed",
              [&](CManager* cm) { return tmh(cm).mk_bv_max_signed(width); });
}

stp_term stp_mk_fp_from_bits(stp_tm tm, stp_sort fp, stp_term bv_value)
{
  return make(tm, "stp_mk_fp_from_bits", [&](CManager* cm) {
    return tmh(cm).mk_fp_from_bits(sort_arg(cm, fp, "stp_mk_fp_from_bits", 1),
                                   term_arg(cm, bv_value, "stp_mk_fp_from_bits", 2));
  });
}

stp_term stp_mk_fp_from_bits_str(stp_tm tm, stp_sort fp, const char* bits)
{
  return make(tm, "stp_mk_fp_from_bits_str", [&](CManager* cm) {
    return tmh(cm).mk_fp_from_bits(sort_arg(cm, fp, "stp_mk_fp_from_bits_str", 1),
                                   std::string_view(str_arg(bits, "stp_mk_fp_from_bits_str", 2)));
  });
}

stp_term stp_mk_fp(stp_tm tm, stp_term sign, stp_term exponent, stp_term significand)
{
  return make(tm, "stp_mk_fp", [&](CManager* cm) {
    return tmh(cm).mk_fp(term_arg(cm, sign, "stp_mk_fp", 1), term_arg(cm, exponent, "stp_mk_fp", 2),
                         term_arg(cm, significand, "stp_mk_fp", 3));
  });
}

stp_term stp_mk_fp_pos_zero(stp_tm tm, stp_sort fp)
{
  return make(tm, "stp_mk_fp_pos_zero", [&](CManager* cm) {
    return tmh(cm).mk_fp_pos_zero(sort_arg(cm, fp, "stp_mk_fp_pos_zero", 1));
  });
}

stp_term stp_mk_fp_neg_zero(stp_tm tm, stp_sort fp)
{
  return make(tm, "stp_mk_fp_neg_zero", [&](CManager* cm) {
    return tmh(cm).mk_fp_neg_zero(sort_arg(cm, fp, "stp_mk_fp_neg_zero", 1));
  });
}

stp_term stp_mk_fp_pos_inf(stp_tm tm, stp_sort fp)
{
  return make(tm, "stp_mk_fp_pos_inf", [&](CManager* cm) {
    return tmh(cm).mk_fp_pos_inf(sort_arg(cm, fp, "stp_mk_fp_pos_inf", 1));
  });
}

stp_term stp_mk_fp_neg_inf(stp_tm tm, stp_sort fp)
{
  return make(tm, "stp_mk_fp_neg_inf", [&](CManager* cm) {
    return tmh(cm).mk_fp_neg_inf(sort_arg(cm, fp, "stp_mk_fp_neg_inf", 1));
  });
}

stp_term stp_mk_fp_nan(stp_tm tm, stp_sort fp)
{
  return make(tm, "stp_mk_fp_nan",
              [&](CManager* cm) { return tmh(cm).mk_fp_nan(sort_arg(cm, fp, "stp_mk_fp_nan", 1)); });
}

stp_term stp_mk_fp_double(stp_tm tm, stp_sort fp, stp_rm rm, double value)
{
  return make(tm, "stp_mk_fp_double", [&](CManager* cm) {
    return tmh(cm).mk_fp(sort_arg(cm, fp, "stp_mk_fp_double", 1), rm_arg(rm, "stp_mk_fp_double", 2),
                         value);
  });
}

stp_term stp_mk_fp_decimal(stp_tm tm, stp_sort fp, stp_rm rm, const char* literal)
{
  return make(tm, "stp_mk_fp_decimal", [&](CManager* cm) {
    return tmh(cm).mk_fp(sort_arg(cm, fp, "stp_mk_fp_decimal", 1),
                         rm_arg(rm, "stp_mk_fp_decimal", 2),
                         std::string_view(str_arg(literal, "stp_mk_fp_decimal", 3)));
  });
}

stp_term stp_mk_rm(stp_tm tm, stp_rm rm)
{
  return make(tm, "stp_mk_rm", [&](CManager* cm) { return tmh(cm).mk_rm(rm_arg(rm, "stp_mk_rm", 1)); });
}

stp_term stp_mk_real_int64(stp_tm tm, int64_t v)
{
  return make(tm, "stp_mk_real_int64", [&](CManager* cm) { return tmh(cm).mk_real(v); });
}

stp_term stp_mk_real_fraction(stp_tm tm, int64_t numerator, int64_t denominator)
{
  return make(tm, "stp_mk_real_fraction",
              [&](CManager* cm) { return tmh(cm).mk_real(numerator, denominator); });
}

stp_term stp_mk_real_str(stp_tm tm, const char* literal)
{
  return make(tm, "stp_mk_real_str", [&](CManager* cm) {
    return tmh(cm).mk_real(std::string_view(str_arg(literal, "stp_mk_real_str", 1)));
  });
}

stp_term stp_mk_const_array(stp_tm tm, stp_sort array_sort, stp_term element)
{
  return make(tm, "stp_mk_const_array", [&](CManager* cm) {
    return tmh(cm).mk_const_array(sort_arg(cm, array_sort, "stp_mk_const_array", 1),
                                  term_arg(cm, element, "stp_mk_const_array", 2));
  });
}

stp_term stp_array_from_bytes(stp_tm tm, size_t n, const uint8_t* bytes, uint32_t index_width)
{
  return make(tm, "stp_array_from_bytes", [&](CManager* cm) {
    if (n > 0 && bytes == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_array_from_bytes", "the byte array is null", 2);
    TermManager t = tmh(cm);
    return array_from_bytes(t, std::vector<std::uint8_t>(bytes, bytes + n), index_width);
  });
}

// ============================================================ generic construction

stp_term stp_mk_term(stp_tm tm, stp_kind kind, size_t n, const stp_term* args)
{
  return make(tm, "stp_mk_term", [&](CManager* cm) {
    return tmh(cm).mk_term(kind_arg(kind, "stp_mk_term", 1), term_args(cm, n, args, "stp_mk_term", 3));
  });
}

stp_term stp_mk_term_indexed(stp_tm tm, stp_kind kind, size_t n, const stp_term* args, size_t m,
                             const uint32_t* idx)
{
  return make(tm, "stp_mk_term_indexed", [&](CManager* cm) {
    if (m > 0 && idx == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_mk_term_indexed", "the index array is null", 5);
    return tmh(cm).mk_term(kind_arg(kind, "stp_mk_term_indexed", 1),
                           term_args(cm, n, args, "stp_mk_term_indexed", 3),
                           std::vector<std::uint32_t>(idx, idx + m));
  });
}

stp_term stp_mk_term_sorted(stp_tm tm, stp_kind kind, size_t n, const stp_term* args, size_t m,
                            const uint32_t* idx, stp_sort result)
{
  return make(tm, "stp_mk_term_sorted", [&](CManager* cm) {
    if (m > 0 && idx == nullptr)
      fail(ErrorCode::NULL_HANDLE, "stp_mk_term_sorted", "the index array is null", 5);
    std::optional<Sort> rs;
    if (result != nullptr)
      rs = sort_arg(cm, result, "stp_mk_term_sorted", 6);
    return tmh(cm).mk_term(kind_arg(kind, "stp_mk_term_sorted", 1),
                           term_args(cm, n, args, "stp_mk_term_sorted", 3),
                           std::vector<std::uint32_t>(idx, idx + m), rs);
  });
}

stp_term stp_mk_term1(stp_tm tm, stp_kind kind, stp_term a)
{
  return make(tm, "stp_mk_term1", [&](CManager* cm) {
    return tmh(cm).mk_term(kind_arg(kind, "stp_mk_term1", 1), {term_arg(cm, a, "stp_mk_term1", 2)});
  });
}

stp_term stp_mk_term2(stp_tm tm, stp_kind kind, stp_term a, stp_term b)
{
  return make(tm, "stp_mk_term2", [&](CManager* cm) {
    return tmh(cm).mk_term(kind_arg(kind, "stp_mk_term2", 1),
                           {term_arg(cm, a, "stp_mk_term2", 2), term_arg(cm, b, "stp_mk_term2", 3)});
  });
}

stp_term stp_mk_term3(stp_tm tm, stp_kind kind, stp_term a, stp_term b, stp_term c)
{
  return make(tm, "stp_mk_term3", [&](CManager* cm) {
    return tmh(cm).mk_term(kind_arg(kind, "stp_mk_term3", 1),
                           {term_arg(cm, a, "stp_mk_term3", 2), term_arg(cm, b, "stp_mk_term3", 3),
                            term_arg(cm, c, "stp_mk_term3", 4)});
  });
}

stp_term stp_mk_term1_indexed1(stp_tm tm, stp_kind kind, stp_term a, uint32_t i)
{
  return make(tm, "stp_mk_term1_indexed1", [&](CManager* cm) {
    return tmh(cm).mk_term(kind_arg(kind, "stp_mk_term1_indexed1", 1),
                           {term_arg(cm, a, "stp_mk_term1_indexed1", 2)}, {i});
  });
}

stp_term stp_mk_term1_indexed2(stp_tm tm, stp_kind kind, stp_term a, uint32_t i, uint32_t j)
{
  return make(tm, "stp_mk_term1_indexed2", [&](CManager* cm) {
    return tmh(cm).mk_term(kind_arg(kind, "stp_mk_term1_indexed2", 1),
                           {term_arg(cm, a, "stp_mk_term1_indexed2", 2)}, {i, j});
  });
}

stp_term stp_mk_term2_indexed1(stp_tm tm, stp_kind kind, stp_term a, stp_term b, uint32_t i)
{
  return make(tm, "stp_mk_term2_indexed1", [&](CManager* cm) {
    return tmh(cm).mk_term(
        kind_arg(kind, "stp_mk_term2_indexed1", 1),
        {term_arg(cm, a, "stp_mk_term2_indexed1", 2), term_arg(cm, b, "stp_mk_term2_indexed1", 3)},
        {i});
  });
}

stp_term stp_mk_term2_indexed2(stp_tm tm, stp_kind kind, stp_term a, stp_term b, uint32_t i,
                               uint32_t j)
{
  return make(tm, "stp_mk_term2_indexed2", [&](CManager* cm) {
    return tmh(cm).mk_term(
        kind_arg(kind, "stp_mk_term2_indexed2", 1),
        {term_arg(cm, a, "stp_mk_term2_indexed2", 2), term_arg(cm, b, "stp_mk_term2_indexed2", 3)},
        {i, j});
  });
}

// ============================================================ named constructors

// the generated per-kind constructors, over stp_mk_term / stp_mk_term2
#include "gen/kind_ctors_c.inc"

stp_term stp_extract(stp_tm tm, uint32_t hi, uint32_t lo, stp_term t)
{
  return make(tm, "stp_extract",
              [&](CManager* cm) { return extract(hi, lo, term_arg(cm, t, "stp_extract", 3)); });
}

stp_term stp_zero_extend(stp_tm tm, uint32_t k, stp_term t)
{
  return make(tm, "stp_zero_extend",
              [&](CManager* cm) { return zero_extend(k, term_arg(cm, t, "stp_zero_extend", 2)); });
}

stp_term stp_sign_extend(stp_tm tm, uint32_t k, stp_term t)
{
  return make(tm, "stp_sign_extend",
              [&](CManager* cm) { return sign_extend(k, term_arg(cm, t, "stp_sign_extend", 2)); });
}

stp_term stp_repeat(stp_tm tm, uint32_t k, stp_term t)
{
  return make(tm, "stp_repeat", [&](CManager* cm) { return repeat(k, term_arg(cm, t, "stp_repeat", 2)); });
}

stp_term stp_rotate_left(stp_tm tm, uint32_t k, stp_term t)
{
  return make(tm, "stp_rotate_left",
              [&](CManager* cm) { return rotate_left(k, term_arg(cm, t, "stp_rotate_left", 2)); });
}

stp_term stp_rotate_right(stp_tm tm, uint32_t k, stp_term t)
{
  return make(tm, "stp_rotate_right",
              [&](CManager* cm) { return rotate_right(k, term_arg(cm, t, "stp_rotate_right", 2)); });
}

stp_term stp_bit(stp_tm tm, stp_term bv, uint32_t i)
{
  return make(tm, "stp_bit", [&](CManager* cm) { return bit(term_arg(cm, bv, "stp_bit", 1), i); });
}

stp_term stp_bool_to_bv1(stp_tm tm, stp_term b)
{
  return make(tm, "stp_bool_to_bv1",
              [&](CManager* cm) { return bool_to_bv1(term_arg(cm, b, "stp_bool_to_bv1", 1)); });
}

stp_term stp_bv1_to_bool(stp_tm tm, stp_term bv1)
{
  return make(tm, "stp_bv1_to_bool",
              [&](CManager* cm) { return bv1_to_bool(term_arg(cm, bv1, "stp_bv1_to_bool", 1)); });
}

stp_term stp_to_fp(stp_tm tm, stp_sort fp, stp_term rm, stp_term x)
{
  return make(tm, "stp_to_fp", [&](CManager* cm) {
    return to_fp(sort_arg(cm, fp, "stp_to_fp", 1), term_arg(cm, rm, "stp_to_fp", 2),
                 term_arg(cm, x, "stp_to_fp", 3));
  });
}

stp_term stp_to_fp_unsigned(stp_tm tm, stp_sort fp, stp_term rm, stp_term bv)
{
  return make(tm, "stp_to_fp_unsigned", [&](CManager* cm) {
    return to_fp_unsigned(sort_arg(cm, fp, "stp_to_fp_unsigned", 1),
                          term_arg(cm, rm, "stp_to_fp_unsigned", 2),
                          term_arg(cm, bv, "stp_to_fp_unsigned", 3));
  });
}

stp_term stp_to_fp_from_bits(stp_tm tm, stp_sort fp, stp_term bv)
{
  return make(tm, "stp_to_fp_from_bits", [&](CManager* cm) {
    return to_fp_from_bits(sort_arg(cm, fp, "stp_to_fp_from_bits", 1),
                           term_arg(cm, bv, "stp_to_fp_from_bits", 2));
  });
}

stp_term stp_fp_to_ubv(stp_tm tm, uint32_t m, stp_term rm, stp_term x)
{
  return make(tm, "stp_fp_to_ubv", [&](CManager* cm) {
    return fp_to_ubv(m, term_arg(cm, rm, "stp_fp_to_ubv", 2), term_arg(cm, x, "stp_fp_to_ubv", 3));
  });
}

stp_term stp_fp_to_sbv(stp_tm tm, uint32_t m, stp_term rm, stp_term x)
{
  return make(tm, "stp_fp_to_sbv", [&](CManager* cm) {
    return fp_to_sbv(m, term_arg(cm, rm, "stp_fp_to_sbv", 2), term_arg(cm, x, "stp_fp_to_sbv", 3));
  });
}

// the _rm variants: the mode as an enum, made into a term first
stp_term stp_fp_add_rm(stp_tm tm, stp_rm rm, stp_term a, stp_term b)
{
  return make(tm, "stp_fp_add_rm", [&](CManager* cm) {
    TermManager t = tmh(cm);
    return t.mk_term(stp::api::Kind::FP_ADD, {t.mk_rm(rm_arg(rm, "stp_fp_add_rm", 1)),
                                    term_arg(cm, a, "stp_fp_add_rm", 2),
                                    term_arg(cm, b, "stp_fp_add_rm", 3)});
  });
}

stp_term stp_fp_sub_rm(stp_tm tm, stp_rm rm, stp_term a, stp_term b)
{
  return make(tm, "stp_fp_sub_rm", [&](CManager* cm) {
    TermManager t = tmh(cm);
    return t.mk_term(stp::api::Kind::FP_SUB, {t.mk_rm(rm_arg(rm, "stp_fp_sub_rm", 1)),
                                    term_arg(cm, a, "stp_fp_sub_rm", 2),
                                    term_arg(cm, b, "stp_fp_sub_rm", 3)});
  });
}

stp_term stp_fp_mul_rm(stp_tm tm, stp_rm rm, stp_term a, stp_term b)
{
  return make(tm, "stp_fp_mul_rm", [&](CManager* cm) {
    TermManager t = tmh(cm);
    return t.mk_term(stp::api::Kind::FP_MUL, {t.mk_rm(rm_arg(rm, "stp_fp_mul_rm", 1)),
                                    term_arg(cm, a, "stp_fp_mul_rm", 2),
                                    term_arg(cm, b, "stp_fp_mul_rm", 3)});
  });
}

stp_term stp_fp_div_rm(stp_tm tm, stp_rm rm, stp_term a, stp_term b)
{
  return make(tm, "stp_fp_div_rm", [&](CManager* cm) {
    TermManager t = tmh(cm);
    return t.mk_term(stp::api::Kind::FP_DIV, {t.mk_rm(rm_arg(rm, "stp_fp_div_rm", 1)),
                                    term_arg(cm, a, "stp_fp_div_rm", 2),
                                    term_arg(cm, b, "stp_fp_div_rm", 3)});
  });
}

stp_term stp_fp_fma_rm(stp_tm tm, stp_rm rm, stp_term a, stp_term b, stp_term c)
{
  return make(tm, "stp_fp_fma_rm", [&](CManager* cm) {
    TermManager t = tmh(cm);
    return t.mk_term(stp::api::Kind::FP_FMA, {t.mk_rm(rm_arg(rm, "stp_fp_fma_rm", 1)),
                                    term_arg(cm, a, "stp_fp_fma_rm", 2),
                                    term_arg(cm, b, "stp_fp_fma_rm", 3),
                                    term_arg(cm, c, "stp_fp_fma_rm", 4)});
  });
}

stp_term stp_fp_sqrt_rm(stp_tm tm, stp_rm rm, stp_term a)
{
  return make(tm, "stp_fp_sqrt_rm", [&](CManager* cm) {
    TermManager t = tmh(cm);
    return t.mk_term(stp::api::Kind::FP_SQRT,
                     {t.mk_rm(rm_arg(rm, "stp_fp_sqrt_rm", 1)), term_arg(cm, a, "stp_fp_sqrt_rm", 2)});
  });
}

stp_term stp_fp_rti_rm(stp_tm tm, stp_rm rm, stp_term a)
{
  return make(tm, "stp_fp_rti_rm", [&](CManager* cm) {
    TermManager t = tmh(cm);
    return t.mk_term(stp::api::Kind::FP_RTI,
                     {t.mk_rm(rm_arg(rm, "stp_fp_rti_rm", 1)), term_arg(cm, a, "stp_fp_rti_rm", 2)});
  });
}

stp_term stp_to_fp_rm(stp_tm tm, stp_sort fp, stp_rm rm, stp_term x)
{
  return make(tm, "stp_to_fp_rm", [&](CManager* cm) {
    return to_fp(sort_arg(cm, fp, "stp_to_fp_rm", 1), rm_arg(rm, "stp_to_fp_rm", 2),
                 term_arg(cm, x, "stp_to_fp_rm", 3));
  });
}

stp_term stp_to_fp_unsigned_rm(stp_tm tm, stp_sort fp, stp_rm rm, stp_term bv)
{
  return make(tm, "stp_to_fp_unsigned_rm", [&](CManager* cm) {
    return to_fp_unsigned(sort_arg(cm, fp, "stp_to_fp_unsigned_rm", 1),
                          rm_arg(rm, "stp_to_fp_unsigned_rm", 2),
                          term_arg(cm, bv, "stp_to_fp_unsigned_rm", 3));
  });
}

stp_term stp_fp_to_ubv_rm(stp_tm tm, uint32_t m, stp_rm rm, stp_term x)
{
  return make(tm, "stp_fp_to_ubv_rm", [&](CManager* cm) {
    return fp_to_ubv(m, rm_arg(rm, "stp_fp_to_ubv_rm", 2), term_arg(cm, x, "stp_fp_to_ubv_rm", 3));
  });
}

stp_term stp_fp_to_sbv_rm(stp_tm tm, uint32_t m, stp_rm rm, stp_term x)
{
  return make(tm, "stp_fp_to_sbv_rm", [&](CManager* cm) {
    return fp_to_sbv(m, rm_arg(rm, "stp_fp_to_sbv_rm", 2), term_arg(cm, x, "stp_fp_to_sbv_rm", 3));
  });
}

// ============================================================ terms

stp_term stp_term_copy(stp_term t)
{
  if (t == nullptr)
    return nullptr;
  ASTInternal* p = raw(t);
  CManager* cm = cm_of_node(p);
  if (cm == nullptr)
  {
    report_code(nullptr, nullptr, "stp_term_copy", ErrorCode::STATE,
                "the term's manager is not known to the C layer (was it released?)", 0);
    return nullptr;
  }
  return guarded<stp_term>(cm, nullptr, "stp_term_copy", nullptr, [&] {
    // rule 2: always an unscoped reference
    auto it = cm->unscoped.find(p);
    if (it == cm->unscoped.end())
      cm->unscoped.emplace(p, 1u);
    else
      ++it->second;
    stp::api::detail::NodeAccess::retain(p);
    ++cm->refs;
    return t;
  });
}

stp_status stp_term_release(stp_term t)
{
  if (t == nullptr)
    return STP_ERROR;
  ASTInternal* p = raw(t);
  CManager* cm = cm_of_node(p);
  if (cm == nullptr)
  {
    report_code(nullptr, nullptr, "stp_term_release", ErrorCode::STATE,
                "the term's manager is not known to the C layer (was it released?)", 0);
    return STP_ERROR;
  }
  auto it = cm->unscoped.find(p);
  if (it == cm->unscoped.end())
  {
    // rule 3
    report_code(cm, nullptr, "stp_term_release", ErrorCode::STATE,
                "scoped handle: copy it to keep it, or let the scope pop", 0);
    return STP_ERROR;
  }
  if (--it->second == 0)
    cm->unscoped.erase(it);
  stp::api::detail::NodeAccess::release(p);
  cm_release(cm);
  return STP_OK;
}

uint64_t stp_term_id(stp_term t)
{
  if (t == nullptr)
    return 0;
  TermRef r;
  if (!term_ref(t, "stp_term_id", r))
    return stp::api::detail::NodeAccess::wrap(raw(t)).GetNodeNum();
  return r.term.id();
}

uint64_t stp_term_hash(stp_term t)
{
  if (t == nullptr)
    return 0;
  TermRef r;
  const std::uint64_t id = stp_term_id(t);
  const std::uint64_t mgr = term_ref(t, "stp_term_hash", r) ? r.cm->impl->id : 0;
  // a 64-bit mix of the two ids
  std::uint64_t h = id ^ (mgr * 0x9E3779B97F4A7C15ull);
  h ^= h >> 32;
  h *= 0xD6E8FEB86659FD93ull;
  h ^= h >> 32;
  return h;
}

stp_tm stp_term_manager(stp_term t)
{
  TermRef r;
  if (!term_ref(t, "stp_term_manager", r))
    return nullptr;
  return export_tm(r.cm);
}

stp_status stp_term_get_kind(stp_term t, stp_kind* out)
{
  return term_status(t, "stp_term_get_kind", [&](const TermRef& r) {
    *out_arg(out, "stp_term_get_kind", 1) = static_cast<stp_kind>(r.term.kind());
  });
}

stp_sort stp_term_sort(stp_term t)
{
  TermRef r;
  if (!term_ref(t, "stp_term_sort", r))
    return nullptr;
  return guarded<stp_sort>(r.cm, nullptr, "stp_term_sort", nullptr,
                           [&] { return export_sort(r.cm, r.term.sort()); });
}

stp_status stp_term_num_children(stp_term t, size_t* out)
{
  return term_status(t, "stp_term_num_children", [&](const TermRef& r) {
    *out_arg(out, "stp_term_num_children", 1) = r.term.num_children();
  });
}

stp_term stp_term_child(stp_term t, size_t i)
{
  return term_term(t, "stp_term_child", [&](const TermRef& r) { return r.term.child(i); });
}

stp_status stp_term_num_indices(stp_term t, size_t* out)
{
  return term_status(t, "stp_term_num_indices", [&](const TermRef& r) {
    *out_arg(out, "stp_term_num_indices", 1) = r.term.indices().size();
  });
}

stp_status stp_term_index(stp_term t, size_t i, uint32_t* out)
{
  return term_status(t, "stp_term_index", [&](const TermRef& r) {
    out_arg(out, "stp_term_index", 2);
    const std::vector<std::uint32_t> idx = r.term.indices();
    if (i >= idx.size())
      fail(ErrorCode::INDEX_OUT_OF_RANGE, "stp_term_index",
           "index " + std::to_string(i) + " out of range [0, " + std::to_string(idx.size()) + ")",
           1);
    *out = idx[i];
  });
}

bool stp_term_is_value(stp_term t)
{
  TermRef r;
  return term_ref(t, "stp_term_is_value", r) && r.term.is_value();
}

bool stp_term_is_const(stp_term t)
{
  TermRef r;
  return term_ref(t, "stp_term_is_const", r) && r.term.is_const();
}

char* stp_term_symbol(stp_term t)
{
  TermRef r;
  if (!term_ref(t, "stp_term_symbol", r))
    return nullptr;
  return guarded<char*>(r.cm, nullptr, "stp_term_symbol", nullptr, [&] {
    const std::optional<std::string> name = r.term.symbol();
    return name.has_value() ? dup_string(*name) : nullptr;
  });
}

char* stp_term_str(stp_term t)
{
  return term_string(t, "stp_term_str", [](const TermRef& r) { return r.term.str(); });
}

char* stp_term_to_string(stp_term t, stp_format f, bool share_subterms)
{
  return term_string(t, "stp_term_to_string", [&](const TermRef& r) {
    return r.term.to_string(format_arg(f, "stp_term_to_string", 1), share_subterms);
  });
}

stp_term stp_term_substitute(stp_term t, size_t n, const stp_term* from, const stp_term* to)
{
  return term_term(t, "stp_term_substitute", [&](const TermRef& r) {
    if (n > 0 && (from == nullptr || to == nullptr))
      fail(ErrorCode::NULL_HANDLE, "stp_term_substitute", "a substitution array is null",
           from == nullptr ? 2 : 3);
    std::vector<std::pair<Term, Term>> map;
    map.reserve(n);
    for (std::size_t i = 0; i < n; ++i)
      map.emplace_back(term_arg(r.cm, from[i], "stp_term_substitute", 2),
                       term_arg(r.cm, to[i], "stp_term_substitute", 3));
    return r.term.substitute(map);
  });
}

stp_term stp_tm_simplify(stp_tm tm, stp_term t)
{
  return make(tm, "stp_tm_simplify",
              [&](CManager* cm) { return tmh(cm).simplify(term_arg(cm, t, "stp_tm_simplify", 1)); });
}

bool stp_term_same(stp_term a, stp_term b)
{
  return a != nullptr && a == b;
}

// ---------------------------------------------------------- readers

stp_status stp_term_to_bool(stp_term t, bool* out)
{
  return term_status(t, "stp_term_to_bool", [&](const TermRef& r) {
    *out_arg(out, "stp_term_to_bool", 1) = r.term.to_bool();
  });
}

bool stp_term_fits_uint64(stp_term t)
{
  TermRef r;
  if (!term_ref(t, "stp_term_fits_uint64", r))
    return false;
  try
  {
    return r.term.fits_uint64();
  }
  catch (...)
  {
    return false; // not a BV value: "fits" is simply false
  }
}

bool stp_term_fits_int64(stp_term t)
{
  TermRef r;
  if (!term_ref(t, "stp_term_fits_int64", r))
    return false;
  try
  {
    return r.term.fits_int64();
  }
  catch (...)
  {
    return false;
  }
}

stp_status stp_term_to_uint64(stp_term t, uint64_t* out)
{
  return term_status(t, "stp_term_to_uint64", [&](const TermRef& r) {
    *out_arg(out, "stp_term_to_uint64", 1) = r.term.to_uint64();
  });
}

stp_status stp_term_to_int64(stp_term t, int64_t* out)
{
  return term_status(t, "stp_term_to_int64", [&](const TermRef& r) {
    *out_arg(out, "stp_term_to_int64", 1) = r.term.to_int64();
  });
}

char* stp_term_to_bv_string(stp_term t, int base, bool pad)
{
  return term_string(t, "stp_term_to_bv_string",
                     [&](const TermRef& r) { return r.term.to_bv_string(base, pad); });
}

stp_status stp_term_bv_num_limbs(stp_term t, size_t* out)
{
  return term_status(t, "stp_term_bv_num_limbs", [&](const TermRef& r) {
    *out_arg(out, "stp_term_bv_num_limbs", 1) = r.term.to_bv_limbs().size();
  });
}

stp_status stp_term_to_bv_limbs(stp_term t, size_t n, uint64_t* out)
{
  return term_status(t, "stp_term_to_bv_limbs", [&](const TermRef& r) {
    copy_limbs(r.term.to_bv_limbs(), n, out, "stp_term_to_bv_limbs");
  });
}

stp_status stp_term_to_bv_bytes(stp_term t, size_t n, uint8_t* out, bool little_endian)
{
  return term_status(t, "stp_term_to_bv_bytes", [&](const TermRef& r) {
    copy_bytes(r.term.to_bv_bytes(little_endian), n, out, "stp_term_to_bv_bytes");
  });
}

stp_status stp_term_to_fp(stp_term t, stp_float_value* out)
{
  return term_status(t, "stp_term_to_fp", [&](const TermRef& r) {
    to_c(r.term.to_fp(), out_arg(out, "stp_term_to_fp", 1));
  });
}

stp_status stp_term_fp_significand_limbs(stp_term t, size_t n, uint64_t* out)
{
  return term_status(t, "stp_term_fp_significand_limbs", [&](const TermRef& r) {
    copy_limbs(r.term.to_fp().significand, n, out, "stp_term_fp_significand_limbs");
  });
}

char* stp_term_fp_bits(stp_term t)
{
  return term_string(t, "stp_term_fp_bits", [](const TermRef& r) { return r.term.to_fp().bits(); });
}

stp_status stp_term_fp_to_double(stp_term t, double* out)
{
  return term_status(t, "stp_term_fp_to_double", [&](const TermRef& r) {
    out_arg(out, "stp_term_fp_to_double", 1);
    *out = fp_double_of(r.term.to_fp(), "stp_term_fp_to_double");
  });
}

stp_status stp_term_fp_to_rational(stp_term t, char** numerator, char** denominator)
{
  return term_status(t, "stp_term_fp_to_rational", [&](const TermRef& r) {
    out_arg(numerator, "stp_term_fp_to_rational", 1);
    out_arg(denominator, "stp_term_fp_to_rational", 2);
    const std::optional<RationalValue> q = r.term.to_fp().to_rational();
    if (!q.has_value())
      fail(ErrorCode::INVALID_ARGUMENT, "stp_term_fp_to_rational",
           "an infinity or NaN has no rational value", 0, {r.term});
    char* num = dup_string(q->numerator);
    try
    {
      *denominator = dup_string(q->denominator);
    }
    catch (...)
    {
      std::free(num);
      throw;
    }
    *numerator = num;
  });
}

stp_status stp_term_to_rm(stp_term t, stp_rm* out)
{
  return term_status(t, "stp_term_to_rm", [&](const TermRef& r) {
    *out_arg(out, "stp_term_to_rm", 1) = static_cast<stp_rm>(r.term.to_rm());
  });
}

char* stp_term_real_numerator(stp_term t)
{
  return term_string(t, "stp_term_real_numerator",
                     [](const TermRef& r) { return r.term.to_rational().numerator; });
}

char* stp_term_real_denominator(stp_term t)
{
  return term_string(t, "stp_term_real_denominator",
                     [](const TermRef& r) { return r.term.to_rational().denominator; });
}

bool stp_term_real_fits_int64(stp_term t)
{
  TermRef r;
  if (!term_ref(t, "stp_term_real_fits_int64", r))
    return false;
  try
  {
    return r.term.to_rational().fits_int64();
  }
  catch (...)
  {
    return false;
  }
}

stp_status stp_term_real_to_int64(stp_term t, int64_t* num, int64_t* den)
{
  return term_status(t, "stp_term_real_to_int64", [&](const TermRef& r) {
    out_arg(num, "stp_term_real_to_int64", 1);
    out_arg(den, "stp_term_real_to_int64", 2);
    const RationalValue q = r.term.to_rational();
    const std::int64_t n = q.num64();
    const std::int64_t d = q.den64();
    *num = n;
    *den = d;
  });
}

stp_status stp_term_real_to_double(stp_term t, double* out)
{
  return term_status(t, "stp_term_real_to_double", [&](const TermRef& r) {
    *out_arg(out, "stp_term_real_to_double", 1) = r.term.to_rational().to_double();
  });
}

stp_status stp_term_to_uninterpreted_index(stp_term t, uint64_t* out)
{
  return term_status(t, "stp_term_to_uninterpreted_index", [&](const TermRef& r) {
    *out_arg(out, "stp_term_to_uninterpreted_index", 1) = r.term.to_uninterpreted_index();
  });
}

} // extern "C"

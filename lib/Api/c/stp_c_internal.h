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

// stp_c_internal.h -- the hand-written runtime behind <stp/stp.h>: the
// per-manager state of the C layer (external reference counts, scope journals,
// the sort handle pool, the first-error record), the handle structs and the
// exception boundary every extern "C" function runs behind.
//
// A term handle is the engine node itself (a retained ASTInternal*); every
// other handle is a small heap object that owns one C++ API object and one
// reference on its CManager. The CManager holds one reference on the
// ManagerImpl for as long as it lives, so anything reachable from a C handle
// keeps the manager alive, in any release order.

#ifndef STP_API_C_INTERNAL_H
#define STP_API_C_INTERNAL_H

#include "../Internal.h"
#include "stp/stp.h"

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace stp
{
namespace api
{
namespace capi
{

struct CManager;

// ---------------------------------------------------------------- errors

// One error record: the strings behind a public stp_error view. The view's
// pointers address the strings of the record, so a record is never moved
// after set(); the objects that own one (CManager, COptions, CSolver, the
// thread-local record) keep it at a fixed address.
struct ErrorRecord
{
  bool pending = false;
  std::string function;
  std::string message;
  std::string option;
  std::vector<Term> terms;
  std::vector<Sort> sorts;
  stp_error view{};

  void clear() noexcept;
  // Never throws: on allocation failure the view falls back to static text.
  void set(ErrorCode code, const char* fn, const std::string& message, int arg,
           const std::string& option, const std::vector<Term>& terms,
           const std::vector<Sort>& sorts = {}, int line = 0, int column = 0) noexcept;
  void set(const char* fn, const Error& e) noexcept;
  void assign(const ErrorRecord& o) noexcept; // a copy with the view re-pointed
};

// The record read by stp_last_error(): for calls with no object to hold one.
ErrorRecord& thread_error() noexcept;

// Thrown by the argument converters on a NULL term or sort: the boundary
// turns it into the failure value with no record (NULL propagation).
struct NullArgument
{
};

// Records e as the first error of `rec` (or of the manager's record, or the
// thread-local one) and delivers it to the manager's callback.
void report(CManager* cm, ErrorRecord* rec, const char* fn, const Error& e) noexcept;
void report_code(CManager* cm, ErrorRecord* rec, const char* fn, ErrorCode code,
                 const char* what, int arg = -1) noexcept;
// Marks the manager poisoned after an engine failure no C++ hub converted, as
// the hubs do (stp_c.cpp, where CManager is complete).
void poison_on_engine_failure(CManager* cm, const char* fn, const char* what) noexcept;

// The exception boundary. Every extern "C" body runs inside one of these; the
// return value on failure is the caller's failure value (NULL, STP_ERROR,
// false, 0). Nothing escapes: bad_alloc becomes RESOURCE, any other exception
// INTERNAL.
template <class R, class F>
R guarded(CManager* cm, ErrorRecord* rec, const char* fn, R fail_value, F&& f) noexcept
{
  try
  {
    return f();
  }
  catch (const NullArgument&)
  {
  }
  catch (const Error& e)
  {
    report(cm, rec, fn, e);
  }
  catch (const std::bad_alloc&)
  {
    report_code(cm, rec, fn, ErrorCode::RESOURCE, "out of memory");
  }
  catch (const stp::EngineFatal& e)
  {
    // An engine failure that no C++ hub converted (they all do; this is the
    // net under them): INTERNAL, and the manager is poisoned as they would.
    poison_on_engine_failure(cm, fn, e.what());
    report_code(cm, rec, fn, ErrorCode::INTERNAL, e.what());
  }
  catch (const std::exception& e)
  {
    report_code(cm, rec, fn, ErrorCode::INTERNAL, e.what());
  }
  catch (...)
  {
    report_code(cm, rec, fn, ErrorCode::INTERNAL, "an unknown exception escaped the engine");
  }
  return fail_value;
}

struct CSolver;

// A mutating solver call (assert, push, pop, parse*, reset*, an option write):
// a failure is recorded in the manager's record as usual AND becomes the
// solver's failed state, unless the solver already carries one (the ORIGINAL
// failure is what the state names).
template <class R, class F>
R solver_mutate(CSolver* cs, const char* fn, R fail_value, F&& f) noexcept;

// A call the failed state refuses (check_sat*, entails, write_cnf, model,
// candidate_model, value): STATE naming the original failure.
template <class R, class F>
R solver_checked(CSolver* cs, const char* fn, R fail_value, F&& f) noexcept;

// ---------------------------------------------------------------- handles

// A sort handle: owned by its manager's pool, one per interned sort index,
// valid while the manager lives. It pins nothing.
struct CSort
{
  CManager* cm;
  std::uint32_t index;
};

struct CManager
{
  long refs = 0;                       // tm handles + unscoped term refs + open scopes + solvers + models + values
  detail::ManagerImpl* impl = nullptr; // retained once for the life of this object
  STPMgr* bm = nullptr;                // the registry key (impl->bm), kept for the erase at death
  // rule 3 needs to know whether a handle has an unscoped reference: the
  // count per node; each count also holds one engine reference
  std::unordered_map<ASTInternal*, std::uint32_t> unscoped;
  // the scope journals; every ASTNode in a journal is one scoped reference
  std::vector<std::vector<ASTNode>> scopes;
  std::vector<std::unique_ptr<CSort>> sorts; // by sort index
  ErrorRecord error;
  stp_error_callback callback = nullptr;
  void* callback_user = nullptr;
};

struct COptions
{
  Options options;
  ErrorRecord error;
};

struct CSolver
{
  CManager* cm;
  Solver solver;
  ErrorRecord failed; // the failed state: pending while the solver refuses checks
  struct Adapter : Terminator
  {
    stp_terminate_callback cb = nullptr;
    void* user = nullptr;
    bool terminate() override { return cb != nullptr && cb(user); }
  } terminator;
  std::string last_reason; // the sentence behind the last result's reason
  // What stp_solver_assertion and stp_solver_unsat_assumption index: built by
  // the first read after a call that can change them (every mutating call
  // and every check drops them), so an enumeration costs one build rather
  // than one per element.
  std::optional<std::vector<Term>> assertions;
  std::optional<std::vector<Term>> unsat_assumptions;

  void drop_views() noexcept
  {
    assertions.reset();
    unsat_assumptions.reset();
  }

  CSolver(CManager* m, const Options& o);
};

template <class R, class F>
R solver_mutate(CSolver* cs, const char* fn, R fail_value, F&& f) noexcept
{
  cs->drop_views();
  ErrorRecord scratch;
  R r = guarded<R>(cs->cm, &scratch, fn, fail_value, f);
  if (scratch.pending)
  {
    if (!cs->cm->error.pending)
      cs->cm->error.assign(scratch);
    if (!cs->failed.pending)
      cs->failed.assign(scratch);
  }
  return r;
}

template <class R, class F>
R solver_checked(CSolver* cs, const char* fn, R fail_value, F&& f) noexcept
{
  cs->drop_views();
  if (cs->failed.pending)
  {
    try
    {
      const std::string what = "the solver is in the failed state: " + cs->failed.message;
      report_code(cs->cm, nullptr, fn, ErrorCode::STATE, what.c_str());
    }
    catch (...)
    {
      report_code(cs->cm, nullptr, fn, ErrorCode::STATE, "the solver is in the failed state");
    }
    return fail_value;
  }
  return guarded<R>(cs->cm, nullptr, fn, fail_value, f);
}

struct CModel
{
  CManager* cm;
  Model model;
  std::optional<std::vector<Term>> symbols; // stp_model_symbol's, built once
};

struct CArrayValue
{
  CManager* cm;
  ArrayValue value;
};

struct CFunValue
{
  CManager* cm;
  FunctionValue value;
};

struct CStatistics
{
  Statistics stats;
  std::vector<std::string> names; // the map's keys, in order, for stp_statistics_name
};

// ---------------------------------------------------------------- managers

CManager* cm_new(const TermManager& tm);       // registers; refs == 1
CManager* cm_retain(CManager* cm) noexcept;    // +1
void cm_release(CManager* cm) noexcept;        // -1; destroys at zero
CManager* cm_of_node(ASTInternal* p) noexcept; // the registry lookup; nullptr if unknown

inline ASTInternal* raw(stp_term t) noexcept
{
  return reinterpret_cast<ASTInternal*>(t);
}
inline stp_term handle(ASTInternal* p) noexcept
{
  return reinterpret_cast<stp_term>(p);
}
inline CManager* cm_of(stp_tm tm) noexcept
{
  return reinterpret_cast<CManager*>(tm);
}
inline stp_tm tm_of(CManager* cm) noexcept
{
  return reinterpret_cast<stp_tm>(cm);
}
inline CSort* csort(stp_sort s) noexcept
{
  return reinterpret_cast<CSort*>(s);
}
inline CSolver* csolver(stp_solver s) noexcept
{
  return reinterpret_cast<CSolver*>(s);
}
inline COptions* coptions(stp_options o) noexcept
{
  return reinterpret_cast<COptions*>(o);
}
inline CModel* cmodel(stp_model m) noexcept
{
  return reinterpret_cast<CModel*>(m);
}

// ---------------------------------------------------------------- exports and arguments

// A term the caller now owns: scoped while a scope is open, unscoped otherwise.
stp_term export_term(CManager* cm, const Term& t);
stp_sort export_sort(CManager* cm, const Sort& s);
stp_tm export_tm(CManager* cm) noexcept; // +1

// Converters for arguments. A NULL term or sort throws NullArgument; a term
// or sort of another manager fails with FOREIGN_MANAGER naming the argument.
Term term_arg(CManager* cm, stp_term t, const char* fn, int arg);
Sort sort_arg(CManager* cm, stp_sort s, const char* fn, int arg);
std::vector<Term> term_args(CManager* cm, std::size_t n, const stp_term* args, const char* fn, int arg);
// A required string or pointer: NULL is NULL_HANDLE.
const char* str_arg(const char* s, const char* fn, int arg);
template <class T>
T* out_arg(T* p, const char* fn, int arg)
{
  if (p == nullptr)
    detail::fail(ErrorCode::NULL_HANDLE, fn, "the output pointer is null", arg);
  return p;
}

// The manager behind a term-only call. Returns false (and records nothing) for
// a NULL term; records STATE in the thread-local record for a node whose
// manager the C layer does not know.
struct TermRef
{
  CManager* cm = nullptr;
  Term term;
};
bool term_ref(stp_term t, const char* fn, TermRef& out) noexcept;

// malloc'd copies for the caller (freed with stp_free)
char* dup_string(const std::string& s);
char* dup_string(const char* s);

// enum bridges; every one range-checks and fails INVALID_ARGUMENT
RoundingMode rm_arg(stp_rm rm, const char* fn, int arg);
Format format_arg(stp_format f, const char* fn, int arg);
Kind kind_arg(stp_kind k, const char* fn, int arg);
inline stp_unknown_reason to_c(UnknownReason r) noexcept
{
  return static_cast<stp_unknown_reason>(r);
}
inline stp_result to_c(const Result& r) noexcept
{
  stp_result out;
  out.kind = static_cast<stp_result_kind>(r.verdict());
  out.reason = to_c(r.reason());
  return out;
}
inline stp_entailment to_c(const Entailment& e) noexcept
{
  stp_entailment out;
  out.kind = static_cast<stp_validity>(e.validity());
  out.reason = to_c(e.reason());
  return out;
}
void to_c(const FloatValue& v, stp_float_value* out) noexcept;
std::optional<CheckBudget> budget_arg(const stp_budget* b);

// The options surface shared by stp_options_* and stp_solver_set_*: one
// template over the two C++ classes, instantiated in stp_c_options.cpp.
const detail::OptionSpec* spec_arg(const char* name, const char* fn, int arg);
const detail::OptionSpec* stable_spec(stp_option o, const char* fn, int arg);
std::string option_text_of(const detail::OptionSpec& spec, const OptionValue& v);

} // namespace capi
} // namespace api
} // namespace stp

#endif

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

/** @file stp.h
 * the STP 3.x C API.
 *
 * A flat C99 view of `<stp/stp.hpp>`: every C++ method has a C function here, plus the
 * hand-written runtime (reference counting, scopes, the error record, the failed state of
 * a solver). The enumerations that the data tables define (kinds, error codes, the stable
 * option tier) are included from the generated headers so that the three languages can
 * never disagree on a value.
 *
 * Conventions
 *   - Every identifier is prefixed stp_ / STP_. Nothing is exported unprefixed.
 *   - Handles are typed opaque pointers. A term handle IS the interned engine node: two
 *     handles compare equal with == exactly when they are the same term. stp_term_id() is
 *     unique within a manager and never reused; stp_term_hash() mixes it with the manager
 *     id, so handles from different managers share a hash only by coincidence.
 *   - Every term handle a function returns carries one reference owned by the caller
 *     (release optional for safety, required for memory). Scopes (stp_tm_scope_push/pop)
 *     release everything exported inside them; the exact rules are at "reclamation".
 *   - Every fallible function either returns a handle (NULL on error) or returns stp_status
 *     (STP_OK / STP_ERROR) with results in out-parameters, except the counts and yes/no
 *     queries (stp_tm_num_symbols, stp_model_in_core, stp_options_is_set, ...), whose 0 or
 *     false on an error is also an answer: they record the error, which says which it was.
 *     Details are in the manager's error
 *     record (stp_tm_error): the FIRST error since stp_tm_clear_error is kept, for diagnosis;
 *     it blocks nothing. An installed callback (stp_tm_set_error_callback) sees EVERY error.
 *   - NULL propagation: a NULL term or sort argument makes a constructor or reader return
 *     NULL / STP_ERROR / false without recording anything, so a chain of constructions can
 *     be checked once, where it is asserted. A NULL manager, solver, options, model, value
 *     or statistics handle, a NULL string and a NULL out-pointer are STP_ERR_NULL_HANDLE,
 *     recorded in the object's record (in the thread-local record when the missing handle
 *     is the object itself).
 *   - The failed state of a solver (the failbit of iostreams): a mutating call on a solver
 *     that fails (assert, push, pop, parse*, reset*, an option write, or an assert of a NULL
 *     term) puts THAT solver into a failed state, in which check_sat*, entails, write_cnf,
 *     model, candidate_model and value refuse with STP_ERR_STATE naming the original
 *     failure, until stp_solver_clear_error(s). A failed construction can therefore never
 *     silently drop an assertion, and a typo never affects the manager, other solvers,
 *     readers or printers. stp_solver_failed(s) reports the state.
 *   - Optional results: stp_solver_candidate_model, stp_solver_symbol, stp_tm_symbol,
 *     stp_term_symbol and stp_model_try_value return NULL with NO error record when there is
 *     nothing to return; they are the only NULL-returning functions for which NULL is not an
 *     error (and the NULL-propagation rule above).
 *   - Strings and buffers returned as char* are caller-owned and freed with stp_free().
 *     Nothing is "valid until the next call" except where a function says "static" (a string
 *     that lives as long as the process) or names the handle that owns it. Collections are
 *     read through indexed accessors.
 *   - Nothing in this library calls exit() or abort(). RESOURCE and INTERNAL errors poison
 *     the object (every later call fails with STP_ERR_STATE);
 *     stp_set_internal_error_policy(STP_ABORT) or STP_ABORT_ON_INTERNAL_ERROR=1 in the
 *     environment restores an abort, for debugging.
 *   - Thread contract: a manager and the solvers/models over it are used by one thread at a
 *     time, whichever thread that is; independent managers are concurrent, except that parses
 *     take one process-wide lock for their whole length (an EXECUTE input's checks and a text
 *     source's waits included); stp_solver_interrupt is the one call safe from any thread and
 *     from a signal handler.
 *   - Callbacks (the sinks, the terminator, the fatal-error handler, a text source, the error
 *     callback) must not call the library: every call from one fails with STP_ERR_STATE but
 *     stp_solver_interrupt, stp_solver_clear_interrupt and stp_solver_interrupt_pending.
 *   - Public struct layouts, versioned by STP_API_VERSION: stp_result, stp_entailment,
 *     stp_budget, stp_error, stp_float_value, stp_version. Every other type is opaque.
 */

#ifndef STP_STP_H
#define STP_STP_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#if defined(__has_include)
#if __has_include(<stp/api/version.hpp>)
#include <stp/api/version.hpp> /* STP_VERSION_MAJOR/MINOR/PATCH/STRING, STP_API_VERSION; macros only */
#endif
#endif

#ifdef __cplusplus
extern "C" {
#endif

/* Export macro, with the engine's convention (DLL_PUBLIC in
 * stp/Util/Attributes.h): on Windows a __declspec only when libstp is a DLL
 * (STP_SHARED_LIB, which STP's CMake package gives its consumers), dllexport
 * while the API itself is compiled (STP_API_BUILDING) and dllimport
 * otherwise; nothing for a static libstp or when STP_STATIC is defined.
 * Elsewhere, default visibility. */
#ifndef STP_API
#if defined(_WIN32) || defined(__CYGWIN__)
#if defined(STP_STATIC) || !defined(STP_SHARED_LIB)
#define STP_API
#elif defined(STP_API_BUILDING)
#define STP_API __declspec(dllexport)
#else
#define STP_API __declspec(dllimport)
#endif
#else
#define STP_API __attribute__((visibility("default")))
#endif
#endif

/* ------------------------------------------------------------------ handles */
typedef struct stp_tm_s* stp_tm;                   /**< term manager */
typedef struct stp_solver_s* stp_solver;
typedef struct stp_options_s* stp_options;         /**< a standalone Options value */
typedef struct stp_model_s* stp_model;
typedef struct stp_term_s* stp_term;               /**< the interned node */
typedef struct stp_sort_s* stp_sort;               /**< interned; owned by the manager; stp_sort_release is a no-op */
typedef struct stp_array_value_s* stp_array_value;
typedef struct stp_fun_value_s* stp_fun_value;
typedef struct stp_statistics_s* stp_statistics;

/* ------------------------------------------------------------------ enums */
/* Generated from the tables (values pinned, append-only): stp_kind / STP_KIND_*,
 * stp_error_code / STP_ERR_*, stp_option / STP_OPT_* (the stable tier). */
#include <stp/api/gen/errors.h>
#include <stp/api/gen/kinds.h>
#include <stp/api/gen/options.h>

/** Every enum of this header, and of the generated ones it includes, ends with
 * *_MAX_ENUM and *_MIN_ENUM members that are not values: together they widen
 * the type to all of int, so that any int a C caller passes, negative ones
 * included, is a value of the enum for the C++ implementation, which refuses
 * the ones it does not know instead of meeting undefined behaviour. */
typedef enum stp_status
{
  STP_OK = 0,
  STP_ERROR = 1,
  STP_STATUS_MAX_ENUM = 0x7fffffff,
  STP_STATUS_MIN_ENUM = -0x7fffffff - 1
} stp_status;

typedef enum stp_sort_kind
{
  STP_SORT_BOOL = 0,
  STP_SORT_BV,
  STP_SORT_FP,
  STP_SORT_RM,
  STP_SORT_REAL,
  STP_SORT_ARRAY,
  STP_SORT_FUN,
  STP_SORT_UNINTERPRETED,
  STP_SORT_MAX_ENUM = 0x7fffffff,
  STP_SORT_MIN_ENUM = -0x7fffffff - 1
} stp_sort_kind;

typedef enum stp_rm
{
  STP_RM_RNE = 0,
  STP_RM_RNA,
  STP_RM_RTP,
  STP_RM_RTN,
  STP_RM_RTZ,
  STP_RM_MAX_ENUM = 0x7fffffff,
  STP_RM_MIN_ENUM = -0x7fffffff - 1
} stp_rm;

typedef enum stp_result_kind
{
  STP_SAT = 1,
  STP_UNSAT = 2,
  STP_UNKNOWN = 3,
  STP_RESULT_MAX_ENUM = 0x7fffffff,
  STP_RESULT_MIN_ENUM = -0x7fffffff - 1
} stp_result_kind; /**< no zero member */

typedef enum stp_validity
{
  STP_VALID = 1,
  STP_INVALID = 2,
  STP_UNKNOWN_VALIDITY = 3,
  STP_VALIDITY_MAX_ENUM = 0x7fffffff,
  STP_VALIDITY_MIN_ENUM = -0x7fffffff - 1
} stp_validity;

typedef enum stp_unknown_reason
{
  STP_REASON_NONE = 0,
  STP_REASON_TIMEOUT,
  STP_REASON_CONFLICT_LIMIT,
  STP_REASON_INTERRUPTED,
  STP_REASON_INCOMPLETE,
  STP_REASON_RESOURCE_LIMIT,
  STP_REASON_CARRIER_EXHAUSTED,
  STP_REASON_ASSUMED_INJECTIVITY,
  STP_REASON_STOPPED_AFTER_CNF,
  STP_REASON_OTHER,
  STP_REASON_MAX_ENUM = 0x7fffffff,
  STP_REASON_MIN_ENUM = -0x7fffffff - 1
} stp_unknown_reason;

typedef enum stp_format
{
  STP_FORMAT_AUTO = 0,
  STP_FORMAT_SMTLIB2,
  STP_FORMAT_DOT,
  STP_FORMAT_GDL,
  STP_FORMAT_MAX_ENUM = 0x7fffffff,
  STP_FORMAT_MIN_ENUM = -0x7fffffff - 1
} stp_format;

typedef enum stp_parse_mode
{
  STP_PARSE_DECLARE_AND_ASSERT = 0,
  STP_PARSE_EXECUTE,
  STP_PARSE_ONLY,
  STP_PARSE_SINGLE_QUERY, /**< a script as data: one query, nothing that changes the solver (ParseMode::SINGLE_QUERY) */
  STP_PARSE_MAX_ENUM = 0x7fffffff,
  STP_PARSE_MIN_ENUM = -0x7fffffff - 1
} stp_parse_mode;

typedef enum stp_cnf_scope
{
  STP_CNF_WHOLE = 0,
  STP_CNF_PARTIAL,
  STP_CNF_OVER_APPROXIMATION,
  STP_CNF_SCOPE_MAX_ENUM = 0x7fffffff,
  STP_CNF_SCOPE_MIN_ENUM = -0x7fffffff - 1
} stp_cnf_scope;

typedef enum stp_tier
{
  STP_TIER_STABLE = 0,
  STP_TIER_EXPERT,
  STP_TIER_EXPERIMENTAL,
  STP_TIER_DIAGNOSTIC,
  STP_TIER_MAX_ENUM = 0x7fffffff,
  STP_TIER_MIN_ENUM = -0x7fffffff - 1
} stp_tier;

typedef enum stp_settable
{
  STP_SETTABLE_ANYTIME = 0,
  STP_SETTABLE_BEFORE_FIRST_CHECK,
  STP_SETTABLE_CONSTRUCTION,
  STP_SETTABLE_MAX_ENUM = 0x7fffffff,
  STP_SETTABLE_MIN_ENUM = -0x7fffffff - 1
} stp_settable;

typedef enum stp_option_scope
{
  STP_SCOPE_SOLVER = 0,
  STP_SCOPE_MANAGER,
  STP_SCOPE_MAX_ENUM = 0x7fffffff,
  STP_SCOPE_MIN_ENUM = -0x7fffffff - 1
} stp_option_scope;

typedef enum stp_fp_class
{
  STP_FP_NORMAL = 0,
  STP_FP_SUBNORMAL,
  STP_FP_ZERO,
  STP_FP_INFINITY,
  STP_FP_NAN,
  STP_FP_MAX_ENUM = 0x7fffffff,
  STP_FP_MIN_ENUM = -0x7fffffff - 1
} stp_fp_class;

typedef enum stp_internal_error_policy
{
  STP_POISON = 0,
  STP_ABORT = 1,
  STP_POLICY_MAX_ENUM = 0x7fffffff,
  STP_POLICY_MIN_ENUM = -0x7fffffff - 1
} stp_internal_error_policy;

/* ------------------------------------------------------------------ by-value structs (the six public layouts) */
typedef struct stp_result
{
  stp_result_kind kind;
  stp_unknown_reason reason; /**< STP_REASON_NONE unless kind == STP_UNKNOWN */
} stp_result;

typedef struct stp_entailment
{
  stp_validity kind;
  stp_unknown_reason reason;
} stp_entailment;

typedef struct stp_budget
{
  bool has_time;
  uint64_t time_ms; /**< 0 means: give up at once; past the clock's range (about 292 years), no limit */
  bool has_conflicts;
  uint64_t conflicts;
} stp_budget;

typedef struct stp_error
{
  stp_error_code code;
  bool recoverable;    /**< false only for RESOURCE and INTERNAL */
  const char* message; /**< owned by the object that holds the record (a static string for
                          an out-of-memory RESOURCE); valid until the record is cleared or
                          the object dies */
  const char* function; /**< the C API function that refused */
  int argument_index;   /**< 0-based; -1 if not applicable */
  const char* option;   /**< the option name for OPTION_* codes; NULL otherwise */
  int line, column;     /**< PARSE: 1-based line and column of the failure; 0 when unknown or another code */
} stp_error;

typedef struct stp_float_value
{
  uint32_t exp_size, sig_size; /**< the format; sig_size includes the hidden bit */
  bool sign;
  uint64_t biased_exponent; /**< exp_size bits */
  stp_fp_class cls;
  /* the trailing significand is read separately: stp_term_fp_significand_limbs /
   * stp_model_fp_significand_limbs (ceil((sig_size - 1) / 64) limbs, LSB first) */
} stp_float_value;

typedef struct stp_version
{
  int major, minor, patch;
  const char* string;
  const char* git_sha;
  const char* git_tag;
  const char* build_info;
} stp_version;

/* ------------------------------------------------------------------ library (infallible unless stated) */
STP_API stp_version stp_get_version(void); /**< strings are static; never freed */
STP_API char* stp_capability(const char* key); /**< NULL if unknown; else caller-owned (stp_free) */
STP_API char* stp_capabilities(void);          /**< "key=value\n..." caller-owned */
STP_API bool stp_has_sat_backend(const char* name);
STP_API size_t stp_num_sat_backends(void);
STP_API const char* stp_sat_backend_name(size_t i); /**< static; NULL when i is out of range */
STP_API void stp_free(void* p);                     /**< the one release function for every returned buffer */
/** thread-local: the most recent error of a call that had no object to record into (stp_tm_new,
 * stp_options_new, a NULL object handle, the registry queries); NULL when none since the last
 * stp_clear_last_error. Its strings live until the next such error on the thread or the clear.
 * Clear it before a registry query whose every answer is also a valid one
 * (stp_option_info_tier("typo") is STABLE), and read it after. */
STP_API const stp_error* stp_last_error(void);
STP_API void stp_clear_last_error(void);
STP_API void stp_set_internal_error_policy(stp_internal_error_policy); /**< process-wide */
STP_API stp_internal_error_policy stp_get_internal_error_policy(void);
STP_API const char* stp_kind_name(stp_kind);     /**< "BV_ADD"; "?" out of range */
STP_API const char* stp_kind_smtlib(stp_kind);   /**< "bvadd" */
STP_API const char* stp_rm_name(stp_rm);         /**< "RNE" */
STP_API const char* stp_unknown_reason_name(stp_unknown_reason);
STP_API const char* stp_error_code_name(stp_error_code);
STP_API const char* stp_result_kind_name(stp_result_kind);
STP_API const char* stp_validity_name(stp_validity);

/* ------------------------------------------------------------------ term manager */
STP_API stp_tm stp_tm_new(stp_options manager_options); /**< NULL: defaults; a SET solver-scoped entry is OPTION_VALUE */
STP_API stp_tm stp_tm_new_with(bool simplify, stp_rm default_rounding_mode, uint32_t uf_sort_width); /**< the three manager entries as arguments */
STP_API stp_tm stp_tm_copy(stp_tm);     /**< another handle to the same manager */
STP_API void stp_tm_release(stp_tm);    /**< the manager dies when nothing refers to it */
STP_API uint64_t stp_tm_id(stp_tm);     /**< process-unique; 0 for NULL */
STP_API bool stp_tm_simplify_enabled(stp_tm); /**< construction-time folding on? */
STP_API stp_rm stp_tm_default_rounding_mode(stp_tm);
STP_API stp_status stp_tm_set_default_rounding_mode(stp_tm, stp_rm);
STP_API uint32_t stp_tm_uf_sort_width(stp_tm);

/** reclamation (the C runtime). Each node carries two external counts: unscoped references
 * (owned by the caller) and scoped references (owned by the innermost open scope, which
 * keeps a journal of them). Four rules:
 *   1. A handle a function RETURNS while a scope is open is scoped; with no scope open it
 *      is unscoped.
 *   2. stp_term_copy(t) always yields an UNSCOPED reference: "copy" means "keep". That is
 *      how a handle produced inside a scope survives the scope.
 *   3. stp_term_release(t) gives back one unscoped reference; if t has none it is
 *      STP_ERR_STATE ("scoped handle: copy it to keep it, or let the scope pop") and nothing
 *      happens.
 *   4. stp_tm_scope_pop releases every reference in the popped journal; stp_tm_release_all
 *      releases every external reference of the manager, scoped and unscoped, and empties
 *      every journal (the scopes stay open). C++ Terms in the same process hold engine
 *      references of their own and are unaffected.
 * Every unscoped reference and every open scope keeps the manager alive; a sort handle does
 * not (sorts are owned by the manager and valid while it lives). The scope functions are
 * infallible (a NULL argument does nothing; a pop with no scope open does nothing). */
STP_API void stp_tm_scope_push(stp_tm);
STP_API void stp_tm_scope_pop(stp_tm);
STP_API size_t stp_tm_scope_depth(stp_tm); /**< open scopes */
STP_API void stp_tm_release_all(stp_tm);   /**< term references only; solver, model, options and statistics handles have their own release */
/* errors */
STP_API const stp_error* stp_tm_error(stp_tm); /**< NULL when no error is pending; infallible */
STP_API size_t stp_tm_error_num_terms(stp_tm); /**< the terms involved in the recorded error (e.g. both operands) */
STP_API stp_term stp_tm_error_term(stp_tm, size_t i); /**< +1; a FOREIGN_MANAGER error lists no term (it would be another manager's) */
STP_API size_t stp_tm_error_num_sorts(stp_tm); /**< the sorts involved in the recorded error */
STP_API stp_sort stp_tm_error_sort(stp_tm, size_t i);
STP_API void stp_tm_clear_error(stp_tm);
typedef void (*stp_error_callback)(const stp_error*, void* user); /**< sees every error; may return; the call still fails; must not call the library; the pointer is valid during the call only */
STP_API void stp_tm_set_error_callback(stp_tm, stp_error_callback, void* user);

/* ------------------------------------------------------------------ sorts */
/** Names supplied to stp_tm_declare_sort, stp_declare and stp_tm_bind_symbol,
 * and prefixes supplied to stp_mk_fresh_sort and stp_mk_fresh, must be
 * representable as SMT-LIB quoted symbols: no '|', backslash, DEL, or ASCII
 * control characters other than tab, newline and carriage return. Spaces
 * and non-ASCII bytes (including UTF-8) are allowed; printing quotes where
 * needed. Leading '@' and '.' are reserved for solver use. Violations are
 * INVALID_ARGUMENT before any name is recorded. Names must be nonempty;
 * fresh-name prefixes may be empty. As with all C strings, the first NUL
 * terminates the name or prefix. */
STP_API stp_sort stp_mk_bool_sort(stp_tm);
STP_API stp_sort stp_mk_bv_sort(stp_tm, uint32_t width); /**< INVALID_ARGUMENT if width == 0 */
STP_API stp_sort stp_mk_fp_sort(stp_tm, uint32_t exp_size, uint32_t sig_size); /**< each >= 2 */
STP_API stp_sort stp_mk_fp16_sort(stp_tm);
STP_API stp_sort stp_mk_fp32_sort(stp_tm);
STP_API stp_sort stp_mk_fp64_sort(stp_tm);
STP_API stp_sort stp_mk_fp128_sort(stp_tm);
STP_API stp_sort stp_mk_rm_sort(stp_tm);
STP_API stp_sort stp_mk_real_sort(stp_tm);
STP_API stp_sort stp_mk_array_sort(stp_tm, stp_sort index, stp_sort element); /**< UNSUPPORTED for combinations the engine lacks */
STP_API stp_sort stp_mk_fun_sort(stp_tm, size_t arity, const stp_sort* domain, stp_sort codomain);
STP_API stp_sort stp_tm_declare_sort(stp_tm, const char* name); /**< a named uninterpreted sort, keyed by name; INVALID_ARGUMENT for a sort SMT-LIB predefines (Bool, Real, ...) */
STP_API stp_sort stp_mk_fresh_sort(stp_tm, const char* prefix); /**< anonymous; printed as prefix!k; NULL prefix means "" */
STP_API stp_sort stp_sort_copy(stp_sort); /**< the same handle */
STP_API void stp_sort_release(stp_sort);  /**< a no-op: sorts are pooled by the manager */
STP_API stp_status stp_sort_get_kind(stp_sort, stp_sort_kind* out);
STP_API stp_status stp_sort_bv_size(stp_sort, uint32_t* out);      /**< INVALID_ARGUMENT unless a BV sort */
STP_API stp_status stp_sort_fp_exp_size(stp_sort, uint32_t* out);  /**< INVALID_ARGUMENT unless an FP sort */
STP_API stp_status stp_sort_fp_sig_size(stp_sort, uint32_t* out);  /**< includes the hidden bit */
STP_API stp_sort stp_sort_array_index(stp_sort);
STP_API stp_sort stp_sort_array_element(stp_sort);
STP_API stp_status stp_sort_fun_arity(stp_sort, uint32_t* out);
STP_API stp_sort stp_sort_fun_domain(stp_sort, uint32_t i);
STP_API stp_sort stp_sort_fun_codomain(stp_sort);
STP_API char* stp_sort_name(stp_sort); /**< uninterpreted sorts only */
STP_API uint64_t stp_sort_id(stp_sort); /**< manager-unique; 0 for NULL */
STP_API char* stp_sort_str(stp_sort);   /**< SMT-LIB 2 */
STP_API stp_tm stp_sort_manager(stp_sort); /**< +1 handle */

/* ------------------------------------------------------------------ symbols and values */
STP_API stp_term stp_declare(stp_tm, const char* name, stp_sort); /**< the manager's name table: the same (name, sort) gives the same term; SORT_MISMATCH on a clash; INVALID_ARGUMENT for a name SMT-LIB predefines (true, select, bvadd, RNE, ...) */
STP_API stp_term stp_mk_fresh(stp_tm, stp_sort, const char* prefix); /**< anonymous, never in the name table; printed as prefix!k; NULL prefix means "" */
STP_API stp_term stp_tm_symbol(stp_tm, const char* name); /**< NULL, no error, if absent; define-fun: the body if nullary, otherwise a callable function term */
STP_API stp_status stp_tm_bind_symbol(stp_tm, const char* name, stp_term); /**< enter an existing symbol into the table under this name; SORT_MISMATCH if taken, INVALID_ARGUMENT for a compound term or a predefined name */
STP_API size_t stp_tm_num_symbols(stp_tm); /**< declared symbols and parameterized definitions, distinct identities */
STP_API stp_term stp_tm_symbol_at(stp_tm, size_t i);
STP_API size_t stp_tm_num_declared_sorts(stp_tm);
STP_API stp_sort stp_tm_declared_sort_at(stp_tm, size_t i);
STP_API stp_term stp_tm_term_from_id(stp_tm, uint64_t id); /**< INVALID_ARGUMENT if no live term has that id */
STP_API stp_term stp_mk_true(stp_tm);
STP_API stp_term stp_mk_false(stp_tm);
STP_API stp_term stp_mk_bool(stp_tm, bool);
STP_API stp_term stp_mk_bv_uint64(stp_tm, uint32_t width, uint64_t value); /**< VALUE_OUT_OF_RANGE unless it fits */
STP_API stp_term stp_mk_bv_int64(stp_tm, uint32_t width, int64_t value);   /**< two's complement range of width */
STP_API stp_term stp_mk_bv_str(stp_tm, uint32_t width, const char* digits, int base); /**< base 2, 10, 16; `#b`/`#x`/0x; '-' in base 10; '_' between two digits */
STP_API stp_term stp_mk_bv_limbs(stp_tm, uint32_t width, size_t n, const uint64_t* lsb_first);
STP_API stp_term stp_mk_bv_bytes(stp_tm, uint32_t width, size_t n, const uint8_t* bytes, bool little_endian);
STP_API stp_term stp_mk_bv_wrapped(stp_tm, uint32_t width, uint64_t value); /**< value mod 2^width, by name */
STP_API stp_term stp_mk_bv_zero(stp_tm, uint32_t width);
STP_API stp_term stp_mk_bv_ones(stp_tm, uint32_t width);
STP_API stp_term stp_mk_bv_min_signed(stp_tm, uint32_t width);
STP_API stp_term stp_mk_bv_max_signed(stp_tm, uint32_t width);
STP_API stp_term stp_mk_fp_from_bits(stp_tm, stp_sort fp, stp_term bv_value); /**< NaN canonicalised */
STP_API stp_term stp_mk_fp_from_bits_str(stp_tm, stp_sort fp, const char* bits); /**< "0b..", "0x.." or bare binary */
STP_API stp_term stp_mk_fp(stp_tm, stp_term sign, stp_term exponent, stp_term significand); /**< (fp ...); symbolic allowed */
STP_API stp_term stp_mk_fp_pos_zero(stp_tm, stp_sort fp);
STP_API stp_term stp_mk_fp_neg_zero(stp_tm, stp_sort fp);
STP_API stp_term stp_mk_fp_pos_inf(stp_tm, stp_sort fp);
STP_API stp_term stp_mk_fp_neg_inf(stp_tm, stp_sort fp);
STP_API stp_term stp_mk_fp_nan(stp_tm, stp_sort fp); /**< the canonical quiet NaN of the format */
STP_API stp_term stp_mk_fp_double(stp_tm, stp_sort fp, stp_rm rm, double value); /**< exact, then rounded once under rm */
STP_API stp_term stp_mk_fp_decimal(stp_tm, stp_sort fp, stp_rm rm, const char* literal); /**< "0.1", "1/3", "-2.5e-3" */
STP_API stp_term stp_mk_rm(stp_tm, stp_rm);
STP_API stp_term stp_mk_real_int64(stp_tm, int64_t);
STP_API stp_term stp_mk_real_fraction(stp_tm, int64_t numerator, int64_t denominator); /**< INVALID_ARGUMENT if 0 */
STP_API stp_term stp_mk_real_str(stp_tm, const char* literal); /**< "-3/7", "0.25", "12" */
STP_API stp_term stp_mk_const_array(stp_tm, stp_sort array_sort, stp_term element); /**< every cell equals element, which may be symbolic */
STP_API stp_term stp_array_from_bytes(stp_tm, size_t n, const uint8_t* bytes, uint32_t index_width); /**< sugar: store chain over (as const ... 0) */

/* ------------------------------------------------------------------ generic construction */
/** indices in SMT-LIB order; result_sort is required for CONST_ARRAY and ignored otherwise */
STP_API stp_term stp_mk_term(stp_tm, stp_kind, size_t n, const stp_term* args); /**< args may be NULL when n == 0 */
STP_API stp_term stp_mk_term_indexed(stp_tm, stp_kind, size_t n, const stp_term* args, size_t m, const uint32_t* idx);
STP_API stp_term stp_mk_term_sorted(stp_tm, stp_kind, size_t n, const stp_term* args, size_t m, const uint32_t* idx, stp_sort result);
STP_API stp_term stp_mk_term1(stp_tm, stp_kind, stp_term);
STP_API stp_term stp_mk_term2(stp_tm, stp_kind, stp_term, stp_term);
STP_API stp_term stp_mk_term3(stp_tm, stp_kind, stp_term, stp_term, stp_term);
STP_API stp_term stp_mk_term1_indexed1(stp_tm, stp_kind, stp_term, uint32_t);
STP_API stp_term stp_mk_term1_indexed2(stp_tm, stp_kind, stp_term, uint32_t, uint32_t);
STP_API stp_term stp_mk_term2_indexed1(stp_tm, stp_kind, stp_term, stp_term, uint32_t);
STP_API stp_term stp_mk_term2_indexed2(stp_tm, stp_kind, stp_term, stp_term, uint32_t, uint32_t);

/* ------------------------------------------------------------------ named constructors */
/* One per non-indexed kind, generated from kinds.toml: stp_bvadd(tm, a, b), stp_fp_fma(tm, rm, a,
 * b, c), stp_select(tm, a, i), stp_store(tm, a, i, v), ... The n-ary Boolean kinds take a count
 * first (stp_and(tm, n, args) with a binary stp_and2); the other n-ary kinds are binary with an
 * _n form (stp_bvadd_n(tm, n, args), stp_concat_n). APPLY is stp_apply(tm, f, x) and
 * stp_apply_n(tm, n, args) with args[0] the function. */
#include <stp/api/gen/kind_ctors.h>

/** the indexed and sort-taking constructors, by hand */
STP_API stp_term stp_extract(stp_tm, uint32_t hi, uint32_t lo, stp_term);
STP_API stp_term stp_zero_extend(stp_tm, uint32_t k, stp_term);
STP_API stp_term stp_sign_extend(stp_tm, uint32_t k, stp_term);
STP_API stp_term stp_repeat(stp_tm, uint32_t k, stp_term);
STP_API stp_term stp_rotate_left(stp_tm, uint32_t k, stp_term);
STP_API stp_term stp_rotate_right(stp_tm, uint32_t k, stp_term);
STP_API stp_term stp_bit(stp_tm, stp_term bv, uint32_t i); /**< sugar: (= ((_ extract i i) bv) `#b1`) */
STP_API stp_term stp_bool_to_bv1(stp_tm, stp_term b);      /**< sugar: (ite b `#b1` `#b0`) */
STP_API stp_term stp_bv1_to_bool(stp_tm, stp_term bv1);    /**< sugar: (= bv1 `#b1`) */
STP_API stp_term stp_to_fp(stp_tm, stp_sort fp, stp_term rm, stp_term fp_or_real_or_sbv); /**< (_ to_fp e s) by argument sort */
STP_API stp_term stp_to_fp_unsigned(stp_tm, stp_sort fp, stp_term rm, stp_term bv);
STP_API stp_term stp_to_fp_from_bits(stp_tm, stp_sort fp, stp_term bv); /**< the reinterpretation */
STP_API stp_term stp_fp_to_ubv(stp_tm, uint32_t m, stp_term rm, stp_term);
STP_API stp_term stp_fp_to_sbv(stp_tm, uint32_t m, stp_term rm, stp_term);
/** Every FP function taking a stp_term rm also has a _rm variant taking stp_rm. */
STP_API stp_term stp_fp_add_rm(stp_tm, stp_rm, stp_term, stp_term);
STP_API stp_term stp_fp_sub_rm(stp_tm, stp_rm, stp_term, stp_term);
STP_API stp_term stp_fp_mul_rm(stp_tm, stp_rm, stp_term, stp_term);
STP_API stp_term stp_fp_div_rm(stp_tm, stp_rm, stp_term, stp_term);
STP_API stp_term stp_fp_fma_rm(stp_tm, stp_rm, stp_term, stp_term, stp_term);
STP_API stp_term stp_fp_sqrt_rm(stp_tm, stp_rm, stp_term);
STP_API stp_term stp_fp_rti_rm(stp_tm, stp_rm, stp_term);
STP_API stp_term stp_to_fp_rm(stp_tm, stp_sort fp, stp_rm, stp_term fp_or_real_or_sbv);
STP_API stp_term stp_to_fp_unsigned_rm(stp_tm, stp_sort fp, stp_rm, stp_term bv);
STP_API stp_term stp_fp_to_ubv_rm(stp_tm, uint32_t m, stp_rm, stp_term);
STP_API stp_term stp_fp_to_sbv_rm(stp_tm, uint32_t m, stp_rm, stp_term);

/* ------------------------------------------------------------------ terms: identity, introspection, readers */
STP_API stp_term stp_term_copy(stp_term);       /**< always unscoped: "copy" means "keep" (rule 2) */
STP_API stp_status stp_term_release(stp_term);  /**< STATE for a scoped handle (rule 3) */
STP_API uint64_t stp_term_id(stp_term);         /**< infallible; 0 for NULL */
STP_API uint64_t stp_term_hash(stp_term);       /**< infallible; 0 for NULL */
STP_API stp_tm stp_term_manager(stp_term);      /**< +1 handle */
STP_API stp_status stp_term_get_kind(stp_term, stp_kind* out); /**< the public view; guaranteed under simplify = false only */
STP_API stp_sort stp_term_sort(stp_term);
STP_API stp_status stp_term_num_children(stp_term, size_t* out);
STP_API stp_term stp_term_child(stp_term, size_t i); /**< INDEX_OUT_OF_RANGE */
STP_API stp_status stp_term_num_indices(stp_term, size_t* out);
STP_API stp_status stp_term_index(stp_term, size_t i, uint32_t* out);
STP_API bool stp_term_is_value(stp_term); /**< infallible; false for NULL */
STP_API bool stp_term_is_defined_function(stp_term); /**< a parameterized define-fun; false for NULL */
STP_API bool stp_term_is_const(stp_term); /**< a declared symbol; infallible; false for NULL */
STP_API char* stp_term_symbol(stp_term);  /**< NULL, no error, if anonymous or not a symbol */
STP_API char* stp_term_str(stp_term);     /**< SMT-LIB 2, untruncated; works while an error is pending */
STP_API char* stp_term_to_string(stp_term, stp_format, bool share_subterms);
STP_API stp_term stp_term_substitute(stp_term, size_t n, const stp_term* from, const stp_term* to);
STP_API stp_term stp_tm_simplify(stp_tm, stp_term); /**< local rewrites only; touches no solver; an unspecified floating-point case (fp.min of +0 and -0, fp.to_ubv of NaN, ...) stays as it is */
STP_API bool stp_term_same(stp_term, stp_term); /**< structural: the same node (== on the handles) */
/** readers: NOT_A_VALUE unless the term is a value; SORT_MISMATCH on the wrong sort; DOES_NOT_FIT where stated */
STP_API stp_status stp_term_to_bool(stp_term, bool* out);
STP_API bool stp_term_fits_uint64(stp_term); /**< false (no record) unless a BV value that fits */
STP_API bool stp_term_fits_int64(stp_term);
STP_API stp_status stp_term_to_uint64(stp_term, uint64_t* out);
STP_API stp_status stp_term_to_int64(stp_term, int64_t* out); /**< two's complement of the width */
STP_API char* stp_term_to_bv_string(stp_term, int base, bool pad); /**< base 2, 10 or 16 */
STP_API stp_status stp_term_bv_num_limbs(stp_term, size_t* out); /**< ceil(width/64) */
STP_API stp_status stp_term_to_bv_limbs(stp_term, size_t n, uint64_t* out_lsb_first); /**< caller buffer of n >= num_limbs */
STP_API stp_status stp_term_to_bv_bytes(stp_term, size_t n, uint8_t* out, bool little_endian); /**< n >= ceil(width/8) */
STP_API stp_status stp_term_to_fp(stp_term, stp_float_value* out);
STP_API stp_status stp_term_fp_significand_limbs(stp_term, size_t n, uint64_t* out_lsb_first); /**< the sig_size-1 trailing bits */
STP_API char* stp_term_fp_bits(stp_term); /**< IEEE interchange bits, MSB first */
STP_API stp_status stp_term_fp_to_double(stp_term, double* out); /**< DOES_NOT_FIT for formats wider than binary64 */
STP_API stp_status stp_term_fp_to_rational(stp_term, char** numerator, char** denominator); /**< finite values only (INVALID_ARGUMENT otherwise); two caller-owned strings */
STP_API stp_status stp_term_to_rm(stp_term, stp_rm* out);
STP_API char* stp_term_real_numerator(stp_term);   /**< decimal; may carry a leading '-' */
STP_API char* stp_term_real_denominator(stp_term); /**< decimal; > 0; lowest terms */
STP_API bool stp_term_real_fits_int64(stp_term);
STP_API stp_status stp_term_real_to_int64(stp_term, int64_t* num, int64_t* den); /**< DOES_NOT_FIT */
STP_API stp_status stp_term_real_to_double(stp_term, double* out); /**< nearest double */
STP_API stp_status stp_term_to_uninterpreted_index(stp_term, uint64_t* out);

/* ------------------------------------------------------------------ options (a standalone value; errors through stp_options_error) */
/* A duration option's "none" (no limit; max-time's default) as the *_duration_ms functions spell
 * it: the getters report it, and the setters take it back as "none". Every other duration is a
 * count of milliseconds up to INT64_MAX; a larger one is VALUE_OUT_OF_RANGE. */
#define STP_DURATION_NONE UINT64_MAX
STP_API stp_options stp_options_new(void); /**< every entry at its default */
STP_API stp_options stp_options_copy(stp_options);
STP_API void stp_options_delete(stp_options);
STP_API const stp_error* stp_options_error(stp_options); /**< the object's own sticky record (same shape and rule as the manager's) */
STP_API void stp_options_clear_error(stp_options);
/** by name; the string form parses the value exactly as the CLI parses it (durations need a unit: "500ms", "0.5s";
 * integers read as C reads them: 0x10 is 16, 010 is 8) */
STP_API stp_status stp_options_set_str(stp_options, const char* name, const char* value);
STP_API stp_status stp_options_set_bool(stp_options, const char* name, bool);
STP_API stp_status stp_options_set_int64(stp_options, const char* name, int64_t);
STP_API stp_status stp_options_set_uint64(stp_options, const char* name, uint64_t);
STP_API stp_status stp_options_set_duration_ms(stp_options, const char* name, uint64_t ms);
STP_API stp_status stp_options_set_names(stp_options, const char* name, size_t n, const char* const* members); /**< set-typed */
/* by enum (stable tier) */
STP_API stp_status stp_options_set_bool_e(stp_options, stp_option, bool);
STP_API stp_status stp_options_set_int64_e(stp_options, stp_option, int64_t);
STP_API stp_status stp_options_set_uint64_e(stp_options, stp_option, uint64_t);
STP_API stp_status stp_options_set_str_e(stp_options, stp_option, const char*);
STP_API stp_status stp_options_set_duration_ms_e(stp_options, stp_option, uint64_t ms);
/** CLI syntax: argv is the option list only (no program name); the stp binary passes argv + 1. A flag
 * (a bool, or a mode such as incremental) takes a value only after '='; `--no-<bool>` takes none. */
STP_API stp_status stp_options_set_args(stp_options, int argc, const char* const* argv);
/* read back */
STP_API char* stp_options_get_str(stp_options, const char* name); /**< the value as the CLI would print it; a set-typed entry's members comma-separated (C++ get_names) */
STP_API stp_status stp_options_get_bool(stp_options, const char* name, bool* out);
STP_API stp_status stp_options_get_int64(stp_options, const char* name, int64_t* out);
STP_API stp_status stp_options_get_uint64(stp_options, const char* name, uint64_t* out);
STP_API stp_status stp_options_get_duration_ms(stp_options, const char* name, uint64_t* out);
STP_API char* stp_options_resolved_str(stp_options, const char* name); /**< after implications */
STP_API bool stp_options_is_set(stp_options, const char* name);
STP_API stp_status stp_options_reset(stp_options, const char* name);
STP_API void stp_options_reset_all(stp_options);
STP_API stp_status stp_options_resolve(stp_options); /**< OPTION_CONFLICT / OPTION_UNAVAILABLE */
STP_API size_t stp_options_num_names(int tier /* -1: all, else stp_tier */);
STP_API const char* stp_options_name(int tier, size_t i); /**< static; NULL out of range */
STP_API char* stp_options_help(int tier);
STP_API const char* stp_option_name(stp_option); /**< static; NULL out of range */
STP_API stp_status stp_option_from_name(const char* name, stp_option* out); /**< OPTION_UNKNOWN unless a stable entry (aliases accepted) */
/** introspection, one field per call (no public struct with strings in it); the const char* results
 * are static; every function records OPTION_UNKNOWN in the thread-local record for an unknown name */
STP_API const char* stp_option_info_type(const char* name); /**< "bool" | "int" | "uint" | "mode" | "enum" | "set" | "string" | "path" | "duration"; NULL if unknown */
STP_API const char* stp_option_info_python_key(const char* name);
STP_API char* stp_option_info_default(const char* name); /**< as the CLI would print it */
STP_API stp_tier stp_option_info_tier(const char* name);
STP_API stp_settable stp_option_info_settable(const char* name);
STP_API stp_option_scope stp_option_info_scope(const char* name);
STP_API const char* stp_option_info_category(const char* name);
STP_API const char* stp_option_info_help(const char* name);
STP_API bool stp_option_info_supported(const char* name); /**< false when the build lacks what it needs */
STP_API stp_status stp_option_info_range(const char* name, bool* has_min, int64_t* min, bool* has_max, int64_t* max);
STP_API size_t stp_option_info_num_values(const char* name);
STP_API const char* stp_option_info_value(const char* name, size_t i);
STP_API size_t stp_option_info_num_aliases(const char* name);
STP_API const char* stp_option_info_alias(const char* name, size_t i);
STP_API const char* stp_option_info_short(const char* name);    /**< "" if none */
STP_API const char* stp_option_info_negation(const char* name); /**< "" if none */

/* ------------------------------------------------------------------ solver */
STP_API stp_solver stp_solver_new(stp_tm, stp_options /* NULL: defaults; copied */); /**< any number of solvers per manager, each with its own stack, options and models */
STP_API void stp_solver_delete(stp_solver); /**< terms, sorts and models stay valid */
STP_API const stp_error* stp_solver_failed(stp_solver); /**< the failure that put the solver in its failed state; NULL if none; infallible */
STP_API size_t stp_solver_failed_num_terms(stp_solver); /**< the terms and sorts of that failure, as stp_tm_error_term/_sort */
STP_API stp_term stp_solver_failed_term(stp_solver, size_t i); /**< +1 */
STP_API size_t stp_solver_failed_num_sorts(stp_solver);
STP_API stp_sort stp_solver_failed_sort(stp_solver, size_t i);
STP_API void stp_solver_clear_error(stp_solver);        /**< leave the failed state */
STP_API stp_tm stp_solver_manager(stp_solver);          /**< +1 handle */
/** the LIVE options: same names as the stp_options_* setters and getters, on the solver,
 * reporting through the manager's record; a write outside the entry's Settable window is
 * OPTION_TIMING. No stp_options handle to the live view exists (nothing to delete by
 * mistake); stp_solver_options_copy gives a detached value. */
STP_API stp_status stp_solver_set_str(stp_solver, const char* name, const char* value);
STP_API stp_status stp_solver_set_bool(stp_solver, const char* name, bool);
STP_API stp_status stp_solver_set_int64(stp_solver, const char* name, int64_t);
STP_API stp_status stp_solver_set_uint64(stp_solver, const char* name, uint64_t);
STP_API stp_status stp_solver_set_duration_ms(stp_solver, const char* name, uint64_t ms);
STP_API stp_status stp_solver_set_names(stp_solver, const char* name, size_t n, const char* const* members);
STP_API stp_status stp_solver_set_bool_e(stp_solver, stp_option, bool);
STP_API stp_status stp_solver_set_int64_e(stp_solver, stp_option, int64_t);
STP_API stp_status stp_solver_set_uint64_e(stp_solver, stp_option, uint64_t);
STP_API stp_status stp_solver_set_str_e(stp_solver, stp_option, const char*);
STP_API stp_status stp_solver_set_duration_ms_e(stp_solver, stp_option, uint64_t ms);
STP_API stp_status stp_solver_set_args(stp_solver, int argc, const char* const* argv);
STP_API char* stp_solver_get_str(stp_solver, const char* name);
STP_API stp_status stp_solver_get_bool(stp_solver, const char* name, bool* out);
STP_API stp_status stp_solver_get_int64(stp_solver, const char* name, int64_t* out);
STP_API stp_status stp_solver_get_uint64(stp_solver, const char* name, uint64_t* out);
STP_API stp_status stp_solver_get_duration_ms(stp_solver, const char* name, uint64_t* out);
STP_API char* stp_solver_resolved_str(stp_solver, const char* name);
STP_API bool stp_solver_option_is_set(stp_solver, const char* name);
STP_API stp_status stp_solver_reset_option(stp_solver, const char* name);
STP_API stp_status stp_solver_reset_all_options(stp_solver); /**< every entry back to its default, or none: OPTION_TIMING when an entry whose window has closed holds anything else */
STP_API stp_status stp_solver_resolve_options(stp_solver); /**< OPTION_CONFLICT / OPTION_UNAVAILABLE, as a check would find them */
STP_API stp_options stp_solver_options_copy(stp_solver); /**< a detached copy; delete it */
/* assertions and checks */
STP_API stp_status stp_solver_assert(stp_solver, stp_term); /**< SORT_MISMATCH unless Bool; FOREIGN_MANAGER; a NULL term is NULL_HANDLE and fails the solver */
STP_API stp_status stp_solver_push(stp_solver, uint32_t n);
STP_API stp_status stp_solver_pop(stp_solver, uint32_t n); /**< INVALID_ARGUMENT if n > level; nothing removed */
STP_API uint32_t stp_solver_level(stp_solver);
STP_API char* stp_solver_declared_logic(stp_solver); /**< the logic the last successful parse named in set-logic, "" for none (not the "logic" option); caller-owned (stp_free) */
STP_API size_t stp_solver_num_assertions(stp_solver); /**< outermost first */
STP_API stp_term stp_solver_assertion(stp_solver, size_t i);
STP_API stp_status stp_solver_reset_assertions(stp_solver); /**< keeps options */
STP_API stp_status stp_solver_reset(stp_solver);            /**< assertions gone, options back to defaults, engine rebuilt */
STP_API stp_status stp_solver_check_sat(stp_solver, stp_result* out); /**< out is written on STP_OK only */
STP_API stp_status stp_solver_check_sat_assuming(stp_solver, size_t n, const stp_term* assumptions, stp_result* out);
STP_API stp_status stp_solver_check_sat_budget(stp_solver, size_t n, const stp_term* assumptions, const stp_budget* /* NULL: the options' limits */, stp_result* out);
STP_API stp_status stp_solver_entails(stp_solver, stp_term formula, const stp_budget* /* NULL */, stp_entailment* out);
STP_API char* stp_solver_last_reason_message(stp_solver); /**< the sentence behind the LAST result's reason ("" unless unknown); overwritten by the next check */
STP_API size_t stp_solver_num_unsat_assumptions(stp_solver); /**< after unsat: the failed subset (0 if there were no assumptions); after sat/unknown: STATE (and 0) */
STP_API stp_term stp_solver_unsat_assumption(stp_solver, size_t i);
/** models: the model of the last check that answered sat, until the next check (assert/push/pop do not invalidate it) */
STP_API stp_model stp_solver_model(stp_solver);           /**< NO_MODEL unless the last check answered sat */
STP_API stp_model stp_solver_candidate_model(stp_solver); /**< NULL, no error, if there is none */
STP_API stp_term stp_solver_value(stp_solver, stp_term);  /**< one lookup in the shared snapshot */
/** interrupts: safe from any thread and from a signal handler; consumed by the check that
 * reports INTERRUPTED (a check an EXECUTE-mode input runs included); a pending interrupt with no
 * check running makes the next check return INTERRUPTED at once; INTERRUPTED > TIMEOUT >
 * CONFLICT_LIMIT */
STP_API void stp_solver_interrupt(stp_solver);
STP_API void stp_solver_clear_interrupt(stp_solver); /**< discard a pending interrupt */
STP_API bool stp_solver_interrupt_pending(stp_solver);
typedef bool (*stp_terminate_callback)(void* user); /**< true: stop. Runs inside the check: it must not call the library except stp_solver_interrupt */
STP_API stp_status stp_solver_set_terminator(stp_solver, stp_terminate_callback, void* user); /**< NULL clears */
STP_API stp_statistics stp_solver_statistics(stp_solver); /**< a snapshot */
/** symbols and scripts (the name table is the manager's) */
STP_API stp_term stp_solver_symbol(stp_solver, const char* name); /**< NULL, no error, if unknown */
STP_API stp_status stp_solver_parse_smt2(stp_solver, const char* script, stp_parse_mode);
STP_API stp_status stp_solver_parse(stp_solver, const char* text, stp_format); /**< SMT-LIB 2: SMTLIB2 or AUTO */
STP_API stp_status stp_solver_parse_file(stp_solver, const char* path, stp_format); /**< SMT-LIB 2: SMTLIB2 or AUTO */
STP_API stp_term stp_solver_parse_term(stp_solver, const char* smt2_term); /**< over the manager's name table */
STP_API char* stp_solver_to_smt2(stp_solver, bool with_check_sat);
STP_API char* stp_solver_to_string(stp_solver, stp_format); /**< SMTLIB2, DOT, GDL */
typedef void (*stp_text_sink)(const char* text, size_t len, void* user);
/** the batch pipeline encodes the assertions up to its first CNF without solving (whatever
 * incremental says), delivered as DIMACS in one call; *scope (NULL: not wanted) says how the CNF
 * relates to them. Not a check: the last check's result, model and failed assumptions stay, a
 * pending interrupt stays pending, the CNF sink does not see it. STATE when an interrupt or a
 * budget stops it first; UNSUPPORTED when the pipeline ends before a CNF for another reason */
STP_API stp_status stp_solver_write_cnf(stp_solver, stp_text_sink, void* user, stp_cnf_scope* scope);
STP_API void stp_solver_set_diagnostic_sink(stp_solver, stp_text_sink, void* user); /**< where diagnostic-tier options write, "Fatal Error:" reports included; NULL: nowhere; must not call the library (STATE) */
/** the input read as far as the parser needs it: the source fills up to max bytes and returns
 * how many, 0 at the end and (size_t)-1 if reading failed (the parse then fails with IO);
 * AUTO reads SMT-LIB 2. The source must not call the library (STATE), and runs under the
 * process-wide parser lock */
typedef size_t (*stp_text_source)(char* buf, size_t max, void* user);
STP_API stp_status stp_solver_parse_source(stp_solver, stp_text_source, void* user, stp_format, stp_parse_mode);
STP_API void stp_solver_set_output_sink(stp_solver, stp_text_sink, void* user); /**< the responses of an EXECUTE or PARSE_ONLY input and what the printing options print; a call with len 0 asks for a flush; NULL: nowhere. A SAT backend's own report (print-functionstat) comes here from CryptoMiniSat only: CaDiCaL and MiniSat write theirs to stdout themselves. Must not call the library (STATE) */
typedef void (*stp_fatal_error_handler)(const char* message, void* user);
STP_API void stp_solver_set_fatal_error_handler(stp_solver, stp_fatal_error_handler, void* user); /**< told of an engine fatal error in this solver's work before anything unwinds; may end the process; must not call the library; NULL: none */
typedef void (*stp_cnf_sink)(const char* dimacs, size_t len, stp_cnf_scope scope, void* user);
STP_API void stp_solver_set_cnf_sink(stp_solver, stp_cnf_sink, void* user); /**< every CNF a check hands to the SAT solver, as DIMACS; NULL: none; must not call the library (STATE) */

/* ------------------------------------------------------------------ model (a detached snapshot) */
STP_API stp_model stp_model_copy(stp_model);
STP_API void stp_model_release(stp_model);
STP_API stp_tm stp_model_manager(stp_model); /**< +1 handle */
/** a VALUE of the term's sort; symbols outside the core are completed. An array's value is the
 * constant array of its default under a store per cell (stp_array_value_as_term); a function has
 * none (SORT_MISMATCH: read it with stp_model_fun_value) */
STP_API stp_term stp_model_value(stp_model, stp_term);
STP_API stp_term stp_model_try_value(stp_model, stp_term); /**< NULL, no error, if completion would be needed; an array whose base is in the core, default included, needs none */
STP_API stp_status stp_model_values(stp_model, size_t n, const stp_term* in, stp_term* out); /**< batch, all or nothing; on STP_OK every out[i] is +1 */
STP_API stp_status stp_model_bool(stp_model, stp_term, bool* out);
STP_API stp_status stp_model_uint64(stp_model, stp_term, uint64_t* out); /**< DOES_NOT_FIT */
STP_API stp_status stp_model_int64(stp_model, stp_term, int64_t* out);
STP_API char* stp_model_bv_string(stp_model, stp_term, int base, bool pad);
STP_API stp_status stp_model_bv_num_limbs(stp_model, stp_term, size_t* out);
STP_API stp_status stp_model_bv_limbs(stp_model, stp_term, size_t n, uint64_t* out_lsb_first);
STP_API stp_status stp_model_bv_bytes(stp_model, stp_term, size_t n, uint8_t* out, bool little_endian);
STP_API stp_status stp_model_fp(stp_model, stp_term, stp_float_value* out);
STP_API stp_status stp_model_fp_significand_limbs(stp_model, stp_term, size_t n, uint64_t* out_lsb_first);
STP_API stp_status stp_model_fp_to_double(stp_model, stp_term, double* out);
STP_API stp_status stp_model_rm(stp_model, stp_term, stp_rm* out);
STP_API char* stp_model_real_numerator(stp_model, stp_term);
STP_API char* stp_model_real_denominator(stp_model, stp_term);
STP_API stp_status stp_model_uninterpreted_index(stp_model, stp_term, uint64_t* out);
STP_API stp_array_value stp_model_array_value(stp_model, stp_term array); /**< any array-sorted term */
STP_API stp_fun_value stp_model_fun_value(stp_model, stp_term fun);       /**< any function symbol */
/** dense read of a BV-indexed BV-element array whose element width is a multiple of 8
 * (INVALID_ARGUMENT otherwise): count elements from first_index, little-endian bytes per
 * element, completed by the model's array fill rule; INVALID_ARGUMENT when the elements
 * leave the index sort */
STP_API stp_status stp_model_array_bytes(stp_model, stp_term array, uint64_t first_index, size_t count, uint8_t* out);
STP_API size_t stp_model_num_symbols(stp_model); /**< the model core: symbols the solver assigned */
STP_API stp_term stp_model_symbol(stp_model, size_t i);
STP_API bool stp_model_in_core(stp_model, stp_term symbol); /**< false: value() would complete it */
STP_API char* stp_model_to_smt2(stp_model);                 /**< the whole model */
/* array values */
STP_API void stp_array_value_release(stp_array_value);
STP_API stp_sort stp_array_value_sort(stp_array_value);
STP_API stp_term stp_array_value_default(stp_array_value); /**< a VALUE of the element sort */
STP_API size_t stp_array_value_size(stp_array_value);      /**< explicit entries */
STP_API stp_status stp_array_value_entry(stp_array_value, size_t i, stp_term* index, stp_term* element); /**< +1 each; ascending by unsigned index value; a cell the model records, every other one holds the default */
STP_API stp_term stp_array_value_at(stp_array_value, stp_term index_value); /**< the element, default if absent */
STP_API stp_term stp_array_value_as_term(stp_array_value); /**< store chain over (as const ...); re-assertable */
/* function values */
STP_API void stp_fun_value_release(stp_fun_value);
STP_API stp_sort stp_fun_value_sort(stp_fun_value);
STP_API uint32_t stp_fun_value_arity(stp_fun_value);
/** A define-fun has a symbolic body instead of a table: size, entry and else
 * report UNSUPPORTED. apply evaluates it in the saved model; as_ite returns
 * its body over the supplied formals, with free symbols fixed to the model
 * (UNSUPPORTED for parameter-dependent partial floating-point operations). */
STP_API bool stp_fun_value_is_tabular(stp_fun_value);
STP_API stp_term stp_fun_value_else(stp_fun_value); /**< always ground: a VALUE of the codomain */
STP_API size_t stp_fun_value_size(stp_fun_value);
STP_API stp_status stp_fun_value_entry(stp_fun_value, size_t i, size_t n, stp_term* args_out /* n slots, at least the arity */, stp_term* value); /**< an application the model records; INVALID_ARGUMENT if n is below the arity */
STP_API stp_term stp_fun_value_apply(stp_fun_value, size_t n, const stp_term* arg_values);
STP_API stp_term stp_fun_value_as_ite(stp_fun_value, size_t n, const stp_term* formals);

/* ------------------------------------------------------------------ statistics (a snapshot keyed by the names in statistics.toml) */
STP_API void stp_statistics_release(stp_statistics);
STP_API size_t stp_statistics_size(stp_statistics);
STP_API const char* stp_statistics_name(stp_statistics, size_t i); /**< owned by the handle; NULL out of range */
STP_API bool stp_statistics_is_uint64(stp_statistics, const char* name);
STP_API bool stp_statistics_is_double(stp_statistics, const char* name);
STP_API stp_status stp_statistics_uint64(stp_statistics, const char* name, uint64_t* out); /**< INVALID_ARGUMENT for an unknown name or a string statistic */
STP_API stp_status stp_statistics_double(stp_statistics, const char* name, double* out);
STP_API char* stp_statistics_str(stp_statistics, const char* name); /**< any statistic, as text */
STP_API stp_tier stp_statistics_tier(const char* name); /**< STP_TIER_STABLE (and a thread-local INVALID_ARGUMENT) for an unknown name */

#ifdef __cplusplus
}
#endif
#endif /* STP_STP_H */

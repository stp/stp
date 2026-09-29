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

// stp.hpp -- the STP 3.x C++ API.
//
// This header is the primary API. The C header (stp.h) and the Cython module
// (stp._core) are derived from it. Everything here is a value type or a movable
// handle; nothing here aborts, exits or prints on its own.
//
// Requires C++17. Requires exceptions. Does not require RTTI.
//
// Conventions
//   - Every precondition is checked in every build type and reported by throwing
//     stp::RecoverableError with a code from stp::ErrorCode. A recoverable error
//     leaves every object exactly as it was.
//   - stp::UnsafeError (RESOURCE, INTERNAL) poisons the object it occurred in;
//     every later call on it throws STATE with the original code in the message.
//   - Terms, sorts and models are values: copying is O(1), destruction order is
//     free. A TermManager lives while anything that came from it lives.
//   - Threads: a manager and the solvers and models over it are used by one
//     thread at a time, whichever thread that is; independent managers run
//     concurrently, except that parses take one process-wide lock for their
//     whole length -- a check an EXECUTE input runs, and a wait on the input
//     stream, included. Solver::interrupt() is the one call safe from any
//     thread and from a signal handler.
//   - Callbacks (the sinks, the terminator, the fatal-error handler, the
//     stream a parse reads) must not call the library: every call from one is
//     refused with STATE, but interrupt(), clear_interrupt() and
//     interrupt_pending().
//   - Term == Term and Term != Term BUILD terms (SMT-LIB '=' and 'distinct').
//     Term has no conversion to bool, so `if (a == b)` does not compile; the
//     structural test is a.same_as(b). std::equal_to<Term> is structural and
//     std::less<Term> orders by id, so every standard container works.
//   - Literal operands: an integer beside a BV or Real term takes that term's
//     sort and must fit (two's complement range for BV); a floating-point
//     number beside an FP term is converted exactly and rounded once under the
//     call's rounding mode, or the manager's default mode for operators.
//     Nothing wraps or truncates silently.
//
// Everything is declared in namespace stp::api and re-exported into namespace
// stp with a using-directive, so client code writes stp::Term, stp::Solver and
// so on. The nested namespace exists because the engine that implements this
// API keeps its own stp::Kind and stp::UnknownReason.

#ifndef STP_STP_HPP
#define STP_STP_HPP

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <functional>
#include <initializer_list>
#include <iosfwd>
#include <map>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

#if defined(__has_include)
#if __has_include(<stp/api/version.hpp>)
#include <stp/api/version.hpp>
#endif
#endif

// Export macro, with the engine's convention (DLL_PUBLIC in
// stp/Util/Attributes.h): on Windows a __declspec only when libstp is a DLL
// (STP_SHARED_LIB, which STP's CMake package gives its consumers), dllexport
// while the API itself is compiled (STP_API_BUILDING) and dllimport
// otherwise; nothing for a static libstp or when STP_STATIC is defined.
// Elsewhere, default visibility. STP_API_EXPORT_INLINE marks the templates and
// is empty everywhere.
#ifndef STP_API_EXPORT
#if defined(_WIN32) || defined(__CYGWIN__)
#if defined(STP_STATIC) || !defined(STP_SHARED_LIB)
#define STP_API_EXPORT
#elif defined(STP_API_BUILDING)
#define STP_API_EXPORT __declspec(dllexport)
#else
#define STP_API_EXPORT __declspec(dllimport)
#endif
#else
#define STP_API_EXPORT __attribute__((visibility("default")))
#endif
#endif
#ifndef STP_API_EXPORT_INLINE
#define STP_API_EXPORT_INLINE
#endif

#include <stp/api/gen/errors.hpp>
#include <stp/api/gen/kinds.hpp>
#include <stp/api/gen/options.hpp>

namespace stp
{
namespace api
{

// ---------------------------------------------------------------------------
// 1. Enumerations. Every enumerator's value is pinned and append-only; the same
//    tables generate the C enums and the Python enums (kinds.toml, options.toml,
//    errors.toml, statistics.toml). Kind, Option and ErrorCode are generated.
// ---------------------------------------------------------------------------

enum class SortKind : std::uint8_t
{
  BOOL = 0,
  BV,
  FP,
  RM,
  REAL,
  ARRAY,
  FUN,
  UNINTERPRETED
};

/// Contiguous; the engine's one-hot carrier is internal.
enum class RoundingMode : std::uint8_t
{
  RNE = 0,
  RNA,
  RTP,
  RTN,
  RTZ
};

enum class UnknownReason : std::uint8_t
{
  NONE = 0,            ///< the result is not unknown
  TIMEOUT,             ///< a time budget expired
  CONFLICT_LIMIT,      ///< a conflict budget expired
  INTERRUPTED,         ///< interrupt() or a Terminator fired
  INCOMPLETE,          ///< the decision procedure is incomplete for this input
  RESOURCE_LIMIT,      ///< an internal resource budget (AIG nodes, ...)
  CARRIER_EXHAUSTED,   ///< an uninterpreted sort ran out of carrier width
  ASSUMED_INJECTIVITY, ///< the answer depended on an injectivity assumption
  STOPPED_AFTER_CNF,   ///< option stop-after-cnf was set
  OTHER
};

enum class Verdict : std::uint8_t
{
  SAT = 1,
  UNSAT = 2,
  UNKNOWN = 3
}; ///< no zero member
enum class Validity : std::uint8_t
{
  VALID = 1,
  INVALID = 2,
  UNKNOWN = 3
};
enum class Format : std::uint8_t
{
  AUTO = 0,
  SMTLIB2,
  SMTLIB1,
  CVC,
  DOT,
  GDL
};
/// How a parse treats its input.
///   DECLARE_AND_ASSERT: the input's declarations, assertions and scopes
///     take effect, silently; check-sat is not executed, and a CVC or
///     SMT-LIB 1 query is asserted negated, so that check_sat() answers it.
///   EXECUTE: the input runs as the stp command line runs it, answering to
///     the output sink: every SMT-LIB 2 command, under the script's own
///     set-logic; a CVC or SMT-LIB 1 input's query decided and answered
///     ("Valid."/"Invalid.", "sat"/"unsat"). Those checks are the input's,
///     not the solver's: they leave no result or model behind. As on the
///     command line, an equality between whole arrays needs
///     array-equality = on there (UNSUPPORTED otherwise).
///   PARSE_ONLY: EXECUTE without the deciding (the command line's
///     --parse-only): check-sat is skipped, and a CVC or SMT-LIB 1 query is
///     left undecided and unasserted.
enum class ParseMode : std::uint8_t
{
  DECLARE_AND_ASSERT = 0,
  EXECUTE,
  PARSE_ONLY
};
/// How a CNF a check hands to the SAT solver relates to the query
/// (Solver::set_cnf_sink, Solver::write_cnf): the whole query; partial, a
/// refinement still to come (array reads, uninterpreted functions, Real
/// arithmetic, the floating-point abstraction) adding what the search asks
/// for; or an over-approximation, the bit-vector abstractions having replaced
/// operations with free inputs.
enum class CnfScope : std::uint8_t
{
  WHOLE = 0,
  PARTIAL,
  OVER_APPROXIMATION
};
enum class Tier : std::uint8_t
{
  STABLE = 0,
  EXPERT,
  EXPERIMENTAL,
  DIAGNOSTIC
};
enum class Settable : std::uint8_t
{
  ANYTIME = 0,
  BEFORE_FIRST_CHECK,
  CONSTRUCTION
};
enum class OptionScope : std::uint8_t
{
  SOLVER = 0,
  MANAGER
};
enum class InternalErrorPolicy : std::uint8_t
{
  POISON = 0,
  ABORT
};

STP_API_EXPORT const char* to_string(Kind);
STP_API_EXPORT const char* smtlib_name(Kind); ///< "bvadd", "fp.add", "select", ...
STP_API_EXPORT const char* to_string(SortKind);
STP_API_EXPORT const char* to_string(RoundingMode); ///< "RNE" ...
STP_API_EXPORT const char* to_string(UnknownReason);
STP_API_EXPORT const char* to_string(ErrorCode);
STP_API_EXPORT const char* to_string(Verdict);
STP_API_EXPORT const char* to_string(Validity);
STP_API_EXPORT const char* to_string(Tier);
STP_API_EXPORT const char* to_string(Settable);
STP_API_EXPORT std::ostream& operator<<(std::ostream&, Kind);
STP_API_EXPORT std::ostream& operator<<(std::ostream&, RoundingMode);
STP_API_EXPORT std::ostream& operator<<(std::ostream&, UnknownReason);
STP_API_EXPORT std::ostream& operator<<(std::ostream&, Verdict);
STP_API_EXPORT std::ostream& operator<<(std::ostream&, Validity);

class Term;
class Sort;
class TermManager;
class Options;
class SolverOptions;
class Solver;
class Model;

namespace detail
{
struct ManagerImpl;
struct SolverImpl;
struct ModelSnapshot;
struct OptionsImpl;
struct ErrorDetails;
struct ValueImpl;
} // namespace detail

// ---------------------------------------------------------------------------
// 2. Errors
// ---------------------------------------------------------------------------

class STP_API_EXPORT Error : public std::exception
{
public:
  ErrorCode code() const noexcept;
  bool recoverable() const noexcept; ///< every code except RESOURCE and INTERNAL
  const char* what() const noexcept override; ///< one line
  std::string_view function() const noexcept; ///< the API function that refused
  std::optional<int> argument_index() const noexcept; ///< 0-based, if any
  /// the terms involved; none for FOREIGN_MANAGER, whose term is another
  /// manager's, which may be in use on another thread
  const std::vector<Term>& terms() const noexcept;
  const std::vector<Sort>& sorts() const noexcept;
  std::string_view option() const noexcept; ///< for OPTION_* codes
  /// Parse errors: 1-based line and column of the failure (0 when unknown).
  int line() const noexcept;
  int column() const noexcept;

  explicit Error(std::shared_ptr<const detail::ErrorDetails>);
  Error(const Error&) noexcept;
  Error& operator=(const Error&) noexcept;
  ~Error() override;

protected:
  std::shared_ptr<const detail::ErrorDetails> d_;
};
/// The call had no effect.
class STP_API_EXPORT RecoverableError : public Error
{
public:
  using Error::Error;
};
/// The object is now poisoned.
class STP_API_EXPORT UnsafeError : public Error
{
public:
  using Error::Error;
};

// ---------------------------------------------------------------------------
// 3. Sorts and terms
// ---------------------------------------------------------------------------

class STP_API_EXPORT Sort
{
public:
  Sort() noexcept; ///< the null sort; is_null() is true
  Sort(const Sort&) noexcept;
  Sort(Sort&&) noexcept;
  Sort& operator=(const Sort&) noexcept;
  Sort& operator=(Sort&&) noexcept;
  ~Sort();
  bool is_null() const noexcept;
  explicit operator bool() const = delete; ///< no implicit truthiness

  SortKind kind() const;
  bool is_bool() const;
  bool is_bv() const;
  bool is_fp() const;
  bool is_rm() const;
  bool is_real() const;
  bool is_array() const;
  bool is_fun() const;
  bool is_uninterpreted() const;

  std::uint32_t bv_size() const;    ///< INVALID_ARGUMENT unless is_bv()
  std::uint32_t fp_exp_size() const; ///< INVALID_ARGUMENT unless is_fp()
  std::uint32_t fp_sig_size() const; ///< includes the hidden bit (SMT-LIB)
  Sort array_index() const;
  Sort array_element() const;
  std::vector<Sort> fun_domain() const;
  Sort fun_codomain() const;
  std::uint32_t fun_arity() const;
  std::string name() const; ///< uninterpreted sorts only

  std::uint64_t id() const noexcept; ///< manager-unique, never reused
  TermManager manager() const;
  std::string str() const; ///< SMT-LIB 2

  friend STP_API_EXPORT bool operator==(const Sort&, const Sort&) noexcept;
  friend STP_API_EXPORT bool operator!=(const Sort&, const Sort&) noexcept;
  friend STP_API_EXPORT bool operator<(const Sort&, const Sort&) noexcept;
  friend STP_API_EXPORT std::ostream& operator<<(std::ostream&, const Sort&);

  // internal
  Sort(detail::ManagerImpl*, std::uint32_t index) noexcept;
  detail::ManagerImpl* impl_manager() const noexcept { return mgr_; }
  std::uint32_t impl_index() const noexcept { return index_; }

private:
  detail::ManagerImpl* mgr_;
  std::uint32_t index_;
};

struct FloatValue;
struct RationalValue;

/// A term is one intrusive pointer to a hash-consed engine node. Equal terms
/// are the same node. The node pins its manager. A value term (kind() ==
/// VALUE) is a term like any other: it can be asserted, compared and decoded.
/// A symbol prints as its declared name, or as prefix!k if made by mk_fresh.
class STP_API_EXPORT Term
{
public:
  Term() noexcept; ///< the null term
  Term(const Term&) noexcept;
  Term(Term&&) noexcept;
  Term& operator=(const Term&) noexcept;
  Term& operator=(Term&&) noexcept;
  ~Term();
  bool is_null() const noexcept;
  explicit operator bool() const = delete;

  Kind kind() const;
  Sort sort() const;
  std::size_t num_children() const;
  Term child(std::size_t i) const; ///< INDEX_OUT_OF_RANGE
  std::vector<Term> children() const;
  std::vector<std::uint32_t> indices() const; ///< empty unless indexed
  std::uint64_t id() const noexcept; ///< unique within the manager; never reused
  TermManager manager() const;

  bool is_value() const noexcept; ///< kind() == VALUE
  bool is_const() const noexcept; ///< kind() == CONSTANT (a declared symbol)
  std::optional<std::string> symbol() const; ///< the declared name, if any

  // -- typed readers; every one throws NOT_A_VALUE unless is_value(),
  //    SORT_MISMATCH on the wrong sort, and DOES_NOT_FIT where stated.
  bool to_bool() const;
  bool fits_uint64() const;
  bool fits_int64() const; ///< int64: two's complement of the BV's own width
  std::uint64_t to_uint64() const; ///< DOES_NOT_FIT if width > 64 and too big
  std::int64_t to_int64() const;
  /// base 2, 10 or 16; padded to the width for 2 and 16 (ceil(n/4) hex digits)
  std::string to_bv_string(int base = 2, bool pad = true) const;
  std::vector<std::uint64_t> to_bv_limbs() const; ///< LSB-first, ceil(w/64)
  std::vector<std::uint8_t> to_bv_bytes(bool little_endian = true) const;
  FloatValue to_fp() const;
  RoundingMode to_rm() const;
  RationalValue to_rational() const;
  std::uint64_t to_uninterpreted_index() const; ///< element index in its sort

  // -- sugar
  Term operator[](const Term& index) const; ///< select
  Term operator()(std::initializer_list<Term> args) const; ///< APPLY
  Term operator()(const std::vector<Term>& args) const;
  template <class... Ts>
  Term operator()(const Term& first, const Ts&... rest) const
  {
    return (*this)(std::vector<Term>{first, rest...});
  }

  Term substitute(const std::vector<std::pair<Term, Term>>& map) const;
  std::string str() const; ///< SMT-LIB 2, untruncated, no let-sharing; any depth
  /// SMT-LIB 2 with let-sharing, CVC, DOT or GDL through the engine's
  /// printers, which recurse once per level of the term: one some ten
  /// thousand levels deep can overflow the stack there (str() cannot).
  std::string to_string(Format f, bool share_subterms = true) const;

  bool same_as(const Term&) const noexcept; ///< structural: the same node
  struct Less
  {
    bool operator()(const Term&, const Term&) const noexcept;
  }; ///< by id; std::less<Term> is this
  friend STP_API_EXPORT Term operator==(const Term&, const Term&); ///< EQUAL
  friend STP_API_EXPORT Term operator!=(const Term&, const Term&); ///< DISTINCT
  friend STP_API_EXPORT std::ostream& operator<<(std::ostream&, const Term&);

  // internal: the node is the engine's ASTInternal*, retained
  Term(detail::ManagerImpl*, void* node) noexcept;
  detail::ManagerImpl* impl_manager() const noexcept { return mgr_; }
  void* impl_node() const noexcept { return node_; }

private:
  detail::ManagerImpl* mgr_;
  void* node_;
};

struct STP_API_EXPORT FloatValue
{
  std::uint32_t exp_size = 0, sig_size = 0; ///< sig_size includes the hidden bit
  bool sign = false;
  std::uint64_t biased_exponent = 0; ///< exp_size bits
  std::vector<std::uint64_t> significand; ///< sig_size-1 trailing bits, LSB-first
  // INF and NOT_A_NUMBER rather than the obvious names: INFINITY and NAN are
  // <cmath> macros, and INFINITE is <windows.h>'s.
  enum class Class : std::uint8_t
  {
    NORMAL,
    SUBNORMAL,
    ZERO,
    INF,
    NOT_A_NUMBER
  } cls = Class::ZERO;
  std::string bits() const; ///< exp_size+sig_size interchange bits, MSB first
  std::optional<double> to_double() const; ///< exact for formats <= binary64
  std::optional<RationalValue> to_rational() const; ///< finite values only
};

struct STP_API_EXPORT RationalValue
{
  std::string numerator;   ///< decimal; may carry a leading '-'
  std::string denominator; ///< decimal; > 0; lowest terms
  bool fits_int64() const; ///< both parts
  std::int64_t num64() const;
  std::int64_t den64() const; ///< DOES_NOT_FIT
  double to_double() const; ///< nearest double
  std::string str() const; ///< "-3/7" or "12"
};

// ---------------------------------------------------------------------------
// 4. The term manager
// ---------------------------------------------------------------------------

/// A shared handle. Copies share one manager. The manager is destroyed when
/// the last handle, term, sort, solver and model referring to it is destroyed.
class STP_API_EXPORT TermManager
{
public:
  struct Config
  {
    bool simplify = true;
    RoundingMode default_rounding_mode = RoundingMode::RNE;
    std::uint32_t uf_sort_width = 16;
  };
  TermManager(); ///< Config{}
  explicit TermManager(const Config&);
  /// The same three entries by registry name; a solver-scoped entry that is
  /// SET in it is OPTION_VALUE.
  explicit TermManager(const Options& manager_options);
  TermManager(const TermManager&) noexcept;
  TermManager(TermManager&&) noexcept;
  TermManager& operator=(const TermManager&) noexcept;
  TermManager& operator=(TermManager&&) noexcept;
  ~TermManager();

  std::uint64_t id() const noexcept; ///< process-unique
  friend STP_API_EXPORT bool operator==(const TermManager&,
                                        const TermManager&) noexcept;
  friend STP_API_EXPORT bool operator!=(const TermManager&,
                                        const TermManager&) noexcept;

  bool simplify() const noexcept; ///< construction-time folding; fixed
  RoundingMode default_rounding_mode() const noexcept;
  void set_default_rounding_mode(RoundingMode);
  std::uint32_t uf_sort_width() const noexcept;

  // -- sorts
  Sort mk_bool_sort();
  Sort mk_bv_sort(std::uint32_t width); ///< INVALID_ARGUMENT if width == 0
  Sort mk_fp_sort(std::uint32_t exp_size, std::uint32_t sig_size); ///< each >= 2
  Sort mk_fp16_sort();
  Sort mk_fp32_sort();
  Sort mk_fp64_sort();
  Sort mk_fp128_sort();
  Sort mk_rm_sort();
  Sort mk_real_sort();
  Sort mk_array_sort(const Sort& index, const Sort& element); ///< UNSUPPORTED for combinations the engine lacks
  Sort mk_fun_sort(const std::vector<Sort>& domain, const Sort& codomain);
  Sort declare_sort(std::string_view name); ///< named uninterpreted sort, keyed by name
  Sort mk_fresh_sort(std::string_view prefix = ""); ///< anonymous, printed as prefix!k

  // -- symbols: two doors with two purposes
  /// A named symbol, keyed by name in the manager's one name table: the same
  /// name and sort give the same term whether it comes from this call, from
  /// Python's BitVec('x', 32), from a parsed script or from bind_symbol;
  /// SORT_MISMATCH if the name is already declared at another sort. Any string
  /// is a legal name; the printer quotes it where SMT-LIB requires.
  Term declare(std::string_view name, const Sort&);
  /// An anonymous symbol that never enters the name table: fresh on every call,
  /// printed as prefix!k with a manager-unique k.
  Term mk_fresh(const Sort&, std::string_view prefix = "");
  std::optional<Term> symbol(std::string_view name) const; ///< name table lookup
  std::vector<Term> symbols() const; ///< every declared symbol, declaration order
  std::vector<Sort> declared_sorts() const; ///< every declared sort, declaration order
  void bind_symbol(std::string_view name, const Term&); ///< a symbol under a second name: SORT_MISMATCH if taken, INVALID_ARGUMENT for a compound term
  Term term_from_id(std::uint64_t id) const; ///< INVALID_ARGUMENT if no live term has that id

  // -- values (strict)
  Term mk_true();
  Term mk_false();
  Term mk_bool(bool);
  Term mk_bv(std::uint32_t width, std::uint64_t value); ///< VALUE_OUT_OF_RANGE unless value < 2^width
  Term mk_bv_signed(std::uint32_t width, std::int64_t value); ///< two's complement range
  /// base 2/10/16; optional #b/#x/0x; '-' in base 10; '_' between two digits
  /// separates them
  Term mk_bv(std::uint32_t width, std::string_view digits, int base);
  Term mk_bv_limbs(std::uint32_t width, const std::vector<std::uint64_t>& lsb_first);
  Term mk_bv_bytes(std::uint32_t width, const std::vector<std::uint8_t>& bytes,
                   bool little_endian = true);
  Term mk_bv_wrapped(std::uint32_t width, std::uint64_t value); ///< value mod 2^width
  Term mk_bv_zero(std::uint32_t width);
  Term mk_bv_ones(std::uint32_t width);
  Term mk_bv_min_signed(std::uint32_t width);
  Term mk_bv_max_signed(std::uint32_t width);

  Term mk_fp_from_bits(const Sort& fp, const Term& bv_value); ///< NaN canonicalised
  Term mk_fp_from_bits(const Sort& fp, std::string_view bits); ///< "0b..", "0x.." or bare binary
  Term mk_fp(const Term& sign, const Term& exponent, const Term& significand); ///< (fp ...); symbolic allowed
  Term mk_fp_pos_zero(const Sort& fp);
  Term mk_fp_neg_zero(const Sort& fp);
  Term mk_fp_pos_inf(const Sort& fp);
  Term mk_fp_neg_inf(const Sort& fp);
  Term mk_fp_nan(const Sort& fp); ///< the canonical quiet NaN of the format
  Term mk_fp(const Sort& fp, RoundingMode rm, double value); ///< exact, then rounded once under rm
  Term mk_fp(const Sort& fp, RoundingMode rm, std::string_view decimal_or_rational); ///< "0.1", "1/3", "-2.5e-3"
  Term mk_rm(RoundingMode);

  Term mk_real(std::int64_t);
  Term mk_real(std::int64_t numerator, std::int64_t denominator); ///< INVALID_ARGUMENT if 0
  Term mk_real(std::string_view literal); ///< "-3/7", "0.25", "12"

  Term mk_const_array(const Sort& array_sort, const Term& element); ///< element: a value (no symbol in it), UNSUPPORTED otherwise

  // -- the generic constructor; indices in SMT-LIB order. result_sort is
  //    required for CONST_ARRAY and ignored otherwise, so a walker can rebuild
  //    any term from kind(), children(), indices() and sort().
  Term mk_term(Kind, const std::vector<Term>& args,
               const std::vector<std::uint32_t>& indices = {},
               std::optional<Sort> result_sort = std::nullopt);
  Term mk_term(Kind, std::initializer_list<Term> args,
               std::initializer_list<std::uint32_t> indices = {});

  Term simplify(const Term&) const; ///< local rewrites only; touches no solver; an unspecified floating-point case (fp.min of +0 and -0, fp.to_ubv of NaN, ...) stays as it is

  // internal
  explicit TermManager(detail::ManagerImpl*) noexcept; ///< retains
  detail::ManagerImpl* impl() const noexcept { return impl_; }

private:
  detail::ManagerImpl* impl_;
};

// -- literal operands. One constrained template per family, so that `x * 3`,
//    `eq(x, 7)` and `fp_add(RNE, a, 1.5)` are never ambiguous: any integral
//    type except bool goes through the int64/uint64 path (by its signedness),
//    any floating type through double.
template <class I>
using if_integral =
    std::enable_if_t<std::is_integral_v<I> && !std::is_same_v<I, bool>, int>;
template <class F>
using if_floating = std::enable_if_t<std::is_floating_point_v<F>, int>;

namespace detail
{
STP_API_EXPORT Term mk_named(Kind, const char* fn, const std::vector<Term>& args);
STP_API_EXPORT Term int_literal_signed(const Term& like, std::int64_t);
STP_API_EXPORT Term int_literal_unsigned(const Term& like, std::uint64_t);
STP_API_EXPORT Term int_literal_signed(const Term& like, std::int64_t, const Term& rm);
STP_API_EXPORT Term int_literal_unsigned(const Term& like, std::uint64_t, const Term& rm);
STP_API_EXPORT Term float_literal(const Term& like, double);
STP_API_EXPORT Term float_literal(const Term& like, double, const Term& rm);
STP_API_EXPORT Term rm_term(const Term& like, RoundingMode);
template <class I>
Term int_literal(const Term& like, I v)
{
  if constexpr (std::is_signed_v<I>)
    return int_literal_signed(like, static_cast<std::int64_t>(v));
  else
    return int_literal_unsigned(like, static_cast<std::uint64_t>(v));
}
template <class I>
Term int_literal(const Term& like, I v, const Term& rm)
{
  if constexpr (std::is_signed_v<I>)
    return int_literal_signed(like, static_cast<std::int64_t>(v), rm);
  else
    return int_literal_unsigned(like, static_cast<std::uint64_t>(v), rm);
}
STP_API_EXPORT Term op_add(const Term&, const Term&);
STP_API_EXPORT Term op_sub(const Term&, const Term&);
STP_API_EXPORT Term op_mul(const Term&, const Term&);
STP_API_EXPORT Term op_div(const Term&, const Term&);
STP_API_EXPORT Term op_neg(const Term&);
} // namespace detail

// -- named constructors: one per kind, generated from kinds.toml (SMT-LIB
//    spelling with '.' -> '_'), plus the literal overloads.
#include <stp/api/gen/kind_ctors.hpp>

// -- the indexed and sort-taking constructors, by hand
STP_API_EXPORT Term extract(std::uint32_t hi, std::uint32_t lo, const Term&);
STP_API_EXPORT Term zero_extend(std::uint32_t k, const Term&);
STP_API_EXPORT Term sign_extend(std::uint32_t k, const Term&);
STP_API_EXPORT Term repeat(std::uint32_t k, const Term&);
STP_API_EXPORT Term rotate_left(std::uint32_t k, const Term&);
STP_API_EXPORT Term rotate_right(std::uint32_t k, const Term&);
STP_API_EXPORT Term concat(const Term&, const Term&); // declared by the generator too
STP_API_EXPORT Term bit(const Term& bv, std::uint32_t i); ///< (= ((_ extract i i) bv) #b1)
STP_API_EXPORT Term bool_to_bv1(const Term& b); ///< (ite b #b1 #b0)
STP_API_EXPORT Term bv1_to_bool(const Term& bv1); ///< (= bv1 #b1)
/// A store chain over (as const ... 0) holding `bytes` at indices [0, n) of an
/// Array BV[index_width] BV8.
STP_API_EXPORT Term array_from_bytes(TermManager& tm,
                                     const std::vector<std::uint8_t>& bytes,
                                     std::uint32_t index_width = 32);
/// The SMT-LIB (_ to_fp e s) family, by argument sort (FP, Real or signed BV).
STP_API_EXPORT Term to_fp(const Sort& fp, const Term& rm, const Term& fp_or_real_or_sbv);
STP_API_EXPORT Term to_fp(const Sort& fp, RoundingMode rm, const Term& fp_or_real_or_sbv);
STP_API_EXPORT Term to_fp_unsigned(const Sort& fp, const Term& rm, const Term& bv);
STP_API_EXPORT Term to_fp_unsigned(const Sort& fp, RoundingMode rm, const Term& bv);
STP_API_EXPORT Term to_fp_from_bits(const Sort& fp, const Term& bv); ///< the reinterpretation
STP_API_EXPORT Term fp_to_ubv(std::uint32_t m, const Term& rm, const Term&);
STP_API_EXPORT Term fp_to_sbv(std::uint32_t m, const Term& rm, const Term&);
STP_API_EXPORT Term fp_to_ubv(std::uint32_t m, RoundingMode rm, const Term&);
STP_API_EXPORT Term fp_to_sbv(std::uint32_t m, RoundingMode rm, const Term&);

// -- operators: only the unambiguous ones. Mixed sorts throw SORT_MISMATCH.
inline Term operator+(const Term& a, const Term& b) { return detail::op_add(a, b); } // BV: bvadd; Real: +; FP: fp.add (default mode)
inline Term operator-(const Term& a, const Term& b) { return detail::op_sub(a, b); }
inline Term operator*(const Term& a, const Term& b) { return detail::op_mul(a, b); }
inline Term operator/(const Term& a, const Term& b) { return detail::op_div(a, b); } // Real, FP; NOT BV
inline Term operator-(const Term& a) { return detail::op_neg(a); }
inline Term operator~(const Term& a) { return bvnot(a); }
inline Term operator&(const Term& a, const Term& b) { return bvand(a, b); }
inline Term operator|(const Term& a, const Term& b) { return bvor(a, b); }
inline Term operator^(const Term& a, const Term& b) { return bvxor(a, b); }
inline Term operator<<(const Term& a, const Term& b) { return bvshl(a, b); } // NOT >>: use bvlshr/bvashr
inline Term operator!(const Term& a) { return not_(a); }
inline Term operator&&(const Term& a, const Term& b) { return and_(a, b); } // builds a term; no short circuit
inline Term operator||(const Term& a, const Term& b) { return or_(a, b); }
// == and != build EQUAL and DISTINCT (declared in Term). No <, <=, >, >= on
// terms: the BV forms are signedness-ambiguous; use bvult/bvslt/real_lt/fp_lt.

// Mixed native/term forms of every operator above, == and != included.
#define STP_API_LITERAL_OPERATOR(op, fn)                                       \
  template <class I, if_integral<I> = 0>                                       \
  Term operator op(const Term& a, I b)                                         \
  {                                                                            \
    return fn(a, detail::int_literal(a, b));                                   \
  }                                                                            \
  template <class I, if_integral<I> = 0>                                       \
  Term operator op(I a, const Term& b)                                         \
  {                                                                            \
    return fn(detail::int_literal(b, a), b);                                   \
  }                                                                            \
  template <class F, if_floating<F> = 0>                                       \
  Term operator op(const Term& a, F b)                                         \
  {                                                                            \
    return fn(a, detail::float_literal(a, b));                                 \
  }                                                                            \
  template <class F, if_floating<F> = 0>                                       \
  Term operator op(F a, const Term& b)                                         \
  {                                                                            \
    return fn(detail::float_literal(b, a), b);                                 \
  }
STP_API_LITERAL_OPERATOR(+, detail::op_add)
STP_API_LITERAL_OPERATOR(-, detail::op_sub)
STP_API_LITERAL_OPERATOR(*, detail::op_mul)
STP_API_LITERAL_OPERATOR(/, detail::op_div)
STP_API_LITERAL_OPERATOR(==, eq)
STP_API_LITERAL_OPERATOR(!=, distinct)
#undef STP_API_LITERAL_OPERATOR
#define STP_API_LITERAL_BV_OPERATOR(op, fn)                                    \
  template <class I, if_integral<I> = 0>                                       \
  Term operator op(const Term& a, I b)                                         \
  {                                                                            \
    return fn(a, detail::int_literal(a, b));                                   \
  }                                                                            \
  template <class I, if_integral<I> = 0>                                       \
  Term operator op(I a, const Term& b)                                         \
  {                                                                            \
    return fn(detail::int_literal(b, a), b);                                   \
  }
STP_API_LITERAL_BV_OPERATOR(&, bvand)
STP_API_LITERAL_BV_OPERATOR(|, bvor)
STP_API_LITERAL_BV_OPERATOR(^, bvxor)
STP_API_LITERAL_BV_OPERATOR(<<, bvshl)
#undef STP_API_LITERAL_BV_OPERATOR

#include <stp/api/gen/kind_ctor_templates.hpp>

// ---------------------------------------------------------------------------
// 5. Options
// ---------------------------------------------------------------------------

using OptionValue = std::variant<bool, std::int64_t, std::uint64_t, std::string,
                                 std::vector<std::string>>;

struct STP_API_EXPORT OptionInfo
{
  std::string name;
  std::string python_key; ///< '-' and '.' become '_'
  std::string type; ///< bool|int|uint|mode|enum|set|string|path|duration
  OptionValue default_value;
  OptionValue current;
  OptionValue resolved; ///< after implications
  std::optional<std::int64_t> min, max;
  std::vector<std::string> values; ///< enum/set members
  Tier tier;
  Settable settable;
  OptionScope scope;
  std::string category;
  std::string help;
  bool supported; ///< false when requires.build is not satisfied
  bool is_set; ///< set explicitly since the last reset
  std::vector<std::string> aliases;
  std::string short_flag;
  std::string negation;
};

/// A value. Validated against the registry at every write. Every setter is
/// named by its type, so no literal can pick the wrong overload. Unknown names
/// are OPTION_UNKNOWN; bad values OPTION_VALUE.
class STP_API_EXPORT Options
{
public:
  Options(); ///< every entry at its default
  Options(const Options&);
  Options(Options&&) noexcept;
  Options& operator=(const Options&);
  Options& operator=(Options&&) noexcept;
  ~Options();

  // by name; the string forms parse the value exactly as the CLI does (a
  // duration string needs a unit: "500ms", "0.5s")
  void set(std::string_view name, std::string_view value);
  void set_bool(std::string_view name, bool);
  void set_int(std::string_view name, std::int64_t);
  void set_uint(std::string_view name, std::uint64_t);
  void set_str(std::string_view name, std::string_view); ///< string/enum/mode/path
  void set_names(std::string_view name, const std::vector<std::string>&); ///< set-typed
  /// -1 ms is "none" (no limit); any other negative duration is OPTION_VALUE.
  void set_duration(std::string_view name, std::chrono::milliseconds);
  // by enum: the stable tier only
  void set_bool(Option, bool);
  void set_int(Option, std::int64_t);
  void set_uint(Option, std::uint64_t);
  void set_str(Option, std::string_view);
  void set_duration(Option, std::chrono::milliseconds);
  // CLI syntax. argv is the option list only (no program name). Duration
  // values here need a unit.
  void set_args(const std::vector<std::string>& argv);
  void set_args(int argc, const char* const* argv);

  OptionValue get(std::string_view name) const;
  bool get_bool(std::string_view name) const;
  std::int64_t get_int(std::string_view name) const;
  std::uint64_t get_uint(std::string_view name) const;
  std::string get_str(std::string_view name) const;
  std::vector<std::string> get_names(std::string_view name) const;
  /// -1 ms for "none" (no limit, max-time's default).
  std::chrono::milliseconds get_duration(std::string_view name) const;
  OptionValue resolved(std::string_view name) const; ///< after implications
  bool is_set(std::string_view name) const;
  void reset(std::string_view name);
  void reset_all();
  OptionInfo info(std::string_view name) const;
  std::vector<std::string> names(std::optional<Tier> = std::nullopt) const;
  std::string help(std::optional<Tier> = std::nullopt) const;

  /// Applies `implied_by`/`follows`, checks `excludes` (OPTION_CONFLICT) and
  /// `requires` (OPTION_UNAVAILABLE). Solver calls it at construction and
  /// before every check.
  void resolve() const;

  static std::string name_of(Option);
  static std::optional<Option> stable_option(std::string_view name);

  // internal
  detail::OptionsImpl* impl() const noexcept { return impl_; }

private:
  detail::OptionsImpl* impl_;
};

/// The live options of a Solver: the same surface as Options, obtained from
/// Solver::options(). A write outside its entry's Settable window throws
/// OPTION_TIMING and leaves the value unchanged. Not copyable; copy() returns
/// a detached Options value.
class STP_API_EXPORT SolverOptions
{
public:
  SolverOptions(const SolverOptions&) = delete;
  SolverOptions& operator=(const SolverOptions&) = delete;
  Options copy() const;

  void set(std::string_view name, std::string_view value);
  void set_bool(std::string_view name, bool);
  void set_int(std::string_view name, std::int64_t);
  void set_uint(std::string_view name, std::uint64_t);
  void set_str(std::string_view name, std::string_view);
  void set_names(std::string_view name, const std::vector<std::string>&);
  void set_duration(std::string_view name, std::chrono::milliseconds);
  void set_bool(Option, bool);
  void set_int(Option, std::int64_t);
  void set_uint(Option, std::uint64_t);
  void set_str(Option, std::string_view);
  void set_duration(Option, std::chrono::milliseconds);
  void set_args(const std::vector<std::string>& argv);
  void set_args(int argc, const char* const* argv);
  OptionValue get(std::string_view name) const;
  bool get_bool(std::string_view name) const;
  std::int64_t get_int(std::string_view name) const;
  std::uint64_t get_uint(std::string_view name) const;
  std::string get_str(std::string_view name) const;
  std::vector<std::string> get_names(std::string_view name) const;
  std::chrono::milliseconds get_duration(std::string_view name) const;
  OptionValue resolved(std::string_view name) const;
  bool is_set(std::string_view name) const;
  void reset(std::string_view name);
  /// Every entry back to its default, or none: OPTION_TIMING when an entry
  /// whose window has closed holds anything else.
  void reset_all();
  OptionInfo info(std::string_view name) const;
  std::vector<std::string> names(std::optional<Tier> = std::nullopt) const;
  std::string help(std::optional<Tier> = std::nullopt) const;
  void resolve() const;

  // internal
  explicit SolverOptions(detail::SolverImpl*) noexcept;

private:
  friend class Solver;
  detail::SolverImpl* solver_;
};

// ---------------------------------------------------------------------------
// 6. Results, budgets, models, statistics
// ---------------------------------------------------------------------------

/// No conversion to bool, by design.
class STP_API_EXPORT Result
{
public:
  Result() noexcept; ///< UNKNOWN(OTHER)
  Result(Verdict, UnknownReason, std::string message) noexcept;
  Verdict verdict() const noexcept;
  bool is_sat() const noexcept;
  bool is_unsat() const noexcept;
  bool is_unknown() const noexcept;
  UnknownReason reason() const noexcept; ///< NONE unless is_unknown()
  std::string reason_message() const; ///< a sentence for people; empty unless unknown
  friend STP_API_EXPORT std::ostream& operator<<(std::ostream&, const Result&); ///< "sat" | "unsat" | "unknown (timeout)"
  std::string str() const;

private:
  Verdict verdict_;
  UnknownReason reason_;
  std::string message_;
};

/// The answer to entails(): is the formula true in every model of the assertions?
class STP_API_EXPORT Entailment
{
public:
  Entailment() noexcept;
  Entailment(Validity, UnknownReason, std::string message) noexcept;
  explicit Entailment(const Result& of_negation) noexcept;
  Validity validity() const noexcept;
  bool is_valid() const noexcept;
  bool is_invalid() const noexcept;
  bool is_unknown() const noexcept;
  UnknownReason reason() const noexcept;
  std::string reason_message() const;
  friend STP_API_EXPORT std::ostream& operator<<(std::ostream&, const Entailment&); ///< "valid" | "invalid" | "unknown (...)"
  std::string str() const;

private:
  Validity validity_;
  UnknownReason reason_;
  std::string message_;
};

/// Per-check overrides of the persistent max-time / max-num-confl options.
struct CheckBudget
{
  std::optional<std::chrono::milliseconds> time; ///< 0ms: give up at once; negative: INVALID_ARGUMENT
  std::optional<std::uint64_t> conflicts;
};

class STP_API_EXPORT ArrayValue
{
public:
  /// A cell the model records; every other cell holds default_value().
  struct Entry
  {
    Term index;
    Term element;
  };
  Sort sort() const;
  Term default_value() const; ///< a VALUE term of the element sort
  std::size_t size() const; ///< explicit entries
  Entry entry(std::size_t i) const; ///< ascending by unsigned index value
  std::vector<Entry> entries() const;
  Term at(const Term& index_value) const; ///< the element, default if absent; SORT_MISMATCH off the index sort
  Term as_term() const; ///< store chain over (as const ...); re-assertable

  // internal
  ArrayValue(std::shared_ptr<const detail::ValueImpl>) noexcept;
  ArrayValue(const ArrayValue&) noexcept;
  ArrayValue& operator=(const ArrayValue&) noexcept;
  ~ArrayValue();

private:
  std::shared_ptr<const detail::ValueImpl> impl_;
};

class STP_API_EXPORT FunctionValue
{
public:
  /// An application the model records; every other one is else_value().
  struct Entry
  {
    std::vector<Term> args;
    Term value;
  };
  Sort sort() const;
  std::size_t size() const;
  Entry entry(std::size_t i) const;
  std::vector<Entry> entries() const;
  Term else_value() const; ///< always ground: a VALUE of the codomain
  Term apply(const std::vector<Term>& arg_values) const;
  Term as_ite_term(const std::vector<Term>& formal_args) const;

  // internal
  FunctionValue(std::shared_ptr<const detail::ValueImpl>) noexcept;
  FunctionValue(const FunctionValue&) noexcept;
  FunctionValue& operator=(const FunctionValue&) noexcept;
  ~FunctionValue();

private:
  std::shared_ptr<const detail::ValueImpl> impl_;
};

/// A detached snapshot. One snapshot exists per successful check, taken at the
/// first model()/value() call (or before the solver's state changes) and
/// shared by every Model handle afterwards. Never refuses, never mutates.
class STP_API_EXPORT Model
{
public:
  TermManager manager() const;

  /// A VALUE of the term's sort; any term of this manager, built before or
  /// after the check; symbols outside the core are COMPLETED with their sort's
  /// default. An array's value is a term with no symbol in it: the constant
  /// array of its default under a store per cell (array_value(t).as_term()).
  /// A function has no value term: SORT_MISMATCH, read it with
  /// function_value.
  Term value(const Term&) const;
  /// nullopt instead of completing; an array is complete when its base is an
  /// array in the core (default included) or a constant array
  std::optional<Term> try_value(const Term&) const;
  std::vector<Term> values(const std::vector<Term>&) const; ///< batch (completing)

  bool bool_value(const Term&) const;
  std::uint64_t uint64_value(const Term&) const; ///< DOES_NOT_FIT
  std::int64_t int64_value(const Term&) const;
  std::string bv_string(const Term&, int base = 2, bool pad = true) const;
  std::vector<std::uint64_t> bv_limbs(const Term&) const;
  std::vector<std::uint8_t> bv_bytes(const Term&, bool little_endian = true) const;
  FloatValue fp_value(const Term&) const;
  RoundingMode rm_value(const Term&) const;
  RationalValue real_value(const Term&) const;
  std::uint64_t uninterpreted_index(const Term&) const;
  ArrayValue array_value(const Term&) const; ///< any array-sorted term
  FunctionValue function_value(const Term&) const; ///< any function-sorted term

  /// Dense read of a BV-indexed, BV-element array whose element width is a
  /// multiple of 8: elements [first_index, first_index + count) as
  /// little-endian bytes per element, completed by the model's array fill rule.
  /// INVALID_ARGUMENT when the interval leaves the index sort.
  void array_bytes(const Term& array, std::uint64_t first_index,
                   std::size_t count, std::uint8_t* out) const;

  std::vector<Term> symbols() const; ///< the model core: symbols the solver assigned
  bool in_core(const Term& symbol) const; ///< false: value() would complete it
  std::string to_smt2() const; ///< the whole model
  friend STP_API_EXPORT std::ostream& operator<<(std::ostream&, const Model&);

  // internal
  explicit Model(std::shared_ptr<const detail::ModelSnapshot>) noexcept;
  Model(const Model&) noexcept;
  Model& operator=(const Model&) noexcept;
  ~Model();
  const detail::ModelSnapshot* impl() const noexcept { return snap_.get(); }

private:
  std::shared_ptr<const detail::ModelSnapshot> snap_;
};

using StatisticValue = std::variant<std::uint64_t, double, std::string>;
/// A snapshot keyed by the names in statistics.toml. Never printed by the library.
class STP_API_EXPORT Statistics
{
public:
  Statistics();
  explicit Statistics(std::map<std::string, StatisticValue>);
  const std::map<std::string, StatisticValue>& entries() const;
  StatisticValue get(std::string_view name) const; ///< INVALID_ARGUMENT for an unknown name
  std::uint64_t uint64(std::string_view name) const;
  double real(std::string_view name) const;
  std::string str(std::string_view name) const;
  Tier tier(std::string_view name) const;
  friend STP_API_EXPORT std::ostream& operator<<(std::ostream&, const Statistics&);

private:
  std::map<std::string, StatisticValue> entries_;
};

/// Polled by every backend and by preprocessing at the same points as
/// interrupt(). It must not throw: an exception from it unwinds through the
/// engine, which is an engine failure (INTERNAL, RESOURCE for std::bad_alloc)
/// that poisons the manager.
class STP_API_EXPORT Terminator
{
public:
  virtual ~Terminator() = default;
  virtual bool terminate() = 0; ///< true: stop; the check returns unknown(INTERRUPTED)
};

// ---------------------------------------------------------------------------
// 7. The solver
// ---------------------------------------------------------------------------

class STP_API_EXPORT Solver
{
public:
  /// Copies options; resolve() runs here. Any number of solvers may be live
  /// over one manager; each has its own assertion stack, options and models.
  explicit Solver(TermManager tm, Options options = Options());
  Solver(Solver&&) noexcept;
  Solver& operator=(Solver&&) noexcept;
  Solver(const Solver&) = delete;
  Solver& operator=(const Solver&) = delete;
  ~Solver();

  TermManager manager() const;
  SolverOptions& options(); ///< live
  const SolverOptions& options() const;

  void assert_formula(const Term& bool_term); ///< SORT_MISMATCH unless Bool; FOREIGN_MANAGER
  void add(const Term& bool_term) { assert_formula(bool_term); }
  void push(std::uint32_t n = 1);
  void pop(std::uint32_t n = 1); ///< INVALID_ARGUMENT if n > level(); nothing removed
  std::uint32_t level() const noexcept;
  std::vector<Term> assertions() const; ///< outermost first
  void reset_assertions(); ///< keeps options
  void reset(); ///< assertions gone, options back to defaults, engine rebuilt

  Result check_sat();
  Result check_sat(const std::vector<Term>& assumptions,
                   std::optional<CheckBudget> budget = std::nullopt);
  Entailment entails(const Term& formula,
                     std::optional<CheckBudget> budget = std::nullopt);
  std::vector<Term> unsat_assumptions() const; ///< after unsat: the failed subset; after sat/unknown: STATE

  /// The model of the last check that answered sat, until the next check
  /// (assert, push and pop do not invalidate it). NO_MODEL otherwise.
  Model model() const;
  std::optional<Model> candidate_model() const; ///< after unknown: the last candidate
  Term value(const Term& t) const { return model().value(t); }

  /// Thread-safe and async-signal-safe. The flag is CONSUMED by the check that
  /// reports it -- a check an input read with ParseMode::EXECUTE runs as much
  /// as check_sat's; if no check is running, the next check returns
  /// unknown(INTERRUPTED) immediately. clear_interrupt() discards a pending
  /// interrupt. INTERRUPTED > TIMEOUT > CONFLICT_LIMIT when several fire. The
  /// terminator reaches a script's checks the same way.
  void interrupt() noexcept;
  void clear_interrupt() noexcept;
  bool interrupt_pending() const noexcept;
  /// Not owned; nullptr clears. A terminator runs inside the check and must
  /// not call the library (STATE), except Solver::interrupt().
  void set_terminator(Terminator*);
  Statistics statistics() const;

  // symbols and scripts (the name table is the manager's)
  std::optional<Term> symbol(std::string_view name) const;
  void parse_smt2(std::string_view script, ParseMode = ParseMode::DECLARE_AND_ASSERT);
  void parse(std::string_view text, Format); ///< SMTLIB2, SMTLIB1 or CVC
  void parse_file(std::string_view path, Format = Format::AUTO); ///< AUTO picks by extension
  /// Reads the input from a stream as far as the parser needs it, taking what
  /// the stream holds after at most one refill: a script driven over a pipe
  /// is answered command by command. AUTO reads SMT-LIB 2. IO if the stream
  /// fails, which ends the parse there. The stream's reads run as a callback
  /// (no library calls) and under the process-wide parser lock.
  void parse(std::istream& in, Format, ParseMode = ParseMode::DECLARE_AND_ASSERT);
  Term parse_term(std::string_view smt2_term) const; ///< over the manager's name table

  /// The assertions through the engine's printers, which recurse once per
  /// level of a term (see Term::to_string).
  std::string to_smt2(bool with_check_sat = false) const;
  std::string to_string(Format) const; ///< SMTLIB2, CVC, DOT, GDL
  /// The last CVC or SMT-LIB 1 input this solver read, as the stp command
  /// line's --print-back options print it: the input's question (its
  /// assertions and its negated query) in CVC (after the declarations and
  /// assertions), SMTLIB2, GDL or DOT. STATE if there was no such input.
  std::string input_to_string(Format) const;
  /// DIMACS of the current assertions: the batch pipeline encodes them up to
  /// its first CNF without solving, whatever `incremental` says, and the
  /// scope says how that CNF relates to them. Not a check: the last check's
  /// result, model and failed assumptions stay, a pending interrupt stays
  /// pending, and the CNF sink does not see it. STATE when an interrupt or a
  /// budget stops it first; UNSUPPORTED when the pipeline ends before a CNF
  /// for another reason.
  CnfScope write_cnf(std::ostream&) const;

  /// Where diagnostic-tier options write: statistics, warnings and the other
  /// text the engine prints for people rather than programs, "Fatal Error:"
  /// reports included. Default: nowhere. A sink must not call the library
  /// (STATE); nor must any other callback.
  void set_diagnostic_sink(std::function<void(std::string_view)>);
  /// Where the solver's printed output goes: the responses of an input read
  /// with ParseMode::EXECUTE or PARSE_ONLY, and what the printing options
  /// print. Default: nowhere. An empty chunk asks the sink to flush: the text
  /// so far is complete. A SAT backend's own report, which print-functionstat
  /// switches on, reaches this sink from CryptoMiniSat only: CaDiCaL and
  /// MiniSat write theirs to standard output themselves. It must not call the
  /// library (STATE).
  void set_output_sink(std::function<void(std::string_view)>);
  /// Called with the engine's report of a fatal error in this solver's work
  /// (an internal failure, or a refusal that ends a parse) where it happens,
  /// before anything unwinds; the report also reaches the diagnostic sink as
  /// "Fatal Error: ...". The handler may end the process; if it returns, the
  /// call fails as it otherwise would. It must not call the library.
  /// Default: none.
  void set_fatal_error_handler(std::function<void(std::string_view)>);
  /// Every CNF a check hands to the SAT solver, as DIMACS, and how it relates
  /// to the query; a check can hand over several (refinement). Default: none.
  /// It must not call the library (STATE).
  void set_cnf_sink(std::function<void(std::string_view dimacs, CnfScope)>);

  // internal
  detail::SolverImpl* impl() const noexcept { return impl_; }

private:
  detail::SolverImpl* impl_;
  SolverOptions options_view_;
};

// ---------------------------------------------------------------------------
// 8. Library-level queries and the one process-level switch
// ---------------------------------------------------------------------------

struct STP_API_EXPORT Version
{
  int major = 0, minor = 0, patch = 0;
  std::string string; ///< "3.0.0"
  std::string git_sha, git_tag, build_info;
};
STP_API_EXPORT Version version();

/// What this build can do. Keys are stable strings.
STP_API_EXPORT std::map<std::string, std::string> capabilities();
STP_API_EXPORT bool has_sat_backend(std::string_view name);
STP_API_EXPORT std::vector<std::string> sat_backends();

/// Process-wide by nature: what an INTERNAL or RESOURCE error does. Default
/// POISON; STP_ABORT_ON_INTERNAL_ERROR=1 in the environment selects ABORT.
STP_API_EXPORT void set_internal_error_policy(InternalErrorPolicy) noexcept;
STP_API_EXPORT InternalErrorPolicy internal_error_policy() noexcept;

} // namespace api

// Client code sees the API as stp::Term, stp::Solver, ...; the library's own
// translation units, which also see the engine's stp::Kind, define
// STP_API_INTERNAL and qualify with stp::api:: instead.
#ifndef STP_API_INTERNAL
using namespace api;
#endif

} // namespace stp

namespace std
{
template <> struct hash<stp::api::Term>
{
  std::size_t operator()(const stp::api::Term& t) const noexcept;
};
template <> struct hash<stp::api::Sort>
{
  std::size_t operator()(const stp::api::Sort& s) const noexcept;
};
template <> struct equal_to<stp::api::Term>
{
  bool operator()(const stp::api::Term& a, const stp::api::Term& b) const noexcept
  {
    return a.same_as(b);
  }
};
template <> struct less<stp::api::Term> : stp::api::Term::Less
{
};
} // namespace std

#endif // STP_STP_HPP

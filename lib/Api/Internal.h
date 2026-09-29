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

// Internal.h -- the private structures behind <stp/stp.hpp>.
//
// Everything the public classes point at lives here: the manager (an STPMgr
// plus the API's own tables), the solver (an STP plus its state), the model
// snapshot, the option store and the error record. The public header names
// these types only as incomplete types.

#ifndef STP_API_INTERNAL_H
#define STP_API_INTERNAL_H

#define STP_API_INTERNAL 1
#include "stp/stp.hpp"

#include "NodeAccess.h"
#include "Registry.h"
#include "stp/AST/AST.h"
#include "stp/AST/SourceSort.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/STPManager/UserDefinedFlags.h"

#include <array>
#include <atomic>
#include <chrono>
#include <exception>
#include <functional>
#include <map>
#include <memory>
#include <string>
#include <thread>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace stp
{
class UFDecl;
namespace api
{
namespace detail
{

// The engine's own node-kind enum, hidden here behind the API's stp::api::Kind.
using Kind_t = ::stp::Kind;

// ---------------------------------------------------------------- errors

struct ErrorDetails
{
  ErrorCode code = ErrorCode::INTERNAL;
  std::string function;
  std::string message;
  std::string option;
  std::optional<int> argument_index;
  std::vector<Term> terms;
  std::vector<Sort> sorts;
  int line = 0;
  int column = 0;
};

// Throw helpers. Every one builds the message from errors.toml's template
// with the pieces given and throws RecoverableError (or UnsafeError for the
// two unsafe codes).
[[noreturn]] void fail(ErrorCode code, const char* fn, const std::string& what,
                       std::optional<int> arg = std::nullopt,
                       std::vector<Term> terms = {}, std::vector<Sort> sorts = {},
                       const std::string& option = "");
[[noreturn]] void fail_option(ErrorCode code, const std::string& option,
                              const std::string& what);
[[noreturn]] void fail_parse(const char* fn, int line, int column,
                             const std::string& what);
[[noreturn]] void fail_internal(const char* fn, const std::string& what);
[[noreturn]] void fail_resource(const char* fn, const char* what);

// Every entry that reaches the engine runs inside one of these: while it is
// alive the engine's FatalError throws stp::EngineFatal instead of ending the
// process (lib/AST/ASTmisc.cpp). engine_call turns that exception into an
// INTERNAL error after poisoning the manager, whose state the failure may
// have left inconsistent: every later call on it, its solvers, models and
// terms is refused with STATE naming the failure. The flag is per thread and
// nests (a scope restores what it found).
// How many user callbacks -- sinks, the terminator, the fatal-error handler,
// a text source, the C error callback -- are running on this thread. Every
// call into the library from one is refused with STATE (check_alive) but
// interrupt(), clear_interrupt() and interrupt_pending(): the engine is part
// way through a call beneath it, and a parse holds the process-wide parser
// lock, so the call would corrupt the one or deadlock on the other.
DLL_PUBLIC int& callback_depth() noexcept;
struct InCallback
{
  InCallback() noexcept { ++callback_depth(); }
  ~InCallback() { --callback_depth(); }
  InCallback(const InCallback&) = delete;
  InCallback& operator=(const InCallback&) = delete;
};

struct EngineScope
{
  bool saved;
  EngineScope() noexcept : saved(stp::FatalErrorThrows()) { stp::SetFatalErrorThrows(true); }
  ~EngineScope() { stp::SetFatalErrorThrows(saved); }
  EngineScope(const EngineScope&) = delete;
  EngineScope& operator=(const EngineScope&) = delete;
};
[[noreturn]] DLL_PUBLIC void fail_engine(ManagerImpl* m, const char* fn, const std::string& what);
// Anything else the engine threw (neither EngineFatal nor one of the API's
// own errors) unwound through the engine as a failure does, and is one:
// INTERNAL, or RESOURCE for bad_alloc, and the manager is poisoned.
[[noreturn]] DLL_PUBLIC void fail_foreign(ManagerImpl* m, const char* fn, const std::exception& e);
// INVALID_ARGUMENT unless `width` is in the uf-sort-width entry's range.
void check_uf_sort_width(std::uint64_t width, const char* fn, std::optional<int> arg);

// ---------------------------------------------------------------- output

// Where the text the engine writes while it works goes. The engine prints to
// std::cout (responses, answers, what the printing options print) and to
// std::cerr (statistics, warnings, "Fatal Error:" reports); while a route is
// alive on a thread, that thread's writes to either stream go to the route's
// sinks instead of the process's streams, and a null or empty sink drops
// them. An empty chunk to `out` is a flush: the text so far is complete.
// Output.cpp installs the streams' dispatching buffers the first time a route
// is made; a thread with no route writes to the process's streams as before.
struct OutputSinks
{
  const std::function<void(std::string_view)>* out = nullptr;
  const std::function<void(std::string_view)>* err = nullptr;
  // Told of a fatal error the engine reports, before anything unwinds
  // (Solver::set_fatal_error_handler).
  const std::function<void(std::string_view)>* fatal = nullptr;
};
// Every write dropped: what an API call that is no solver's work routes to.
extern const OutputSinks kNoOutput;
const OutputSinks* current_output_route() noexcept;
class OutputRoute
{
public:
  explicit OutputRoute(const OutputSinks* sinks);
  ~OutputRoute();
  OutputRoute(const OutputRoute&) = delete;
  OutputRoute& operator=(const OutputRoute&) = delete;

private:
  const OutputSinks* saved_;
  stp::FatalErrorObserver saved_observer_;
  void* saved_opaque_;
};

// Boots the constant bit-vector library for the calling thread (see
// Manager.cpp); every entry that reaches the engine calls it first.
void boot_constant_bv();

template <class F>
auto engine_call(ManagerImpl* m, const char* fn, F&& f) -> decltype(f())
{
  boot_constant_bv();
  EngineScope scope;
  // Engine work that is no solver's (a solver's entry routes to its own
  // sinks before it gets here) prints nowhere.
  const OutputSinks* route = current_output_route();
  OutputRoute quiet(route != nullptr ? route : &kNoOutput);
  try
  {
    return f();
  }
  catch (const stp::EngineFatal& e)
  {
    fail_engine(m, fn, e.what());
  }
  catch (const Error&)
  {
    throw; // the call's own refusal
  }
  catch (const std::exception& e)
  {
    fail_foreign(m, fn, e);
  }
}
const char* error_template(ErrorCode code);
bool error_recoverable(ErrorCode code);

// ---------------------------------------------------------------- nodes

inline ASTNode node_of(const Term& t)
{
  return NodeAccess::wrap(static_cast<ASTInternal*>(t.impl_node()));
}
inline ASTInternal* internal_of(const Term& t)
{
  return static_cast<ASTInternal*>(t.impl_node());
}

struct ManagerImpl;

Term make_term(ManagerImpl* m, const ASTNode& n);
Sort make_sort(ManagerImpl* m, std::uint32_t index);

// ---------------------------------------------------------------- sorts

struct SortRec
{
  SortKind kind = SortKind::BOOL;
  std::uint32_t a = 0; // BV width; FP exponent width
  std::uint32_t b = 0; // FP significand width; uninterpreted carrier width
  std::uint32_t index = 0;   // arrays: the index sort
  std::uint32_t element = 0; // arrays: the element sort
  std::vector<std::uint32_t> domain; // functions
  std::uint32_t codomain = 0;
  std::string name;          // uninterpreted sorts: the declared name
  unsigned engine_id = 0;    // uninterpreted sorts: the engine's registry id
  bool anonymous = false;    // mk_fresh_sort
  SourceSort source;         // the engine's view, for every kind but FUN
  bool has_source = false;
};

// ---------------------------------------------------------------- symbols

struct SymbolRec
{
  ASTNode node;
  std::uint32_t sort = 0;
  bool anonymous = false; // made by mk_fresh: never returned by symbol()
  bool is_function = false;
  const UFDecl* decl = nullptr;
};

// ---------------------------------------------------------------- the manager

struct OptionsImpl;
struct SolverImpl;

struct ManagerImpl
{
  long refs = 0;
  std::uint64_t id = 0;
  STPMgr* bm = nullptr;
  // Every live solver over this manager, and the one whose assertion levels
  // are installed in the engine's stack and whose options are applied to the
  // engine's flags; the others keep their levels shelved (SolverImpl::activate).
  std::vector<SolverImpl*> solvers;
  SolverImpl* active = nullptr;
  TermManager::Config config;

  // sorts, interned by a structural key
  std::vector<SortRec> sorts;
  std::unordered_map<std::string, std::uint32_t> sort_keys;
  std::unordered_map<std::string, std::uint32_t> sorts_by_name; // declared sorts
  std::unordered_map<unsigned, std::uint32_t> sorts_by_engine_id;
  std::vector<std::uint32_t> declared_sort_order;
  std::uint32_t bool_sort = 0, rm_sort = 0, real_sort = 0;

  // symbols: one name table (declared and fresh alike)
  std::unordered_map<std::string, SymbolRec> symbols;
  std::vector<std::string> symbol_order; // declaration order, declared only
  // symbol_order's distinct symbols, in the same order (a name that
  // bind_symbol gave a symbol already listed adds nothing): what
  // TermManager::symbols() returns, kept up as names are recorded, so that
  // counting or indexing the symbols (the C API's stp_tm_symbol_at) rebuilds
  // nothing
  std::vector<ASTNode> symbol_list;
  ASTNodeSet symbol_list_members;
  void record_symbol_name(const std::string& name, const ASTNode& node);
  std::unordered_map<ASTNode, std::string, ASTNode::ASTNodeHasher> names_by_node;
  std::unordered_map<ASTNode, std::uint32_t, ASTNode::ASTNodeHasher> fun_sort_of_identity;
  std::uint64_t fresh_counter = 0;

  // ids handed out by Term::id(), for term_from_id

  // constant arrays are the engine's (STPMgr::CreateConstArray registers the
  // symbol with its default, and the hashing factory folds every read of
  // one); these are the API's spellings of the two queries
  bool is_const_array(const ASTNode& n) const;
  const ASTNode& const_array_default(const ASTNode& n) const;
  // options that forbid what construction would otherwise enable on demand
  bool array_equality_off = false;
  // an equality between arrays was built or parsed: what array-equality = auto engages
  bool array_equality_seen = false;
  // Names that spell a predefined SMT-LIB symbol are taken as given (for
  // libstp2: 2.x took any name); refused otherwise.
  bool predefined_names_accepted = false;

  // poison
  bool poisoned = false;
  std::string poison_message;

  ManagerImpl(const TermManager::Config& cfg);
  ~ManagerImpl();
  ManagerImpl(const ManagerImpl&) = delete;
  ManagerImpl& operator=(const ManagerImpl&) = delete;

  void retain() noexcept { ++refs; }
  void release() noexcept
  {
    if (--refs == 0)
      delete this;
  }

  // Refuses a poisoned manager, and readies the calling thread for the
  // engine (the constant bit-vector library boots per thread): a manager may
  // be used from any thread, one call at a time. Settles a pending adoption.
  void check_alive(const char* fn);

  // sorts
  std::uint32_t intern_sort(const std::string& key, SortRec&& rec);
  std::uint32_t bv_sort(std::uint32_t width);
  std::uint32_t fp_sort(std::uint32_t e, std::uint32_t s);
  std::uint32_t array_sort(std::uint32_t index, std::uint32_t element, const char* fn);
  std::uint32_t fun_sort(const std::vector<std::uint32_t>& domain, std::uint32_t codomain);
  std::uint32_t uninterpreted_sort(const std::string& name, bool anonymous);
  std::uint32_t sort_of_source(const SourceSort& ss, const char* fn);
  std::uint32_t sort_of_node(const ASTNode& n, const char* fn);
  const SortRec& rec(std::uint32_t index) const { return sorts[index]; }
  std::string sort_text(std::uint32_t index) const;

  // symbols
  Term declare(const char* fn, const std::string& name, std::uint32_t sort, bool anonymous);
  const SymbolRec* find_symbol(const std::string& name) const;
  const SymbolRec* find_symbol(const ASTNode& n) const; // by node, any name
  const UFDecl* decl_of(const ASTNode& identity) const;
  std::string fresh_name(std::string_view prefix);
  void adopt_engine_symbols(const std::vector<ASTNode>& roots); // after a parse
  // What an SMT-LIB 2 script that ran leaves to adopt: the roots of what it
  // declared and asserted, whose symbols become the manager's and whose
  // array equalities engage array-equality = auto. Adopted by the next call
  // on the manager (check_alive) rather than at the end of the parse, so that
  // a caller that makes none -- the stp binary, whose process ends with its
  // script -- does not walk everything the script built; nothing reads the
  // manager in between.
  std::vector<ASTNode> pending_roots;
  bool adoption_pending = false;
  void settle(const char* fn); // defined beside the parse, in Solver.cpp

  // values
  ASTNode bv_const(std::uint32_t width, std::uint64_t value);
  ASTNode bv_const_bits(std::uint32_t width, const std::string& bits);
  ASTNode fp_const_from_bits(std::uint32_t e, std::uint32_t s, const ASTNode& bits);
  ASTNode rm_const(RoundingMode);
  ASTNode real_const(const char* fn, const std::string& text);
  ASTNode default_value(std::uint32_t sort, const char* fn);

  // The node factory the API builds with: the simplifying one, or the
  // hashing one when the manager was made with simplify = false. The
  // engine's own factory (bm->defaultNodeFactory) folds either way: the
  // switch is about the terms a caller builds and a script declares, not
  // about the terms the solver makes as it goes.
  NodeFactory* factory() const { return build_factory_; }
  NodeFactory* folding_factory() const { return bm->defaultNodeFactory; } // for evaluation
  NodeFactory* build_factory_ = nullptr;
};

// ---------------------------------------------------------------- options

// The registry's tables (OptionSpec and the command line's rows) are in
// Registry.h, which the stp binary reads too.

// The engine's default of every field-mapped entry, rendered as the registry
// spells a value, so a test can hold the two sets of defaults together.
struct DefaultCheck
{
  const char* name;
  std::string (*engine_default)(const UserDefinedFlags&);
};
DLL_PUBLIC const DefaultCheck* option_default_checks(std::size_t& count);
inline std::string flag_text(bool b) { return b ? "true" : "false"; }
template <class I, std::enable_if_t<std::is_integral<I>::value && !std::is_same<I, bool>::value, int> = 0>
std::string flag_text(I i) { return std::to_string(i); }
template <class E, std::enable_if_t<std::is_enum<E>::value, int> = 0>
std::string flag_text(E e) { return e == E::ON ? "on" : e == E::OFF ? "off" : "auto"; }
OptionValue parse_option_text(const OptionSpec& spec, std::string_view text);
std::string option_text(const OptionSpec& spec, const OptionValue& v);
OptionValue option_default(const OptionSpec& spec);
void validate_option_value(const OptionSpec& spec, const OptionValue& v);

// Exported for the registry suite, which applies the registry to a
// bare UserDefinedFlags.
struct DLL_PUBLIC OptionsImpl
{
  // By registry index. Written only by set, reset and reset_all, which give
  // the options a new generation: what is derived from the values can be
  // kept for as long as the generation stands (SolverImpl::derived_options).
  std::vector<OptionValue> values;
  std::vector<bool> is_set;
  // Unique to one content of the options across the process; a copy carries
  // its source's, which describes it as well.
  std::uint64_t generation;
  OptionsImpl();
  void set(const char* fn, std::string_view name, const OptionValue& v, OptType via);
  void set_text(const char* fn, std::string_view name, std::string_view text);
  void set_args(const char* fn, const std::vector<std::string>& argv);
  const OptionValue& get(const char* fn, std::string_view name, OptType expect) const;
  OptionValue resolved(std::size_t index) const;
  void resolve(const char* fn) const;
  OptionInfo info(std::string_view name) const;
  std::vector<std::string> names(std::optional<Tier>) const;
  std::string help(std::optional<Tier>) const;
  void reset(std::string_view name);
  void reset_all();
};

// Each entry's resolved value (OptionsImpl::resolved) and whether it is the
// entry's default, for the options of one generation (0: none yet).
struct DerivedOptions
{
  std::uint64_t generation = 0;
  std::vector<OptionValue> resolved;
  std::vector<bool> at_default;
};

// Where a validated value goes: the engine. `flags` is the manager's
// UserDefinedFlags; the solver applies through this after every write.
struct EngineTarget
{
  UserDefinedFlags& flags;
  ManagerImpl* mgr;
  SolverImpl* solver;
  // Whether the value being applied was set by the caller (true) or is a
  // registry default re-applied by apply_all_options (false): the engine's
  // "explicitly requested" markers follow it, so a default never counts as a
  // request (the CaDiCaL factor warning fires on requests only).
  bool explicit_value = true;
};
bool apply_option_to_engine(EngineTarget& t, std::size_t index,
                            const OptionSpec& spec, const OptionValue& v);
DLL_PUBLIC void apply_all_options(EngineTarget& t, const OptionsImpl& o, bool force_all = false);
std::vector<std::string> unmapped_options(); // rows the apply table cannot reach yet

// ---------------------------------------------------------------- models

struct ArrayCells
{
  std::uint32_t sort = 0;
  ASTNode array; // the symbol
  std::vector<std::pair<ASTNode, ASTNode>> entries; // (index, element), ascending
  ASTNode fill; // the default element
};

struct FunctionCases
{
  std::uint32_t sort = 0;
  ASTNode identity;
  std::vector<std::pair<std::vector<ASTNode>, ASTNode>> cases;
  ASTNode else_value;
};

// What the result of a partial floating-point operation in an unspecified case
// is a function of, as the solve indexes its choice (FpTotalise): the kind,
// the operands' values and each float operand's format. Every NaN is one
// value, so a NaN operand is the null node.
struct PartialChoiceKey
{
  Kind_t kind;
  std::vector<ASTNode> operands;
  std::vector<std::uint32_t> formats; // exponent and significand width per float operand
  bool operator==(const PartialChoiceKey& o) const
  {
    return kind == o.kind && operands == o.operands && formats == o.formats;
  }
};

struct PartialChoiceKeyHash
{
  std::size_t operator()(const PartialChoiceKey& k) const
  {
    std::size_t h = static_cast<std::size_t>(k.kind);
    for (const ASTNode& o : k.operands)
      h = h * 31 + (o.IsNull() ? 0 : o.Hash());
    for (const std::uint32_t f : k.formats)
      h = h * 31 + f;
    return h;
  }
};

struct ModelSnapshot
{
  ManagerImpl* mgr = nullptr; // retained
  std::unordered_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher> scalars; // symbol -> VALUE
  std::unordered_map<ASTNode, ArrayCells, ASTNode::ASTNodeHasher> arrays;
  std::unordered_map<ASTNode, FunctionCases, ASTNode::ASTNodeHasher> functions;
  // The solve's choice in each unspecified case of a partial floating-point
  // operation in the checked formula, by operand values: an application the
  // check never saw, over the same values, takes the same choice.
  std::unordered_map<PartialChoiceKey, ASTNode, PartialChoiceKeyHash> partial_choices;
  std::vector<ASTNode> core; // symbols the solver assigned, in name order
  bool fill_ones = false;
  Verdict verdict = Verdict::UNKNOWN; // SAT for a real model, UNKNOWN for a candidate
  ~ModelSnapshot();
};

struct ValueImpl
{
  std::shared_ptr<const ModelSnapshot> snap;
  ASTNode key; // the array symbol / function identity, or a null node for a synthesised value
  ArrayCells cells;
  FunctionCases cases;
  bool is_array = false;
};

// Evaluates any term against a snapshot; the recursion is bounded by the
// term's DAG size through the memo.
class Evaluator
{
public:
  Evaluator(const ModelSnapshot& s, const char* fn, bool complete);
  ASTNode eval(const ASTNode& n);
  bool incomplete() const noexcept { return incomplete_; }
  ASTNode eval_read_public(const ASTNode& array, const ASTNode& index)
  {
    return eval_read(array, index);
  }
  // The entry points: eval and eval_read inside an engine scope (the constant
  // evaluator the folds reach is engine code).
  ASTNode evaluate(const ASTNode& n);
  ASTNode read(const ASTNode& array, const ASTNode& index);

private:
  // One term being valued on the explicit stack; a read keeps the read
  // index's value and its place in the chain it walks.
  struct Frame
  {
    ASTNode n;
    ASTNode cursor;
    ASTNode index;
    bool started;
  };
  void step(Frame& f, std::vector<ASTNode>& needs, ASTNode& out);
  const ASTNode* valued(const ASTNode& n) const;
  ASTNode read_symbol(const ASTNode& array, const ASTNode& index);
  ASTNode eval_read(const ASTNode& array, const ASTNode& index);
  ASTNode apply_values(const ASTNode& n);
  bool arrays_equal(const ASTNode& a, const ASTNode& b);
  ASTNode fold(const ASTNode& n, const ASTVec& kids);
  const ModelSnapshot& s_;
  ManagerImpl* m_;
  const char* fn_;
  bool complete_;
  bool incomplete_ = false;
  std::unordered_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher> memo_;
};

// ---------------------------------------------------------------- the solver

struct SolverImpl
{
  ManagerImpl* mgr = nullptr; // retained
  STP* stp = nullptr;
  OptionsImpl options;
  std::uint32_t level = 0;
  std::size_t checks = 0; // for the before-first-check window
  bool constructed = false;
  bool produce_models = true;
  bool fill_ones = false; // model-array-fill = ones
  std::string logic;
  bool pushed = false; // a push has happened: what incremental = auto engages on

  // the last check
  Result last;
  bool have_last = false;
  std::vector<ASTNode> last_assumptions;
  std::vector<ASTNode> last_failed_assumptions;
  bool model_pending = false; // the engine's tables hold a model not yet snapshotted
  std::shared_ptr<const ModelSnapshot> model;
  std::shared_ptr<const ModelSnapshot> candidate;
  std::chrono::steady_clock::duration last_wall{0};
  // The last check's time in each phase, from the engine's run-time
  // categories: simplification, bit-blasting, CNF generation, SAT.
  std::array<double, 4> last_phase_ms{};
  bool last_incremental = false;
  bool batch_only = false; // write_cnf: the batch pipeline, whatever `incremental` says

  // interrupts
  std::atomic<bool> interrupt{false};
  Terminator* terminator = nullptr;
  bool terminator_fired = false;
  bool interrupt_consumed = false;

  // What the engine prints while it works for this solver (OutputSinks), the
  // handler told of its fatal errors, and the CNF sink.
  std::function<void(std::string_view)> output_sink;
  std::function<void(std::string_view)> diagnostic_sink;
  std::function<void(std::string_view)> fatal_handler;
  std::function<void(std::string_view, CnfScope)> cnf_sink;
  const OutputSinks route_sinks{&output_sink, &diagnostic_sink, &fatal_handler};

  // C layer: the failed state
  std::shared_ptr<const ErrorDetails> failed;

  // While another solver of the manager is active, this solver's assertion
  // levels (the base level first) live here; while this one is active they
  // are the engine's own stack.
  std::vector<std::vector<ASTNode>> shelf;
  // The same for the engine's counters (UserDefinedFlags::coverage, one per
  // manager): this solver's while another is active, so that each solver's
  // statistics count its own checks.
  UserDefinedFlags::EncodingCoverage coverage{};
  UserDefinedFlags::SATSolvers backend_when_shelved = UserDefinedFlags::MINISAT_SOLVER;
  bool shelved_backend_known = false;
  // By registry index: whether the engine holds something other than the
  // entry's default for this solver (the entry is set, or resolves away from
  // its default through another), as last applied. An entry that goes back
  // to its default is applied again only then (apply_all_options).
  std::vector<bool> engine_off_default;
  // What apply_all_options derives from the options at every application --
  // each entry's resolved value, and whether that is its default -- kept for
  // the options' generation, so that a check after no write derives nothing;
  // and the generation whose consistency (OptionsImpl::resolve) a check last
  // established.
  DerivedOptions derived_options;
  std::uint64_t consistent_generation = 0;

  SolverImpl(ManagerImpl* m, const Options& o);
  ~SolverImpl();
  SolverImpl(const SolverImpl&) = delete;
  SolverImpl& operator=(const SolverImpl&) = delete;

  void check_alive(const char* fn) const;
  void enter(const char* fn); // check_alive, then activate: every engine-touching entry
  void activate();            // install this solver's levels and options in the engine
  void deactivate();          // shelve them (the active solver only)
  std::size_t level_count() const; // engine levels while active, shelved ones otherwise
  void reapply_engine_defaults(); // every registry default, then this solver's options
  void apply_options(const char* fn);
  Settable effective_settable(const OptionSpec& spec) const; // latched_by applied
  bool option_window_open(const OptionSpec& spec) const;
  void ensure_snapshot(); // materialise a pending model before the tables change
  std::shared_ptr<const ModelSnapshot> take_snapshot(Verdict v);
  Result run_check(const char* fn, const std::vector<ASTNode>& assumptions,
                   const std::optional<CheckBudget>& budget);
  Result run_check_impl(const char* fn, const std::vector<ASTNode>& assumptions,
                        const std::optional<CheckBudget>& budget);
  static bool poll_stop(void* opaque);
  void rebuild_engine();
};

// ---------------------------------------------------------------- kinds

struct KindSpec
{
  Kind kind;
  const char* name;
  const char* smtlib;
  const char* c;
  int min_arity;
  int max_arity; // -1: unbounded
  int indices;
  const char* sig;
  const char* engine_note;
  const char* py;
};
const KindSpec& kind_spec(Kind k);

// The public view of an engine node: kind, children and indices as the
// kinds.toml table describes them.
struct View
{
  Kind kind = Kind::VALUE;
  std::vector<ASTNode> children;
  std::vector<std::uint32_t> indices;
};
View view_of(ManagerImpl* m, const ASTNode& n);
// `n` rebuilt with new children through `f`, keeping its widths and
// floating-point format (Terms.cpp).
ASTNode rebuild_node(ManagerImpl* m, NodeFactory* f, const ASTNode& n, const ASTVec& kids);

// Construction over the engine; every precondition checked.
ASTNode build_term(ManagerImpl* m, const char* fn, Kind k,
                   const std::vector<ASTNode>& args,
                   const std::vector<std::uint32_t>& indices,
                   std::optional<std::uint32_t> result_sort);
ASTNode literal_for(ManagerImpl* m, const char* fn, std::uint32_t sort,
                    std::int64_t v, bool is_signed, std::uint64_t uv,
                    const ASTNode* rm);
ASTNode float_literal_for(ManagerImpl* m, const char* fn, std::uint32_t sort,
                          double v, const ASTNode* rm);

// value readers over constant nodes
std::vector<std::uint64_t> bv_limbs_of(const ASTNode& c);
std::string bv_bits_of(const ASTNode& c); // MSB first
FloatValue fp_value_of(const ASTNode& c, std::uint32_t e, std::uint32_t s);
RoundingMode rm_of(const ASTNode& c, const char* fn);
RationalValue rational_of(const ASTNode& c);
unsigned rm_encoding(RoundingMode rm);

// printing
std::string print_term(ManagerImpl* m, const ASTNode& n, Format f, bool share);
std::string quote_symbol(const std::string& name); // SMT-LIB |quoting| where needed
// A symbol, or a sort symbol, that SMT-LIB's theories predefine (true, bvadd,
// select, RNE, +, Bool, ...): |quoting| cannot tell a declaration apart from
// it, since |true| and true are the same symbol.
bool predefined_symbol(const std::string& name);
bool predefined_sort_symbol(const std::string& name);

// The process-wide parser lock: the bison parsers use global state.
std::mutex& parser_mutex();

} // namespace detail
} // namespace api
} // namespace stp

#endif

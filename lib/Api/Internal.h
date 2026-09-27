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
#include "stp/AST/AST.h"
#include "stp/AST/SourceSort.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/STPManager/UserDefinedFlags.h"

#include <atomic>
#include <chrono>
#include <functional>
#include <map>
#include <memory>
#include <string>
#include <thread>
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
  SolverImpl* solver = nullptr; // this alpha: the one live solver
  TermManager::Config config;
  std::thread::id owner;

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
  std::unordered_map<ASTNode, std::string, ASTNode::ASTNodeHasher> names_by_node;
  std::unordered_map<ASTNode, std::uint32_t, ASTNode::ASTNodeHasher> fun_sort_of_identity;
  std::uint64_t fresh_counter = 0;

  // ids handed out by Term::id(), for term_from_id
  std::unordered_map<std::uint64_t, ASTNode> exposed_ids;

  // constant arrays: an internal array symbol standing for (as const ...) v
  std::unordered_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher> const_array_default;
  std::map<std::pair<std::uint32_t, ASTNode>, ASTNode> const_arrays; // (sort, element) -> symbol
  bool const_arrays_involved(const ASTNode& array) const;
  // options that forbid what construction would otherwise enable on demand
  bool array_equality_off = false;
  // an equality between arrays was built or parsed: what array-equality = auto engages
  bool array_equality_seen = false;

  // poison
  bool poisoned = false;
  std::string poison_message;

  // the C layer's first-error record and callback (owned here so that the C
  // runtime needs no table of its own)
  std::shared_ptr<const ErrorDetails> c_error;
  void (*c_error_callback)(const void* error, void* user) = nullptr;
  void* c_error_user = nullptr;
  // the C layer's scope journal
  std::vector<std::vector<ASTNode>> c_scopes;

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

  void check_alive(const char* fn) const;
  void check_thread(const char* fn) const;

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

  // values
  ASTNode bv_const(std::uint32_t width, std::uint64_t value);
  ASTNode bv_const_bits(std::uint32_t width, const std::string& bits);
  ASTNode fp_const_from_bits(std::uint32_t e, std::uint32_t s, const ASTNode& bits);
  ASTNode rm_const(RoundingMode);
  ASTNode real_const(const char* fn, const std::string& text);
  ASTNode default_value(std::uint32_t sort, const char* fn);

  // the node factory the API builds with (simplifying or hashing)
  NodeFactory* factory() const { return bm->defaultNodeFactory; }
  NodeFactory* folding_factory(); // always the simplifying one, for evaluation
  NodeFactory* folding_factory_ = nullptr;
};

// ---------------------------------------------------------------- options

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
  const char* legacy_letter;
  const char* legacy_iface;
  const char* legacy_cli_unit;
  const char* engine;
  bool has_engine;
};

const OptionSpec* option_specs(std::size_t& count);
const OptionSpec* find_option(std::string_view name); // name or alias; nullptr if unknown
std::size_t option_index(const OptionSpec* spec);
OptionValue parse_option_text(const OptionSpec& spec, std::string_view text);
std::string option_text(const OptionSpec& spec, const OptionValue& v);
OptionValue option_default(const OptionSpec& spec);
void validate_option_value(const OptionSpec& spec, const OptionValue& v);
bool option_build_supported(const OptionSpec& spec);

struct OptionsImpl
{
  std::vector<OptionValue> values;    // by registry index
  std::vector<bool> is_set;
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

// Where a validated value goes: the engine. `flags` is the manager's
// UserDefinedFlags; the solver applies through this after every write.
struct EngineTarget
{
  UserDefinedFlags& flags;
  ManagerImpl* mgr;
  SolverImpl* solver;
};
bool apply_option_to_engine(EngineTarget& t, std::size_t index,
                            const OptionSpec& spec, const OptionValue& v);
void apply_all_options(EngineTarget& t, const OptionsImpl& o, bool force_all = false);
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

struct ModelSnapshot
{
  ManagerImpl* mgr = nullptr; // retained
  std::unordered_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher> scalars; // symbol -> VALUE
  std::unordered_map<ASTNode, ArrayCells, ASTNode::ASTNodeHasher> arrays;
  std::unordered_map<ASTNode, FunctionCases, ASTNode::ASTNodeHasher> functions;
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

private:
  ASTNode eval_read(const ASTNode& array, const ASTNode& index);
  ASTNode eval_apply(const ASTNode& n);
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

  // the last check
  Result last;
  bool have_last = false;
  std::vector<ASTNode> last_assumptions;
  std::vector<ASTNode> last_failed_assumptions;
  bool model_pending = false; // the engine's tables hold a model not yet snapshotted
  std::shared_ptr<const ModelSnapshot> model;
  std::shared_ptr<const ModelSnapshot> candidate;
  std::chrono::steady_clock::duration last_wall{0};
  bool last_incremental = false;

  // interrupts
  std::atomic<bool> interrupt{false};
  Terminator* terminator = nullptr;
  bool terminator_fired = false;
  bool interrupt_consumed = false;

  std::function<void(std::string_view)> diagnostic_sink;

  // C layer: the failed state
  std::shared_ptr<const ErrorDetails> failed;

  SolverImpl(ManagerImpl* m, const Options& o);
  ~SolverImpl();
  SolverImpl(const SolverImpl&) = delete;
  SolverImpl& operator=(const SolverImpl&) = delete;

  void check_alive(const char* fn) const;
  void apply_options(const char* fn);
  bool option_window_open(const OptionSpec& spec) const;
  void ensure_snapshot(); // materialise a pending model before the tables change
  std::shared_ptr<const ModelSnapshot> take_snapshot(Verdict v);
  Result run_check(const char* fn, const std::vector<ASTNode>& assumptions,
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

// The process-wide parser lock: the bison parsers use global state.
std::mutex& parser_mutex();

} // namespace detail
} // namespace api
} // namespace stp

#endif

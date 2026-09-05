/********************************************************************
 * AUTHORS: Trevor Hansen, Andrew Teylu
 *
 * BEGIN DATE: Apr, 2010
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

#ifndef CPP_INTERFACE_H_
#define CPP_INTERFACE_H_

#include "stp/AST/AST.h"
#include "stp/UninterpretedFunctions/UFDecl.h"
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/Util/Attributes.h"
#include <ankerl/unordered_dense.h>
#include <cstdint>
#include <map>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace stp
{

// There's no BVTypeCheck() function. Use a typechecking node factory instead.

// Foward declarations
struct UserDefinedFlags;
class STPMgr;
class LetMgr;
enum class FPSpecial; // see STPManager.h

// The (exponent bits, significand bits) of a parsed floating-point sort;
// parser plumbing (bison's %union carries a pointer to one).
struct float_size
{
  explicit float_size(int exp, int sig) : exp_bits(exp), sig_bits(sig) {}
  int exp_bits;
  int sig_bits;
};

// One component -- index or element -- of a parsed (Array X Y) sort, and
// the assembled pair; parser plumbing like float_size. Keeping the complete
// SourceSort here, rather than just a carrier width and a few special cases,
// preserves the identity of a sort introduced by declare-sort.
struct array_sort_component
{
  explicit array_sort_component(const SourceSort& source_sort)
      : sort(source_sort)
  {
    assert(sort.isScalar());
  }

  SourceSort sort;
  unsigned width() const { return sort.packedWidth(); }
  SourceSort sourceSort() const { return sort; }
};

struct array_sort
{
  array_sort_component index;
  array_sort_component elem;

  SourceSort sourceSort() const
  {
    return SourceSort::array(index.sourceSort(), elem.sourceSort());
  }
};

// Command-local semantic carrier for one sort in a nonzero-arity
// declare-fun. Keeping unsupported sorts as data lets the enclosing
// declaration report its name and argument position without parser-global
// latches, while still postponing every mutation until the signature is valid.
struct parsed_uf_sort
{
  parsed_uf_sort(SourceSort sourceSort, std::string display,
                 bool isSupported, bool isKnown = true)
      : sort(std::move(sourceSort)), spelling(std::move(display)),
        supported(isSupported), known(isKnown)
  {
  }

  SourceSort sort;
  std::string spelling;
  bool supported;
  bool known;
};

// Heterogeneous string hash: lets a string-keyed table be probed with a
// string_view (e.g. straight from a lexer buffer) without materialising a
// std::string first.
struct TransparentStringHash
{
  using is_transparent = void;
  using is_avalanching = void;
  uint64_t operator()(std::string_view s) const noexcept
  {
    return ankerl::unordered_dense::hash<std::string_view>{}(s);
  }
};

class Cpp_interface
{
  STPMgr& bm;
  // Sort names the script introduced: define-sort's nullary floating-point
  // aliases, and declare-sort's uninterpreted sorts. Both resolve to a
  // SourceSort, so a name in sort position needs one lookup whichever
  // command introduced it.
  std::map<std::string, SourceSort> sort_aliases;
  bool print_success;
  bool ignoreCheckSatRequest;

  // Used to cache prior queries.
  struct Entry
  {
    // No node has this number, so it marks "nothing recorded yet".
    static constexpr uint64_t NO_NODE = UINT64_MAX;

    explicit Entry(SOLVER_RETURN_TYPE result_)
    {
      result = result_;
      node_number = NO_NODE;
    }

    SOLVER_RETURN_TYPE result;
    uint64_t node_number; // a weak pointer.

    // The unsat verdict came from a deeper check whose failed assumptions
    // all lay at or below this level -- recorded so a later check of this
    // stack can answer without solving, and so the shortcut is observable
    // under --stats.
    bool fromCore = false;
  };
  vector<Entry> cache;

public:
  // A stored define-fun. Public because the SMT-LIB2 parser carries a
  // pointer to one through a token (see lookupFunction).
  struct Function
  {
    ASTVec params;
    ASTNode function;
    std::string name;
  };

private:
  ankerl::unordered_dense::map<std::string, Function> functions;

  // Nested helper class to encapsulate a frame (i.e., between push a pop)
  class SolverFrame
  {
  public:
    // Functions are (currently) managed at global scope; we need a pointer to
    // the global functions to be able to remove functions when we pop
    SolverFrame(ankerl::unordered_dense::map<std::string, Function>*
                    global_function_context,
                std::map<std::string, SourceSort>*
                    global_sort_alias_context,
                STPMgr* manager);
    virtual ~SolverFrame();

    // Obtain the functions for the current frame
    vector<std::string>& getFunctions();

    // Obtain the symbols for the current frame

    void addSortAlias(const std::string& name);
    void addSymbol(const ASTNode& symbol);
    void addTemporarySymbol(const ASTNode& symbol);
    void clearTemporarySymbols();
    void addUFDeclaration(const UFDecl* declaration);
    bool removeSymbol(const ASTNode& symbol);
    bool lookupSymbol(std::string_view name, ASTNode& output) const;
    bool lookupTemporarySymbol(std::string_view name, ASTNode& output) const;

    // Take over every declaration made in `donor`, leaving it empty. Used
    // for :global-declarations true, where a pop removes the assertion
    // level but must not end the lifetime of the names declared in it: the
    // frame being destroyed hands them to the base frame first, so its
    // destructor has nothing left to erase from the global contexts.
    void adoptDeclarations(SolverFrame& donor);

  private:
    vector<std::string> _scoped_functions;
    vector<std::string> _scoped_sort_aliases;
    vector<const UFDecl*> _scoped_uf_declarations;
    ASTVec _scoped_symbols;
    // Hash map, not std::map: files declare tens of thousands of symbols
    // with long common prefixes, and a tree walk memcmps the prefix at
    // every level. Nothing iterates this in order.
    ankerl::unordered_dense::map<std::string, std::vector<ASTNode>,
                                 TransparentStringHash, std::equal_to<>>
        _symbol_bindings;
    ankerl::unordered_dense::map<std::string, std::vector<ASTNode>,
                                 TransparentStringHash, std::equal_to<>>
        _temporary_symbol_bindings;
    ankerl::unordered_dense::map<std::string, Function>*
        _global_function_context;
    std::map<std::string, SourceSort>*
        _global_sort_alias_context;
    STPMgr* _manager;
  };

  // The vector of all frames that have been created by calling push
  std::vector< SolverFrame* > frames;

  // Obtain the symbols/functions for the current frame
  vector<std::string>& getCurrentFunctions();

  // What the most recent check-sat charged to each pipeline stage: the
  // difference between two readings of the manager's run times taken around
  // the solve, which is the granularity (get-info :all-statistics) reports on.
  // Taking a difference rather than reading the totals is what keeps the
  // answer to "the most recent check" from growing into a session total, and
  // keeps it independent of --print-quickstat, which clears as it prints.
  // Categories are held by index so this header need not know the enum.
  struct CategoryWork
  {
    int category;
    int count;
    int64_t time_ms;
  };
  std::vector<CategoryWork> last_check_work;

  void checkInvariant();
  void init();

  // The manager's run times as they stand, and -- given a reading taken in
  // front of a solve -- what that solve added, which is what
  // last_check_work holds. Declared over CategoryWork rather than over the
  // run-time class's own type so this header does not have to know it.
  std::vector<CategoryWork> currentWork() const;
  void recordCheckWork(const std::vector<CategoryWork>& before);

  // Report (set-option :<option> <value>) where the option's argument is a
  // <b_value> and the value is neither true nor false. Malformed rather than
  // unsupported, so it is an error response and not "unsupported"; STP's
  // :error-behavior is immediate-exit, so it does not return.
  ATTR_NORETURN void badBooleanOptionValue(const std::string& option,
                                           const std::string& value);
  void addFrame();
  void removeFrame();
  void assertRoundingModeValid(const ASTNode& s);
  void resetIncrementalSolver();

  bool produce_models;

  // :global-declarations. False (the required default) scopes declarations
  // and definitions to the assertion level that made them; true makes them
  // permanent, so pop and reset-assertions keep them and reset -- which
  // discards every declaration -- is the only thing that takes them away.
  //
  // Initialised here rather than in init(), which reset() re-runs: reset
  // empties the assertion stack and with it the declarations, but the option
  // saying how later declarations are scoped outlives it.
  bool global_declarations = false;

  // Whether anything has been declared, defined, asserted, pushed or solved
  // since start-up or the last reset. :global-declarations may only be set
  // while this is false -- see setOption. init() clears it, so reset makes
  // the option settable again; reset-assertions deliberately does not.
  bool session_touched;

  // Whether the model held by the counterexample tables answers for the
  // current assertion stack. Set by checkSat from the solve's outcome;
  // cleared by anything SMT-LIB says invalidates a model (assert, push,
  // pop, reset, reset-assertions). get-value/get-model refuse when false
  // rather than print a model of an assertion set that no longer exists.
  bool model_valid;

  // A malformed UF expression is diagnosed without aborting the SMT-LIB
  // script.  The parser still has to reduce the enclosing typed production,
  // so it carries a canonical value of the declared result sort to the end
  // of the command.  This latch prevents that parser-only carrier (or any
  // other side effect in the rejected command) from entering solver state.
  // It is cleared exactly at the outer command boundary.
  bool current_command_rejected;
  bool current_command_active;

  // set-logic may select UF for this SMT-LIB session without changing the
  // caller's lasting runtime configuration. Remember that configuration so
  // reset (which clears the logic) and parser teardown can restore it, while
  // reset-assertions deliberately retains both the logic and this selection.
  bool uf_enabled_by_logic = false;
  bool uf_option_before_logic = false;
  void restoreUFOptionAfterLogic();

  // QF_AX needs declared sorts and extensional array equality, but it does
  // not contain uninterpreted functions. Keep that selection separate from
  // enable_uninterpreted_functions and restore the caller's array-equality
  // option when reset clears the logic or parser teardown ends the session.
  bool ax_enabled_by_logic = false;
  bool array_equality_option_before_logic = false;
  void restoreArrayEqualityOptionAfterLogic();

  // Unless --incremental=on or an explicit threshold overrides it, pure
  // QF_BV/QF_ABV sessions delay the persistent driver until solve 32; other
  // and unknown logics retain solve 3. The first solves carry the largest
  // all-new formulas, and the batch pipeline's whole-formula simplification
  // earns its keep there.
  // The user's REQUEST, read once from the flags, and the SESSION's state,
  // which a push turns on unless --incremental=off forbids it. Keeping them
  // apart matters because reset() starts a new session: folding the session
  // bit back into the request made a session that pushed and then reset
  // behave for the rest of its life as though --incremental=on had been
  // passed, forced-first-solve policies and all.
  bool incremental_from_start;
  bool session_incremental;
  bool delayed_bv_auto_engagement;
  size_t solves_run;

  // The most recent check-sat-assuming: its assumption terms, its verdict,
  // and whether it is still the last thing that happened to the assertion
  // stack -- get-unsat-assumptions answers from these, and any stack
  // change or ordinary check invalidates them, mirroring model_valid.
  ASTVec lastAssumptionTerms;
  SOLVER_RETURN_TYPE lastAssumingResult = SOLVER_UNDECIDED;
  bool lastCheckWasAssuming = false;

  // Remove the frame checkSatAssuming pushed, keeping the solver's derived
  // tables -- and with them the model just constructed -- readable. Every
  // real solve begins by clearing those tables (checkSat calls resetSolver
  // first), so nothing later can observe them as anything but a model.
  // Ordinary pop() must NOT do this: user pops can drop symbol
  // declarations, which the derived tables may reference.
  void popAssumptionFrame();

  // Set by the constructors that point GlobalParserBM at bm themselves, so
  // that the destructor knows to clear it again. Constructors that leave the
  // global alone leave it alone on the way out too -- callers such as the
  // rewrite-rule tools set GlobalParserBM once and then build and destroy
  // several interfaces over the same manager.
  bool set_global_parser_bm;

public:
  std::unique_ptr<LetMgr> letMgr;
  NodeFactory* nf;

  DLL_PUBLIC ~Cpp_interface();

  DLL_PUBLIC Cpp_interface(STPMgr& bm_);
  DLL_PUBLIC Cpp_interface(STPMgr& bm_, NodeFactory* factory);

  DLL_PUBLIC void startup();

  // FIXME: What is the difference between these two methods?
  DLL_PUBLIC const ASTVec GetAsserts(void);
  DLL_PUBLIC const ASTVec getAssertVector(void);

  DLL_PUBLIC UserDefinedFlags& getUserFlags();

  DLL_PUBLIC void AddAssert(const ASTNode& assert);
  DLL_PUBLIC void SetQuery(const ASTNode& q);

  // NODES//
  DLL_PUBLIC ASTNode CreateNode(stp::Kind kind,
                                const stp::ASTVec& children = _empty_ASTVec);

  DLL_PUBLIC ASTNode CreateNode(stp::Kind kind, const stp::ASTNode n0,
                                const stp::ASTNode n1);

  //	These belong in the node factory..

  // TERMS//
  DLL_PUBLIC ASTNode CreateZeroConst(unsigned int width);
  DLL_PUBLIC ASTNode CreateOneConst(unsigned int width);
  DLL_PUBLIC ASTNode CreateFPSpecialConst(stp::FPSpecial which,
                                          unsigned exp_width,
                                          unsigned sig_width);

  // Sort names the script introduced. A real table: the alias name is NOT
  // interned as a symbol (the old scheme made the sort name resolvable as a
  // term variable). Aliases follow assertion-frame scope, and
  // :global-declarations along with the other declarations.
  DLL_PUBLIC void addSortAlias(const std::string& name, const SourceSort& sort);
  DLL_PUBLIC bool lookupSortAlias(const std::string& name,
                                  SourceSort& sort) const;

  // The floating-point spelling of the same pair, kept because define-sort's
  // callers speak in exponent/significand widths.
  DLL_PUBLIC void addSortAlias(const std::string& name, unsigned exp_width,
                               unsigned sig_width);
  DLL_PUBLIC bool lookupSortAlias(const std::string& name,
                                  unsigned& exp_width,
                                  unsigned& sig_width) const;

  DLL_PUBLIC ASTNode CreateBVConst(std::string& strval, int base,
                                   int bit_width);
  DLL_PUBLIC ASTNode CreateBVConst(unsigned int width,
                                   uint64_t bvconst);
  DLL_PUBLIC ASTNode CreateRMConst(unsigned mode);
  DLL_PUBLIC ASTNode CreateSourceSymbol(const char* name,
                                        const SourceSort& source_sort);
  DLL_PUBLIC ASTNode LookupOrCreateSymbol(const char* const name);

  // A boolean variable applied to a constant, e.g. p(0x3), names an
  // ordinary boolean variable "p(0x3)".
  DLL_PUBLIC ASTNode CreateParameterisedBooleanVar(const ASTNode& var,
                                                   const ASTNode& constant);

  void removeSymbol(ASTNode to_remove);

  // Release query-local generated state whenever assertions/scoped symbols
  // are discarded; durable user expressions contain opaque ARRAY_EQ nodes.
  void discardExtensionalitySolveState();

  // Declare a function. We can't keep references to the declared variables
  // though. So rename them..
  DLL_PUBLIC void storeFunction(const std::string& name, const ASTVec& params,
                                const ASTNode& function);

  DLL_PUBLIC ASTNode applyFunction(const std::string& name,
                                   const ASTVec& params);

  // Resolve a name to its stored function in a single map probe, or NULL if
  // no such function exists. The pointer is into `functions`, which only
  // mutates between commands (define-fun stores, frame pops erase), never
  // while a term is being parsed -- so a pointer handed to the parser via a
  // token is valid for the lifetime of that token.
  DLL_PUBLIC const Function* lookupFunction(const std::string& name) const;

  // Apply an already-resolved function, skipping the by-name map probe.
  DLL_PUBLIC ASTNode applyFunction(const Function& f, const ASTVec& params);

  bool hasFunctions() const { return !functions.empty(); }

  // Context-owned uninterpreted declarations are distinct from stored
  // define-fun macros. The general forms are the direct C++ API (context
  // lifetime); the scoped declaration form is the SMT-LIB frame funnel.
  DLL_PUBLIC const UFDecl* declareUninterpretedFunction(
      const std::string& name, const std::vector<SourceSort>& domain,
      const SourceSort& codomain, std::string* diagnostic = NULL);
  DLL_PUBLIC const UFDecl* declareScopedUninterpretedFunction(
      const std::string& name, const std::vector<SourceSort>& domain,
      const SourceSort& codomain, std::string* diagnostic = NULL);
  DLL_PUBLIC const UFDecl* lookupUninterpretedFunction(
      const std::string& name) const;
  DLL_PUBLIC ASTNode applyUninterpretedFunction(
      const UFDecl* declaration, const ASTVec& actuals,
      std::string* diagnostic = NULL);
  // Evaluate an active durable UF_APPLY in the most recently certified
  // model. The returned node is a public Bool/BV constant, never a lowered
  // result symbol. Failure is nonfatal and returns ASTUndefined.
  DLL_PUBLIC ASTNode getUninterpretedApplicationValue(
      const ASTNode& application, std::string* diagnostic = NULL);
  bool hasUninterpretedFunctions() const;

  DLL_PUBLIC ASTNode LookupOrCreateSymbol(std::string name);
  DLL_PUBLIC bool LookupSymbol(const char* const name, ASTNode& output);
  DLL_PUBLIC bool LookupTemporarySymbol(const char* name, ASTNode& output);
  DLL_PUBLIC void setPrintSuccess(bool ps);
  DLL_PUBLIC bool isSymbolAlreadyDeclared(std::string name);

  // Retain the SMT-LIB2 set-logic classification needed by automatic
  // incremental engagement, select UF when the logic names it, and select
  // declared-sort arrays plus extensional equality for QF_AX. reset clears
  // these selections; reset-assertions retains them.
  DLL_PUBLIC void setLogic(const std::string& logic);

  // declare-sort is part of the UF logics and QF_AX. The latter deliberately
  // does not turn on nonzero-arity UF declarations in the lexer/parser.
  bool declaredSortsEnabled() const;

  // Create the node, then "new" it.
  DLL_PUBLIC ASTNode* newNode(const Kind k, const ASTNode& n0,
                              const ASTNode& n1);

  // Create the node, then "new" it.
  DLL_PUBLIC ASTNode* newNode(const Kind k, const int width, const ASTNode& n0,
                              const ASTNode& n1);

  // Create the node, then "new" it.

  // On testcase20 it took about 4.2 seconds to parse using the standard
  // allocator and the pool allocator.
  DLL_PUBLIC ASTNode* newNode(const ASTNode& copyIn);

  DLL_PUBLIC void deleteNode(ASTNode* n);
  DLL_PUBLIC void addSymbol(ASTNode& s);
  // Function formal parameters are parser-local bindings. They may shadow a
  // top-level declaration, and are installed for as long as the containing
  // define-fun command is being reduced.
  DLL_PUBLIC void addTemporarySymbol(ASTNode& s);

  // Check the shared top-level name space before the parser mutates a frame.
  // With UF enabled, a NONZERO-ARITY declare-fun name is deliberately lexed
  // unclassified so that a collision reaches this semantic check, which names
  // the owner it collided with. Every UF-free shape (zero-arity declare-fun,
  // declare-const, define-fun) keeps the legacy classified-token syntax error
  // at the name instead; for those this check is a backstop the lexer
  // normally pre-empts. Either way the collision ends the session -- the
  // caller reports through refuseCurrentCommand.
  DLL_PUBLIC bool validateTopLevelDeclarationName(
      const std::string& name, std::string* diagnostic = NULL);

  // Declare a symbol of SMT-LIB's RoundingMode sort: registers it like
  // addSymbol, marks it for the model printers, and asserts that it takes
  // one of the five one-hot mode encodings. The sort has exactly five
  // values but the 5-bit carrier has 32; without the constraint a model
  // can pick an encoding that denotes no rounding mode at all (e.g.
  // "r differs from all five modes" used to answer sat).
  DLL_PUBLIC void addRoundingModeSymbol(ASTNode& s);

  // Declare an array symbol of the parsed (Array X Y) sort: registers it
  // like addSymbol, lays the widths onto the node, stamps a float element's
  // format there too, and records any float-index, RoundingMode-index or
  // RoundingMode-element sort in the manager's array registries (the node
  // itself cannot carry those -- see STPMgr). The registries are dropped
  // with the symbol when its frame pops.
  DLL_PUBLIC void addArraySymbol(ASTNode& s, const array_sort& sort);

  // Whether an array-valued term's sorts -- base-symbol registries plus the
  // element format on the node -- agree with a parsed (Array X Y) sort.
  // Width agreement is the caller's (cheaper, better-reported) check; this
  // answers for the sort classes that share one width.
  DLL_PUBLIC bool arraySortsAgree(const ASTNode& arr, const array_sort& sort);

  DLL_PUBLIC void success();
  DLL_PUBLIC void error(std::string msg);
  DLL_PUBLIC void unsupported();

  // Command bookkeeping for the typed UF funnel: a malformed subexpression
  // is reduced to a carrier so the command can reach its outer boundary and
  // be discarded whole, with no malformed UF_APPLY or fresh placeholder
  // constructed or registered.
  DLL_PUBLIC void beginCurrentCommand();
  DLL_PUBLIC void abortCurrentCommand();
  // Reports the diagnostic and marks the command discarded, but returns:
  // for the parser's yyerror, where bison abandons the parse of its own
  // accord and the caller decides what to do about it. A caller that would
  // otherwise carry on wants refuseCurrentCommand.
  DLL_PUBLIC void rejectCurrentCommand(const std::string& diagnostic);
  // The same report, and then out. STP answers (get-info :error-behavior)
  // with immediate-exit, so an error it recovered from was a false claim --
  // and, where the discarded command was an assert, a claim that cost a
  // conjunct: the assertion went missing and the next check-sat answered
  // the query that was left.
  DLL_PUBLIC ATTR_NORETURN void refuseCurrentCommand(
      const std::string& diagnostic);
  DLL_PUBLIC void finishCurrentCommand();
  bool currentCommandRejected() const { return current_command_rejected; }

  // Resets the tables used by STP, but keeps all the nodes that have been
  // created.
  DLL_PUBLIC void resetSolver();

  // Reset STP back to "just started up" state.
  DLL_PUBLIC void reset();

  // Empty the assertion stack while retaining solver options and the
  // selected logic. Under the default :global-declarations false this
  // discards the declarations and definitions too; under true they stay.
  DLL_PUBLIC void resetAssertions();
  DLL_PUBLIC void pop();
  DLL_PUBLIC void push();
  DLL_PUBLIC void popToFirstLevel(); // We can't pop off the zeroeth level

  // Useful when printing back, so that you can parse, but ignore the request.
  DLL_PUBLIC void ignoreCheckSat();
  DLL_PUBLIC void checkSat(const ASTVec& assertionsSMT2,
                           bool fromCheckSatAssuming = false);

  // (check-sat-assuming (a1 ... an)): check-sat of the current stack
  // conjoined with the assumptions, which are discarded again afterwards.
  // Implemented as an internal push / assert each / checkSat / frame pop
  // that retains the model, so get-value and get-model afterwards answer
  // under the assumptions, and the assertion stack is unchanged.
  DLL_PUBLIC void checkSatAssuming(const ASTVec& assumptions);

  // After an unsat check-sat-assuming: the subset of its assumptions the
  // refutation used, printed as an SMT-LIB list of terms. The driver
  // supplies per-assumption granularity when it ran; otherwise the full
  // assumption set is reported, which is always a correct core.
  DLL_PUBLIC void getUnsatAssumptions();

  DLL_PUBLIC void cleanUp();

  DLL_PUBLIC void setOption(std::string, std::string);
  DLL_PUBLIC void getOption(std::string);
  DLL_PUBLIC void getInfo(std::string);
  // True when some declared sort's carrier cannot hold the terms this query
  // names of it, with a sentence saying which and what to raise. Neither
  // verdict is reportable then -- see the call site in checkSat.
  bool sortCarrierExhausted(const ASTVec& assertions,
                            std::string& detail) const;

  DLL_PUBLIC void getAssertions();

  DLL_PUBLIC void getModel();
  DLL_PUBLIC void getValue(const ASTVec& v);
};
}

#endif

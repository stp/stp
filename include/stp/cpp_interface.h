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
#include "stp/NodeFactory/NodeFactory.h"
#include "stp/Util/Attributes.h"
#include "extlib-unordered-dense/ankerl/unordered_dense.h"
#include <cstdint>
#include <map>
#include <memory>
#include <string>
#include <string_view>
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
// the assembled pair; parser plumbing like float_size. `width` is the bit
// width the sort is laid out on: the declared width for a bitvector, the
// packed width for a float, five for a rounding mode.
struct array_sort_component
{
  enum Kind
  {
    BITVECTOR,
    FLOATINGPOINT,
    ROUNDINGMODE
  };
  Kind kind;
  unsigned width;
  unsigned exp_bits; // FLOATINGPOINT only
  unsigned sig_bits; // FLOATINGPOINT only

  SourceSort sourceSort() const
  {
    switch (kind)
    {
      case BITVECTOR:
        return SourceSort::bitVector(width);
      case FLOATINGPOINT:
        return SourceSort::floatingPoint(exp_bits, sig_bits);
      case ROUNDINGMODE:
        return SourceSort::roundingMode();
    }
    return SourceSort::unknown();
  }
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
  std::map<std::string, std::pair<unsigned, unsigned>> sort_aliases;
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
                std::map<std::string, std::pair<unsigned, unsigned>>*
                    global_sort_alias_context);
    virtual ~SolverFrame();

    // Obtain the functions for the current frame
    vector<std::string>& getFunctions();

    // Obtain the symbols for the current frame
    ASTVec& getSymbols();

    void addSortAlias(const std::string& name);
    void addSymbol(const ASTNode& symbol);
    bool removeSymbol(const ASTNode& symbol);
    bool lookupSymbol(std::string_view name, ASTNode& output) const;

  private:
    vector<std::string> _scoped_functions;
    vector<std::string> _scoped_sort_aliases;
    ASTVec _scoped_symbols;
    // Hash map, not std::map: files declare tens of thousands of symbols
    // with long common prefixes, and a tree walk memcmps the prefix at
    // every level. Nothing iterates this in order.
    ankerl::unordered_dense::map<std::string, std::vector<ASTNode>,
                                 TransparentStringHash, std::equal_to<>>
        _symbol_bindings;
    ankerl::unordered_dense::map<std::string, Function>*
        _global_function_context;
    std::map<std::string, std::pair<unsigned, unsigned>>*
        _global_sort_alias_context;
  };

  // The vector of all frames that have been created by calling push
  std::vector< SolverFrame* > frames;

  // Obtain the symbols/functions for the current frame
  ASTVec& getCurrentSymbols();
  vector<std::string>& getCurrentFunctions();

  void checkInvariant();
  void init();
  void addFrame();
  void removeFrame();
  void assertRoundingModeValid(const ASTNode& s);

  bool produce_models;
  bool changed_model_status;

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

  // define-sort aliases for floating-point sorts. A real table: the alias
  // name is NOT interned as a symbol (the old scheme made the sort name
  // resolvable as a term variable). Aliases follow assertion-frame scope;
  // STP does not support global declarations.
  DLL_PUBLIC void addSortAlias(const std::string& name, unsigned exp_width,
                               unsigned sig_width);
  DLL_PUBLIC bool lookupSortAlias(const std::string& name,
                                  unsigned& exp_width,
                                  unsigned& sig_width) const;

  DLL_PUBLIC ASTNode CreateBVConst(std::string& strval, int base,
                                   int bit_width);
  DLL_PUBLIC ASTNode CreateBVConst(const char* const strval, int base);
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

  // Classify a name by its carrier return type in a single map probe:
  // BITVECTOR_TYPE or BOOLEAN_TYPE, or UNKNOWN_TYPE when the name is not a
  // stored function. Source-only distinctions are available from
  // functionReturnSourceSort().
  DLL_PUBLIC types functionReturnType(const std::string& name);
  DLL_PUBLIC SourceSort functionReturnSourceSort(const std::string& name);
  bool hasFunctions() const { return !functions.empty(); }

  DLL_PUBLIC ASTNode LookupOrCreateSymbol(std::string name);
  DLL_PUBLIC bool LookupSymbol(const char* const name, ASTNode& output);
  DLL_PUBLIC bool isSymbolAlreadyDeclared(char* name);
  DLL_PUBLIC void setPrintSuccess(bool ps);
  DLL_PUBLIC bool isSymbolAlreadyDeclared(std::string name);

  // Create the node, then "new" it.
  DLL_PUBLIC ASTNode* newNode(const Kind k, const ASTNode& n0,
                              const ASTNode& n1);

  // Create the node, then "new" it.
  DLL_PUBLIC ASTNode* newNode(const Kind k, const int width, const ASTNode& n0,
                              const ASTNode& n1);

  // Create the node, then "new" it.
  DLL_PUBLIC ASTNode* newNode(const Kind k, const int width, const ASTVec& v);

  // On testcase20 it took about 4.2 seconds to parse using the standard
  // allocator and the pool allocator.
  DLL_PUBLIC ASTNode* newNode(const ASTNode& copyIn);

  DLL_PUBLIC void deleteNode(ASTNode* n);
  DLL_PUBLIC void addSymbol(ASTNode& s);

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

  // Resets the tables used by STP, but keeps all the nodes that have been
  // created.
  DLL_PUBLIC void resetSolver();

  // Reset STP back to "just started up" state.
  DLL_PUBLIC void reset();

  // Empty the assertion stack and discard its declarations/definitions,
  // while retaining solver options and the selected logic. STP does not
  // support :global-declarations, so its required default is false.
  DLL_PUBLIC void resetAssertions();
  DLL_PUBLIC void pop();
  DLL_PUBLIC void push();
  DLL_PUBLIC void popToFirstLevel(); // We can't pop off the zeroeth level

  // Useful when printing back, so that you can parse, but ignore the request.
  DLL_PUBLIC void ignoreCheckSat();
  DLL_PUBLIC void checkSat(const ASTVec& assertionsSMT2);

  DLL_PUBLIC void cleanUp();

  DLL_PUBLIC void setOption(std::string, std::string);
  DLL_PUBLIC void getOption(std::string);
  DLL_PUBLIC void getInfo(std::string);
  DLL_PUBLIC void getAssertions();

  DLL_PUBLIC void getModel();
  DLL_PUBLIC void getValue(const ASTVec& v);
};

// Functions used by C++ clients of STP. TODO: either export abc cleanly or don't use this in clients.

/// Export version of Cnf_ClearMemory.
DLL_PUBLIC void CNFClearMemory();
}

#endif

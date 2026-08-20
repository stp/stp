/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
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

#ifndef STPMGR_H
#define STPMGR_H

#include "stp/AST/ASTBVConst.h"
#include "stp/AST/ASTFPConst.h"
#include "stp/AST/ASTRMConst.h"
#include "stp/AST/ASTInterior.h"
#include "stp/AST/ASTNode.h"
#include "stp/AST/ASTSymbol.h"

#include "stp/AST/AST.h"
#include "stp/NodeFactory/HashingNodeFactory.h"
#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Util/Attributes.h"
#include "extlib-unordered-dense/ankerl/unordered_dense.h"
#include <cstdint>

namespace stp
{
class ExtensionalityContext;

// The five SMT-LIB floating-point special values. Their nodes are ordinary
// packed interned constants (see STPMgr::CreateFPSpecialConst); a childless
// special-value node would hash-cons every format's NaN to one mutable node.
enum class FPSpecial
{
  NaN,
  PlusInfinity,
  MinusInfinity,
  PlusZero,
  MinusZero,
};

// One (distinct t1 ... tn) as the parser saw it, before it was dissolved into
// pairwise disequalities: the operands in source order, and the node the
// dissolution produced. Declared here rather than beside the pass that reads
// it, so that a core header does not have to include a Simplifier one.
struct DLL_PUBLIC DistinctGroup
{
  ASTVec operands;
  ASTNode emitted;
};

/*
 * STP Node Manager. Tools for managing AST nodes.
 */
class STPMgr
{
  friend class ASTNode;
  friend class ASTInterior;
  friend class ASTBVConst;
  friend class ASTSymbol;
  friend ASTNode HashingNodeFactory::CreateNode(
      Kind kind, ASTChildren back_children);

private:
  // Typedef for unique Interior node table.
  typedef ankerl::unordered_dense::set<ASTInterior*,
                                       ASTInterior::ASTInteriorHasher,
                                       ASTInterior::ASTInteriorEqual>
      ASTInteriorSet;

  // Typedef for unique Symbol node (leaf) table.
  typedef ankerl::unordered_dense::set<ASTSymbol*,
                                       ASTSymbol::ASTSymbolHasher,
                                       ASTSymbol::ASTSymbolEqual>
      ASTSymbolSet;

  // Typedef for unique BVConst node (leaf) table.
  typedef ankerl::unordered_dense::set<ASTBVConst*,
                                       ASTBVConst::ASTBVConstHasher,
                                       ASTBVConst::ASTBVConstEqual>
      ASTBVConstSet;

  // Unique node tables that enables common subexpression sharing
  ASTInteriorSet _interior_unique_table;

  // Interior nodes whose last reference has gone while another one was
  // already being deleted. Releasing a node releases its children, so
  // deleting the root of a deeply nested DAG would otherwise nest one
  // destructor per level and run off the stack; ASTInterior::CleanUp drains
  // this instead. See DeepDag_Test.cpp.
  std::vector<ASTInterior*> _pending_deletion;
  uint8_t _interior_deletion_depth = 0;

  // Table for variable names, let names etc.
  ASTSymbolSet _symbol_unique_table;

  ExtensionalityContext* extensionality = nullptr;

  // Table to uniquefy bvconst
  ASTBVConstSet _bvconst_unique_table;

  uint8_t last_iteration;

public:
  HashingNodeFactory* hashingNodeFactory;
  NodeFactory* defaultNodeFactory;

  // (distinct ...) groups as the parser saw them, before it dissolved each
  // into pairwise disequalities. Kept so a later pass can ask whether the
  // operands are symmetric and, if they are, state an order instead. Cleared
  // whenever the assertion stack is.
  std::vector<DistinctGroup> distinctGroups;

  // State of the array-equality (extensional arrays) decision procedure:
  // solve-local equality records, the complete per-solve array graph, and
  // pending refinement. Created lazily when a completed solve root containing
  // an opaque equality first reaches lowering.
  DLL_PUBLIC ExtensionalityContext* getExtensionality();
  ExtensionalityContext* getExtensionalityIfAny() const
  {
    return extensionality;
  }

  // frequently used nodes
  ASTNode ASTFalse, ASTTrue, ASTUndefined;

  bool soft_timeout_expired;

  // No nodes should already have the iteration number that is returned from
  // here. This never returns zero.
  uint8_t getNextIteration()
  {
    if (last_iteration == 255)
    {
      resetIteration();
      last_iteration = 0;
    }

    uint8_t result = ++last_iteration;
    assert(result != 0);
    return result;
  }

  // Detauls the iteration count back to zero.
  void resetIteration()
  {
    for (ASTInteriorSet::iterator it = _interior_unique_table.begin();
         it != _interior_unique_table.end(); it++)
    {
      (*it)->iteration = 0;
    }

    for (ASTSymbolSet::iterator it = _symbol_unique_table.begin();
         it != _symbol_unique_table.end(); it++)
    {
      (*it)->iteration = 0;
    }

    for (ASTBVConstSet::iterator it = _bvconst_unique_table.begin();
         it != _bvconst_unique_table.end(); it++)
    {
      (*it)->iteration = 0;
    }
  }

  size_t getAssertLevel() { return _asserts.size(); }

private:
  // Stack of Logical Context. each entry in the stack is a logical
  // context. A logical context is a vector of assertions. The
  // logical context is represented by a ptr to a vector of
  // assertions in that logical context. Logical contexts are
  // created by PUSH/POP
  vector<ASTVec*> _asserts;

  // Memo table that tracks terms already seen
  ASTNodeMap TermsAlreadySeenMap;

  // The query for the current logical context. BUG probably wrongly handled
  // and gets mixed up with the state, which it shouldn't (otherwise, next
  // query will be affected)
  ASTNode _current_query;

  // Ptr to class that reports on the running time of various parts
  // of the code
  RunTimes* runTimes;

  /****************************************************************
   * Private Member Functions                                     *
   ****************************************************************/

  // Look up a unique interior node by (kind, children), creating it -- as a
  // single tail-allocated block -- only on a miss. Probes with a non-owning
  // key, so a cache hit builds nothing.
  ASTInterior* LookupOrCreateInterior(Kind kind, ASTChildren children);

  // Create unique ASTSymbol node.
  ASTSymbol* LookupOrCreateSymbol(ASTSymbol& s);

  // Called whenever we want to make sure that the Symbol is
  // declared during semantic analysis
  bool LookupSymbol(ASTSymbol& s);

  // Called by ASTNode constructors to uniqueify ASTBVConst
  ASTBVConst* LookupOrCreateBVConst(ASTBVConst& s);

  ASTFPConst* LookupOrCreateFPConst(ASTFPConst& s);
  ASTRMConst* LookupOrCreateRMConst(ASTRMConst& s);

  // Cache of zero/one/max BVConsts of different widths.
  ASTVec zeroes;
  ASTVec ones;
  ASTVec max;

  // Set of new symbols introduced that replace the array read terms
  ASTNodeSet Introduced_SymbolsSet;

  CBV CreateBVConstVal;

  // Name -> symbols declared under it, in declaration order.
  //
  // A symbol's source sort is part of its identity, so the unique table is
  // keyed on (name, sort) and a name-only probe cannot be built for it. That
  // is what turned the two name lookups below into a scan of every symbol --
  // and they are not rare: LookupOrCreateSymbol(name) is how every internally
  // minted symbol is made (ArrayTransformer's per-abstracted-read variable,
  // RemoveUnconstrained's per-unconstrained-parent variable), so the scan made
  // symbol creation quadratic on problems with no floating point in them.
  //
  // This index answers those lookups in constant time. Entries are appended
  // where the unique table is inserted into and removed where a symbol is
  // cleaned up, so the two stay in step; the vector is for the case the sorted
  // key admits and the old name-keyed one could not -- one name at two sorts.
  typedef ankerl::unordered_dense::map<std::string, std::vector<ASTSymbol*>>
      SymbolNameIndex;
  SymbolNameIndex _symbol_name_index;

  // Distinct source sorts, interned so a derived one can be memoised on the
  // node as a pointer. std::unordered_set rather than a dense map because the
  // addresses have to stay put as it grows.
  std::unordered_set<SourceSort, SourceSort::Hasher> _source_sort_pool;

  // The symbols STP introduces under a name of its own choosing, so that the
  // name identifies the object without being looked up in the symbol table.
  // See introducedSymbol.
  std::map<std::string, ASTNode> _introduced_by_name;

public:
  bool LookupSymbol(const char* const name);
  bool LookupSymbol(const char* const name, ASTNode& output);

  // Intern `sort` and return its stable address, for ASTInternal's source-sort
  // memo. Unknown interns like anything else, so the memo needs no separate
  // negative sentinel.
  const SourceSort* internSourceSort(const SourceSort& sort)
  {
    return &*_source_sort_pool.insert(sort).first;
  }

  // How many times a source sort has actually been derived, as opposed to
  // answered from a node's memo. Counted so that the memo is directly
  // testable: a derivation walks children, so "once per node" versus "once
  // per path" is the whole difference, and it cannot be read off a result
  // that is correct either way.
  uint64_t source_sort_derivations = 0;

  // Record/forget a symbol in the name index. Called only from the unique
  // table's insertion point and from ASTSymbol::CleanUp.
  void indexSymbolName(ASTSymbol* symbol);
  void unindexSymbolName(ASTSymbol* symbol);

  /****************************************************************
   * Public Flags                                                 *
   ****************************************************************/
  UserDefinedFlags UserFlags;

  // This flag indicates as to whether the input has been determined
  // to be valid or not by this tool
  bool ValidFlag;

  // count is used in the creation of new variables
  unsigned int _symbol_count;

  // The value to append to the filename when saving the CNF.
  unsigned int CNFFileNameCounter;

  /****************************************************************
   * Public Member Functions                                      *
   ****************************************************************/

  DLL_PUBLIC STPMgr()
      : last_iteration(0), soft_timeout_expired(false), _symbol_count(0),
        CNFFileNameCounter(0)
  {
    ValidFlag = false;

    // Need to initiate the node factories before any nodes are created.
    hashingNodeFactory = new HashingNodeFactory(*this);
    defaultNodeFactory = hashingNodeFactory;

    ASTFalse = CreateNode(FALSE);
    ASTTrue = CreateNode(TRUE);
    ASTUndefined = CreateNode(UNDEFINED);
    runTimes = new RunTimes();
    _current_query = ASTUndefined;
    CreateBVConstVal = NULL;
  }

  RunTimes* GetRunTimes(void) { return runTimes; }

  unsigned int NodeSize(const ASTNode& a);

  /****************************************************************
   * Create Symbol and BVConst functions                          *
   ****************************************************************/

  // Create and return an ASTNode for a symbol
  ASTNode LookupOrCreateSymbol(const char* const name);

  // Create and return an ASTNode for a symbol Width is number of bits.
  ASTNode CreateOneConst(unsigned int width);
  ASTNode CreateTwoConst(unsigned int width);
  ASTNode CreateMaxConst(unsigned int width);
  ASTNode CreateZeroConst(unsigned int width);
  DLL_PUBLIC ASTNode CreateBVConst(CBV bv, unsigned width);
  ASTNode CreateBVConst(const char* strval, int base);
  ASTNode CreateBVConst(std::string strval, int base, int bit_width);
  ASTNode CreateBVConst(unsigned int width, uint64_t bvconst);
  ASTNode charToASTNode(unsigned char* strval, int base, int bit_width);

  DLL_PUBLIC ASTNode CreateFPConst(const stp::ASTNode& bvconst,
                                   unsigned exp_width, unsigned sig_width);
  DLL_PUBLIC ASTNode CreateRMConst(unsigned mode);

  // Restore a model carrier value to the immutable sort of the source term
  // it answers. The solver itself continues to evaluate plain bitvectors.
  ASTNode LiftSourceValue(const ASTNode& carrier,
                          const SourceSort& source_sort);

  // Create a source-language leaf atomically. Its complete sort participates
  // in hash-consing and cannot subsequently be changed by width setters.
  DLL_PUBLIC ASTNode CreateSourceSymbol(const char* name,
                                        const SourceSort& source_sort);

  // Conservative manager-lifetime hint: whether a floating-point node has
  // ever been created. Set by the format funnels (CreateFPConst,
  // ASTNode::SetExpWidth and FloatBlaster::withFormat, all through
  // noteFloatingPoint). False is a cheap proof that no query needs FP
  // lowering; true is not query state -- an unused term or a popped scope may
  // have set it -- so positive decisions must also inspect the current DAG.
  bool has_floating_point = false;

  // The same hint for the floating-point *theory* rather than for floats: a
  // RoundingMode symbol, constant or array element carries no format, so it
  // never reaches noteFloatingPoint, yet it still needs FpTotalise to pin it
  // to the five legal encodings. TopLevelSTP's theory test is the one place
  // that needs the broader question, and without this latch it had no cheap
  // negative and walked the DAG of every pure bit-vector query.
  bool has_floating_point_theory = false;

  void noteFloatingPointTheory() { has_floating_point_theory = true; }

  // Record that a float of a real format has been built. Every float's format
  // arrives through one of the funnels above, so calling this there is what
  // makes the fast-negative hint complete -- and it must be called whether or
  // not the format then needs storing on a node, since a node that derives its
  // format from its kind and children may later occur in a query.
  DLL_PUBLIC void noteFloatingPoint();

  bool isRoundingModeSymbol(const ASTNode& n) const
  {
    return n.GetKind() == SYMBOL &&
           n.GetSourceSort().kind() == SourceSort::Kind::RoundingMode;
  }

  // The five-way one-hot validity constraint for a RoundingMode symbol:
  // (or (= s RNE) ... (= s RNA)). Every path that introduces a
  // RoundingMode variable must assert this: the sort has exactly five values,
  // while the 5-bit carrier has thirty-two.
  ASTNode roundingModeValidConstraint(const ASTNode& s);

  // Whether `n` denotes a value of SMT-LIB's RoundingMode source sort.
  //
  // Everything that takes a rounding mode must ask this rather than test the
  // carrier's width. The sort has five values and the carrier thirty-two, and
  // symfpu's roundingDecision falls through to truncate-with-overflow-to-max
  // when every mode equality is false -- a sixth, non-IEEE mode. Accepting a
  // bare (_ BitVec 5) there let an input compute under it.
  bool isRoundingModeSortedTerm(const ASTNode& n) const;

  DLL_PUBLIC ASTNode CreateFPSpecialConst(FPSpecial which, unsigned exp_width,
                                          unsigned sig_width);

  // The declared symbol under an array term. Complete index/element sorts
  // live immutably on source symbols; WRITE and ITE derive them.
  // Null when no symbol is underneath.
  ASTNode arrayBaseSymbol(const ASTNode& arr) const;

  // Compatibility queries over the immutable SourceSort representation.
  bool arrayHasFpIndex(const ASTNode& arr, unsigned& exp_width,
                       unsigned& sig_width) const;
  bool arrayHasRmIndex(const ASTNode& arr) const;
  bool arrayHasRmElement(const ASTNode& arr) const;

  /****************************************************************
   * Create Node functions                                        *
   ****************************************************************/

  DLL_PUBLIC inline ASTNode
  CreateSymbol(const char* const name, unsigned indexWidth, unsigned valueWidth)
  {
    return defaultNodeFactory->CreateSymbol(name, indexWidth, valueWidth);
  }

  // Create and return an interior ASTNode
  DLL_PUBLIC inline ASTNode CreateNode(stp::Kind kind,
                                       const ASTVec& children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateNode(kind, children);
  }

  DLL_PUBLIC inline ASTNode
  CreateNode(Kind kind, const ASTNode& child0,
             const ASTVec& back_children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateNode(kind, child0, back_children);
  }

  DLL_PUBLIC inline ASTNode
  CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1,
             const ASTVec& back_children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateNode(kind, child0, child1, back_children);
  }

  DLL_PUBLIC inline ASTNode
  CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1,
             const ASTNode& child2, const ASTVec& back_children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateNode(kind, child0, child1, child2,
                                          back_children);
  }

  /****************************************************************
   * Create Term functions                                        *
   ****************************************************************/

  // Create and return an ASTNode for a term
  inline ASTNode CreateTerm(stp::Kind kind, unsigned int width,
                            const ASTVec& children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateTerm(kind, width, children);
  }

  inline ASTNode CreateArrayTerm(stp::Kind kind, unsigned int indexWidth,
                                 unsigned int width,
                                 const ASTVec& children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateArrayTerm(kind, indexWidth, width,
                                               children);
  }

  inline ASTNode CreateTerm(Kind kind, unsigned int width,
                            const ASTNode& child0,
                            const ASTVec& children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateTerm(kind, width, child0, children);
  }

  inline ASTNode CreateTerm(Kind kind, unsigned int width,
                            const ASTNode& child0, const ASTNode& child1,
                            const ASTVec& children = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateTerm(kind, width, child0, child1,
                                          children);
  }

  inline ASTNode CreateTerm(Kind kind, unsigned int width,
                            const ASTNode& child0, const ASTNode& child1,
                            const ASTNode& child2,
                            const ASTVec& /*children*/ = _empty_ASTVec)
  {
    return defaultNodeFactory->CreateTerm(kind, width, child0, child1, child2);
  }

  /****************************************************************
   * Functions that manage logical context                        *
   ****************************************************************/

  void Pop(void);
  void Push(void);

  // Queries aren't maintained on a stack.
  // Used by CVC & C-interface.
  const ASTNode GetQuery();
  void SetQuery(const ASTNode& q);

  const ASTVec GetAsserts();
  const ASTVec getVectorOfAsserts();

  // Every assertion currently on the stack, appended to out. Unlike
  // getVectorOfAsserts() this does not collapse each level into a
  // single conjunct, so it is safe to call outside a solve.
  void collectAsserts(ASTVec& out) const
  {
    for (size_t i = 0; i < _asserts.size(); i++)
      out.insert(out.end(), _asserts[i]->begin(), _asserts[i]->end());
  }

  // add a query/assertion to the current logical context
  void AddAssert(const ASTNode& assert);

  /****************************************************************
   * Toplevel printing and stats functions                        *
   ****************************************************************/

  // For printing purposes
  // Used just by the CVC parser.
  ASTVec ListOfDeclaredVars;

  // For printing purposes
  // Used just via the C-interface.
  // Note, not maintained properly wrt push/pops
  vector<stp::ASTNode> decls;

  // C API declarations have manager lifetime and no lexical binding frame.
  // Keep their printed names unambiguous even if the caller clears the list
  // used only for printing declarations.
  std::map<std::string, SourceSort> c_api_source_sorts;

  // Nodes seen so far
  ASTNodeSet PLPrintNodeSet;

  // Map from ASTNodes to LetVars
  ASTNodeMap NodeLetVarMap;

  // This is a vector which stores the Node to LetVars pairs. It
  // allows for sorted printing, as opposed to NodeLetVarMap
  vector<std::pair<ASTNode, ASTNode>> NodeLetVarVec;

  // A partial Map from ASTNodes to LetVars. Needed in order to
  // correctly print shared subterms inside the LET itself
  ASTNodeMap NodeLetVarMap1;

  // prints statistics for the ASTNode.
  void ASTNodeStats(const char* c, const ASTNode& a);

  // Print variable to the input stream
  void printVarDeclsToStream(ostream& os, ASTNodeSet& symbols);

  // Print assertions to the input stream
  void printAssertsToStream(ostream& os);

  // Variables are added automatically to the introduced_symbolset. Variables
  // in the set aren't printed out as part of the counter example.
  ASTNode CreateFreshVariable(int indexWidth, int valueWidth,
                              std::string prefix)
  {
    // The '@' prefix puts the name in the namespace SMT-LIB 2 reserves for
    // solver use: symbols beginning with '@' (or '.') may not be declared by
    // the user, so an introduced variable can never collide with an input one.
    char* d = (char*)alloca(sizeof(char) * (32 + prefix.length()));
    sprintf(d, "@%s_%d", prefix.c_str(), _symbol_count++);
    assert(!LookupSymbol(d));

    ASTNode CurrentSymbol = CreateSymbol(d, indexWidth, valueWidth);
    Introduced_SymbolsSet.insert(CurrentSymbol);
    return CurrentSymbol;
  }

  ASTNode CreateFreshSourceVariable(const SourceSort& source_sort,
                                    std::string prefix)
  {
    char* d = (char*)alloca(sizeof(char) * (32 + prefix.length()));
    sprintf(d, "@%s_%d", prefix.c_str(), _symbol_count++);
    ASTNode current = CreateSourceSymbol(d, source_sort);
    Introduced_SymbolsSet.insert(current);
    return current;
  }

  // Deterministic siblings of CreateFreshVariable: the name is a function
  // of the node(s) the variable stands for, so re-deriving the same thing
  // -- in a later solve, or a later incremental round -- yields the SAME
  // variable instead of a fresh one. Get-or-create by construction, since
  // symbols are hash-consed by (name, widths).
  //
  // PRECONDITION, and it is the caller's: keep `key` alive for as long as the
  // name derived from it means anything. Node numbers are unique among LIVE
  // nodes, not for the manager's lifetime -- the ASTNode GC frees unreferenced
  // interior nodes and re-mints their numbers -- so a key that dies can have
  // its number handed to an unrelated node, and the next derivation under that
  // number returns a variable already standing for something else. Nothing
  // here can check it: the node is gone by the time it would matter.
  //
  // Callers whose key is a live map key hold it by construction. The one that
  // does not is the incremental driver's per-round spine, which pins the raw,
  // prepared and lowered forms in `exactStackKeepAlive` for exactly this
  // reason. A new caller deriving a name from a node it does not otherwise
  // retain owes the same pin.
  //
  // The "_k" spelling keeps this namespace disjoint from the counter-named
  // variables, whose suffix is digits only.
  ASTNode CreateDeterministicVariable(int indexWidth, int valueWidth,
                                      const std::string& prefix,
                                      const ASTNode& key)
  {
    char* d = (char*)alloca(sizeof(char) * (48 + prefix.length()));
    sprintf(d, "@%s_k%lu", prefix.c_str(),
            (unsigned long)key.GetNodeNum());
    ASTNode current = CreateSymbol(d, indexWidth, valueWidth);
    Introduced_SymbolsSet.insert(current);
    return current;
  }

  ASTNode CreateDeterministicVariable(int indexWidth, int valueWidth,
                                      const std::string& prefix,
                                      const ASTNode& key,
                                      const ASTNode& key2)
  {
    char* d = (char*)alloca(sizeof(char) * (64 + prefix.length()));
    sprintf(d, "@%s_k%lu_k%lu", prefix.c_str(),
            (unsigned long)key.GetNodeNum(),
            (unsigned long)key2.GetNodeNum());
    ASTNode current = CreateSymbol(d, indexWidth, valueWidth);
    Introduced_SymbolsSet.insert(current);
    return current;
  }

  bool FoundIntroducedSymbolSet(const ASTNode& in)
  {
    if (Introduced_SymbolsSet.find(in) != Introduced_SymbolsSet.end())
    {
      return true;
    }
    return false;
  }

  // Whether `name` is in the namespace SMT-LIB 2 reserves for solver use.
  //
  // STP relies on that reservation rather than merely respecting it:
  // CreateFreshVariable mints '@'-prefixed names, and so do the objects
  // supplying the unspecified results of the partial floating-point
  // operations. The public boundaries refuse to declare such a name, which is
  // what makes the reliance sound -- see Cpp_interface::CreateSourceSymbol and
  // createPublicSourceSymbol.
  static bool isReservedSymbolName(const char* name)
  {
    return name != NULL && (name[0] == '@' || name[0] == '.');
  }

  // Record a symbol STP introduced rather than the user declaring it, so the
  // counterexample printers leave it out. CreateFreshVariable does this for
  // the names it mints; this is the way in for an introduced symbol whose
  // *name* is load-bearing and so cannot be minted there -- the arrays and
  // free bits supplying the unspecified results of the partial floating-point
  // operations, whose identity is their name (see
  // FloatBlaster::unspecifiedValue and FloatBlaster::unspecifiedCells).
  void noteIntroducedSymbol(const ASTNode& in)
  {
    Introduced_SymbolsSet.insert(in);
  }

  // The one symbol STP introduces under `name`, minted on first request.
  //
  // Identity is the name here on purpose: the solve and the two counterexample
  // re-derivations each rebuild these independently and have to arrive at the
  // same object, which a minted-per-call fresh variable cannot give them.
  //
  // That identity used to be nothing but the name, handed to a lookup that
  // matches on name alone and returns the first symbol declared under it at
  // *any* sort -- and whose width setters are then silent no-ops. A user
  // declaration at the matching sort therefore *became* the object: pinning a
  // cell of fp.min's choice map decided the solver's "unspecified" answer, the
  // user's own symbol vanished from the model, and a declaration at a
  // different sort aborted on a width assert. The '@' prefix was the whole
  // defence, and nothing enforced it.
  //
  // Now the map is the identity: after the first call the name is never looked
  // up again, and the first call refuses rather than adopts a name already
  // taken. The public boundaries make that refusal unreachable by rejecting
  // reserved names outright, so it is a backstop and not an expected error.
  DLL_PUBLIC ASTNode introducedSymbol(const std::string& name,
                                      unsigned index_width,
                                      unsigned value_width);

  // Whether a counterexample entry belongs to an introduced symbol. Entries
  // for an introduced *array* are keyed on the read rather than on the array
  // itself, so look through one: testing the key alone let every read of an
  // introduced array print.
  bool isIntroducedCounterExampleEntry(const ASTNode& in)
  {
    return FoundIntroducedSymbolSet(in) ||
           (in.GetKind() == READ && in.Degree() > 0 &&
            FoundIntroducedSymbolSet(in[0]));
  }

  bool VarSeenInTerm(const ASTNode& var, const ASTNode& term);

  ASTNode NewParameterized_BooleanVar(const ASTNode& var,
                                      const ASTNode& constant);

  void TermsAlreadySeenMap_Clear(void) { TermsAlreadySeenMap.clear(); }

  // This is called before SAT solving, so only junk that isn't needed
  // after SAT solving should be cleaned out.
  void ClearAllTables(void)
  {
    NodeLetVarMap.clear();
    NodeLetVarMap1.clear();
    PLPrintNodeSet.clear();
    TermsAlreadySeenMap.clear();
    NodeLetVarVec.clear();
    ListOfDeclaredVars.clear();
  }

  DLL_PUBLIC ~STPMgr();

  // Used just via the C-Interface, to allow some nodes to be automaticaly deleted.
  vector<stp::ASTNode*> persist;

  void print_stats() const
  {

    if (_interior_unique_table.size() > 0)
    {
      std::cerr << "Interiors:" << _interior_unique_table.size() << " of ";
      std::cerr << sizeof(**_interior_unique_table.begin()) << " bytes each"
                << std::endl;
    }

    std::map<Kind, int> freq;
    for (auto it : _interior_unique_table)
    {
      freq[it->GetKind()]++;
    }

    for (auto it : freq)
      std::cerr << it.first << " " << it.second << std::endl;

    if (_symbol_unique_table.size() > 0)
    {
      std::cerr << "Symbols:" << _symbol_unique_table.size() << " of ";
      std::cerr << sizeof(**_symbol_unique_table.begin()) << " bytes each"
                << std::endl;
    }

    if (_bvconst_unique_table.size() > 0)
    {
      std::cerr << "BVConsts:" << _bvconst_unique_table.size() << " of ";
      std::cerr << sizeof(**_bvconst_unique_table.begin()) << " bytes each"
                << std::endl;
    }
  }

  ASTNodeSet getSymbols()
  {
     ASTNodeSet symbols;
     symbols.reserve(_symbol_unique_table.size());

     for (const auto& s : _symbol_unique_table)
      {
          ASTNode n(s);
          symbols.insert(n);
      }

    return symbols; //hopefully move semantics.
  }

};

} // end of namespace

#endif

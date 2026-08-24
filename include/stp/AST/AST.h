/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
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

#ifndef AST_H
#define AST_H

#include "ASTNode.h"
#include "UsefulDefs.h"
#include "stp/Util/Attributes.h"
#include <ankerl/unordered_dense.h>

namespace stp
{
DLL_PUBLIC ATTR_NORETURN void FatalError(const char* str, const ASTNode& a,
                                         int w = 0);
DLL_PUBLIC ATTR_NORETURN void FatalError(const char* str);
void SortByExprNum(ASTVec& c);
void SortByArith(ASTVec& c);
bool exprless(const ASTNode& n1, const ASTNode& n2);
bool arithless(const ASTNode& n1, const ASTNode& n2);

// Functor form of exprless. Passing a free function to std::sort/is_sorted
// hands it a function pointer, which the algorithm cannot inline, so every
// comparison is an indirect call. This functor's operator() inlines (and
// GetNodeNum is itself inline), folding the comparison into the sort's inner
// loop. Ordering is identical to exprless. Used on the node-creation hot
// path, where sorting commutative children dominates parse time.
struct ExprLess
{
  bool operator()(const ASTNode& n1, const ASTNode& n2) const
  {
    return n1.GetNodeNum() < n2.GetNodeNum();
  }
};

// Functor form of arithless, for the same reason as ExprLess above. Ordering
// is identical to arithless.
struct ArithLess
{
  bool operator()(const ASTNode& n1, const ASTNode& n2) const
  {
    return arithless(n1, n2);
  }
};
bool isCommutative(const Kind k);
// Complete-DAG containment, iterative so input-chosen AST depth cannot consume
// the C++ call stack. Use for solve-boundary barriers whose answer cannot be
// taken from a manager-lifetime "has ever seen" hint.
bool containsKind(const ASTNode& n, Kind kind);
bool containsArrayOps(const ASTNode& n, STPMgr* stp);
// Query-local source-theory checks. The first asks whether FP lowering is
// needed; the second also includes RoundingMode-only syntax for printing.
bool containsFloatingPoint(const ASTNode& n, STPMgr* stp);
bool containsFloatingPointTheory(const ASTNode& n, STPMgr* stp);
bool numberOfReadsLessThan(const ASTNode& n, int v);
// Whether the estimated structural cost of eagerly expanding every array read
// is less than `limit`. See the definition: the read count alone does not
// distinguish a cheap expansion from one that is dozens of times slower than
// refinement.
bool arrayEagerCostLessThan(const ASTNode& n, uint64_t limit);

// A constant-aware estimate of how many index comparisons eager array
// Ackermannisation would introduce.
//
// The transform compares each read's index against every earlier index on the
// same base array, but CreateSimplifiedEQ decides a comparison between two
// constants, so constant-against-constant pairs cost nothing. For a base
// array reached by C distinct constant indexes and S symbolic ones, the
// comparisons that survive are |C|*|S| + |S|*(|S|-1)/2: three hundred
// constants against two symbolic indexes is 601, where a raw pairwise count
// reports 45451 and a raw read count reports 302. Neither of those is a
// number a policy can use.
//
// Writes are accesses -- a read pushed through a write chain is compared
// against each link's index. Indexes are attributed to the base symbols an
// array term resolves to, matching how the transform keys its read table.
// An array-valued if-then-else contributes to both branches, because the
// transform pushes reads through both.
uint64_t arrayCongruenceEstimate(const ASTNode& n);

// Whether two constants spell the same bits. Node identity understates
// this: a floating-point constant interns apart from the plain bitvector
// constant with its bits (the format is part of a constant's identity),
// so two distinct constant nodes may denote one bitvector value. Any
// rule that concludes "different value" from "different constant nodes"
// must compare through here instead.
bool constantsSameBits(const ASTNode& a, const ASTNode& b);

// Whether two constants are known to denote *different* values.
//
// This is the unsound direction, and the reason it has a name of its own:
// `a != b` answers it correctly for plain bitvector constants and wrongly
// for a floating-point or rounding-mode constant that shares its bits with
// one, and the two spellings look alike at a glance. Every rule that skips
// a write, proves two array indexes address different cells, or otherwise
// concludes "different value" must ask through here, so that the sites which
// depend on the distinction can be found by looking for this name.
inline bool constantsDenoteDifferentValues(const ASTNode& a, const ASTNode& b)
{
  return !constantsSameBits(a, b);
}

// The plain bit-vector constant spelling the same bits as `c`, or `c`
// itself when it already is one. A floating-point or rounding-mode
// constant interns apart from the plain constant with its bits, so two
// nodes can spell one value -- and anything that keys a container or
// builds a lookup node from a constant is asking about the spelling
// unless it normalises through here first.
ASTNode plainBitVectorConstant(STPMgr* bm, const ASTNode& c);

// Whether two constants denote the same value *of a given sort*, which
// for a floating-point sort is a weaker question than sharing bits.
//
// SMT-LIB's = on floats is identity of values, and NaN is one value with
// many packings, so two cells or indexes holding different NaN payloads
// hold the same value. Every other float value has exactly one packing,
// and every bit-vector and rounding-mode value has exactly one encoding,
// so for those this is constantsSameBits. The extensionality layer
// builds the circuit form of the same rule (packedFloatEq); this is the
// form for constants already in hand, used where the model is read back
// rather than constrained.
bool constantsSameSourceValue(const ASTNode& a, const ASTNode& b,
                              const SourceSort& sort);

inline bool constantsDenoteDifferentSourceValues(const ASTNode& a,
                                                 const ASTNode& b,
                                                 const SourceSort& sort)
{
  return !constantsSameSourceValue(a, b, sort);
}

// Whether `n` denotes bits to the bit-vector layers, which is not the same
// question as GetType() == BITVECTOR_TYPE.
//
// FloatBlast removes every floating-point *operation* but deliberately leaves
// float symbols, constants and the structural nodes over them as their packed
// bits, still reporting FLOATINGPOINT_TYPE so that model reconstruction can
// recover the sort. So a lowered formula handed to the bit-vector layers
// contains float-typed leaves that are, at that boundary, ordinary bitvectors.
//
// Every bit-vector-only pass that classifies a node by GetType() needs this
// question rather than the raw comparison, and it must be asked in one place:
// spelling it out per call site is what left BitBlaster::simplify_during_bb
// behind when the invariant was introduced, so that --bb.simplify-during-bb
// aborted on any query with a float leaf in it.
bool isBitsValued(const ASTNode& n);

// If (a > b) in the termorder, then return 1 elseif (a < b) in the
// termorder, then return -1 else return 0
int TermOrder(const ASTNode& a, const ASTNode& b);

// FUNCTION TypeCheck: Assumes that the immediate Children of the
// input ASTNode have been typechecked. This function is suitable
// in scenarios like where you are building the ASTNode Tree, and
// you typecheck as you go along. It is not suitable as a general
// typechecker

// NB: The boolean value is always true!
bool BVTypeCheck(const ASTNode& n);

ASTVec FlattenKind(Kind k, const ASTChildren& children, int maxDepth = INT_MAX);

// Checks recursively all the way down.
bool BVTypeCheckRecursive(const ASTNode& n);

// Takes a BVCONST and returns its constant value
unsigned int GetUnsignedConst(const ASTNode n);

typedef std::unordered_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    ASTNodeMap;

// Flat open-addressing alternative to ASTNodeMap. Much faster to probe and
// insert, but: values move on insert/erase (no pointer or reference
// stability), erase reorders survivors, and iteration is in insertion order.
// Only use where nothing points into the map and iteration order never
// reaches a decision.
typedef ankerl::unordered_dense::map<ASTNode, ASTNode, ASTNode::ASTNodeHasher,
                                     ASTNode::ASTNodeEqual>
    DenseNodeMap;

typedef std::unordered_map<ASTNode, int32_t, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    ASTNodeCountMap;

typedef std::unordered_set<ASTNode, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    ASTNodeSet;

typedef std::unordered_multiset<ASTNode, ASTNode::ASTNodeHasher,
                                ASTNode::ASTNodeEqual>
    ASTNodeMultiSet;

typedef std::unordered_map<ASTNode, ASTVec, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    ASTNodeToVecMap;

void FlattenKindNoDuplicates(const Kind k, const ASTChildren& children,
                             ASTVec& flat_children,
                             ASTNodeSet& alreadyFlattened);

// Needed for defining the MAP below
struct ltint
{
  bool operator()(int s1, int s2) const { return s1 < s2; }
};

class ClauseList;

// Datatype for ClauseLists
typedef std::map<int, ClauseList*, ltint> ClauseBuckets;

typedef std::map<int, ASTVec*, ltint> IntToASTVecMap;

// Function to dump contents of ASTNodeMap
ostream& operator<<(ostream& os, const ASTNodeMap& nmap);

void buildListOfSymbols(const ASTNode& n, ASTNodeSet& visited,
                        ASTNodeSet& symbols);

// The one iterative symbol-collection walk, shared by every
// visited-marking representation: firstVisit(n) answers true exactly
// once per node. buildListOfSymbols wraps it over a plain ASTNodeSet;
// the incremental driver wraps it over allocation-free paged epoch
// marks. The walk keeps its position on the heap, so input-chosen DAG
// depth cannot exhaust the call stack.
template <class FirstVisit>
void collectSymbols(const ASTVec& roots, FirstVisit firstVisit,
                    ASTNodeSet& symbols)
{
  ASTVec pending = roots;
  while (!pending.empty())
  {
    const ASTNode n = pending.back();
    pending.pop_back();
    if (!firstVisit(n))
      continue;
    if (n.GetKind() == SYMBOL)
      symbols.insert(n);
    for (unsigned i = 0; i < n.Degree(); i++)
      pending.push_back(n[i]);
  }
}
} // end namespace stp

#endif

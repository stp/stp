/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
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

#include "stp/AST/AST.h"
#include "stp/UninterpretedFunctions/UFDecl.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/NodeIterator.h"
#include <unordered_map>
#include <unordered_set>
#include <vector>

#if !defined(_MSC_VER)
// Needed for signal()
#include <unistd.h>
#endif

namespace stp
{
using std::cout;
using std::cerr;
using std::endl;

THREAD_LOCAL_IE uint64_t ASTInternal::node_uid_cntr = 0;

/****************************************************************
 * Universal Helper Functions                                   *
 ****************************************************************/

// Sort ASTNodes by expression numbers
bool exprless(const ASTNode& n1, const ASTNode& n2)
{
  return (n1.GetNodeNum() < n2.GetNodeNum());
}

// This is for sorting by arithmetic expressions (for
// combining like terms, etc.)
bool arithless(const ASTNode& n1, const ASTNode& n2)
{
  Kind k1 = n1.GetKind();
  Kind k2 = n2.GetKind();

  if (n1 == n2)
  {
    // necessary for "strict weak ordering"
    return false;
  }
  else if (BVCONST == k1 && BVCONST != k2)
  {
    // put consts first
    return true;
  }
  else if (BVCONST != k1 && BVCONST == k2)
  {
    // put consts first
    return false;
  }
  else if (SYMBOL == k1 && SYMBOL != k2)
  {
    // put symbols next
    return true;
  }
  else if (SYMBOL != k1 && SYMBOL == k2)
  {
    // put symbols next
    return false;
  }
  else
  {
    // otherwise, sort by exprnum (descendents will appear
    // before ancestors).
    return (n1.GetNodeNum() < n2.GetNodeNum());
  }
}

// True if the number of reads in "n" is less than "limit"
bool numberOfReadsLessThan(const ASTNode& n, int limit)
{
  if (limit <= 0)
    return false;

  std::unordered_set<uint64_t> visited;
  int reads = 0;

  // Admit a node once and say whether its children need walking. Atoms were
  // deliberately absent from the old memo and remain so here.
  auto descend = [&](const ASTNode& current) {
    if (current.isAtom() || !visited.insert(current.GetNodeNum()).second)
      return false;

    if (current.GetKind() == READ)
      reads++;
    return current.Degree() != 0;
  };

  if (!descend(n))
    return reads < limit;
  if (reads >= limit)
    return false;

  struct Frame
  {
    const ASTNode* node;
    size_t nextChild = 0;
  };
  static_assert(sizeof(Frame) <= 2 * sizeof(void*),
                "read-count frames must contain only traversal state");

  // Keep only suspended ancestors. More importantly, return globally as
  // soon as the strict bound is reached: unwinding the rest of the walk is
  // unnecessary, and may itself be a large untouched subtree.
  Frame current{&n};
  std::vector<Frame> parents;
  while (true)
  {
    if (current.nextChild < current.node->Degree())
    {
      const ASTNode* child = &(*current.node)[current.nextChild++];
      if (!descend(*child))
      {
        if (reads >= limit)
          return false;
        continue;
      }
      if (reads >= limit)
        return false;

      parents.push_back(current);
      current = Frame{child};
      continue;
    }

    if (parents.empty())
      return true;
    current = parents.back();
    parents.pop_back();
  }
}

// A bounded estimate of eager array Ackermannisation's structural cost.
//
// The read count the policy gates on is a proxy for how much the transform
// builds, and it is a bad one: a read whose array operand is a chain of
// WRITEs becomes one if-then-else per link in that chain, so nine reads over a
// four-thousand-deep store chain add thirty-six thousand nodes beyond the
// flat-array baseline. Measured, that is the difference between 0.12s and 5.8s
// on the same query -- the eager path is 48x SLOWER there than leaving it to
// read refinement.
//
// So this charges each distinct read for the WRITE and array-valued ITE nodes
// reachable beneath its array operand, and stops as soon as the bound is
// reached. It says nothing about the index-equality axioms the transform also
// builds; it is the structural term that makes the difference between a cheap
// eager expansion and a catastrophic one.
bool arrayEagerCostLessThan(const ASTNode& n, uint64_t limit)
{
  if (limit == 0)
    return false;

  uint64_t cost = 0;
  const auto charge = [&]() {
    // The predicate is strict. Checking before incrementing also avoids
    // wrapping when a caller supplies the largest possible bound.
    if (cost >= limit - 1)
      return false;
    ++cost;
    return true;
  };

  // Charge the structural expansion under one read. The transform pushes a
  // read through both branches of an array-valued ITE, so both branches must
  // be visited: following only one makes the policy depend on branch order.
  // Shared array nodes are charged once per read, matching the transform map's
  // sharing, while a shared spine reached by different reads is charged once
  // for each read because each index produces its own expansion.
  const auto chargeExpansion = [&](const ASTNode& start) {
    std::unordered_set<uint64_t> expanded;
    std::vector<ASTNode> pending(1, start);
    while (!pending.empty())
    {
      const ASTNode current = pending.back();
      pending.pop_back();
      const auto kind = current.GetKind();
      const bool arrayIte = kind == ITE && current.GetIndexWidth() > 0;
      if ((kind != WRITE && !arrayIte) ||
          !expanded.insert(current.GetNodeNum()).second)
        continue;

      if (!charge())
        return false;
      if (kind == WRITE)
        pending.push_back(current[0]);
      else
      {
        pending.push_back(current[1]);
        pending.push_back(current[2]);
      }
    }
    return true;
  };

  std::unordered_set<uint64_t> visited;
  std::vector<ASTNode> pending(1, n);
  while (!pending.empty())
  {
    const ASTNode current = pending.back();
    pending.pop_back();
    if (current.isAtom() || !visited.insert(current.GetNodeNum()).second)
      continue;
    if (current.GetKind() == READ)
    {
      if (!charge() || !chargeExpansion(current[0]))
        return false;
    }
    for (size_t i = 0; i < current.Degree(); ++i)
      pending.push_back(current[i]);
  }
  return true;
}

// See the declaration for why this exists: constants of one value need
// not be one node, because a floating-point constant interns apart from
// the plain constant with its bits.
bool constantsSameBits(const ASTNode& a, const ASTNode& b)
{
  assert(a.GetKind() == BVCONST && b.GetKind() == BVCONST);
  if (a == b)
    return true;
  return a.GetValueWidth() == b.GetValueWidth() &&
         0 == CONSTANTBV::BitVector_Lexicompare(a.GetBVConst(),
                                                b.GetBVConst());
}

// See the declaration.
ASTNode plainBitVectorConstant(STPMgr* bm, const ASTNode& c)
{
  assert(c.isConstant());
  const SourceSort::Kind sort = c.GetSourceSort().kind();
  if (c.GetKind() != BVCONST ||
      (c.GetExpWidth() == 0 && sort != SourceSort::Kind::RoundingMode))
    return c;
  return bm->CreateBVConst(CONSTANTBV::BitVector_Clone(c.GetBVConst()),
                           c.GetValueWidth());
}

// Whether the packed floating-point constant x of format (eb, sb) holds
// a NaN: an all-ones exponent over a nonzero significand, the layout
// being [sign | exponent eb | significand sb-1]. The value-level twin of
// the circuit ExtensionalityContext builds as isPackedNaN; keep the two
// reading alike.
static bool packedConstantIsNaN(const ASTNode& x, unsigned eb, unsigned sb)
{
  const unsigned w = eb + sb;
  if (x.GetKind() != BVCONST || x.GetValueWidth() != w)
    return false;
  CBV bits = x.GetBVConst();
  for (unsigned i = sb - 1; i + 1 < w; i++)
    if (!CONSTANTBV::BitVector_bit_test(bits, i))
      return false;
  for (unsigned i = 0; i + 1 < sb; i++)
    if (CONSTANTBV::BitVector_bit_test(bits, i))
      return true;
  return false;
}

// See the declaration.
bool constantsSameSourceValue(const ASTNode& a, const ASTNode& b,
                              const SourceSort& sort)
{
  if (constantsSameBits(a, b))
    return true;
  if (sort.kind() != SourceSort::Kind::FloatingPoint)
    return false;
  const unsigned eb = sort.exponentWidth();
  const unsigned sb = sort.significandWidth();
  return packedConstantIsNaN(a, eb, sb) && packedConstantIsNaN(b, eb, sb);
}

bool containsKind(const ASTNode& root, Kind kind)
{
  ASTNodeSet visited;
  ASTVec pending(1, root);
  while (!pending.empty())
  {
    const ASTNode node = pending.back();
    pending.pop_back();
    if (!visited.insert(node).second)
      continue;
    if (node.GetKind() == kind)
      return true;
    for (unsigned i = 0; i < node.Degree(); ++i)
      pending.push_back(node[i]);
  }
  return false;
}

// True if any descendants are arrays.
bool containsArrayOps(const ASTNode& n, STPMgr* mgr)
{

  NodeIterator ni(n, mgr->ASTUndefined, *mgr);
  ASTNode current;
  while ((current = ni.next()) != ni.end())
    if (current.GetIndexWidth() > 0)
      return true;

  return false;
}

bool containsFloatingPoint(const ASTNode& n, STPMgr* mgr)
{
  NodeIterator ni(n, mgr->ASTUndefined, *mgr);
  ASTNode current;
  while ((current = ni.next()) != ni.end())
  {
    if (is_FP_kind(current.GetKind()) ||
        current.GetSourceSort().containsFloatingPoint())
      return true;
  }
  return false;
}

bool containsFloatingPointTheory(const ASTNode& n, STPMgr* mgr)
{
  NodeIterator ni(n, mgr->ASTUndefined, *mgr);
  ASTNode current;
  while ((current = ni.next()) != ni.end())
  {
    if (is_FP_kind(current.GetKind()) ||
        current.GetSourceSort().usesFloatingPointTheory())
      return true;
  }
  return false;
}

bool isCommutative(const Kind k)
{
  switch (k)
  {
    case BVOR:
    case BVAND:
    case BVXOR:
    case BVNAND:
    case BVNOR:
    case BVXNOR:
    case BVPLUS:
    case BVMULT:
    case EQ:
    case ARRAY_EQ:
    case AND:
    case OR:
    case NAND:
    case NOR:
    case XOR:
    case IFF:
    case BVNOT:
    case NOT:
    case BVUMINUS:
      return true;
    default:
      return false;
  }

  return false;
}

ATTR_NORETURN void FatalError(const char* str, const ASTNode& a, int w)
{
  if (a.GetKind() != UNDEFINED)
  {
    cerr << "Fatal Error: " << str << endl << a << endl;
    cerr << w << endl;
  }
  else
  {
    cerr << "Fatal Error: " << str << endl;
    cerr << w << endl;
  }
  if (vc_error_hdlr)
  {
    vc_error_hdlr(str);
  }
  abort();
}

ATTR_NORETURN void FatalError(const char* str)
{
  cerr << "Fatal Error: " << str << endl;
  if (vc_error_hdlr)
  {
    vc_error_hdlr(str);
  }
  abort();
}

void SortByExprNum(ASTVec& v)
{
  sort(v.begin(), v.end(), ExprLess{});
}

void SortByArith(ASTVec& v)
{
  sort(v.begin(), v.end(), ArithLess{});
}

// If there is a lot of sharing in the graph, this will take a long
// time.  it doesn't mark subgraphs as already having been
// typechecked.
bool BVTypeCheckRecursive(const ASTNode& n)
{
  const ASTChildren c = n.GetChildren();

  if (!BVTypeCheck(n))
  {
    return false;
  }

  for (auto it = c.begin(), itend = c.end(); it != itend;
       it++)
  {
    if (!BVTypeCheckRecursive(*it))
    {
      return false;
    }
  }

  return true;
}

void buildListOfSymbols(const ASTNode& n, ASTNodeSet& visited,
                        ASTNodeSet& symbols)
{
  collectSymbols(ASTVec(1, n),
                 [&visited](const ASTNode& node)
                 { return visited.insert(node).second; },
                 symbols);
}

// A float is carried internally as its packed bits, so after FloatBlast a
// float-typed leaf may stand in a bitvector circuit -- but this is not public
// subtyping. The parser and C API reject BV operations over FP terms; this
// predicate exists for lowered and model-evaluation nodes built inside STP.
// A leaf's format is declared (a symbol) or
// fixed when it is made (an ASTFPConst, which interns apart from the plain
// constant with the same bits); a read, a store and an ITE derive theirs from
// the array or the branches they carry; an operation's comes from its kind.
// See deriveFPFormat: in every one of those cases the format follows from the
// node, so nothing can disagree about it.
//
// A bitvector-kind interior node is entitled to none. Its format could only
// have been stamped on by whoever lowered a float to those bits -- and nodes
// are hash-consed, so that stamp retypes every other use of the same bits.
// The input's own bitvectors start reporting FLOATINGPOINT_TYPE solver-wide.
// That is what BVSRSHIFT and the comparison predicates used to abort on, and
// what made to_fp read an integer source as a float and answer wrongly.
// ASTNode::SetExpWidth now refuses such a stamp; this rejects the result of
// one wherever the bits are used, so the two ends agree.
// Declared in AST.h; shared, because every bit-vector-only pass that
// classifies a node by GetType() has to ask this question and they must all
// ask it the same way.
bool isBitsValued(const ASTNode& n)
{
  const types t = n.GetType();

  if (BITVECTOR_TYPE == t)
    return true;
  if (FLOATINGPOINT_TYPE != t)
    return false;

  const Kind k = n.GetKind();
  return 0 == n.Degree() || is_FP_kind(k) || READ == k || WRITE == k ||
         ITE == k;
}

void checkChildrenAreBV(const ASTChildren& v, const ASTNode& n)
{
  // See isBitsValued. (This check was fully disabled during the
  // floating-point work because blasted circuits mix float-stamped and plain
  // children; accepting both types restores it for the genuine errors.)
  for (auto it = v.begin(), itend = v.end(); it != itend; it++)
  {
    if (!isBitsValued(*it))
    {
      cerr << "The type is: " << it->GetType() << endl;
      FatalError(
          "BVTypeCheck:ChildNodes of bitvector-terms must be bitvectors\n", n);
    }
  }
}

/* Maintains a set of nodes that have already been seen. So that deeply shared
 * AND,OR operations are not
 * flattened multiple times.
 */
ASTVec toASTVec(const ASTChildren& c)
{
  return ASTVec(c.begin(), c.end());
}

// Where the walk of one node's children has got to. `depth` is how much
// further the depth-limited form below may descend; the deduplicating one
// ignores it, as it always has.
//
// The frames are on the heap. A nested same-kind chain is as deep as the
// input nests, and a call per level exhausts the stack: measured to die
// between 100,000 and 150,000 at 8 MiB. Reached from the simplifier, the BV
// solver, PropagateEqualities, MergeSame and UseITEContext -- and while no
// parsed query gets there today, because the simplifying factory flattens a
// conjunction as it builds one, that is a property of the factory rather
// than of these functions. A pass building through the hashing factory
// reaches it. See DeepDag_Test.cpp.
namespace
{
struct FlattenFrame
{
  ASTChildren children;
  size_t i;
  int depth;

  FlattenFrame(const ASTChildren& c, int d) : children(c), i(0), depth(d) {}
};
}

void FlattenKindNoDuplicates(const Kind k, const ASTChildren& children,
                             ASTVec& flat_children,
                             ASTNodeSet& alreadyFlattened)
{
  // Children left to right, and a same-kind one expanded where it is reached,
  // so flat_children comes out in the order the recursion built it. The
  // frames hold spans into each node's own child storage, which its parent
  // keeps alive for the whole walk. Keep the current frame local so a flat
  // input never allocates a traversal stack; parents are needed only after
  // the first same-kind child is reached.
  FlattenFrame current(children, 0);
  std::vector<FlattenFrame> parents;

  while (true)
  {
    if (current.i == current.children.size())
    {
      if (parents.empty())
        break;
      current = parents.back();
      parents.pop_back();
      continue;
    }

    const ASTNode& child = current.children[current.i++];

    if (k != child.GetKind())
    {
      flat_children.push_back(child);
      continue;
    }

    // A same-kind child seen before contributes nothing a second time: its
    // operands are already in flat_children.
    if (!alreadyFlattened.insert(child).second)
      continue;

    parents.push_back(current);
    current = FlattenFrame(child.GetChildren(), 0);
  }
}

// A same-kind child is expanded every time it is reached, which on a DAG means
// once per root-to-leaf path rather than once per node. That is exponential in
// the input's sharing, and `depth` does not bound it: depth limits how far down
// the walk goes, and the cost is in how many ways it gets there. On
// QF_BV/Sage2/bench_16265.smt2 this grew one ASTVec past 30GB and the process
// was killed.
//
// Repeats cannot simply be dropped the way FlattenKindNoDuplicates drops them:
// that is sound only for the idempotent kinds, and BVPLUS is not one -- x + x
// is not x. So what bounds this is an output budget. Every step either pushes
// an operand or descends one level, so capping the pushes caps the walk.
//
// Returns false if the budget was passed, in which case flat_children holds a
// prefix of the operands and must be discarded: a truncated sum is not the sum.
//
// The budget only has to stop the explosion, so it is set far above what a
// formula plausibly needs rather than close to it. Declining to flatten is not
// a small loss: generated-tests/form_32.var_64.bits_32.cvc wants 1054 operands
// at its widest, and capping it below that leaves BVPLUS nested, which turns a
// two-second solve into one that has not finished after five minutes. A cap
// tight enough to be reached by an ordinary formula is worse than no pass at
// all. Against that, raising it costs the pathological file almost nothing:
// on QF_BV/Sage2/bench_16265.smt2 the walk that used to reach 30GB is abandoned
// at 0.68s and 53MB here, against 0.53s and 53MB at a thousand.
const size_t FLATTEN_OUTPUT_BUDGET = 100000;

bool FlattenKind(const Kind k, const ASTChildren& children, ASTVec& flat_children, int depth)
{
  FlattenFrame current(children, depth);
  std::vector<FlattenFrame> parents;

  while (true)
  {
    if (current.i == current.children.size())
    {
      if (parents.empty())
        break;
      current = parents.back();
      parents.pop_back();
      continue;
    }

    const ASTNode& child = current.children[current.i++];
    const int below = current.depth - 1;

    if (k == child.GetKind() && current.depth >= 0)
    {
      parents.push_back(current);
      current = FlattenFrame(child.GetChildren(), below);
    }
    else
    {
      flat_children.push_back(child);
      if (flat_children.size() > FLATTEN_OUTPUT_BUDGET)
        return false;
    }
  }

  return true;
}

// Flatten (k ... (k ci cj) ...) to (k ... ci cj ...)
ASTVec FlattenKind(Kind k, const ASTChildren& children, int maxDepth)
{
  ASTVec flat_children;
  if (k == OR || k == BVOR || k == BVAND || k == AND)
  {
    bool nested = false;
    for (const ASTNode& child : children)
      if (child.GetKind() == k)
      {
        nested = true;
        break;
      }

    // The overwhelmingly common flat case needs neither the traversal nor
    // its deduplication set. Range assignment sizes the vector exactly once.
    if (!nested)
    {
      flat_children.assign(children.begin(), children.end());
      return flat_children;
    }

    ASTNodeSet alreadyFlattened;
    FlattenKindNoDuplicates(k, children, flat_children, alreadyFlattened);
  }
  else
  {
    // This form never discards repeated same-kind subtrees, so its output has
    // at least the input's arity. The deduplicating form above can turn a
    // very wide list of repeated edges into only a few operands; reserving
    // the input's full width there retains memory for operands it discarded.
    flat_children.reserve(children.size());
    if (!FlattenKind(k, children, flat_children, maxDepth))
    {
      // Over budget: hand the operands back exactly as they arrived. Not
      // flattened, but every caller can rebuild from this, and no caller can
      // rebuild from a prefix.
      flat_children.clear();
      flat_children.assign(children.begin(), children.end());
    }
  }

  return flat_children;
}

// Rounding modes are carried as 5-bit one-hot bitvectors, so a well-formed
// one is any 5-bit bitvector: a literal from the grammar, or a symbol of
// SMT-LIB's RoundingMode sort.
//
// Deliberately the carrier's shape and not the sort. Whether a term really
// denotes one of RoundingMode's five values is
// STPMgr::isRoundingModeSortedTerm, and that is what the parser and the C
// API ask before building an operation -- but this runs over nodes STP
// builds for itself as well, including the operations model evaluation
// rebuilds with their children resolved, whose rounding mode can be the
// model's value for a read the solve never constrained. Those are
// well-formed and must type check.
static bool isRoundingMode(const ASTNode& n)
{
  return n.GetType() == BITVECTOR_TYPE && n.GetValueWidth() == 5;
}

bool BVTypeCheck_term_kind(const ASTNode& n, const Kind& k)
{
  // Symbols are a large share of the nodes built while parsing and have no
  // children, so return before paying the virtual call that fetches them.
  if (SYMBOL == k)
    return true;

  // The children of bitvector terms are in turn bitvectors.
  const ASTChildren v = n.GetChildren();

  switch (k)
  {
    case UF_APPLY:
    {
      if (n.Degree() < 2 || n[0].GetKind() != SYMBOL)
        FatalError("BVTypeCheck: malformed UF_APPLY declaration/arity", n);
      const SourceSort sort = n.GetSourceSort();
      if (!UFSignature::isSupportedSort(sort))
        FatalError("BVTypeCheck: unsupported UF_APPLY result sort", n);
      if (sort.kind() == SourceSort::Kind::Bool)
      {
        if (n.GetType() != BOOLEAN_TYPE)
          FatalError("BVTypeCheck: Bool UF_APPLY has a non-Bool carrier", n);
      }
      // A float-codomain application derives its format from the same
      // declaration identity its sort comes from, so it types as a float
      // rather than as its packed carrier. Every other admitted sort has a
      // bit-vector carrier of the packed width.
      else if (sort.kind() == SourceSort::Kind::FloatingPoint)
      {
        if (n.GetType() != FLOATINGPOINT_TYPE ||
            n.GetExpWidth() != sort.exponentWidth() ||
            n.GetSigWidth() != sort.significandWidth())
          FatalError("BVTypeCheck: float UF_APPLY has the wrong format", n);
      }
      else if (n.GetType() != BITVECTOR_TYPE ||
               n.GetValueWidth() != sort.packedWidth())
        FatalError("BVTypeCheck: UF_APPLY has the wrong carrier width", n);
      break;
    }

    case BVCONST:
      if (BITVECTOR_TYPE != n.GetType() && FLOATINGPOINT_TYPE != n.GetType())
        FatalError("BVTypeCheck: The term t does not typecheck, where t = \n",
                   n);
      break;

    case ITE:
      if (n.Degree() != 3)
        FatalError("BVTypeCheck: should have exactly 3 args\n", n);
      // At this internal checker boundary a lowered float branch and its
      // packed-bit circuit are one class. Public construction has already
      // required the source-level branches to have exactly the same sort.
      if (BOOLEAN_TYPE != n[0].GetType() ||
          (n[1].GetType() == BOOLEAN_TYPE) != (n[2].GetType() == BOOLEAN_TYPE))
        FatalError("BVTypeCheck: The term t does not typecheck, where t = \n",
                   n);
      if (n[1].GetValueWidth() != n[2].GetValueWidth())
      {
        FatalError("BVTypeCheck: length of THENbranch != length of "
                   "ELSEbranch in the term t = \n",
                   n);
      }
      if (n[1].GetIndexWidth() != n[2].GetIndexWidth())
        FatalError("BVTypeCheck: length of THENbranch != length of "
                   "ELSEbranch in the term t = \n",
                   n);
      // Branches that BOTH claim to be floats must agree on the format, as
      // for EQ below: two formats can share one packed width -- (8, 24) and
      // (24, 8) are both 32 bits -- so the width checks cannot tell them
      // apart, and the node would derive whichever branch's format comes
      // first (see deriveFPFormat) and silently read the other branch's
      // bits at it. A float branch and a plain bitvector branch remain legal
      // only here: that mix arises once lowering replaces a branch with its
      // circuit, after the public sort check.
      if (n[1].GetExpWidth() != 0 && n[2].GetExpWidth() != 0 &&
          (n[1].GetExpWidth() != n[2].GetExpWidth() ||
           n[1].GetSigWidth() != n[2].GetSigWidth()))
      {
        cerr << "expwidth of THENbranch: " << n[1].GetExpWidth() << endl;
        cerr << "expwidth of ELSEbranch: " << n[2].GetExpWidth() << endl;
        cerr << "sigwidth of THENbranch: " << n[1].GetSigWidth() << endl;
        cerr << "sigwidth of ELSEbranch: " << n[2].GetSigWidth() << endl;
        FatalError("BVTypeCheck: the THENbranch and ELSEbranch differ in "
                   "floating-point format in the term t = \n",
                   n);
      }
      break;

    case READ:
      if (n.GetChildren().size() != 2)
        FatalError("2 params to read.");
      if (n[0].GetIndexWidth() != n[1].GetValueWidth())
      {
        cerr << "Length of indexwidth of array: " << n[0]
             << " is : " << n[0].GetIndexWidth() << endl;
        cerr << "Length of the actual index is: " << n[1]
             << " is : " << n[1].GetValueWidth() << endl;
        FatalError("BVTypeCheck: length of indexwidth of array != length of "
                   "actual index in the term t = \n",
                   n);
      }
      if (ARRAY_TYPE != n[0].GetType())
        FatalError("First parameter to read should be an array", n[0]);
      // A float-indexed array's index is a float laid out as its packed
      // bits, exactly as a float element is (see WRITE's value below). The
      // pre-solve pass rewrites such indexes to canonical bits.
      if (BITVECTOR_TYPE != n[1].GetType() &&
          FLOATINGPOINT_TYPE != n[1].GetType())
        FatalError("Second parameter to read should be a bitvector or a float",
                   n[1]);
      break;

    case WRITE:
      if (n.GetChildren().size() != 3)
        FatalError("3 params to write.");
      if (n[0].GetIndexWidth() != n[1].GetValueWidth())
        FatalError("BVTypeCheck: length of indexwidth of array != length of "
                   "actual index in the term t = \n",
                   n);
      if (n[0].GetValueWidth() != n[2].GetValueWidth())
        FatalError("BVTypeCheck: valuewidth of array != length of actual "
                   "value in the term t = \n",
                   n);
      if (ARRAY_TYPE != n[0].GetType())
        FatalError("First parameter to read should be an array", n[0]);
      // As for READ: a float index rides as its packed bits.
      if (BITVECTOR_TYPE != n[1].GetType() &&
          FLOATINGPOINT_TYPE != n[1].GetType())
        FatalError("Second parameter to write should be a bitvector or a float",
                   n[1]);
      // The element of an array of floats is a float. It is laid out exactly
      // like a bitvector of the same width -- the array carries the format --
      // so everything below this point treats the two alike.
      if (BITVECTOR_TYPE != n[2].GetType() &&
          FLOATINGPOINT_TYPE != n[2].GetType())
        FatalError("Third parameter to write should be a bitvector or a float",
                   n[2]);
      break;

    case BVDIV:
    case BVMOD:
    case BVSUB:

    case SBVDIV:
    case SBVREM:
    case SBVMOD:

    case BVLEFTSHIFT:
    case BVRIGHTSHIFT:
    case BVSRSHIFT:
      if (n.Degree() != 2)
        FatalError("BVTypeCheck: should have exactly 2 args\n", n);
      /*FALLTHROUGH*/
    // run on.
    case BVOR:
    case BVAND:
    case BVXOR:
    case BVNOR:
    case BVNAND:
    case BVXNOR:

    case BVPLUS:
    case BVMULT:
    {
      if (!(v.size() >= 2))
        FatalError("BVTypeCheck:bitwise Booleans and BV arith operators must "
                   "have at least two arguments\n",
                   n);

      unsigned int width = n.GetValueWidth();
      for (auto it = v.begin(), itend = v.end(); it != itend;
           it++)
      {
        if (width != it->GetValueWidth())
        {
          cerr << "BVTypeCheck:Operands of bitwise-Booleans and BV arith "
                  "operators must be of equal length\n";
          cerr << n << endl;
          cerr << "width of term:" << width << endl;
          cerr << "width of offending operand:" << it->GetValueWidth() << endl;
          FatalError("BVTypeCheck:Offending operand:\n", *it);
        }
        if (BITVECTOR_TYPE != it->GetType())
          FatalError("BVTypeCheck: ChildNodes of bitvector-terms must be "
                     "bitvectors\n",
                     n);
      }
      break;
    }
    case BVSX:
    case BVZX:
      // in BVSX(n[0],len), the length of the BVSX term must be
      // greater than the length of n[0]
      if (n[0].GetValueWidth() > n.GetValueWidth())
      {
        FatalError("BVTypeCheck: BV[SZ]X(t,bv[sz]x_len) : length of 't' must "
                   "be <= bv[sz]x_len\n",
                   n);
      }
      if ((v.size() != 2))
        FatalError("BVTypeCheck:BV[SZ]X must have two arguments. The second "
                   "is the new width\n",
                   n);
      break;

    case BVCONCAT:
      checkChildrenAreBV(v, n);
      if (n.Degree() != 2)
        FatalError("BVTypeCheck: should have exactly 2 args\n", n);
      if (n.GetValueWidth() != n[0].GetValueWidth() + n[1].GetValueWidth())
        FatalError("BVTypeCheck:BVCONCAT: lengths do not add up\n", n);
      break;

    case BVUMINUS:
    case BVNOT:
      checkChildrenAreBV(v, n);
      if (n.Degree() != 1)
        FatalError("BVTypeCheck: should have exactly 1 args\n", n);
      if (n.GetValueWidth() != n[0].GetValueWidth())
        FatalError("BVTypeCheck: should have same value width\n", n);
      break;

    case BVEXTRACT:
      checkChildrenAreBV(v, n);
      if (n.Degree() != 3)
        FatalError("BVTypeCheck: should have exactly 3 args\n", n);
      if (!(BVCONST == n[1].GetKind() && BVCONST == n[2].GetKind()))
        FatalError("BVTypeCheck: indices should be BVCONST\n", n);
      if (n.GetValueWidth() !=
          n[1].GetUnsignedConst() - n[2].GetUnsignedConst() + 1)
        FatalError("BVTypeCheck: length mismatch\n", n);
      if (n[1].GetUnsignedConst() >= n[0].GetValueWidth())
        FatalError("BVTypeCheck: Top index of select is greater or equal to "
                   "the bitwidth.\n",
                   n);
      break;
    // The arithmetic operations take a rounding mode as their first child,
    // then their float operands; the rest take only floats. A rounding mode
    // is carried as a 5-bit one-hot bitvector (see symbolic_fp.h).
    case FP_ABS:
    case FP_NEG:
    case FP_ADD:
    case FP_SUB:
    case FP_MUL:
    case FP_DIV:
    case FP_FMA:
    case FP_SQRT:
    case FP_REM:
    case FP_ROUNDTOINTEGRAL:
    case FP_MIN:
    case FP_MAX:
    {
      unsigned int expected_args;
      unsigned int first_float;

      switch (k)
      {
        case FP_ABS:
        case FP_NEG:
          expected_args = 1;
          first_float = 0;
          break;
        case FP_SQRT:
        case FP_ROUNDTOINTEGRAL:
          expected_args = 2;
          first_float = 1;
          break;
        case FP_REM:
          expected_args = 2;
          first_float = 0;
          break;
        // fp.min/fp.max gain a third child -- the choice of zero -- once
        // FpTotalise has run, so both arities are well formed.
        case FP_MIN:
        case FP_MAX:
          expected_args = n.Degree() == 3 ? 3 : 2;
          first_float = 0;
          break;
        case FP_FMA:
          expected_args = 4;
          first_float = 1;
          break;
        default: // FP_ADD, FP_SUB, FP_MUL, FP_DIV
          expected_args = 3;
          first_float = 1;
          break;
      }

      std::string error_msg("");
      bool failed(false);

      if (n.Degree() != expected_args)
      {
        error_msg = "<fp> has the wrong number of arguments";
        failed = true;
      }
      else if (first_float == 1 && !isRoundingMode(n[0]))
      {
        error_msg = "first argument to <fp> is not a rounding mode";
        failed = true;
      }

      // The trailing choice-of-zero child is a 1-bit bitvector, not a float,
      // so it is checked separately.
      const bool has_choice = (k == FP_MIN || k == FP_MAX) && n.Degree() == 3;
      const unsigned int last_float = has_choice ? n.Degree() - 1 : n.Degree();

      if (!failed && has_choice &&
          (n[2].GetType() != BITVECTOR_TYPE || n[2].GetValueWidth() != 1))
      {
        error_msg = "<fp> min/max's choice of zero is not a 1-bit bitvector";
        failed = true;
      }

      for (unsigned int i = first_float; !failed && i < last_float; i++)
      {
        if (n[i].GetType() != FLOATINGPOINT_TYPE)
        {
          error_msg = "argument to <fp> is not an fp";
          failed = true;
        }
        else if (n[i].GetSigWidth() != n[first_float].GetSigWidth() ||
                 n[i].GetExpWidth() != n[first_float].GetExpWidth())
        {
          error_msg = "arguments to <fp> differ in format";
          failed = true;
        }
      }

      if (failed)
      {
        cerr << error_msg << endl;
        FatalError(error_msg.c_str(), n);
      }
      break;
    }

    // ((_ to_fp e s) bv) is (e, s, bits); ((_ to_fp e s) rm f) is
    // (e, s, rm, expr). The e/s children record the target format.
    case FP_TOFP:
    {
      std::string error_msg("");
      bool failed(false);

      if (n.Degree() != 3 && n.Degree() != 4)
      {
        error_msg = "to_fp should have 3 or 4 args";
        failed = true;
      }
      else if (!n[0].isConstant() || !n[1].isConstant())
      {
        error_msg = "to_fp's format arguments must be constants";
        failed = true;
      }
      // The target format is checked against the e/s children rather than
      // against the node's own exp/sig widths: the node factory type checks
      // while creating the node, which is before the parser has had a chance
      // to stamp the format onto it.
      else if (n.Degree() == 3)
      {
        // The packed bits are judged by width, and a float is allowed to
        // stand for them (see isBitsValued). Blasting ((_ to_fp e s) bits)
        // yields those same bits stamped with the format -- and nodes are
        // hash-consed, so the stamp can land on the very node 'bits' names,
        // which reports FLOATINGPOINT_TYPE from then on. It holds the same
        // e + s bits either way; insisting on BITVECTOR_TYPE aborted the
        // re-solve of a formula that had just solved.
        if (!isBitsValued(n[2]) ||
            n[2].GetValueWidth() !=
                n[0].GetUnsignedConst() + n[1].GetUnsignedConst())
        {
          error_msg = "to_fp's argument is not a bitvector of width e + s";
          failed = true;
        }
      }
      else if (!isRoundingMode(n[2]))
      {
        error_msg = "to_fp's second argument is not a rounding mode";
        failed = true;
      }
      // With a rounding mode this reformats a float. Converting a signed
      // integer is FP_TOFP_SIGNED; the sorts differ, so the kinds do.
      else if (n[3].GetType() != FLOATINGPOINT_TYPE)
      {
        error_msg = "to_fp's argument is not an fp";
        failed = true;
      }

      if (failed)
      {
        cerr << error_msg << endl;
        FatalError(error_msg.c_str(), n);
      }
      break;
    }

    // ((_ to_fp e s) rm bv) over a signed integer, and its unsigned
    // counterpart: (e, s, rm, bits) for both.
    case FP_TOFP_SIGNED:
    case FP_TOFP_UNSIGNED:
    {
      std::string error_msg("");
      bool failed(false);

      if (n.Degree() != 4)
      {
        error_msg = "to_fp/to_fp_unsigned over an integer should have 4 args";
        failed = true;
      }
      else if (!n[0].isConstant() || !n[1].isConstant())
      {
        error_msg = "to_fp's format arguments must be constants";
        failed = true;
      }
      else if (!isRoundingMode(n[2]))
      {
        error_msg = "to_fp's second argument is not a rounding mode";
        failed = true;
      }
      // The integer this converts rides in a bitvector -- or in a float leaf,
      // whose bits are just as good and which isBitsValued admits. What it
      // must not be is a bitvector some lowering has stamped a format onto.
      else if (!isBitsValued(n[3]))
      {
        error_msg = "to_fp's integer argument is not a bitvector";
        failed = true;
      }

      if (failed)
      {
        cerr << error_msg << endl;
        FatalError(error_msg.c_str(), n);
      }
      break;
    }

    // ((_ fp.to_ubv m) rm x): (m, rm, x), plus the unspecified value once
    // FpTotalise has run. Yields a bitvector of width m.
    case FP_TO_UBV:
    case FP_TO_SBV:
    {
      std::string error_msg("");
      bool failed(false);

      if (n.Degree() != 3 && n.Degree() != 4)
      {
        error_msg = "fp.to_ubv/fp.to_sbv should have 3 or 4 args";
        failed = true;
      }
      else if (!n[0].isConstant())
      {
        error_msg = "fp.to_ubv/fp.to_sbv's width must be a constant";
        failed = true;
      }
      else if (n.GetValueWidth() != n[0].GetUnsignedConst())
      {
        error_msg = "fp.to_ubv/fp.to_sbv's result width does not match";
        failed = true;
      }
      else if (!isRoundingMode(n[1]))
      {
        error_msg =
            "fp.to_ubv/fp.to_sbv's first argument is not a rounding mode";
        failed = true;
      }
      else if (n[2].GetType() != FLOATINGPOINT_TYPE)
      {
        error_msg = "fp.to_ubv/fp.to_sbv's argument is not an fp";
        failed = true;
      }
      else if (n.Degree() == 4 &&
               (n[3].GetType() != BITVECTOR_TYPE ||
                n[3].GetValueWidth() != n.GetValueWidth()))
      {
        error_msg =
            "fp.to_ubv/fp.to_sbv's unspecified value has the wrong width";
        failed = true;
      }

      if (failed)
      {
        cerr << error_msg << endl;
        FatalError(error_msg.c_str(), n);
      }
      break;
    }

    // fp -> IEEE bits: one float in, an (eb + sb)-bit bitvector out.
    case FP_TO_IEEE_BV:
    {
      if (n.Degree() != 1 || n[0].GetType() != FLOATINGPOINT_TYPE)
      {
        FatalError("fp -> IEEE bits takes one floating-point argument", n);
      }
      if (n.GetValueWidth() != n[0].GetExpWidth() + n[0].GetSigWidth())
      {
        FatalError("fp -> IEEE bits result width must be exp + sig width", n);
      }
      break;
    }

    default:
      cerr << _kind_names[k];
      FatalError("No type checking for type");
      break;
  }
  return true;
}

bool BVTypeCheck_nonterm_kind(const ASTNode& n, const Kind& k)
{
  // The children of bitvector terms are in turn bitvectors.
  const ASTChildren v = n.GetChildren();

  if (!(is_Form_kind(k) && BOOLEAN_TYPE == n.GetType()))
    FatalError("BVTypeCheck: not a formula:", n);

  switch (k)
  {
    case TRUE:
    case FALSE:
    case SYMBOL:
      return true;

    case BOOLEXTRACT:
      checkChildrenAreBV(v, n);

      if (n.Degree() != 2)
        FatalError("BVTypeCheck: should have exactly 2 args\n", n);
      if (!(BVCONST == n[1].GetKind()))
        FatalError("BVTypeCheck: index should be BVCONST\n", n);
      if (n[1].GetUnsignedConst() >= n[0].GetValueWidth())
      {
        FatalError("BVTypeCheck: index is greater or equal to the bitwidth.\n",
                   n);
      }
      break;

    case EQ:
      if (n.Degree() != 2)
        FatalError("BVTypeCheck: should have exactly 2 args\n", n);

      // The widths must always match. A blasted float keeps its bitvector
      // shape, so a float-stamped node may be equated with a plain bitvector
      // of the same width -- but two nodes that BOTH claim to be floats must
      // agree on the format: (8, 24) and (24, 8) share a total width of 32
      // yet are different sorts.
      if (n[0].GetValueWidth() != n[1].GetValueWidth() ||
          n[0].GetIndexWidth() != n[1].GetIndexWidth() ||
          (n[0].GetExpWidth() != 0 && n[1].GetExpWidth() != 0 &&
           (n[0].GetExpWidth() != n[1].GetExpWidth() ||
            n[0].GetSigWidth() != n[1].GetSigWidth())))
      {
        cerr << "valuewidth of lhs of EQ: " << n[0].GetValueWidth() << endl;
        cerr << "valuewidth of rhs of EQ: " << n[1].GetValueWidth() << endl;
        cerr << "indexwidth of lhs of EQ: " << n[0].GetIndexWidth() << endl;
        cerr << "indexwidth of rhs of EQ: " << n[1].GetIndexWidth() << endl;
        cerr << "expwidth of lhs of EQ: " << n[0].GetExpWidth() << endl;
        cerr << "expwidth of rhs of EQ: " << n[1].GetExpWidth() << endl;
        cerr << "sigwidth of lhs of EQ: " << n[0].GetSigWidth() << endl;
        cerr << "sigwidth of rhs of EQ: " << n[1].GetSigWidth() << endl;
        FatalError(
            "BVTypeCheck: terms in atomic formulas must be of equal length", n);
      }
      break;

    case ARRAY_EQ:
      if (n.Degree() != 2)
        FatalError("BVTypeCheck: ARRAY_EQ should have exactly 2 args\n", n);

      if (n[0].GetType() != ARRAY_TYPE || n[1].GetType() != ARRAY_TYPE ||
          n[0].GetValueWidth() != n[1].GetValueWidth() ||
          n[0].GetIndexWidth() != n[1].GetIndexWidth())
      {
        FatalError("BVTypeCheck: ARRAY_EQ requires identically typed arrays",
                   n);
      }
      break;

    case DISTINCT:
    {
      if (n.Degree() < 2)
        FatalError("BVTypeCheck: DISTINCT requires at least 2 operands", n);
      const SourceSort sort = n[0].GetSourceSort();
      if (!sort.isKnown())
        FatalError("BVTypeCheck: DISTINCT operands need a known source sort",
                   n);
      for (size_t i = 1; i < n.Degree(); ++i)
        if (n[i].GetSourceSort() != sort)
          FatalError("BVTypeCheck: DISTINCT operands have different source "
                     "sorts",
                     n);
      break;
    }

    case BVLT:
    case BVLE:
    case BVGT:
    case BVGE:
    case BVSLT:
    case BVSLE:
    case BVSGT:
    case BVSGE:
    case BVUADDO:
    case BVSADDO:
    case BVUMULO:
    case BVSMULO:
    case BVUSUBO:
    case BVSSUBO:
      if (n.Degree() != 2)
        FatalError("BVTypeCheck: should have exactly 2 args\n", n);
      if (BITVECTOR_TYPE != n[0].GetType() || BITVECTOR_TYPE != n[1].GetType())
      {
        FatalError("BVTypeCheck: terms in atomic formulas must be bitvectors",
                   n);
      }
      if (n[0].GetValueWidth() != n[1].GetValueWidth())
      {
        FatalError(
            "BVTypeCheck: terms in atomic formulas must be of equal length", n);
      }
      if (n[0].GetIndexWidth() != n[1].GetIndexWidth())
      {
        FatalError(
            "BVTypeCheck: terms in atomic formulas must be of equal length", n);
      }
      break;

    case NOT:
      if (1 != n.Degree())
      {
        FatalError("BVTypeCheck: NOT formula can have exactly one childNode",
                   n);
      }
      assert(n.GetNodeNum() == n[0].GetNodeNum() + 1);
      break;

    case AND:
    case OR:
    case XOR:
    case NAND:
    case NOR:
      if (2 > n.Degree())
      {
        FatalError("BVTypeCheck: AND/OR/XOR/NAND/NOR: must have atleast 2 "
                   "ChildNodes",
                   n);
      }
      break;

    case IFF:
    case IMPLIES:
      if (2 != n.Degree())
      {
        FatalError("BVTypeCheck:IFF/IMPLIES must have exactly 2 ChildNodes", n);
      }
      break;

    case ITE:
      if (3 != n.Degree())
        FatalError("BVTypeCheck:ITE must have exactly 3 ChildNodes", n);
      break;

    // The classification predicates: one float in, a Boolean out.
    case FP_ISNORMAL:
    case FP_ISSUBNORMAL:
    case FP_ISZERO:
    case FP_ISINFINITE:
    case FP_ISNAN:
    case FP_ISNEGATIVE:
    case FP_ISPOSITIVE:
      if (n.Degree() != 1)
        FatalError("BVTypeCheck: <fp> predicate takes exactly 1 arg", n);
      if (n[0].GetType() != FLOATINGPOINT_TYPE)
        FatalError("BVTypeCheck: argument of <fp> predicate is not an fp", n);
      break;

    case FP_LEQ:
    case FP_LT:
    case FP_GEQ:
    case FP_GT:
    case FP_EQ:
    case FP_SMT_EQ:
    {

      std::string error_msg("");
      bool failed(false);

      if (n.Degree() != 2)
      {
        error_msg = "<fp> should have exactly 2 args";
        failed = true;
      }
      else if (n[0].GetType() != FLOATINGPOINT_TYPE)
      {
        error_msg = "lhs of <fp> is not an fp";
        failed = true;
      }
      else if (n[1].GetType() != FLOATINGPOINT_TYPE)
      {
        error_msg = "rhs of <fp> is not an fp";
        failed = true;
      }
      else if (n[0].GetSigWidth() != n[1].GetSigWidth())
      {
        error_msg = "arguments to <fp> differ in sig width";
        cerr << n[0].GetSigWidth() << " " << n[1].GetSigWidth();
        failed = true;
      }
      else if (n[0].GetExpWidth() != n[1].GetExpWidth())
      {
        error_msg = "arguments to <fp> differ in exp width";
        cerr << n[0].GetExpWidth() << " " << n[1].GetExpWidth();
        failed = true;
      }

      if (failed)
      {
        cerr << error_msg << endl;
        FatalError(error_msg.c_str(), n);
      }
      break;
    }

    default:
      cerr << _kind_names[k];
      FatalError("BVTypeCheck: Unrecognized kind: ");
      break;
  }
  return true;
}

namespace
{
// The base array terms an array operand resolves to: down through write
// chains, and through both arms of an array-valued if-then-else. Anything
// else -- a symbol, or a term this cannot see through -- is a base.
void collectArrayBases(const ASTNode& array, std::vector<ASTNode>& bases)
{
  std::unordered_set<uint64_t> seen;
  std::vector<ASTNode> pending(1, array);
  while (!pending.empty())
  {
    const ASTNode current = pending.back();
    pending.pop_back();
    if (!seen.insert(current.GetNodeNum()).second)
      continue;

    const Kind kind = current.GetKind();
    if (kind == WRITE)
      pending.push_back(current[0]);
    else if (kind == ITE && current.GetIndexWidth() > 0)
    {
      pending.push_back(current[1]);
      pending.push_back(current[2]);
    }
    else
      bases.push_back(current);
  }
}

// The distinct constant and symbolic access indexes reaching one base array.
struct ArrayAccess
{
  std::unordered_set<uint64_t> constants;
  std::unordered_set<uint64_t> symbolic;
};
} // namespace

uint64_t arrayCongruenceEstimate(const ASTNode& n)
{
  // Node numbers stand in for the index nodes: only distinctness matters.
  std::unordered_map<uint64_t, ArrayAccess> byBase;

  const auto note = [&](const ASTNode& array, const ASTNode& index) {
    std::vector<ASTNode> bases;
    collectArrayBases(array, bases);
    for (size_t i = 0; i < bases.size(); i++)
    {
      ArrayAccess& a = byBase[bases[i].GetNodeNum()];
      if (index.isConstant())
        a.constants.insert(index.GetNodeNum());
      else
        a.symbolic.insert(index.GetNodeNum());
    }
  };

  std::unordered_set<uint64_t> visited;
  std::vector<ASTNode> pending(1, n);
  while (!pending.empty())
  {
    const ASTNode current = pending.back();
    pending.pop_back();
    if (current.isAtom() || !visited.insert(current.GetNodeNum()).second)
      continue;

    const Kind kind = current.GetKind();
    if (kind == READ || kind == WRITE)
      note(current[0], current[1]);

    for (size_t i = 0; i < current.Degree(); i++)
      pending.push_back(current[i]);
  }

  uint64_t total = 0;
  for (std::unordered_map<uint64_t, ArrayAccess>::const_iterator it =
           byBase.begin(); it != byBase.end(); ++it)
  {
    const uint64_t c = it->second.constants.size();
    const uint64_t s = it->second.symbolic.size();
    total += c * s + s * (s - 1) / 2;
  }
  return total;
}


/* FUNCTION: Typechecker for terms and formulas
 *
 * TypeChecker: Assumes that the immediate Children of the input
 * ASTNode have been typechecked. This function is suitable in
 * scenarios like where you are building the ASTNode Tree, and you
 * typecheck as you go along. It is not suitable as a general
 * typechecker.
 *
 * If this returns, this ALWAYS returns true. If there is an error it
 * will call FatalError() and abort.
 */
bool BVTypeCheck(const ASTNode& n)
{
  const Kind k = n.GetKind();

  if (is_Term_kind(k))
  {
    return BVTypeCheck_term_kind(n, k);
  }
  else
  {
    return BVTypeCheck_nonterm_kind(n, k);
  }
}

} // end of namespace

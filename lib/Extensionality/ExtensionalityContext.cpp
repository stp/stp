/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July, 2026
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

#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/ToSat/ToSATBase.h"
#include "stp/Util/DagWalk.h"
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <limits>

namespace stp
{

namespace
{

bool isArrayType(const ASTNode& n)
{
  return n.GetType() == ARRAY_TYPE;
}

bool nodeNumLess(const ASTNode& a, const ASTNode& b)
{
  return a.GetNodeNum() < b.GetNodeNum();
}

// Why this layer normalises every constant it keeps through
// plainBitVectorConstant (see AST.h): it works on packed bits and
// compares model constants by node identity, so a float-element write
// value held as a float constant would never compare equal to the same
// bits read back from the SAT assignment, and the checker would report
// the same phantom conflict on every refinement iteration. Scalar
// names, checker model values and lemma leaves are all kept plain.

// Whether the packed floating-point cell x of format (eb, sb) holds a NaN:
// an all-ones exponent with a nonzero significand, the layout being
// [sign | exponent eb | significand sb-1]. Built as a plain bitvector
// circuit because witness clauses can be minted during preparation, after
// the floating-point lowering has already run.
ASTNode isPackedNaN(NodeFactory* hf, const ASTNode& x, unsigned eb,
                    unsigned sb)
{
  // Each sub-term is built in its own statement. C++ does not sequence a
  // call's arguments against each other, so building two of them inside one
  // call leaves the order to the compiler -- and node ids are handed out in
  // creation order, which decides the numbering all the way out to the CNF.
  const unsigned w = eb + sb;
  const ASTNode expHigh = hf->CreateBVConst(32, w - 2);
  const ASTNode expLow = hf->CreateBVConst(32, sb - 1);
  const ASTNode exponent = hf->CreateTerm(BVEXTRACT, eb, x, expHigh, expLow);
  const ASTNode sigHigh = hf->CreateBVConst(32, sb - 2);
  const ASTNode sigLow = hf->CreateBVConst(32, 0);
  const ASTNode significand =
      hf->CreateTerm(BVEXTRACT, sb - 1, x, sigHigh, sigLow);
  const ASTNode expAllOnes =
      hf->CreateNode(EQ, exponent, hf->CreateMaxConst(eb));
  const ASTNode sigZero =
      hf->CreateNode(EQ, significand, hf->CreateZeroConst(sb - 1));
  return hf->CreateNode(AND, expAllOnes, hf->CreateNode(NOT, sigZero));
}

// SMT-LIB's = between two packed floating-point cells of format (eb, sb).
// Equal bits is too strong a test: every NaN bit pattern denotes the one
// NaN value, so two cells holding different payloads hold the same value.
// Every other value has exactly one packing, so the cells are equal
// exactly when their bits agree or both are NaN. Built as a plain
// bitvector circuit for the same reason isPackedNaN is.
ASTNode packedFloatEq(NodeFactory* hf, const ASTNode& l, const ASTNode& r,
                      unsigned eb, unsigned sb)
{
  // Sequenced deliberately; see the note in isPackedNaN.
  const ASTNode sameBits = hf->CreateNode(EQ, l, r);
  const ASTNode lNaN = isPackedNaN(hf, l, eb, sb);
  const ASTNode rNaN = isPackedNaN(hf, r, eb, sb);
  return hf->CreateNode(OR, sameBits, hf->CreateNode(AND, lNaN, rNaN));
}

// The packed bits of the one canonical quiet NaN of format (eb, sb):
// positive sign, all-ones exponent, only the quiet bit of the stored
// significand set -- exactly the pattern CreateFPConst interns every NaN
// literal to and pack produces for a symbolic NaN, so pinning a witness
// index to it keeps bit-level index congruence equal to value congruence.
ASTNode canonicalQuietNaN(STPMgr* bm, unsigned eb, unsigned sb)
{
  const unsigned w = eb + sb;
  const unsigned stored_sig = sb - 1; // the hidden bit is not stored
  CBV bits = CONSTANTBV::BitVector_Create(w, true);
  for (unsigned i = 0; i < eb; i++)
    CONSTANTBV::BitVector_Bit_On(bits, stored_sig + i);
  CONSTANTBV::BitVector_Bit_On(bits, stored_sig - 1);
  return bm->CreateBVConst(bits, w);
}

// Collect every node beneath (and including) n. The input chooses the DAG's
// depth, so retain suspended ancestors on the heap rather than recursing once
// per level.
void collectDag(const ASTNode& n, ASTNodeSet& visited)
{
  walkPreOrder(n, [&](const ASTNode& current) {
    return visited.insert(current).second;
  });
}

// The current form of an equality operand, read back from its witness
// anchor. The anchor was recorded as name = read(operand, lambda), and
// what this returns is whatever array that read now stands over.
//
// Two rewrites in the tree can act on a read of that shape, and they
// are dangerous in different ways.
//
// Distributing the read over an array if-then-else changes the shape,
// so it cannot go unnoticed -- and it is suppressed while the procedure
// is active anyway, because the checker reasons about those directly
// and needs the read left where it stands.
//
// Chasing the read through a write does not change the shape. It
// returns a read at the same index over a strictly deeper array, which
// would pass every check here and hand back an operand the equality was
// never about. Nothing suppresses it: SimplifyingNodeFactory::chaseRead
// runs on every READ built over a WRITE. What makes it safe is that it
// only steps over a write whose index it can prove different from the
// read index, and lambda is fresh -- no term outside the two anchors
// mentions it, so no context-free rule can decide "write index =
// lambda" either way, and the chase stops at the first write. That is a
// property of the formula rather than of this function, so
// locateCanonicalOperands checks it directly instead of leaving it as
// an argument in a comment.
//
// Anything else means an anchor was rewritten beyond recognition:
// refuse loudly rather than guess.
ASTNode recoverAnchoredOperand(const ASTNode& rhs, const ASTNode& lambda,
                               const ASTNode& proxy)
{
  if (rhs.GetKind() == READ)
  {
    if (rhs[1] != lambda)
      FatalError("array-equality: a witness read's index was rewritten "
                 "away, although witness indices are protected from "
                 "substitution",
                 proxy);
    return rhs[0];
  }
  if (rhs.GetKind() == ITE)
    FatalError("array-equality: a witness read was distributed over an "
               "array if-then-else, although that is suppressed while the "
               "procedure is active",
               proxy);
  FatalError("array-equality: a witness-read defining equation was "
             "rewritten into a shape operand recovery does not "
             "recognize",
             proxy);
  return rhs; // unreachable; FatalError does not return
}

} // namespace

ExtensionalityContext::ExtensionalityContext(STPMgr* bm_)
    : lemmasEmitted(0), lemmaAtomsFolded(0), lemmaRounds(0),
      lemmasInLargestRound(0), bm(bm_), solveInProgress(false),
      registrySealed(false),
      arrayGraphIsFrozen(false), graphBound(false),
      readTransformInProgress(false), readTransformComplete(false),
      pendingLemmaValid(false)
{
}

bool ExtensionalityContext::enabled() const
{
  return bm->UserFlags.enable_array_equality;
}

void ExtensionalityContext::collectAnticipatedArraySymbols(const ASTNode& n)
{
  ASTNodeSet visited;
  collectDag(n, visited);
  for (ASTNodeSet::const_iterator it = visited.begin(); it != visited.end();
       ++it)
    if (it->GetKind() == SYMBOL && isArrayType(*it))
      anticipatedArraySymbols.insert(*it);
}

// An equality between a chain of writes and the chain's own base
// array,
//
//   write(...write(base, i_n, v_n)..., i_1, v_1) = base
//
// (i_1 outermost), holds exactly when every written value is already
// in the base at its index, unless an outer write shadows it:
//
//   AND_k [ i_k = i_1 OR ... OR i_k = i_{k-1}
//           OR read(base, i_k) = v_k ]
//
// This dissolves the common "array unchanged except at a few indices"
// frame-condition shape into plain bitvector-and-read constraints --
// no abstraction variable, no witness, no refinement. The two-sided
// variant, where both operands stack writes on a shared deeper base,
// is deliberately not attempted: its guards grow quadratically, and
// the general lemmas-on-demand procedure already covers that shape.
//
// The cell comparison is the element sort's equality, not bit equality:
// over a float-element array two cells are equal when their bits agree
// or both are NaN (packedFloatEq). Comparing the bits alone lets a NaN
// payload that the base holds and a written value that is the canonical
// NaN -- what every symfpu-computed NaN packs to -- "differ", so the
// chain and its base come apart when they hold the same array. The
// index comparisons need no such qualification: an index sort that
// quotients its bit patterns has had its indexes canonicalised by
// FpTotalise before an opaque equality over the array is lowered.
//
// Built with the plain hashing factory; the result is ordinary formula
// content that STP's later passes simplify as usual. A conjunct whose
// index term is identical to an outer write's index term is certainly
// shadowed and is dropped here, since the hashing factory would not
// fold the reflexive equality itself. The outermost write never has
// outer writes, so the conjunction is never empty.
ASTNode ExtensionalityContext::solveWriteChain(const ASTNode& a,
                                               const ASTNode& b) const
{
  for (int orientation = 0; orientation < 2; orientation++)
  {
    const ASTNode& chain = (orientation == 0) ? a : b;
    const ASTNode& base = (orientation == 0) ? b : a;

    // Peel writes off the chain side, outermost first, until the base
    // side appears; anything else is not this shape.
    ASTVec writesOutermostFirst;
    ASTNode cur = chain;
    bool matched = false;
    while (cur.GetKind() == WRITE)
    {
      writesOutermostFirst.push_back(cur);
      cur = cur[0];
      if (cur == base)
      {
        matched = true;
        break;
      }
    }
    if (!matched)
      continue;

    NodeFactory* hf = bm->hashingNodeFactory;
    const unsigned ew = base.GetValueWidth();
    const SourceSort baseSort = base.GetSourceSort();
    assert(baseSort.kind() == SourceSort::Kind::Array);
    const SourceSort elementSort = baseSort.element();
    const bool floatElements =
        elementSort.kind() == SourceSort::Kind::FloatingPoint;
    const unsigned eb = floatElements ? elementSort.exponentWidth() : 0;
    const unsigned sb = floatElements ? elementSort.significandWidth() : 0;
    ASTVec conjuncts;
    for (size_t k = 0; k < writesOutermostFirst.size(); k++)
    {
      const ASTNode& indexK = writesOutermostFirst[k][1];
      const ASTNode& valueK = writesOutermostFirst[k][2];
      ASTVec disjuncts;
      bool certainlyShadowed = false;
      for (size_t m = 0; m < k; m++)
      {
        const ASTNode& indexM = writesOutermostFirst[m][1];
        if (indexK == indexM)
        {
          certainlyShadowed = true;
          break;
        }
        disjuncts.push_back(hf->CreateNode(EQ, indexK, indexM));
      }
      if (certainlyShadowed)
        continue;
      const ASTNode cell = hf->CreateTerm(READ, ew, base, indexK);
      disjuncts.push_back(eb != 0 ? packedFloatEq(hf, cell, valueK, eb, sb)
                                  : hf->CreateNode(EQ, cell, valueK));
      conjuncts.push_back(disjuncts.size() == 1
                              ? disjuncts[0]
                              : hf->CreateNode(OR, disjuncts));
    }
    return conjuncts.size() == 1 ? conjuncts[0]
                                 : hf->CreateNode(AND, conjuncts);
  }
  return ASTNode();
}

// The equality arm of the paper's formula abstraction (section 5), applied by
// solve-boundary lowering: return a fresh Boolean abstraction variable and
// cache the pair's witness bundle. Reflexive
// requests fold to true. The record's constraint bundle corresponds
// to the paper's preprocessing step 1 -- a fresh witness index
// lambda, the two virtual reads read(a,lambda) and read(b,lambda)
// (kept alive through named defining equations), and the witness
// clause "proxy OR nameL != nameR". The paper orders that
// preprocessing before abstraction; here the bundle is built
// alongside the variable, over the construction operands, with the
// plain hashing factory so no simplifying rewrite can alter the
// recorded terms, and enters the formula at solve time.
ASTNode ExtensionalityContext::makeEquality(const ASTNode& a, const ASTNode& b)
{
  const SourceSort aSort = a.GetSourceSort();
  const SourceSort bSort = b.GetSourceSort();
  if (!isArrayType(a) || !isArrayType(b) ||
      aSort.kind() != SourceSort::Kind::Array ||
      bSort.kind() != SourceSort::Kind::Array ||
      a.GetIndexWidth() != b.GetIndexWidth() ||
      a.GetValueWidth() != b.GetValueWidth())
  {
    FatalError("array-equality: equality between arrays requires "
               "identical index and element widths",
               a);
  }

  // Same packed width is not the same sort: a floating-point-element
  // array and a bitvector-element array of one packed width (or two
  // floating-point formats splitting one width differently) may not be
  // equated, mirroring the parser's rejection of = between a float and
  // a bitvector.
  if (aSort.element() != bSort.element())
  {
    FatalError("array-equality: equality between arrays requires "
               "identical element sorts",
               a);
  }

  if (aSort.index() != bSort.index())
    FatalError("array-equality: equality between arrays requires "
               "identical index sorts",
               a);

  // TopLevelSTP totalises the complete formula while ARRAY_EQ is still an
  // opaque, traversable node, before solve-boundary lowering calls here.
  // In particular its operands' partial FP operations, float indexes and
  // rounding modes have already been handled. Index canonicalisation is not
  // structurally idempotent, so applying FpTotalise again here would create a
  // second wrapper and disconnect the equality records from the constraints
  // established by that whole-formula pass.
  if (a == b)
    return bm->ASTTrue;

  // A chain of writes equated with its own base needs no abstraction
  // at all; solve it by rewriting.
  {
    const ASTNode solved = solveWriteChain(a, b);
    if (!solved.IsNull())
      return solved;
  }

  // The hashing factory sorts EQ children, so callers may present the
  // operands in either order; canonicalize the registry key the same
  // way.
  const bool ordered = a.GetNodeNum() < b.GetNodeNum();
  const ASTNode& left = ordered ? a : b;
  const ASTNode& right = ordered ? b : a;

  const std::pair<ASTNode, ASTNode> key(left, right);
  std::map<std::pair<ASTNode, ASTNode>, size_t>::const_iterator it =
      keyToRecord.find(key);
  if (it != keyToRecord.end())
  {
    // The key is the operand pair, so a hit is a record built from these
    // very operands. Check it, because nothing downstream ever recovers
    // the pair an abstraction variable stands for: a key that collapsed
    // two distinct equalities would hand this one a variable standing
    // for the other one's arrays, and the witness bundle, the checker
    // edges and the model would then all be consistent about the wrong
    // question.
    const Record& existing = records[it->second];
    if (!(existing.constructionLeft == left &&
          existing.constructionRight == right))
      FatalError("array-equality: the record registry returned an "
                 "abstraction variable built from a different operand pair",
                 left);
    return existing.proxy;
  }

  if (registrySealed)
    FatalError("array-equality: an array equality was built during a "
               "solve, after the registry's constraints were taken; its "
               "witness bundle could not reach the formula",
               left);

  NodeFactory* hf = bm->hashingNodeFactory;
  const unsigned iw = left.GetIndexWidth();
  const unsigned ew = left.GetValueWidth();

  // The registry is rebuilt every solve (beginSolve), but the variables a
  // record mints are deterministic in its operand pair: re-deriving the
  // same equality -- in a later solve, or a later incremental round --
  // re-mints the same proxy, lambda and witness names, so encodings and
  // lemmas over them stay meaningful across rounds. The left/right
  // witnesses need distinct prefixes now that no counter tells them apart.
  Record r;
  r.id = records.size();
  r.proxy = bm->CreateDeterministicVariable(0, 0, "ext_eq", left, right);
  r.constructionLeft = left;
  r.constructionRight = right;
  r.lambda = bm->CreateDeterministicVariable(0, iw, "ext_lam", left, right);
  r.nameL = bm->CreateDeterministicVariable(0, ew, "ext_wit_l", left, right);
  r.nameR = bm->CreateDeterministicVariable(0, ew, "ext_wit_r", left, right);

  ASTNode readL = hf->CreateTerm(READ, ew, left, r.lambda);
  ASTNode readR = hf->CreateTerm(READ, ew, right, r.lambda);
  r.anchorL = hf->CreateNode(EQ, r.nameL, readL);
  r.anchorR = hf->CreateNode(EQ, r.nameR, readR);

  // The witness disequality. Bitvector cells differ exactly when their
  // bits differ. Packed floating-point cells denote the one NaN value
  // under every NaN bit pattern (SMT-LIB = on floats is identity of
  // values, and symfpu carries no payload), so differing bits witness
  // a real difference only when the cells are not both NaN -- without
  // that qualification a false equality between float arrays could be
  // "witnessed" by two NaN payloads of pointwise-equal arrays.
  ASTNode differ =
      hf->CreateNode(NOT, hf->CreateNode(EQ, r.nameL, r.nameR));
  const SourceSort arraySort = left.GetSourceSort();
  assert(arraySort.kind() == SourceSort::Kind::Array);
  const SourceSort elementSort = arraySort.element();
  if (elementSort.kind() == SourceSort::Kind::FloatingPoint)
  {
    const unsigned eb = elementSort.exponentWidth();
    const unsigned sb = elementSort.significandWidth();
    // Sequenced deliberately; see the note in isPackedNaN.
    const ASTNode lNaN = isPackedNaN(hf, r.nameL, eb, sb);
    const ASTNode rNaN = isPackedNaN(hf, r.nameR, eb, sb);
    differ = hf->CreateNode(
        AND, differ, hf->CreateNode(NOT, hf->CreateNode(AND, lNaN, rNaN)));
  }
  else if (elementSort.kind() == SourceSort::Kind::RoundingMode)
  {
    // RoundingMode cells denote only through the five one-hot patterns,
    // so a witness difference must be a difference of modes: both cells
    // are pinned valid. (The reads of the formula are pinned by
    // FpTotalise; these virtual reads enter the formula after it ran.)
    // Sequenced deliberately; see the note in isPackedNaN.
    const ASTNode lValid = bm->roundingModeValidConstraint(r.nameL);
    const ASTNode rValid = bm->roundingModeValidConstraint(r.nameR);
    differ = hf->CreateNode(AND, differ,
                            hf->CreateNode(AND, lValid, rValid));
  }
  r.witnessClause = hf->CreateNode(OR, r.proxy, differ);

  // Where the index sort quotients its bit patterns, the witness index
  // may only range over the denoting patterns; see indexSortClause.
  {
    const SourceSort indexSort = arraySort.index();
    if (indexSort.kind() == SourceSort::Kind::FloatingPoint)
    {
      const unsigned ieb = indexSort.exponentWidth();
      const unsigned isb = indexSort.significandWidth();
      // Sequenced deliberately; see the note in isPackedNaN.
      const ASTNode notNaN =
          hf->CreateNode(NOT, isPackedNaN(hf, r.lambda, ieb, isb));
      const ASTNode isCanonical =
          hf->CreateNode(EQ, r.lambda, canonicalQuietNaN(bm, ieb, isb));
      r.indexSortClause = hf->CreateNode(OR, notNaN, isCanonical);
    }
    else if (indexSort.kind() == SourceSort::Kind::RoundingMode)
    {
      r.indexSortClause = bm->roundingModeValidConstraint(r.lambda);
    }
  }

  protectedSymbols.insert(r.proxy);
  protectedSymbols.insert(r.lambda);
  protectedSymbols.insert(r.nameL);
  protectedSymbols.insert(r.nameR);
  keyToRecord[key] = r.id;
  proxyToRecord[r.proxy] = r.id;
  records.push_back(r);
  return records.back().proxy;
}

ASTNode ExtensionalityContext::lowerArrayEqualities(const ASTNode& root)
{
  const ASTNodeMap noRewrites;
  return lowerArrayEqualities(root, noRewrites);
}

ASTNode ExtensionalityContext::lowerArrayEqualities(
    const ASTNode& root, const ASTNodeMap& preLoweringRewrites)
{
  if (!enabled())
    FatalError("array-equality: opaque equality reached lowering while the "
               "decision procedure is disabled");

  ASTNodeMap cache;
  NodeFactory* hf = bm->hashingNodeFactory;

  // Lower the DAG in the same left-to-right post-order as the former
  // recursive std::function. That function consumed one native call frame
  // per input level (and made a type-erased call per edge); a sufficiently
  // deep write operand therefore exhausted the stack before ordinary STP
  // preprocessing began.
  //
  // Most nodes do not contain ARRAY_EQ and come back unchanged. Keep the
  // current node's original children in its immutable storage and acquire an
  // owned vector only after one child changes. Scratch slots are nested and
  // released in traversal order, so unchanged frames stay compact while a
  // changed ancestor can retain its prefix across a changed descendant.
  struct Frame
  {
    enum : unsigned
    {
      noScratch = std::numeric_limits<unsigned>::max()
    };

    const ASTNode* node;
    size_t nextChild = 0;
    unsigned scratch = noScratch;
    bool waiting = false;

    explicit Frame(const ASTNode* n) : node(n) {}
  };
  static_assert(sizeof(Frame) <= 32,
                "array-equality lowering frames must stay compact");

  ASTNode result;

  // The recursive form cached leaves too. Settle them without allocating a
  // frame, at the same point in the traversal at which their call returned.
  auto settled = [&](const ASTNode& n) -> bool {
    const ASTNodeMap::const_iterator found = cache.find(n);
    if (found != cache.end())
    {
      result = found->second;
      return true;
    }
    if (n.Degree() != 0)
      return false;
    result = n;
    cache.insert(std::make_pair(n, result));
    return true;
  };

  ASTNode lowered;
  if (settled(root))
  {
    lowered = result;
  }
  else
  {
    std::vector<Frame> stack;
    stack.emplace_back(&root);

    std::vector<ASTVec> scratches;
    unsigned scratchesInUse = 0;

    auto scratchFor = [&](Frame& frame) -> ASTVec& {
      if (frame.scratch == Frame::noScratch)
      {
        assert(scratchesInUse < Frame::noScratch);
        frame.scratch = scratchesInUse++;
        if (frame.scratch == scratches.size())
          scratches.emplace_back();
      }
      return scratches[frame.scratch];
    };

    auto releaseScratch = [&](Frame& frame) {
      if (frame.scratch == Frame::noScratch)
        return;
      assert(frame.scratch + 1 == scratchesInUse);
      scratches[frame.scratch].clear();
      --scratchesInUse;
    };

    // Consume the answer for frame.nextChild, copying the original prefix
    // only when this is the first child that changed.
    auto acceptChild = [&](Frame& frame) {
      const ASTChildren original = frame.node->GetChildren();
      assert(frame.nextChild < original.size());
      if (result != original[frame.nextChild] &&
          frame.scratch == Frame::noScratch)
      {
        ASTVec& changed = scratchFor(frame);
        changed.reserve(original.size());
        changed.insert(changed.end(), original.begin(),
                       original.begin() + frame.nextChild);
      }
      if (frame.scratch != Frame::noScratch)
        scratches[frame.scratch].push_back(result);
      ++frame.nextChild;
    };

    while (true)
    {
      Frame& current = stack.back();

      if (current.waiting)
      {
        current.waiting = false;
        acceptChild(current);
      }

      bool descended = false;
      while (current.nextChild < current.node->Degree())
      {
        const ASTNode* child = &(*current.node)[current.nextChild];
        if (settled(*child))
        {
          acceptChild(current);
          continue;
        }

        current.waiting = true;
        stack.emplace_back(child);
        descended = true;
        break;
      }
      if (descended)
        continue;

      const ASTNode& n = *current.node;
      const ASTVec* changed =
          current.scratch == Frame::noScratch
              ? NULL
              : &scratches[current.scratch];

      if (n.GetKind() == ARRAY_EQ)
      {
        assert(n.Degree() == 2);
        const ASTNode& left = changed == NULL ? n[0] : (*changed)[0];
        const ASTNode& right = changed == NULL ? n[1] : (*changed)[1];
        result = makeEquality(left, right);
        currentLowerings[n] = result;
      }
      else if (changed == NULL)
      {
        result = n;
      }
      else if (n.GetValueWidth() == 0)
      {
        result = hf->CreateNode(n.GetKind(), *changed);
      }
      else if (n.GetIndexWidth() > 0)
      {
        result = hf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                                     n.GetValueWidth(), *changed);
      }
      else
      {
        result = hf->CreateTerm(n.GetKind(), n.GetValueWidth(), *changed);
      }

      cache.insert(std::make_pair(n, result));
      releaseScratch(current);
      stack.pop_back();
      if (stack.empty())
      {
        lowered = result;
        break;
      }
    }
  }

  // FpTotalise runs before this pass. If it changed an operand of an opaque
  // equality, the public expression handle still names the original node
  // while this traversal saw a rebuilt one. Alias only rewrites whose result
  // was reachable from this solve's root; `cache` is the reachability proof
  // and supplies the exact post-lowering formula (including TRUE when
  // totalisation made the operands reflexive).
  for (ASTNodeMap::const_iterator it = preLoweringRewrites.begin();
       it != preLoweringRewrites.end(); ++it)
  {
    assert(it->first.GetKind() == ARRAY_EQ);

    // Rebuilding ARRAY_EQ can prove reflexivity. That value remains exact
    // even if an enclosing Boolean simplification dropped it from the final
    // root, so retain the proved result for the original public handle.
    if (it->second.GetKind() != ARRAY_EQ)
    {
      assert(it->second.GetType() == BOOLEAN_TYPE);
      currentLowerings[it->first] = it->second;
      continue;
    }

    const ASTNodeMap::const_iterator loweredRewrite = cache.find(it->second);
    if (loweredRewrite != cache.end())
      currentLowerings[it->first] = loweredRewrite->second;
  }

  // Activation walks this exact root next and checks the lowering
  // postcondition while it does so; do not inventory the whole DAG once
  // merely to traverse it again immediately afterwards.
  activateReachableRecords(lowered);

  return lowered;
}

bool ExtensionalityContext::getCurrentLowering(const ASTNode& opaque,
                                               ASTNode& lowered) const
{
  const ASTNodeMap::const_iterator it = currentLowerings.find(opaque);
  if (it == currentLowerings.end())
    return false;
  lowered = it->second;
  return true;
}

void ExtensionalityContext::activateReachableRecords(
    const ASTNode& loweredRoot)
{
  std::set<size_t> activeIds;
  ASTNodeSet visited;
  visited.insert(loweredRoot);
  ASTVec pending(1, loweredRoot);
  while (!pending.empty())
  {
    const ASTNode node = pending.back();
    pending.pop_back();

    // ARRAY_EQ is legal only in the user-facing AST. Ordinary
    // simplification, array transformation and bit-blasting intentionally
    // have no case for it. This used to be a separate complete walk just
    // before activation.
    if (node.GetKind() == ARRAY_EQ)
      FatalError("array-equality: query lowering left an opaque equality",
                 node);

    auto enqueue = [&](const ASTNode& next) {
      if (visited.insert(next).second)
        pending.push_back(next);
    };

    const std::map<ASTNode, size_t>::const_iterator proxy =
        proxyToRecord.find(node);
    if (proxy != proxyToRecord.end() && activeIds.insert(proxy->second).second)
    {
      const Record& r = records[proxy->second];
      // An outer equality can hide an inner equality proxy in an array-ITE
      // condition or another operand subterm. Follow cached operands so that
      // activation is the transitive closure, not merely the proxies still
      // visible at the Boolean root.
      enqueue(r.constructionLeft);
      enqueue(r.constructionRight);
    }

    for (unsigned i = 0; i < node.Degree(); ++i)
      enqueue(node[i]);
  }

  activeRecordIds.assign(activeIds.begin(), activeIds.end());

  // Forget the lowering of every equality this solve did not keep. The
  // map is written for each opaque node as it is visited, before there
  // is any activation to consult, and lowering can then throw the
  // result away: an equality between a write chain and its own base is
  // solved by rewriting, and a conjunct of that rewriting is dropped
  // when an outer write to the same index certainly shadows it, taking
  // a nested equality's abstraction variable with it. The record is
  // never activated, so the variable occurs in no constraint and the
  // solver never assigns it -- but the entry survived, and the model
  // surfaces resolve public handles through it. They would then report
  // the two arrays unequal, because an unassigned Boolean completes to
  // false, while the same model prints them identically.
  //
  // A proxy that did not activate is exactly an equality unreachable in
  // this solve, so its entry has nothing left to say. Reflexive and
  // rewritten lowerings carry no proxy and are unaffected.
  for (ASTNodeMap::iterator it = currentLowerings.begin();
       it != currentLowerings.end();)
  {
    const std::map<ASTNode, size_t>::const_iterator record =
        proxyToRecord.find(it->second);
    if (record != proxyToRecord.end() &&
        activeIds.find(record->second) == activeIds.end())
      it = currentLowerings.erase(it);
    else
      ++it;
  }

  anticipatedArraySymbols.clear();
  for (size_t i = 0; i < activeRecordIds.size(); ++i)
  {
    const Record& r = records[activeRecordIds[i]];
    collectAnticipatedArraySymbols(r.constructionLeft);
    collectAnticipatedArraySymbols(r.constructionRight);
  }
}

void ExtensionalityContext::beginSolve()
{
  registrySealed = false;
  records.clear();
  keyToRecord.clear();
  proxyToRecord.clear();
  activeRecordIds.clear();
  currentLowerings.clear();
  protectedSymbols.clear();
  anticipatedArraySymbols.clear();
  arrayGraphIsFrozen = false;
  ownedArrays.clear();
  ownedWrites.clear();
  ownedWriteParents.clear();
  ownedItes.clear();
  ownedIteParents.clear();
  eqEdges.clear();
  eqAdjacency.clear();
  witnessObls.clear();
  // Scalar and condition names are rebuilt for each preprocessed formula.
  scalarNames.clear();
  nameToTermMap.clear();
  lemmaOnlySymbols.clear();
  graph = ExtGraph();
  graphBound = false;
  preparedTransformRoot = ASTNode();
  preparedReads.clear();
  transformedReads.clear();
  eliminatedReads.clear();
  readTransformInProgress = false;
  readTransformComplete = false;
  pendingLemmaValid = false;
  pendingLemmas.clear();
  eqLitCache.clear();
  lastObserved.clear();
}

void ExtensionalityContext::releaseSolveStorage()
{
  assert(!solveInProgress);
  beginSolve();
  std::vector<Record>().swap(records);
  std::vector<size_t>().swap(activeRecordIds);
  ASTNodeMap().swap(currentLowerings);
  std::vector<ExtEqEdge>().swap(eqEdges);
  std::vector<ExtWitness>().swap(witnessObls);
  std::vector<ExtConflict>().swap(pendingLemmas);
}

ASTNode ExtensionalityContext::conjoinRecordConstraints(const ASTNode& root)
{
  if (activeRecordIds.empty())
    return root;
  ASTVec conjuncts;
  conjuncts.push_back(root);
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    conjuncts.push_back(r.anchorL);
    conjuncts.push_back(r.anchorR);
    conjuncts.push_back(r.witnessClause);
    if (!r.indexSortClause.IsNull())
      conjuncts.push_back(r.indexSortClause);
  }
  ASTNode out = bm->defaultNodeFactory->CreateNode(AND, conjuncts);

  // Anticipate the complete owned graph before any pass can act on the
  // answer. Once an equality is active, the checker owns every array read in
  // the solve: access indices and values may themselves contain reads of
  // otherwise unrelated arrays, so a syntactic equality cone is not closed
  // under scalar data dependencies.
  //
  // All READ-headed substitutions are suppressed while the procedure is
  // active. anticipatedArraySymbols instead records this complete ownership
  // boundary before preprocessing, so prepare() can reject any array symbol
  // introduced later by a pass. It must therefore come from the whole root,
  // not just equality operands: an unrelated array or an array-ITE branch is
  // owned too.
  collectAnticipatedArraySymbols(out);

  // Everything the decision procedure needs is now in this solve's
  // formula; anything minted after this point could not be.
  registrySealed = true;
  return out;
}

bool ExtensionalityContext::equalityQuotientsBitPatterns() const
{
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const SourceSort sort =
        records[activeRecordIds[i]].constructionLeft.GetSourceSort();
    assert(sort.kind() == SourceSort::Kind::Array);
    if (sort.usesFloatingPointTheory())
      return true;
  }
  return false;
}

// Every distinct access-index term in the solve, grouped by the
// accessed array's shape. Writes are accesses exactly as they are for
// the lazy checker (paper section 11.4): equal stores at equal
// indices force equal values with no read anywhere near, so a write
// index is a point where an equality is observed and must be
// instantiated. One shared inventory per shape rather than one per
// equality-connected component: extra indexes only add valid
// implications of the guarding proxy, and sharing is what lets a
// chain a = b, b = c contradict a witness for a distinct (a, c) --
// the (a, c) record's lambda reaches the other two records' lemmas.
void ExtensionalityContext::collectIndexInventory(
    const ASTNode& root, IndexInventory& indexesByShape) const
{
  ASTNodeSet nodes;
  collectDag(root, nodes);
  for (ASTNodeSet::const_iterator it = nodes.begin(); it != nodes.end(); ++it)
  {
    const Kind k = it->GetKind();
    if (k == READ)
      indexesByShape[ArrayShape((*it)[0].GetIndexWidth(),
                                (*it)[0].GetValueWidth())]
          .insert((*it)[1]);
    else if (k == WRITE)
      indexesByShape[ArrayShape(it->GetIndexWidth(), it->GetValueWidth())]
          .insert((*it)[1]);
  }
}

uint64_t ExtensionalityContext::eagerLemmaCount(
    const IndexInventory& indexesByShape) const
{
  uint64_t lemmas = 0;
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    const IndexInventory::const_iterator it = indexesByShape.find(ArrayShape(
        r.constructionLeft.GetIndexWidth(), r.constructionLeft.GetValueWidth()));
    if (it != indexesByShape.end())
      lemmas += it->second.size();
  }
  return lemmas;
}

// The reads instantiation is about to create, and what they cost the read
// side afterwards.
//
// Every lemma reads both of its record's operands at every index of the
// record's shape, so an operand that is a bare array symbol acquires the
// whole shared inventory: its abstraction variables are fresh, nothing
// folds them, and read congruence then squares the inventory for that one
// array. An operand that is a write chain does not, because the read folds
// through the chain and lands on a base the input estimate already counted.
//
// This is the term that matters and the input formula does not show it. One
// query of thirty-six same-shape arrays reads 2036 comparisons before
// instantiation and 608685 after -- against a store-permutation query that
// reads 1830 before and none after. Judged on the input alone the two are
// indistinguishable, and taking the first one costs 6 GB against 129 MB.
uint64_t ExtensionalityContext::eagerInstantiationCongruence(
    const IndexInventory& indexesByShape) const
{
  uint64_t total = 0;
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    const IndexInventory::const_iterator it = indexesByShape.find(ArrayShape(
        r.constructionLeft.GetIndexWidth(),
        r.constructionLeft.GetValueWidth()));
    if (it == indexesByShape.end())
      continue;
    const uint64_t size = it->second.size();
    const ASTNode operands[2] = {r.constructionLeft, r.constructionRight};
    for (int k = 0; k < 2; k++)
    {
      // Only a write chain is known to fold. Anything else -- a symbol, an
      // array-valued if-then-else, a term this cannot see through -- is
      // charged in full, because being wrong in that direction costs a
      // solve that refines instead of one that exhausts memory.
      if (operands[k].GetKind() != WRITE)
        total += size * (size - 1) / 2;
    }
  }
  return total;
}

// The eager arm replaces the refinement loop with one conjoined block of
// records-times-indexes lemmas, and puts the solve on the eager read path
// besides. Both halves of that trade are decided on the same currency the
// array policy uses -- the index comparisons the transform would introduce,
// with constant-against-constant pairs charged nothing because they are
// decided rather than built -- so one budget governs both, and a query is
// judged on the work it causes rather than on how many reads it contains.
//
// The lemma block itself is deliberately not charged. It is linear in
// records times indexes and it is what pays for retiring the refinement
// loop; measured over the QF_AX corpus, a large block is the case that wins
// 3-5x, so charging for it would refuse exactly the queries worth taking.
//
// The structural cost of the read side is a different unit and keeps its own
// bound: a read over a chain of writes expands per link and is catastrophic
// eagerly. Both bounds short-circuit, and this runs once per solve.
bool ExtensionalityContext::eagerEqualityPreferred(
    const ASTNode& root, const IndexInventory& indexesByShape) const
{
  constexpr uint64_t expansionLimit = 1000;

  // Zero is off, not "only what costs nothing". A query whose indexes are
  // all constant estimates no comparisons at all, so a bare <= would take
  // the arm at a budget of zero -- which is the one setting whose whole
  // purpose is to leave the solve alone.
  if (bm->UserFlags.array_eager_budget == 0)
    return false;

  // What the solve pays is what the input already costs plus what
  // instantiation adds to it.
  const uint64_t cost = arrayCongruenceEstimate(root) +
                        eagerInstantiationCongruence(indexesByShape);

  return cost <= bm->UserFlags.array_eager_budget &&
         arrayEagerCostLessThan(root, expansionLimit);
}

ASTNode ExtensionalityContext::instantiateEagerAckermann(
    const ASTNode& root, const IndexInventory& indexesByShape)
{
  assert(!activeRecordIds.empty());
  assert(registrySealed); // the witness bundles are already in `root`
  assert(!equalityQuotientsBitPatterns());

  // records-times-indexes lemmas, before the transform's own quadratic
  // read expansion. That cost is what the user's --ackermanize opted
  // into; it is the same trade the eager path makes without equalities.
  NodeFactory* hf = bm->hashingNodeFactory;
  ASTVec conjuncts;
  conjuncts.push_back(root);
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    const unsigned ew = r.constructionLeft.GetValueWidth();
    const IndexInventory::const_iterator shape = indexesByShape.find(
        ArrayShape(r.constructionLeft.GetIndexWidth(), ew));
    if (shape == indexesByShape.end())
      continue;
    for (std::set<ASTNode>::const_iterator idx = shape->second.begin();
         idx != shape->second.end(); ++idx)
    {
      const ASTNode readL = hf->CreateTerm(READ, ew, r.constructionLeft, *idx);
      const ASTNode readR = hf->CreateTerm(READ, ew, r.constructionRight, *idx);
      conjuncts.push_back(hf->CreateNode(OR, hf->CreateNode(NOT, r.proxy),
                                         hf->CreateNode(EQ, readL, readR)));
    }
  }
  const ASTNode out = bm->defaultNodeFactory->CreateNode(AND, conjuncts);

  // Retire the records. Deliberately not beginSolve(): the current
  // lowerings must survive for the model surfaces, and the protected-
  // symbol set simply goes unconsulted once active() is false.
  activeRecordIds.clear();
  return out;
}

ASTNode ExtensionalityContext::prepareInitialFormula(const ASTNode& root)
{
  if (!active())
    return root;

  const ASTNode constrained = conjoinRecordConstraints(root);

  // Pointwise bit-equality is stronger than value equality for a sort that
  // quotients its bit patterns (NaN payloads, non-denoting patterns), so a
  // packed instantiation could refuse a genuine model. Such solves stay on
  // lemmas on demand; only a request by name is worth a warning.
  if (equalityQuotientsBitPatterns())
  {
    if (bm->UserFlags.ackermannisation)
    {
      std::cerr << "Warning: --ackermanize is disabled for queries with "
                   "array equality over floating-point sorts."
                << std::endl;
      bm->UserFlags.ackermannisation = false;
    }
    return constrained;
  }

  IndexInventory indexesByShape;
  collectIndexInventory(constrained, indexesByShape);

  if (!bm->UserFlags.ackermannisation &&
      !eagerEqualityPreferred(constrained, indexesByShape))
    return constrained;

  // The lemma block stands in for the equality refinement loop, and the read
  // side has to match it: retiring the records leaves ordinary array
  // operations behind, and the eager transform is what removes them. Both
  // drivers save and restore this flag around the solve, so selecting it
  // here cannot outlive the query.
  bm->UserFlags.ackermannisation = true;

  const ASTNode eager = instantiateEagerAckermann(constrained, indexesByShape);
  bm->ASTNodeStats("after eager equality instantiation: ", eager);
  return eager;
}

// Recover each record's canonical operands from its anchor equations
// in the current formula. The anchors were conjoined before STP's
// simplifications ran, so they were rewritten by exactly the passes
// that rewrote the rest of the formula; the array operand under each
// witness read is therefore the current form of the recorded operand.
// Fails loudly when an anchor is missing or malformed -- a protected
// definition was eliminated, which the substitution guards should have
// prevented.
void ExtensionalityContext::locateCanonicalOperands(const ASTNode& root)
{
  // Only the witness names are ever looked up below, so only they are
  // collected: a protected lambda or proxy turning up in an equation of
  // the same shape is none of this function's business.
  std::set<ASTNode> witnessNames;
  ASTNodeSet witnessIndexes;
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    witnessNames.insert(r.nameL);
    witnessNames.insert(r.nameR);
    witnessIndexes.insert(r.lambda);
  }

  // name symbol -> the anchored right-hand side: the witness read, or
  // the if-then-else the simplifier pushed it into.
  //
  // Exactly one equation of this shape may exist per name. The names
  // are fresh, so no user term mentions them; they occur only in their
  // own anchor and in the witness clause, whose equality has the other
  // NAME on its far side and so does not match here; substitution
  // cannot move them (SubstitutionMap::extensionalityProtected refuses
  // any pair with a protected symbol on either side) and unconstrained
  // removal cannot delete them (MutableASTNode's untouchable set); and
  // because nodes are immutable and hash-consed, a rewritten anchor's
  // predecessor is no longer reachable from the root, so the walk
  // cannot see both.
  //
  // That is a property of every pass that runs in between, not
  // something this function can arrange, and the walk visits the whole
  // DAG rather than the top-level conjuncts -- so a second equation of
  // this shape would be believed even nested under a disjunction. The
  // container is hash-ordered, so silently keeping the last one found
  // would pick a different operand from run to run and certify the
  // candidate against the wrong arrays. Refuse instead.
  std::map<ASTNode, ASTNode> anchorRhs;
  ASTNodeSet visited;
  collectDag(root, visited);

  // The question is existential and every write asks it against the same set
  // of witness indexes. Once a node's complete subtree has been checked and
  // found safe, every later write which shares that node is safe without a
  // fresh post-order map. Across all writes this visits each unique index-DAG
  // node once rather than once per write.
  //
  // The set is marked in pre-order, so a walk that finds a witness stops
  // with the subtrees of already-marked nodes unexamined. That never leaks
  // into a later answer only because a hit is fatal below: every call that
  // returns false ran to completion, and only completed walks leave nodes
  // behind for a later walk to trust. If the FatalError ever becomes a soft
  // skip, this memo must go back to per-walk state.
  ASTNodeSet checkedWriteIndexNodes;
  auto writeIndexMentionsWitness = [&](const ASTNode& index) {
    bool mentions = false;
    walkPreOrder(index, [&](const ASTNode& current) {
      if (mentions || !checkedWriteIndexNodes.insert(current).second)
        return false;
      if (witnessIndexes.find(current) != witnessIndexes.end())
      {
        mentions = true;
        return false;
      }
      return true;
    });
    return mentions;
  };

  for (ASTNodeSet::const_iterator it = visited.begin(); it != visited.end();
       ++it)
  {
    const ASTNode& n = *it;

    // No write index mentions a witness index. That is what stops a
    // read-over-write chase from stepping an anchor onto a deeper array
    // and handing recovery an operand the equality was never about (see
    // recoverAnchoredOperand): the chase steps over a write only when it
    // can decide that write's index against the read's, and a
    // context-free rule can decide nothing about a fresh symbol the
    // write index does not mention.
    //
    // Deliberately not the stronger "a witness index appears only as an
    // anchor read's index". It legitimately appears elsewhere -- a
    // constraint confining it to the patterns its sort denotes is one,
    // and a sort whose values are not all denoting needs exactly that --
    // and no such position gives a rewrite anything to work with. Only a
    // write index does.
    if (n.GetKind() == WRITE && writeIndexMentionsWitness(n[1]))
      FatalError("array-equality: a write index mentions a witness index, "
                 "so a rewrite could decide that write against an anchor "
                 "read and move the operand recovery reads",
                 n);

    if (n.GetKind() != EQ || n.Degree() != 2)
      continue;
    for (int side = 0; side < 2; side++)
    {
      const ASTNode& s = n[side];
      const ASTNode& other = n[1 - side];
      if (s.GetKind() != SYMBOL ||
          witnessNames.find(s) == witnessNames.end() ||
          !(other.GetKind() == READ || other.GetKind() == ITE))
        continue;
      const std::map<ASTNode, ASTNode>::const_iterator prev = anchorRhs.find(s);
      if (prev != anchorRhs.end() && !(prev->second == other))
        FatalError("array-equality: a witness read's defining equation "
                   "occurs twice with different right-hand sides, so which "
                   "one gives the equality operand's current form is not "
                   "determined",
                   s);
      anchorRhs[s] = other;
    }
  }

  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    Record& r = records[activeRecordIds[i]];
    std::map<ASTNode, ASTNode>::const_iterator lit = anchorRhs.find(r.nameL);
    std::map<ASTNode, ASTNode>::const_iterator rit = anchorRhs.find(r.nameR);
    if (lit == anchorRhs.end() || rit == anchorRhs.end())
      FatalError("array-equality: a witness-read defining equation was "
                 "lost during preprocessing, so the current form of an "
                 "equality operand cannot be recovered",
                 r.proxy);
    r.canonicalLeft = recoverAnchoredOperand(lit->second, r.lambda, r.proxy);
    r.canonicalRight = recoverAnchoredOperand(rit->second, r.lambda, r.proxy);
  }
}

// Compute the owned array-term graph directly from every array-valued
// node reachable in the prepared root. Record write parenthood at the
// same time; array-if-then-else parenthood is populated with its reified
// condition below, after scalar naming.
void ExtensionalityContext::computeArrayGraph(
    const ASTNode& root, std::set<ASTNode>& arrays,
    std::map<ASTNode, std::vector<ASTNode>>& parents)
{
  arrays.clear();
  parents.clear();

  ASTNodeSet visited;
  collectDag(root, visited);
  for (ASTNodeSet::const_iterator it = visited.begin(); it != visited.end();
       ++it)
  {
    const ASTNode& n = *it;
    if (isArrayType(n))
      arrays.insert(n);
    if (n.GetKind() == WRITE)
      parents[n[0]].push_back(n);
  }
  for (std::map<ASTNode, std::vector<ASTNode>>::iterator it = parents.begin();
       it != parents.end(); ++it)
    std::sort(it->second.begin(), it->second.end(), nodeNumLess);
}

// Create or reuse a scalar name for a checker-visible term and queue
// its defining constraint name = term. The defining equation is
// conjoined before bit-blasting, so the name has SAT variables and a
// lemma mentioning the term can be encoded over them.
ASTNode ExtensionalityContext::freshName(const ASTNode& term,
                                         ASTVec& namingConstraints)
{
  if (term.isConstant())
    return plainBitVectorConstant(bm, term);
  std::map<ASTNode, ASTNode>::const_iterator it = scalarNames.find(term);
  if (it != scalarNames.end())
    return it->second;
  // Deterministic per term: the same checker-visible term gets the same
  // scalar name in every solve, which is what lets an incremental round's
  // encoded lemmas and naming equations be reused when the round repeats.
  ASTNode name = bm->CreateDeterministicVariable(0, term.GetValueWidth(),
                                                 "ext_name", term);
  protectedSymbols.insert(name);
  namingConstraints.push_back(
      bm->defaultNodeFactory->CreateNode(EQ, name, term));
  scalarNames[term] = name;
  nameToTermMap[name] = term;
  return name;
}

// See the header. The Boolean analogue of freshName.
ASTNode ExtensionalityContext::conditionName(const ASTNode& cond,
                                             ASTVec& namingConstraints)
{
  std::map<ASTNode, ASTNode>::const_iterator it = scalarNames.find(cond);
  if (it != scalarNames.end())
    return it->second;
  // Deterministic per condition, as in freshName.
  ASTNode name = bm->CreateDeterministicVariable(0, 0, "ext_cond", cond);
  protectedSymbols.insert(name);
  namingConstraints.push_back(
      bm->defaultNodeFactory->CreateNode(IFF, name, cond));
  scalarNames[cond] = name;
  nameToTermMap[name] = cond;
  return name;
}

// Final preparation before STP's main array transformation: recover
// canonical operands, collect and freeze the complete array graph,
// inventory its writes as accesses (section 11.4), and give every
// compound write index/value a scalar name.
//
// Array-valued if-then-elses remain structural and are inventoried here;
// the consistency checker's T-up/T-down rules reason about the selected
// branch directly.
ASTNode ExtensionalityContext::prepare(const ASTNode& root_)
{
  if (!active())
    FatalError("array-equality: preparation ran without an active equality");
  if (arrayGraphIsFrozen || graphBound)
    FatalError("array-equality: the complete array graph was prepared twice");
  ASTNode root = root_;
  ASTVec extraConstraints;

  std::set<ASTNode> arrays;
  std::map<ASTNode, std::vector<ASTNode>> parents;

  locateCanonicalOperands(root);
  computeArrayGraph(root, arrays, parents);

  for (size_t i = 0; i < activeRecordIds.size(); ++i)
  {
    const Record& r = records[activeRecordIds[i]];
    if (arrays.find(r.canonicalLeft) == arrays.end() ||
        arrays.find(r.canonicalRight) == arrays.end())
      FatalError("array-equality: a canonical equality operand is absent "
                 "from the complete prepared array graph",
                 r.proxy);
  }

  // anticipatedArraySymbols is the ownership inventory before preprocessing;
  // this graph contains the arrays that remain afterwards. Because
  // conjoinRecordConstraints walked the complete formula, the first set must
  // cover every symbol in the second unless a pass introduced new array
  // structure after the boundary. The checker graph is frozen here, so make
  // that maintenance invariant explicit rather than silently accepting the
  // new symbol.
  for (std::set<ASTNode>::const_iterator it = arrays.begin();
       it != arrays.end(); ++it)
  {
    if (it->GetKind() == SYMBOL && !wasArrayAnticipated(*it))
      FatalError("array-equality: an array symbol entered the prepared graph "
                 "without appearing at the pre-preprocessing ownership "
                 "boundary",
                 *it);
  }

  // Freeze the complete graph; it must not change for the rest of the solve.
  ownedArrays = arrays;
  ownedWriteParents = parents;

  // Inventory the owned graph's writes as accesses (a write is treated as a
  // read of its own index yielding the written value, paper section
  // 11.4), and give their indexes and values scalar names: writes occur
  // inside array terms, so their scalar children can otherwise disappear
  // when every read of the array is directly abstracted.
  std::vector<ASTNode> writeNodes;
  for (std::set<ASTNode>::const_iterator it = arrays.begin();
       it != arrays.end(); ++it)
    if (it->GetKind() == WRITE)
      writeNodes.push_back(*it);
  std::sort(writeNodes.begin(), writeNodes.end(), nodeNumLess);

  for (size_t i = 0; i < writeNodes.size(); i++)
  {
    const ASTNode& w = writeNodes[i];
    ExtWriteNode info;
    info.write = w;
    info.base = w[0];
    info.indexTerm = w[1];
    info.indexName = freshName(w[1], extraConstraints);
    ownedWrites[w] = info;
    // write value names are needed when the access list is built
    freshName(w[2], extraConstraints);
  }

  // Inventory the owned graph's array-valued if-then-elses. Unlike section
  // 4.1's elimination, these stay as terms: the checker reasons about
  // them directly with rules T-down/T-up, which fire on whichever
  // branch sigma selects. That costs one Boolean literal per
  // if-then-else instead of two array equalities, two witness indices
  // and four virtual reads -- and, because exactly one branch is live
  // per candidate, it leaves no unconstrained proxy for the solver to
  // guess and the checker to refute.
  //
  // The condition is reified as a Boolean symbol here. The checker must
  // branch on the value the bit-blasted circuit took; re-deriving it
  // from the counterexample is the failure class that let a scalar name
  // disagree with its term, and here it would make the wrong branch
  // live and certify a model that does not satisfy the if-then-else
  // axiom. The same symbol is what a lemma premise names.
  std::vector<ASTNode> iteNodes;
  for (std::set<ASTNode>::const_iterator it = arrays.begin();
       it != arrays.end(); ++it)
    if (it->GetKind() == ITE && isArrayType(*it))
      iteNodes.push_back(*it);
  std::sort(iteNodes.begin(), iteNodes.end(), nodeNumLess);

  for (size_t i = 0; i < iteNodes.size(); i++)
  {
    const ASTNode& t = iteNodes[i];
    ExtIteNode info;
    info.ite = t;
    info.condTerm = t[0];
    info.condName = conditionName(t[0], extraConstraints);
    info.thn = t[1];
    info.els = t[2];
    ownedItes[t] = info;
    ownedIteParents[t[1]].push_back(t);
    if (t[2] != t[1])
      ownedIteParents[t[2]].push_back(t);
  }
  for (std::map<ASTNode, std::vector<ASTNode>>::iterator it =
           ownedIteParents.begin();
       it != ownedIteParents.end(); ++it)
    std::sort(it->second.begin(), it->second.end(), nodeNumLess);

  // Equality edges over canonical operands + witness obligations.
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    ExtEqEdge e;
    e.record = r.id;
    e.left = r.canonicalLeft;
    e.right = r.canonicalRight;
    e.proxy = r.proxy;
    eqEdges.push_back(e);

    ExtWitness w;
    w.record = r.id;
    w.proxy = r.proxy;
    w.index = r.lambda;
    w.leftValue = r.nameL;
    w.rightValue = r.nameR;
    witnessObls.push_back(w);
  }

  // adjacency, sorted by (record, other endpoint) per source
  {
    std::map<ASTNode, std::vector<std::pair<std::pair<size_t, uint64_t>,
                                            size_t>>> adj;
    for (size_t i = 0; i < eqEdges.size(); i++)
    {
      const ExtEqEdge& e = eqEdges[i];
      adj[e.left].push_back(std::make_pair(
          std::make_pair(e.record, e.right.GetNodeNum()), i));
      if (!(e.left == e.right))
        adj[e.right].push_back(std::make_pair(
            std::make_pair(e.record, e.left.GetNodeNum()), i));
    }
    for (std::map<ASTNode,
                  std::vector<std::pair<std::pair<size_t, uint64_t>,
                                        size_t>>>::iterator it = adj.begin();
         it != adj.end(); ++it)
    {
      std::sort(it->second.begin(), it->second.end());
      std::vector<size_t>& out = eqAdjacency[it->first];
      for (size_t i = 0; i < it->second.size(); i++)
        out.push_back(it->second[i].second);
    }
  }

  const ASTNode prepared =
      extraConstraints.empty()
          ? root
          : bm->defaultNodeFactory->CreateNode(AND, root, extraConstraints);

  // This is the last word-level root before the array transform.  Inventory
  // that exact DAG, including the naming equations just added above.  Graph
  // discovery alone is not a sufficient hand-off invariant: a later
  // transformer shortcut could otherwise omit a checker-owned read while
  // leaving all of its array nodes present.
  ASTNodeSet finalDag;
  collectDag(prepared, finalDag);
  for (ASTNodeSet::const_iterator it = finalDag.begin(); it != finalDag.end();
       ++it)
  {
    if (it->GetKind() == ARRAY_EQ)
      FatalError("array-equality: an opaque equality reached the final "
                 "prepared root",
                 *it);
    if (it->GetKind() != READ)
      continue;
    if (ownedArrays.find((*it)[0]) == ownedArrays.end())
      FatalError("array-equality: a read in the final prepared root is "
                 "outside the complete owned array graph",
                 *it);
    preparedReads.insert(*it);
  }

  preparedTransformRoot = prepared;
  arrayGraphIsFrozen = true;
  return prepared;
}

void ExtensionalityContext::beginReadTransform(const ASTNode& root)
{
  if (!arrayGraphIsFrozen || preparedTransformRoot.IsNull())
    FatalError("array-equality: read transformation began before final "
               "preparation");
  if (readTransformInProgress || readTransformComplete)
    FatalError("array-equality: the prepared read inventory was transformed "
               "twice");
  if (root != preparedTransformRoot)
    FatalError("array-equality: the array transformer did not receive the "
               "exact final prepared root",
               root);
  readTransformInProgress = true;
}

void ExtensionalityContext::noteAbstractedRead(
    const ASTNode& originalRead, const ASTNode& transformedIndex,
    const ASTNode& valueSymbol)
{
  if (!readTransformInProgress)
    FatalError("array-equality: a read abstraction was reported outside the "
               "prepared transform");
  if (originalRead.GetKind() != READ ||
      preparedReads.find(originalRead) == preparedReads.end())
    FatalError("array-equality: the transformer abstracted a read absent "
               "from the final prepared root",
               originalRead);
  if (!ownsArray(originalRead[0]))
    FatalError("array-equality: the transformer abstracted a read outside "
               "the complete owned array graph",
               originalRead);
  if (transformedIndex.GetValueWidth() != originalRead[1].GetValueWidth() ||
      valueSymbol.GetValueWidth() != originalRead.GetValueWidth())
    FatalError("array-equality: a read abstraction has incompatible scalar "
               "widths",
               originalRead);

  ReadBinding binding;
  binding.array = originalRead[0];
  binding.index = transformedIndex;
  binding.symbol = valueSymbol;
  const std::map<ASTNode, ReadBinding>::const_iterator old =
      transformedReads.find(originalRead);
  if (old != transformedReads.end())
  {
    if (old->second.array != binding.array ||
        old->second.index != binding.index ||
        old->second.symbol != binding.symbol)
      FatalError("array-equality: one prepared read acquired two different "
                 "transformer bindings",
                 originalRead);
    return;
  }
  transformedReads[originalRead] = binding;
}

void ExtensionalityContext::noteEliminatedReadSubtree(
    const ASTNode& deadTerm)
{
  if (!readTransformInProgress)
    FatalError("array-equality: a dead read subtree was reported outside the "
               "prepared transform");
  ASTNodeSet deadDag;
  collectDag(deadTerm, deadDag);
  for (ASTNodeSet::const_iterator it = deadDag.begin(); it != deadDag.end();
       ++it)
  {
    if (it->GetKind() != READ)
      continue;
    if (preparedReads.find(*it) == preparedReads.end())
      FatalError("array-equality: constant term-ITE elimination reported a "
                 "read absent from the final prepared root",
                 *it);
    eliminatedReads.insert(*it);
  }
}

void ExtensionalityContext::finishReadTransform()
{
  if (!readTransformInProgress)
    FatalError("array-equality: the prepared read transform was not in "
               "progress");
  for (std::set<ASTNode>::const_iterator it = preparedReads.begin();
       it != preparedReads.end(); ++it)
    if (transformedReads.find(*it) == transformedReads.end() &&
        eliminatedReads.find(*it) == eliminatedReads.end())
      FatalError("array-equality: a read in the final prepared root was "
                 "neither abstracted nor eliminated by constant term-ITE "
                 "selection",
                 *it);
  readTransformInProgress = false;
  readTransformComplete = true;
}

// After the main ArrayTransformer pass: the complete read inventory
// (ordinary reads plus witness reads) now carries its abstraction and index
// symbols; bind everything into the immutable checker graph.
void ExtensionalityContext::bindAfterTransform(ArrayTransformer* at)
{
  if (!arrayGraphIsFrozen)
    FatalError("array-equality: binding began before the complete array "
               "graph was frozen");
  if (graphBound)
    FatalError("array-equality: the complete array graph was bound twice");
  if (!readTransformComplete || readTransformInProgress)
    FatalError("array-equality: binding began before the exact prepared read "
               "inventory was accounted for");

  graph = ExtGraph();

  std::set<ReadBinding> reportedBindings;
  for (std::map<ASTNode, ReadBinding>::const_iterator it =
           transformedReads.begin();
       it != transformedReads.end(); ++it)
    reportedBindings.insert(it->second);

  std::set<ReadBinding> tableBindings;

  // reads, deterministically ordered by (array, index) node numbers
  struct ReadRow
  {
    ASTNode array;
    ASTNode index;
    ASTNode symbol;
    ASTNode indexSymbol;
    bool operator<(const ReadRow& o) const
    {
      if (array.GetNodeNum() != o.array.GetNodeNum())
        return array.GetNodeNum() < o.array.GetNodeNum();
      return index.GetNodeNum() < o.index.GetNodeNum();
    }
  };
  std::vector<ReadRow> reads;
  // The transformer must have put every read into the complete graph.
  // There is deliberately no complementary host-refinement partition:
  // sharing scalar indexes across such a partition was the source of
  // candidates that neither subsystem could prove or refute.
  for (ArrayTransformer::ArrType::const_iterator it =
           at->arrayToIndexToRead.begin();
       it != at->arrayToIndexToRead.end(); ++it)
  {
    if (!ownsArray(it->first))
      FatalError("array-equality: the transformer registered a read outside "
                 "the complete owned array graph",
                 it->first);
    for (std::map<ASTNode, ArrayTransformer::ArrayRead>::const_iterator it2 =
             it->second.begin();
         it2 != it->second.end(); ++it2)
    {
      ReadRow row;
      row.array = it->first;
      row.index = it2->first;
      row.symbol = it2->second.symbol;
      row.indexSymbol = it2->second.index_symbol;
      reads.push_back(row);

      ReadBinding binding;
      binding.array = row.array;
      binding.index = row.index;
      binding.symbol = row.symbol;
      tableBindings.insert(binding);
    }
  }
  if (reportedBindings != tableBindings)
    FatalError("array-equality: the transformer's read table does not exactly "
               "match the bindings reported for the final prepared root");
  std::sort(reads.begin(), reads.end());

  for (size_t i = 0; i < reads.size(); i++)
  {
    const ReadRow& row = reads[i];
    ExtAccess a;
    a.id = graph.accesses.size();
    a.isWrite = false;
    a.site = row.array;
    a.indexTerm = row.index;
    NodeFactory* hf = bm->hashingNodeFactory;
    a.valueTerm = hf->CreateTerm(READ, row.array.GetValueWidth(), row.array,
                                 row.index);
    a.indexName = row.indexSymbol.IsNull() ? row.index : row.indexSymbol;
    a.valueName = row.symbol;
    if (!(a.indexName.GetKind() == SYMBOL || a.indexName.isConstant()))
      FatalError("array-equality: an owned read index has no "
                 "bit-blasted scalar name to encode lemmas over",
                 row.index);
    // An owned read's semantics live entirely in refinement lemmas, so
    // its abstraction variable and index may legally never reach the
    // bit-blasted formula (the read's only occurrence can sit inside
    // another abstracted term); the translator allocates fresh SAT
    // variables for whichever of these it never saw.
    lemmaOnlySymbols.insert(a.valueName);
    if (a.indexName.GetKind() == SYMBOL)
      lemmaOnlySymbols.insert(a.indexName);
    graph.accesses.push_back(a);
  }

  // writes, deterministically ordered by node number
  std::vector<ASTNode> writeNodes;
  for (std::map<ASTNode, ExtWriteNode>::const_iterator it = ownedWrites.begin();
       it != ownedWrites.end(); ++it)
    writeNodes.push_back(it->first);
  std::sort(writeNodes.begin(), writeNodes.end(), nodeNumLess);
  for (size_t i = 0; i < writeNodes.size(); i++)
  {
    const ExtWriteNode& info = ownedWrites[writeNodes[i]];
    ExtAccess a;
    a.id = graph.accesses.size();
    a.isWrite = true;
    a.site = info.write;
    a.indexTerm = info.indexTerm;
    a.valueTerm = info.write[2];
    a.indexName = info.indexName;
    std::map<ASTNode, ASTNode>::const_iterator nit =
        scalarNames.find(info.write[2]);
    a.valueName = info.write[2].isConstant()
                      ? info.write[2]
                      : (nit != scalarNames.end() ? nit->second : ASTNode());
    if (a.valueName.IsNull())
      FatalError("array-equality: an owned write value has no "
                 "bit-blasted scalar name to encode lemmas over",
                 info.write);
    graph.accesses.push_back(a);
  }

  // The property that lets namesAgreeWithCandidate skip the witness
  // names: every witness read reached the inventory. It holds by
  // construction -- the anchor is protected from substitution, and
  // locateCanonicalOperands fails loudly if one is lost, so the read is
  // in the transformed formula; the transformer registers it; and the
  // operand it reads is in the owned graph, so bindAfterTransform harvests
  // it.
  // Defend it at runtime so release builds cannot silently certify an
  // incomplete graph.
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    bool haveL = false, haveR = false;
    for (size_t z = 0; z < graph.accesses.size(); z++)
    {
      const ExtAccess& acc = graph.accesses[z];
      if (acc.isWrite || !(acc.indexTerm == r.lambda))
        continue;
      haveL = haveL || acc.site == r.canonicalLeft;
      haveR = haveR || acc.site == r.canonicalRight;
    }
    if (!haveL || !haveR)
      FatalError("array-equality: a witness read is absent from the complete "
                 "owned access graph",
                 r.proxy);
  }

  graph.writes = ownedWrites;
  graph.writeParents = ownedWriteParents;
  graph.ites = ownedItes;
  graph.iteParents = ownedIteParents;
  graph.eqEdges = eqEdges;
  graph.eqAdjacency = eqAdjacency;
  graph.witnesses = witnessObls;
  graphBound = true;
}

namespace
{
// The candidate assignment sigma, read out of STP's materialized
// counterexample.
class CEModelView : public ExtModelView
{
  AbsRefine_CounterExample* ce;
  STPMgr* bm;

public:
  CEModelView(AbsRefine_CounterExample* ce_, STPMgr* bm_)
      : ce(ce_), bm(bm_)
  {
  }

  virtual ASTNode bvValue(const ASTNode& term)
  {
    if (term.GetKind() == BVCONST)
      return plainBitVectorConstant(bm, term);
    if (term.GetKind() != SYMBOL)
      FatalError("array-equality: the checker requested a bit-vector term "
                 "instead of its scalar SAT name",
                 term);
    ASTNode v = ce->LookupAssignedValue(term);
    if (v.IsNull() || v.GetKind() != BVCONST ||
        v.GetValueWidth() != term.GetValueWidth())
      FatalError("array-equality: the materialized SAT assignment has no "
                 "concrete value for a scalar name the consistency checker "
                 "depends on",
                 term);
    // Substitution entries can hand a float-element symbol back as a
    // float constant; the checker compares constants by node identity,
    // so give it the plain twin.
    return plainBitVectorConstant(bm, v);
  }

  virtual bool boolValue(const ASTNode& term)
  {
    if (term.GetKind() == TRUE || term.GetKind() == FALSE)
      return term.GetKind() == TRUE;
    if (term.GetKind() != SYMBOL)
      FatalError("array-equality: the checker requested a Boolean term "
                 "instead of its scalar SAT name",
                 term);
    ASTNode v = ce->LookupAssignedValue(term);
    if (v.IsNull() || !(v.GetKind() == TRUE || v.GetKind() == FALSE))
      FatalError("array-equality: the materialized SAT assignment has no "
                 "Boolean value for a scalar name the consistency checker "
                 "depends on",
                 term);
    return v.GetKind() == TRUE;
  }
};
} // namespace

ExtensionalityContext::CertificationAction
ExtensionalityContext::decideCertification(bool ordinaryResult,
                                           bool checkerActive,
                                           CandidateOutcome ext)
{
  if (!checkerActive)
  {
    if (!(ext == EXT_SKIPPED || ext == EXT_CONSISTENT))
      return INTERNAL_ERROR;
    return ordinaryResult ? RETURN_SAT : RUN_HOST_REFINEMENT;
  }
  if (ext == EXT_CONFLICT)
    return ADD_EXT_LEMMA;
  if (ext == EXT_WITNESS_ERROR)
    return INTERNAL_ERROR;
  if (ext != EXT_CONSISTENT)
    return INTERNAL_ERROR;
  // With the complete array graph owned here, a conflict-free fixed
  // point must make the semantic input true on the same scalar
  // assignment. There is no second array-refinement subsystem to hand
  // a disagreement to.
  return ordinaryResult ? RETURN_SAT : INTERNAL_ERROR;
}

ExtensionalityContext::CandidateOutcome
ExtensionalityContext::checkCandidate(AbsRefine_CounterExample* ce)
{
  if (!graphBound)
    FatalError("array-equality: candidate checking began before the complete "
               "array graph was bound");
  if (pendingLemmaValid || !pendingLemmas.empty())
    FatalError("array-equality: a new candidate was checked before the prior "
               "conflict certificates were encoded");
  lastObserved.clear();
  CEModelView view(ce, bm);
  ExtCheckResult res = ExtChecker::check(graph, view, false);
  switch (res.status)
  {
    case ExtCheckResult::CONSISTENT:
      lastObserved = res.observed;
      // Publishing first makes the certified array contents visible
      // to term evaluation; only then can an owned read's term be
      // compared against its name.
      publishObservations(ce);
      if (!namesAgreeWithCandidate(view, ce))
        FatalError("array-equality: a scalar name disagrees with its term "
                   "after the complete array graph reached a conflict-free "
                   "fixed point");
      return EXT_CONSISTENT;
    case ExtCheckResult::CONFLICT:
      if (res.conflicts.empty())
        FatalError("array-equality: the checker reported a conflict without "
                   "a refinement certificate");
      pendingLemmas.swap(res.conflicts);
      pendingLemmaValid = true;
      return EXT_CONFLICT;
    case ExtCheckResult::WITNESS_VIOLATION:
    default:
      return EXT_WITNESS_ERROR;
  }
}

// The checker reads the candidate through scalar names whose defining
// equations were part of the initial bit-blast. Verify, with certified
// observations published, that every name still evaluates exactly like
// its term. Since every read abstraction is in this graph, a mismatch
// is an ownership/encoding invariant violation rather than a third
// refinement outcome; equal concrete indexes with different values
// must already have produced a rule-C conflict.
bool ExtensionalityContext::namesAgreeWithCandidate(
    ExtModelView& view, AbsRefine_CounterExample* ce) const
{
  for (size_t i = 0; i < graph.accesses.size(); i++)
  {
    const ExtAccess& a = graph.accesses[i];
    if (!(a.indexName == a.indexTerm))
    {
      const ASTNode termValue = ce->ModelValueOfTerm(a.indexTerm);
      if (termValue.IsNull() || termValue.GetKind() != BVCONST ||
          termValue.GetValueWidth() != a.indexTerm.GetValueWidth())
        FatalError("array-equality: an access index has no concrete value in "
                   "the certified model",
                   a.indexTerm);
      if (view.bvValue(a.indexName) != termValue)
        return false;
    }
    if (!(a.valueName == a.valueTerm))
    {
      const ASTNode termValue = ce->ModelValueOfTerm(a.valueTerm);
      if (termValue.IsNull() || termValue.GetKind() != BVCONST ||
          termValue.GetValueWidth() != a.valueTerm.GetValueWidth())
        FatalError("array-equality: an access value has no concrete value in "
                   "the certified model",
                   a.valueTerm);
      if (view.bvValue(a.valueName) != termValue)
        return false;
    }
  }

  // Each reified if-then-else condition against the condition it names.
  // The checker branches on these to decide which branch is live, so a
  // name that disagrees with its term selects the wrong one and can
  // certify a model that does not satisfy the if-then-else axiom. This
  // is the same guard the access names get, for the same reason, and it
  // is the failure class the direct integration reopened.
  for (std::map<ASTNode, ExtIteNode>::const_iterator it = ownedItes.begin();
       it != ownedItes.end(); ++it)
  {
    const ASTNode termValue = ce->ModelValueOfFormula(it->second.condTerm);
    if (termValue.IsNull() ||
        !(termValue.GetKind() == TRUE || termValue.GetKind() == FALSE))
      FatalError("array-equality: an array-if-then-else condition has no "
                 "concrete value in the certified model",
                 it->second.condTerm);
    if (view.boolValue(it->second.condName) != (termValue.GetKind() == TRUE))
      return false;
  }

  // The witness names -- the records' nameL and nameR, which the
  // checker's witness loop reads directly -- need no comparison of
  // their own. Each is anchored by nameL = read(left, lambda) in the
  // bit-blasted formula, so the candidate gives it the value of that
  // read's abstraction variable; that read is always in the inventory
  // (bindAfterTransform asserts it), so the loop above has already
  // checked its variable against its term. Transitivity does the rest.
  return true;
}

// Encode the pending lemma into the persistent incremental SAT solver
// as the clause
//   NOT p1 OR ... OR NOT pk OR conclusion
// over reified equality literals of already-encoded scalar symbols.
// This is the abstraction alpha of the theory lemma (paper section 8);
// adding it as clauses over the existing CNF is what makes each
// refinement iteration incremental -- no new word-level formula is
// ever handed back to the bit-blaster.
// A lemma leaf is legal only as a constant or as a SYMBOL with a
// stable, completely encoded SAT-variable vector. Anything else is an
// internal error, never a reason to allocate fresh SAT variables in
// the middle of refinement: a freshly invented variable would carry no
// connection to the term the candidate assignment was checked against,
// so the resulting clause could fail to rule the candidate out.
const char*
ExtensionalityContext::checkPreencodedBV(const ASTNode& n,
                                         const ToSATBase::ASTNodeToSATVar& satVar)
{
  if (n.isConstant())
    return NULL;
  if (n.GetKind() != SYMBOL)
    return "array-equality: lemma leaf is neither a constant nor a "
           "variable";
  ToSATBase::ASTNodeToSATVar::const_iterator it = satVar.find(n);
  if (it == satVar.end())
    return "array-equality: lemma leaf was never bit-blasted (it has no "
           "SAT-variable vector)";
  if (it->second.size() != n.GetValueWidth())
    return "array-equality: lemma leaf's SAT-variable vector has the "
           "wrong width";
  for (size_t i = 0; i < it->second.size(); i++)
    if (it->second[i] == ~((unsigned)0))
      return "array-equality: lemma leaf has an unencoded SAT-variable "
             "bit";
  return NULL;
}

void ExtensionalityContext::encodePendingLemmas(SATSolver& solver,
                                                ToSATBase* tosat,
                                                int guardLit)
{
  if (!pendingLemmaValid || pendingLemmas.empty())
    FatalError("array-equality: lemma encoding began without a pending "
               "certificate");
  lemmaRounds++;
  if ((int)pendingLemmas.size() > lemmasInLargestRound)
    lemmasInLargestRound = (int)pendingLemmas.size();
  for (size_t i = 0; i < pendingLemmas.size(); i++)
    encodeOneLemma(pendingLemmas[i], solver, tosat, guardLit);
  pendingLemmas.clear();
  pendingLemmaValid = false;
}

// See the header. Every figure is cumulative over the context lifetime -- a
// running total and a lifetime maximum -- and only the printing is per
// solve, so that a multi-query file shows how the accounting grew rather
// than only where it ended up.
void ExtensionalityContext::reportLemmaStats() const
{
  if (!bm->UserFlags.stats_flag || lemmaRounds == 0)
    return;
  std::cerr << "Array equality: " << lemmasEmitted << " lemmas, "
            << lemmaRounds << " rounds, largest " << lemmasInLargestRound
            << ", " << lemmaAtomsFolded << " atoms folded (cumulative)."
            << std::endl;
}

// See the header. A premise is dropped when it is valid, the
// conclusion when it is unsatisfiable; a lemma conclusion is always an
// equality, so BV_NE there is not a position the encoder produces.
ExtensionalityContext::FoldVerdict
ExtensionalityContext::requiredFoldVerdict(ExtLemmaAtom::Op op,
                                           LemmaPosition where)
{
  if (where == LEMMA_PREMISE)
  {
    if (op == ExtLemmaAtom::BV_EQ)
      return FOLD_VALID;
    if (op == ExtLemmaAtom::BV_NE)
      return FOLD_UNSAT;
    return FOLD_UNDECIDED;
  }
  return op == ExtLemmaAtom::BV_EQ ? FOLD_UNSAT : FOLD_UNDECIDED;
}

void ExtensionalityContext::encodeOneLemma(const ExtConflict& pendingLemma,
                                           SATSolver& solver,
                                           ToSATBase* tosat, int guardLit)
{
  ToSATBase::ASTNodeToSATVar& satVar = tosat->SATVar_to_SymbolIndexMap();

  // Validate every bit-vector leaf of the lemma before any SAT
  // mutation, so a violation is a localized internal error and
  // getEquals below can never fall into its fresh-variable fallback.
  {
    std::vector<ASTNode> leaves;
    for (size_t i = 0; i < pendingLemma.abstractPremise.size(); i++)
    {
      const ExtLemmaAtom& atom = pendingLemma.abstractPremise[i];
      if (atom.op == ExtLemmaAtom::BV_EQ || atom.op == ExtLemmaAtom::BV_NE)
      {
        leaves.push_back(atom.a);
        leaves.push_back(atom.b);
      }
    }
    leaves.push_back(pendingLemma.abstractConclusionA);
    leaves.push_back(pendingLemma.abstractConclusionB);
    for (size_t i = 0; i < leaves.size(); i++)
    {
      const char* reason = checkPreencodedBV(leaves[i], satVar);
      if (reason != NULL)
        FatalError(reason, leaves[i]);
    }
  }

  SATSolver::vec_literals clause;

  // Returns the reified equality variable q with q <-> (a = b) -- full
  // equivalence in both directions -- or, when the atom needs no circuit
  // because it is structurally decided, one of the two sentinels below.
  //
  // Which sentinel it is matters. Dropping a literal from the clause is
  // only equivalence-preserving on one side per position: a premise may
  // be dropped when it is valid, the conclusion when it is
  // unsatisfiable. Dropping on the other side yields a strictly
  // stronger clause -- a silent wrong unsat. So the fold reports its
  // direction and each consumer checks it against the position it is
  // filling; a mismatch is an internal error, not something to encode.
  struct EqLit
  {
    ExtensionalityContext* self;
    SATSolver& solver;
    ToSATBase::ASTNodeToSATVar& satVar;
    EqLit(ExtensionalityContext* s, SATSolver& sol,
          ToSATBase::ASTNodeToSATVar& sv)
        : self(s), solver(sol), satVar(sv)
    {
    }
    int operator()(const ASTNode& a, const ASTNode& b)
    {
      // Two constants: equal iff the same *bits*. That used to be the same
      // question as being the same node, and is not any more -- a
      // floating-point or rounding-mode constant carries its source sort as
      // part of its identity, so it interns apart from the plain bit-vector
      // constant holding its bits.
      //
      // The two sides here are names from accesses on arrays being equated,
      // so their sorts agree and both constants are the same flavour; the
      // pair that could differ cannot reach this. It is asked on bits
      // anyway, because the answer feeds FOLD_UNSAT and so decides whether
      // a conclusion is dropped, and getting that wrong is the
      // strictly-stronger clause the comment above warns about -- too sharp
      // an edge to leave resting on an invariant that holds for a reason
      // outside this function.
      if (a.isConstant() && b.isConstant())
        return constantsSameBits(a, b) ? FOLD_VALID : FOLD_UNSAT;
      const uint64_t na = a.GetNodeNum(), nb = b.GetNodeNum();
      const std::pair<uint64_t, uint64_t> key(std::min(na, nb),
                                              std::max(na, nb));
      std::map<std::pair<uint64_t, uint64_t>, int>::const_iterator it =
          self->eqLitCache.find(key);
      if (it != self->eqLitCache.end())
        return it->second;

      // An atom the simplifier can decide from the defining terms needs
      // no circuit: each name equals its term through the anchoring
      // equations, so the factory's verdict on the terms is a verdict on
      // the names. Write indices that are offsets from a shared pointer
      // are the common win: the simplifying factory cancels the shared
      // operand and decides the equality, sparing the SAT solver a
      // 32-bit arithmetic case split per lemma.
      //
      // This transfers to the SAT abstraction only because the factory's
      // EQ path treats every READ subterm as an opaque leaf --
      // CreateSimpleEQ has no array rule and constructs no READ, so
      // chaseRead cannot fire on it. The defining equations are
      // conjoined before the array transform, so what SAT holds is
      // "name = T(term)" with T abstracting reads into lazily
      // axiomatized variables; a factory verdict that used an array
      // axiom would not survive T. Anyone adding an array rule to the
      // EQ dispatch has to revisit this.
      {
        const std::map<ASTNode, ASTNode>& n2t = self->nameToTermMap;
        std::map<ASTNode, ASTNode>::const_iterator ta = n2t.find(a);
        std::map<ASTNode, ASTNode>::const_iterator tb = n2t.find(b);
        const ASTNode& termA = (ta == n2t.end()) ? a : ta->second;
        const ASTNode& termB = (tb == n2t.end()) ? b : tb->second;
        const ASTNode folded =
            self->bm->defaultNodeFactory->CreateNode(EQ, termA, termB);
        if (folded.GetKind() == TRUE || folded.GetKind() == FALSE)
        {
          const int verdict =
              folded.GetKind() == TRUE ? FOLD_VALID : FOLD_UNSAT;
          self->lemmaAtomsFolded++;
          self->eqLitCache[key] = verdict;
          return verdict;
        }
      }

      const int q = getEquals(solver, a, b, satVar, Polarity::BOTH);
      // Unlike the host's read axioms, which build their reified
      // variables fresh for each clause, these are cached and reused by
      // later refinement rounds -- with the solver's own simplification
      // running in between. A backend that eliminates variables would
      // be handed a dead one, so keep them.
      solver.setFrozen(q);
      self->eqLitCache[key] = q;
      return q;
    }
  } eqLit(this, solver, satVar);

  for (size_t i = 0; i < pendingLemma.abstractPremise.size(); i++)
  {
    const ExtLemmaAtom& atom = pendingLemma.abstractPremise[i];
    if (atom.op == ExtLemmaAtom::BV_EQ || atom.op == ExtLemmaAtom::BV_NE)
    {
      const int q = eqLit(atom.a, atom.b);
      if (q < 0)
      {
        // The premise is dropped only on the side that keeps the clause
        // equivalent. The other direction makes the premise
        // unsatisfiable, so the lemma is vacuous and the shortened
        // clause asserts something the theory does not entail.
        // validateAbstractLemma has already established that the atom
        // holds in the candidate, so reaching here means the structural
        // verdict disagrees with the candidate.
        if (q != requiredFoldVerdict(atom.op, LEMMA_PREMISE))
          FatalError("array-equality: a lemma premise was structurally "
                     "decided against the polarity the conflict needs, so "
                     "dropping its literal would strengthen the clause",
                     atom.a);
        continue;
      }
      // premise literal appears negated in the final clause
      clause.push(SATSolver::mkLit(q, atom.op == ExtLemmaAtom::BV_EQ));
    }
    else
    {
      assert(atom.op == ExtLemmaAtom::BOOL_LIT ||
             atom.op == ExtLemmaAtom::BOOL_LIT_NEG);
      ToSATBase::ASTNodeToSATVar::const_iterator vit =
          satVar.find(atom.boolTerm);
      if (vit == satVar.end() || vit->second.size() != 1 ||
          vit->second[0] == ~((unsigned)0))
        FatalError("array-equality: an equality abstraction variable "
                   "was never bit-blasted, so the lemma cannot be "
                   "encoded",
                   atom.boolTerm);
      // A premise literal appears negated in the clause, so a
      // negatively-taken condition appears positively.
      clause.push(SATSolver::mkLit(vit->second[0],
                                   atom.op == ExtLemmaAtom::BOOL_LIT));
    }
  }

  {
    const int q =
        eqLit(pendingLemma.abstractConclusionA, pendingLemma.abstractConclusionB);
    if (q >= 0)
      clause.push(SATSolver::mkLit(q, false));
    else if (q != requiredFoldVerdict(ExtLemmaAtom::BV_EQ, LEMMA_CONCLUSION))
      // The conclusion may be dropped only when it is unsatisfiable:
      // the premises then cannot all hold, and the negated premises
      // alone are the theory-valid clause. A structurally valid
      // conclusion makes the whole lemma a tautology, and dropping its
      // literal would leave a clause forbidding the premises for no
      // reason.
      FatalError("array-equality: a lemma conclusion was structurally "
                 "decided true, so dropping its literal would leave an "
                 "unsound clause",
                 pendingLemma.abstractConclusionA);
  }

  if (clause.size() == 0)
    FatalError("array-equality: refinement produced an empty clause "
               "(the candidate should have been unsatisfiable already)");

  // Scope the clause to the formula whose equations give its symbols
  // their meaning (see the header). Added after the emptiness check:
  // a lemma that is empty before its guard still means the candidate
  // should never have existed, and must keep failing loudly rather
  // than quietly asserting the block's negation.
  if (guardLit >= 0)
    clause.push(SATSolver::mkLit(guardLit >> 1, (guardLit & 1) != 0));

  solver.addClause(clause);
  lemmasEmitted++;
}

// Publish the conflict-free observed values of every owned array
// (symbols, writes, and array-if-then-else terms alike) into the
// counterexample map, so model evaluation, the model
// APIs, and the printers see the array contents certified by the
// consistency check. Indices with no observation default to zero at
// lookup/print time.
void ExtensionalityContext::publishObservations(AbsRefine_CounterExample* ce)
{
  ASTNodeMap batch;
  for (std::map<ASTNode,
                std::vector<std::pair<ASTNode, ASTNode>>>::const_iterator it =
           lastObserved.begin();
       it != lastObserved.end(); ++it)
  {
    const ASTNode& array = it->first;
    NodeFactory* hf = bm->hashingNodeFactory;
    for (size_t i = 0; i < it->second.size(); i++)
    {
      const ASTNode key = hf->CreateTerm(READ, array.GetValueWidth(), array,
                                         it->second[i].first);
      ASTNodeMap::const_iterator prior = batch.find(key);
      if (prior != batch.end() && !(prior->second == it->second[i].second))
        FatalError("array-equality: a conflict-free checker result assigns "
                   "two values to one concrete array cell",
                   key);
      batch[key] = it->second[i].second;
    }
  }

  // Validate the entire batch before mutating the public model. Active
  // candidates normally have no READ entries yet; this check also makes
  // that ownership boundary fail closed if a future preprocessing path
  // introduces one.
  for (ASTNodeMap::const_iterator it = batch.begin(); it != batch.end(); ++it)
  {
    const ASTNode prior = ce->LookupAssignedValue(it->first);
    if (!prior.IsNull() && !(prior == it->second))
      FatalError("array-equality: certified array observation conflicts with "
                 "an existing counterexample entry",
                 it->first);
  }
  for (ASTNodeMap::const_iterator it = batch.begin(); it != batch.end(); ++it)
    ce->InsertIntoCounterExampleMap(it->first, it->second);

  // No model evaluation should precede certification, but clearing the
  // cache here makes publication an explicit phase boundary.
  ce->ClearComputeFormulaMap();
}

// See the header. Unobserved cells hold `absent` on both sides, so two
// arrays agree everywhere exactly when they agree at every index either
// one observes.
bool ExtensionalityContext::contentsAgree(
    const std::vector<std::pair<ASTNode, ASTNode>>& left,
    const std::vector<std::pair<ASTNode, ASTNode>>& right,
    const ASTNode& absent, const SourceSort& elementSort)
{
  std::map<ASTNode, ASTNode> leftCells, rightCells;
  for (size_t i = 0; i < left.size(); i++)
    leftCells[left[i].first] = left[i].second;
  for (size_t i = 0; i < right.size(); i++)
    rightCells[right[i].first] = right[i].second;

  // Cells are compared by value at the element's sort, never by node
  // identity. A float-element cell holds a floating-point constant,
  // which interns apart from the plain bit-vector constant with the same
  // bits -- and one side of most of these comparisons is exactly such a
  // plain constant, the zero an unobserved cell completes to. Node
  // identity would report two identical arrays as differing; equal bits
  // would do the same to two NaN payloads, which are one value.
  for (std::map<ASTNode, ASTNode>::const_iterator it = leftCells.begin();
       it != leftCells.end(); ++it)
  {
    const std::map<ASTNode, ASTNode>::const_iterator other =
        rightCells.find(it->first);
    if (constantsDenoteDifferentSourceValues(
            it->second, other == rightCells.end() ? absent : other->second,
            elementSort))
      return false;
  }
  // Only the indexes the first array does not observe are left to check;
  // there it holds `absent`.
  for (std::map<ASTNode, ASTNode>::const_iterator it = rightCells.begin();
       it != rightCells.end(); ++it)
    if (leftCells.find(it->first) == leftCells.end() &&
        constantsDenoteDifferentSourceValues(it->second, absent, elementSort))
      return false;
  return true;
}

// See the header. Runs against the published model, so it must come
// after publishObservations -- the contents it compares are the ones
// the model APIs and the printers will hand back.
const char* ExtensionalityContext::recheckCertifiedEqualities(
    AbsRefine_CounterExample* ce) const
{
  if (!activeRecordIds.empty() && !graphBound)
    return "array-equality: the counterexample check ran before the "
           "complete array graph was bound";

  static const std::vector<std::pair<ASTNode, ASTNode>> unobserved;
  typedef std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>> ObsMap;

  // The certified cells of every active record's canonical operands
  // against its abstraction variable. Empty when the only equalities in
  // the query were ones lowering solved outright, which is why the
  // second loop below is not conditioned on this one having run.
  for (size_t i = 0; i < activeRecordIds.size(); i++)
  {
    const Record& r = records[activeRecordIds[i]];
    // Both loops decide an equality by comparing the cells the model
    // published. Whether that is answerable at all is one question,
    // asked in one place.
    if (!ce->arrayEqualityIsModelDecidable(r.constructionLeft) ||
        !ce->arrayEqualityIsModelDecidable(r.constructionRight))
      continue;
    const ASTNode assigned = ce->LookupAssignedValue(r.proxy);
    if (assigned.IsNull() ||
        !(assigned.GetKind() == TRUE || assigned.GetKind() == FALSE))
      return "array-equality: an equality abstraction variable has no "
             "Boolean value in the model it was certified against";

    // An array the fixed point never reached observes nothing, so it is
    // the constant array the printer would emit for it. Taking the cell
    // value from the model surface rather than spelling it out here is
    // what keeps this comparison asking about the model that gets
    // published.
    // Observations are keyed on the canonical operands, but the
    // completion is asked of the constructed one: it follows the
    // element sort, and the canonical form is what the solve rewrote
    // its way to, which need not still carry the sort the user wrote.
    const ObsMap::const_iterator obsL = lastObserved.find(r.canonicalLeft);
    const ObsMap::const_iterator obsR = lastObserved.find(r.canonicalRight);
    const ASTNode absent = ce->defaultCellValue(r.constructionLeft);
    // The element sort comes from the operands the user wrote: the
    // canonical forms are post-lowering carriers, and what a cell means
    // is a property of the source sort, not of its carrier. That is
    // also why the default above is asked of the construction operand.
    const SourceSort constructionSort = r.constructionLeft.GetSourceSort();
    const SourceSort elementSort =
        constructionSort.kind() == SourceSort::Kind::Array
            ? constructionSort.element()
            : SourceSort::unknown();
    const bool agree =
        contentsAgree(obsL == lastObserved.end() ? unobserved : obsL->second,
                      obsR == lastObserved.end() ? unobserved : obsR->second,
                      absent, elementSort);

    if (agree != (assigned.GetKind() == TRUE))
      return agree ? "array-equality: the model makes an array equality's "
                     "operands identical at every certified cell, but its "
                     "abstraction variable was assigned false -- the "
                     "witness of preprocessing step 1 did not hold"
                   : "array-equality: an array equality's abstraction "
                     "variable was assigned true, but the model gives its "
                     "operands different contents -- read propagation "
                     "across the equality was incomplete";
  }

  // The same question asked of every equality this solve lowered, and
  // asked about the operands the user wrote rather than the canonical
  // forms the checker reasoned over.
  //
  // This is the part re-evaluating the query cannot reach. That walk
  // resolves an opaque equality through exactly this map, so it agrees
  // with the lowering by construction and a lowering that says
  // something other than what its operands do in the finished model is
  // invisible to it. Two lowerings mint no record at all and so are
  // covered by nothing else: the reflexive fold, and the rewritten form
  // of a write chain equated with its own base -- the one place the
  // decision procedure is bypassed entirely, where a wrong rewrite is a
  // wrong answer with no checker behind it.
  for (ASTNodeMap::const_iterator it = currentLowerings.begin();
       it != currentLowerings.end(); ++it)
  {
    // Same restriction, same reason; see the loop above.
    if (!ce->arrayEqualityIsModelDecidable(it->first[0]) ||
        !ce->arrayEqualityIsModelDecidable(it->first[1]))
      continue;
    const ASTNode verdict = ce->QueryFormulaAgainstModel(it->second);
    if (!(verdict.GetKind() == TRUE || verdict.GetKind() == FALSE))
      return "array-equality: an array equality's lowering has no truth "
             "value in the model that answered the query";
    if (ce->ArraysEqualUsingModel(it->first[0], it->first[1]) !=
        (verdict.GetKind() == TRUE))
      return verdict.GetKind() == TRUE
                 ? "array-equality: an array equality's lowering is true in "
                   "the model, but the model gives the two operands the "
                   "user equated different contents"
                 : "array-equality: an array equality's lowering is false in "
                   "the model, but the model gives the two operands the "
                   "user equated identical contents";
  }
  return NULL;
}

} // namespace stp

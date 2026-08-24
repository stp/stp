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

/* Transform:
 *
 * Removes array selects and stores from the formula. Arrays are
 * replaced by equivalent bit-vector variables
 */
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/Simplifier/Simplifier.h"
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <sstream>
#include <utility>
#include <vector>

namespace stp
{
using std::make_pair;

// Temporarily lend the transformer a caller-owned persistent registry while
// preserving the batch registry already installed in the object. Tracking is
// part of the same transaction, so callers cannot forget to restore one of
// the maps or leave touched-read recording enabled after the run.
class ArrayTransformer::RegistryScope
{
  ArrayTransformer& owner;
  Registry& registry;
  bool savedRecordTouchedReads;
  ReadKeys savedTouchedReads;
  ReadKeys savedTouchedChains;

public:
  RegistryScope(ArrayTransformer& owner, Registry& registry)
      : owner(owner), registry(registry),
        savedRecordTouchedReads(owner.recordTouchedReads)
  {
    assert(owner.TransformMap == NULL);
    assert(!owner.recordTouchedReads);
    owner.arrayToIndexToRead.swap(registry.reads);
    owner.ack_pair.swap(registry.ackPairs);
    owner.chainReads.swap(registry.chains);
    owner.chainAnchorOf.swap(registry.chainAnchors);
    owner.touchedReads.swap(savedTouchedReads);
    owner.touchedChains.swap(savedTouchedChains);
    owner.recordTouchedReads = true;
  }

  ~RegistryScope()
  {
    owner.recordTouchedReads = savedRecordTouchedReads;
    owner.touchedReads.clear();
    owner.touchedReads.swap(savedTouchedReads);
    owner.touchedChains.clear();
    owner.touchedChains.swap(savedTouchedChains);
    owner.arrayToIndexToRead.swap(registry.reads);
    owner.ack_pair.swap(registry.ackPairs);
    owner.chainReads.swap(registry.chains);
    owner.chainAnchorOf.swap(registry.chainAnchors);
  }
};

// Core top-level entry point. It sets up the cache that the recursive pieces
// share; persistent callers reach it through TransformFormulaWithRegistry.
ASTNode ArrayTransformer::TransformFormula_TopLevel(const ASTNode& form)
{
  runTimes->start(RunTimes::Transforming);

  assert(TransformMap == NULL);
  TransformMap = new ASTNodeMap(100);
  cellSortConstraints.clear();

  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  // Constant-bit propagation also creates local ArrayTransformers for
  // scalar-only auxiliary formulas.  Only the transform of the frozen root
  // participates in the extensionality hand-off; an early transform which
  // actually encounters an owned READ still fails in TransformArrayRead.
  const bool extPrepared =
      ext != NULL && ext->activeInSolve() && ext->arrayGraphFrozen();
  if (extPrepared)
    ext->beginReadTransform(form);
  ASTNode result = TransformFormula(form);
  if (extPrepared)
    ext->finishReadTransform();

#if 0
    {
    	ASTNodeSet visited;
    	assertTransformPostConditions(result,visited);
    }
#endif

  TransformMap->clear();
  delete TransformMap;
  TransformMap = NULL;

  if (bm->UserFlags.stats_flag)
    printArrayStats();

  ASTVec sideConstraints;

  // This establishes equalities between every indexes, and a fresh variable.
  if (!bm->UserFlags.ackermannisation)
  {
    ASTNodeMap replaced;

    ASTVec equalsNodes;
    for (ArrayTransformer::ArrType::iterator
             iset = arrayToIndexToRead.begin(),
             iset_end = arrayToIndexToRead.end();
         iset != iset_end; iset++)
    {
      std::map<ASTNode, ArrayTransformer::ArrayRead>& mapper = iset->second;

      // With array equality active, the index of a read in the owned
      // graph must reach the bit-blaster even when it is a
      // plain variable: once the read is replaced by its abstraction
      // variable the index may occur nowhere else, yet future
      // refinement lemmas will be encoded over its SAT variables. Such
      // reads therefore take the fresh-index-variable path (which
      // conjoins index = fresh) for every non-constant index.
      const bool forceIndexAnchor =
          ext != NULL && ext->activeInSolve() && ext->needsIndexAnchor(iset->first);

      for (std::map<ASTNode, ArrayTransformer::ArrayRead>::iterator it =
               mapper.begin();
           it != mapper.end(); it++)
      {
        const ASTNode& the_index = it->first;

        // A row that already carries its anchor was bound when it was
        // created, and its binding equation was conjoined onto whatever
        // formula created it. Re-emitting it here would attach the whole
        // table's anchors to every formula transformed afterwards -- which
        // costs nothing in clauses, since the equations are interned and the
        // AIG is strashed, but puts every row ever seen into every root's
        // live cone. That is invisible in batch, where the table holds only
        // the current query's rows and no row is ever seen already bound; it
        // matters for a caller that keeps a registry across solves, whose
        // relief valve then sees almost everything as live.
        if (!it->second.index_symbol.IsNull())
          continue;

        if (the_index.isConstant() ||
            (the_index.GetKind() == SYMBOL && !forceIndexAnchor))
        {
          it->second.index_symbol = the_index;
        }
        else if (replaced.find(the_index) !=
                 replaced.end()) // Already associated with a variable.
        {
          it->second.index_symbol = replaced.find(the_index)->second;
        }
        else
        {
          ASTNode newV = bm->CreateDeterministicVariable(
              0, the_index.GetValueWidth(), "STP__IndexVariables", the_index);
          equalsNodes.push_back(nf->CreateNode(EQ, the_index, newV));
          replaced.insert(make_pair(the_index, newV));
          it->second.index_symbol = newV;
        }
        assert(it->second.index_symbol.GetValueWidth() ==
               the_index.GetValueWidth());
      }
    }

    // The anchors minted for abstracted write chains bind the same way the
    // index variables above do.
    equalsNodes.insert(equalsNodes.end(), chainAnchorEquations.begin(),
                       chainAnchorEquations.end());
    chainAnchorEquations.clear();

    sideConstraints.insert(sideConstraints.end(), equalsNodes.begin(),
                           equalsNodes.end());
  }

  // The sort constraints the fresh read abstractions owe. Not inside the
  // branch above: eager Ackermannisation abstracts each read to one of
  // these variables too -- it builds the if-then-else over them instead of
  // leaving the refinement loop to relate them -- so the cells are exactly
  // as much in need of pinning either way.
  sideConstraints.insert(sideConstraints.end(), cellSortConstraints.begin(),
                         cellSortConstraints.end());
  cellSortConstraints.clear();

  runTimes->stop(RunTimes::Transforming);

  if (sideConstraints.size() > 0)
    return nf->CreateNode(AND, result, sideConstraints);
  return result;
}

ArrayTransformer::TransformResult
ArrayTransformer::TransformFormulaWithRegistry(const ASTNode& form,
                                               Registry& registry)
{
  RegistryScope scope(*this, registry);
  const ASTNode transformed = TransformFormula_TopLevel(form);
  return TransformResult(transformed, touchedReads, touchedChains);
}

// Choose where a read of this write chain stops being expanded eagerly:
// after the configured number of may-alias levels the rest of the chain is
// abstracted to a refinement row, provided it runs through writes to a
// plain array symbol and still holds at least two may-alias levels (a
// shorter tail is cheaper expanded). May-aliasing is judged on the raw
// index terms; a comparison that only resolves after transformation costs
// eagerness, never soundness. Called once per (top read, index); the
// suffix reads the eager expansion creates skip it (see the WRITE arm).
bool ArrayTransformer::markLazyChainCut(const ASTNode& writeNode,
                                        const ASTNode& readIndex)
{
  if (!bm->UserFlags.lazy_write_reads || bm->UserFlags.ackermannisation)
    return false;
  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  if (ext != NULL && ext->active())
    return false;

  const int64_t budget =
      std::max<int64_t>(0, bm->UserFlags.lazy_write_reads_depth);
  int64_t unresolved = 0;
  ASTNode cut;
  ASTNode n = writeNode;
  while (n.GetKind() == WRITE)
  {
    const ASTNode cond = simp->CreateSimplifiedEQ(n[1], readIndex);
    if (cond == ASTTrue)
      break; // the read resolves here; the levels below are dead
    if (cond != ASTFalse)
    {
      if (unresolved == budget)
        cut = n;
      unresolved++;
    }
    n = n[0];
  }
  if (cut.IsNull() || n.GetKind() != SYMBOL || unresolved < budget + 2)
    return false;
  lazyCutTargets[cut].insert(readIndex);
  qualifiedScansOf[n]++;
  cutDepthOf[cut] = (size_t)(unresolved - budget);
  return true;
}

// The variable that carries a chain term's bits into the SAT encoding, so
// refinement lemmas can be stated over it: the term itself when it already
// is a symbol or a constant, otherwise a deterministic fresh variable
// bound by an equation conjoined at top level.
ASTNode ArrayTransformer::anchorForChainTerm(const ASTNode& term)
{
  if (term.GetKind() == SYMBOL || term.isConstant())
    return term;
  ASTNodeMap::const_iterator it = chainAnchorOf.find(term);
  if (it != chainAnchorOf.end())
    return it->second;
  ASTNode anchor = bm->CreateDeterministicVariable(
      0, term.GetValueWidth(), "STP__ChainAnchor", term);
  anchor.SetExpWidth(term.GetExpWidth());
  anchor.SetSigWidth(term.GetSigWidth());
  chainAnchorOf.insert(std::make_pair(term, anchor));
  chainAnchorEquations.push_back(nf->CreateNode(EQ, term, anchor));
  return anchor;
}

// Check that the transformations have occurred.
void ArrayTransformer::assertTransformPostConditions(const ASTNode& term,
                                                     ASTNodeSet& visited)
{

  // I haven't measure whether this is the quickest way to do it?
  std::pair<ASTNodeSet::iterator, bool> p = visited.insert(term);
  if (!p.second)
    return;

  // Only consumed by the asserts, which an NDEBUG build compiles out.
  [[maybe_unused]] const Kind k = term.GetKind();

  // Check the array reads / writes have been removed
  assert(READ != k);
  assert(WRITE != k);

  // There should be no nodes left of type array.
  assert(0 == term.GetIndexWidth());

  const ASTChildren c = term.GetChildren();
  auto it = c.begin();
  const auto itend = c.end();
  for (; it != itend; it++)
  {
    assertTransformPostConditions(*it, visited);
  }
}

// The tail every arm of TransformTerm shares.
ASTNode ArrayTransformer::finishTransformTerm(const ASTNode& term,
                                              const ASTNode& result)
{
  if (term.Degree() > 0)
    (*TransformMap)[term] = result;
  if (term.GetValueWidth() != result.GetValueWidth())
    FatalError("TransformTerm: "
               "result and input terms are of different length",
               result);
  if (term.GetIndexWidth() != result.GetIndexWidth())
  {
    std::cerr << "TransformTerm: input term is : " << term << std::endl;
    FatalError("TransformTerm: "
               "result & input terms have different index length",
               result);
  }
  return result;
}

// The formula kinds TransformFormula has an arm for. Anything else boolean
// that is not TRUE, FALSE or a symbol reaches its default and dies there, so
// the test happens here, in the same place: after the memo lookup and before
// any operand is touched.
static bool transformableFormula(const Kind k)
{
  switch (k)
  {
    case NOT:
    case BOOLEXTRACT:
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
    case EQ:
    case AND:
    case OR:
    case NAND:
    case NOR:
    case IFF:
    case XOR:
    case ITE:
    case IMPLIES:
    case FP_LEQ:
    case FP_LT:
    case FP_GEQ:
    case FP_GT:
    case FP_EQ:
    case FP_ISNORMAL:
    case FP_ISSUBNORMAL:
    case FP_ISZERO:
    case FP_ISINFINITE:
    case FP_ISNAN:
    case FP_ISNEGATIVE:
    case FP_ISPOSITIVE:
    case FP_SMT_EQ:
      return true;
    default:
      return false;
  }
}

// What a formula's operand is transformed as. The connectives take formulas,
// the comparisons and the floating-point predicates take terms, and
// BOOLEXTRACT is the one kind that carries an operand through untouched --
// its bit index.
enum FormulaOperand
{
  OperandFormula,
  OperandTerm,
  OperandAsIs
};

static FormulaOperand formulaOperand(const Kind k, const size_t i)
{
  switch (k)
  {
    case NOT:
    case AND:
    case OR:
    case NAND:
    case NOR:
    case IFF:
    case XOR:
    case ITE:
    case IMPLIES:
      return OperandFormula;
    case BOOLEXTRACT:
      return i == 0 ? OperandTerm : OperandAsIs;
    default:
      return OperandTerm;
  }
}

// Where one node's transform has got to.
//
// The three functions this replaces called each other once per level of the
// input -- a formula's operands through TransformTerm, a term's condition
// back through TransformFormula, a read's index and the array under it
// through both -- so they are one walk with its frames on the heap rather
// than three sets of call frames. See DeepDag_Test.cpp.
//
// Each job has its own resume-point type, so a request cannot accidentally
// resume a term as a formula or a read as a term.
class ArrayTransformer::TransformDriver
{
  ArrayTransformer& owner;
  ASTNodeMap*& TransformMap;
  Simplifier* const simp;
  STPMgr* const bm;
  NodeFactory* const nf;
  ASTNode& ASTTrue;
  ASTNode& ASTFalse;
  ASTNode& ASTUndefined;
  ArrType& arrayToIndexToRead;
  ArrayTransformer::AckPairMap& ack_pair;
  const bool& recordTouchedReads;
  std::vector<std::pair<ASTNode, ASTNode>>& touchedReads;
  ASTVec& cellSortConstraints;

  // Tail reads created by eager expansions still in progress: they skip
  // the chain-cut scan (the original read's scan covered their spine).
  ASTNodeSet internalTailReads;

  ASTNode finishTransformTerm(const ASTNode& term, const ASTNode& result)
  {
    return owner.finishTransformTerm(term, result);
  }

  // A cell of an array of modes holds a mode, and five bits carry one only
  // through five of their thirty-two patterns. FpTotalise pins the reads the
  // formula names, and it has run by now; a read minted here is either newer
  // than that pass -- the ones read-over-write and read-over-if-then-else
  // expansion introduce over a base array, and the ones a solved write chain
  // or a refinement lemma introduces -- or is one the pass did cover, in
  // which case this is the same constraint again and the conjunction absorbs
  // it. Left free, such a cell is not merely an unanswered don't-care: the
  // solve is entitled to witness a disequality of two arrays of modes with
  // carriers that name no mode at all, and every reader downstream -- the
  // congruence axioms, which compare the carriers, and the model, which must
  // publish a mode -- is then reading a different cell than the other. Pin it
  // where the array-equality checker pins its own virtual reads, so that
  // there is one answer.
  void pinRoundingModeCell(const ASTNode& arrName, const ASTNode& cell)
  {
    if (bm->arrayHasRmElement(arrName))
      cellSortConstraints.push_back(bm->roundingModeValidConstraint(cell));
  }

  struct Frame
  {
    enum Job
    {
      Formula,
      Term,
      Read
    };

    enum class FormulaPhase : uint8_t
    {
      Start,
      CollectOperands,
      AfterOperand
    };

    enum class TermPhase : uint8_t
    {
      Start,
      CollectOperands,
      AfterOperand,
      AfterRead,
      AfterIteCondition,
      AfterIteSelectedBranch,
      AfterIteThen,
      AfterIteElse
    };

    enum class ReadPhase : uint8_t
    {
      Start,
      AfterIndex,
      AfterWriteIndex,
      AfterWriteValue,
      AfterPushedRead,
      ChainLevel,
      AfterIteCondition,
      AfterIteSelectedBranch,
      AfterIteThen,
      AfterIteElse
    };

    Job job;
    union
    {
      FormulaPhase formulaPhase;
      TermPhase termPhase;
      ReadPhase readPhase;
    };
    ASTNode n;

    // Formula and ordinary-term frames use storage for the beginning of their
    // operands in the shared arena. Read frames use it for their state slots in
    // that same arena; those jobs never need both meanings.
    size_t storage = 0;
    size_t i = 0; // the operand being worked on

    // Term ITEs and reads share these. The rest of a slow-path read's
    // continuation lives in the shared arena so every formula and ordinary
    // term does not carry it.
    ASTNode cond;
    ASTNode thn;

    explicit Frame(ASTNode node, const FormulaPhase phase = FormulaPhase::Start)
        : job(Formula), formulaPhase(phase), n(std::move(node))
    {
    }

    Frame(ASTNode node, const TermPhase phase)
        : job(Term), termPhase(phase), n(std::move(node))
    {
    }

    Frame(ASTNode node, const ReadPhase phase)
        : job(Read), readPhase(phase), n(std::move(node))
    {
    }

    void resumeAt(const FormulaPhase phase)
    {
      assert(job == Formula);
      formulaPhase = phase;
    }
    void resumeAt(const TermPhase phase)
    {
      assert(job == Term);
      termPhase = phase;
    }
    void resumeAt(const ReadPhase phase)
    {
      assert(job == Read);
      readPhase = phase;
    }

    bool ownsReadState() const
    {
      assert(job == Read);
      return readPhase != ReadPhase::Start &&
             readPhase != ReadPhase::AfterIndex;
    }
  };

  // TransformFormula, TransformTerm and TransformArrayRead, walked together
  // with their frames on the heap. Everything the three did is here in the
  // order they did it: the same memo reads and writes, the same node-factory
  // calls, and the same decisions about which operand is transformed at all --
  // which matters most in the two places that transform only the branch of an
  // if-then-else that its condition leaves alive, and tell the extensionality
  // context about the one they dropped.
  ASTNode result;
  std::vector<Frame> stack;
  ASTVec activeParts;

  enum ReadStateSlot : size_t
  {
    ReadIndexSlot,
    WriteIndexSlot,
    WriteValueSlot,
    ElseReadSlot,
    ReadStateSlots
  };

  // The chain-collection frames use a different layout: the fixed slots,
  // then two slots per residual level holding the raw index and value
  // until their transforms overwrite them in place.
  enum ChainStateSlot : size_t
  {
    ChainReadIndexSlot,
    ChainBaseSlot,
    ChainCountSlot,
    ChainFixedSlots
  };

  static_assert(sizeof(Frame) <= 56,
                "common array-transform frames must remain compact");

  ASTChildren partsFor(const Frame& f) const
  {
    assert(f.n.Degree() > 0);
    assert(activeParts.size() - f.storage == f.n.Degree());
    return ASTChildren(activeParts.data() + f.storage,
                       activeParts.size() - f.storage);
  }

  // Decide whether transforming `n` needs a frame. A root which is already
  // answered returns before the stack is constructed; descendant callers
  // use the same checks before pushing a frame.
  bool prepare(const Frame::Job job, const ASTNode& n)
  {
    if (job == Frame::Read)
    {
      if (READ != n.GetKind())
      {
        result = n;
        return false;
      }

      const ASTNodeMap::const_iterator it = TransformMap->find(n);
      if (it != TransformMap->end())
      {
        result = it->second;
        return false;
      }

      return true;
    }

    const Kind k = n.GetKind();

    if (job == Frame::Formula)
    {
      if (!(is_Form_kind(k) && BOOLEAN_TYPE == n.GetType()))
      {
        // FIXME: "You have inputted a NON-formula"?
        FatalError("TransformFormula:"
                   "You have input a NON-formula",
                   n);
      }

      const ASTNodeMap::const_iterator it = TransformMap->find(n);
      if (it != TransformMap->end())
      {
        result = it->second;
        return false;
      }

      // TRUE, FALSE and a boolean symbol transform to themselves, and are
      // not recorded: the map was only ever written for a node with
      // children.
      if (k == TRUE || k == FALSE || k == SYMBOL)
      {
        result = n;
        return false;
      }

      if (!transformableFormula(k))
        FatalError("TransformFormula: Illegal kind: ", ASTUndefined, k);

      return true;
    }

    if (!is_Term_kind(k))
      FatalError("TransformTerm: Illegal kind: You have input a nonterm:", n,
                 k);

    const ASTNodeMap::const_iterator it = TransformMap->find(n);
    if (it != TransformMap->end())
    {
      result = it->second;
      return false;
    }

    if (k == SYMBOL || k == BVCONST)
    {
      // Leaves are not memoized, and their width checks are true by
      // construction because the result is the input itself.
      result = n;
      return false;
    }

    if (k == WRITE)
      FatalError("TransformTerm: this kind is not supported", n);

    return true;
  }

  // Ask for a formula descendant. Either `prepare` leaves its immediate
  // answer in `result`, or the walk goes below a new frame. Formula and term
  // requests stay separate so their hot paths do not redispatch on Job.
  template <typename ResumePhase>
  bool requestFormula(Frame& parent, const ResumePhase resume, const ASTNode& n)
  {
    parent.resumeAt(resume);
    if (!prepare(Frame::Formula, n))
      return false;
    ASTNode owned = n;
    stack.emplace_back(std::move(owned), Frame::FormulaPhase::Start);
    return true;
  }

  // The term counterpart. Own the requested node before vector growth
  // invalidates a reference which may point into the current frame.
  template <typename ResumePhase>
  bool requestTerm(Frame& parent, const ResumePhase resume, const ASTNode& n)
  {
    parent.resumeAt(resume);
    if (!prepare(Frame::Term, n))
      return false;
    ASTNode owned = n;
    stack.emplace_back(std::move(owned), Frame::TermPhase::Start);
    return true;
  }

  // Read is requested from one place only. Keep its uncommon state-allocation
  // path out of the formula and term helpers used for every operand.
  bool requestRead(Frame& parent, const Frame::TermPhase resume,
                   const ASTNode& n)
  {
    parent.resumeAt(resume);
    if (!prepare(Frame::Read, n))
      return false;
    ASTNode owned = n;
    stack.emplace_back(std::move(owned), Frame::ReadPhase::Start);
    return true;
  }

  // One step of TransformFormula: collect the operands, then rebuild.
  bool stepFormula(Frame& f)
  {
    assert(f.job == Frame::Formula);
    if (f.formulaPhase == Frame::FormulaPhase::Start)
    {
      f.formulaPhase = Frame::FormulaPhase::CollectOperands;
      f.storage = activeParts.size();
    }

    if (f.formulaPhase == Frame::FormulaPhase::AfterOperand)
    {
      activeParts.push_back(result);
      f.formulaPhase = Frame::FormulaPhase::CollectOperands;
    }

    const Kind k = f.n.GetKind();

    while (f.i < f.n.Degree())
    {
      const size_t i = f.i++;
      const FormulaOperand op = formulaOperand(k, i);

      if (op == OperandAsIs)
      {
        activeParts.push_back(f.n[i]);
        continue;
      }

      // The request helper installs the continuation only when it will push,
      // and does so before vector growth can move `f`.
      const bool descended =
          op == OperandFormula
              ? requestFormula(f, Frame::FormulaPhase::AfterOperand, f.n[i])
              : requestTerm(f, Frame::FormulaPhase::AfterOperand, f.n[i]);
      if (descended)
        return true;
      activeParts.push_back(result);
    }

    const ASTChildren parts = partsFor(f);
    if (k == EQ && bm->UserFlags.optimize_flag)
      result = simp->CreateSimplifiedEQ(parts[0], parts[1]);
    else
      result = nf->CreateNode(k, parts);
    activeParts.resize(f.storage);

    assert(!result.IsNull());
    if (f.n.Degree() > 0)
      (*TransformMap)[f.n] = result;
    return false;
  }

  // One step of TransformTerm. READ hands over to the array-read job, ITE
  // transforms its condition and then only the branch that survives it, and
  // everything else transforms its own children and rebuilds.
  bool stepTerm(Frame& f)
  {
    assert(f.job == Frame::Term);
    const Kind k = f.n.GetKind();

    if (k == READ)
    {
      if (f.termPhase == Frame::TermPhase::Start)
      {
        if (requestRead(f, Frame::TermPhase::AfterRead, f.n))
          return true;
      }
      result = finishTransformTerm(f.n, result);
      return false;
    }

    if (k == ITE)
    {
      if (f.termPhase == Frame::TermPhase::Start)
      {
        if (requestFormula(f, Frame::TermPhase::AfterIteCondition, f.n[0]))
          return true;
      }

      if (f.termPhase == Frame::TermPhase::AfterIteCondition)
      {
        f.cond = result;
        ExtensionalityContext* ext = bm->getExtensionalityIfAny();

        if (ASTTrue == f.cond || ASTFalse == f.cond)
        {
          const bool takeThen = (ASTTrue == f.cond);
          if (ext != NULL && ext->activeInSolve())
            ext->noteEliminatedReadSubtree(takeThen ? f.n[2] : f.n[1]);

          if (requestTerm(f, Frame::TermPhase::AfterIteSelectedBranch,
                          takeThen ? f.n[1] : f.n[2]))
            return true;
        }
        else
        {
          if (requestTerm(f, Frame::TermPhase::AfterIteThen, f.n[1]))
            return true;
        }
      }

      if (f.termPhase == Frame::TermPhase::AfterIteSelectedBranch)
      {
        assert(result.GetIndexWidth() == f.n.GetIndexWidth());
        result = finishTransformTerm(f.n, result);
        return false;
      }

      if (f.termPhase == Frame::TermPhase::AfterIteThen)
      {
        f.thn = result;
        if (requestTerm(f, Frame::TermPhase::AfterIteElse, f.n[2]))
          return true;
      }

      const ASTNode els = result;
      if (bm->UserFlags.optimize_flag)
        result = simp->CreateSimplifiedTermITE(f.cond, f.thn, els);
      else
        result = nf->CreateTerm(ITE, f.thn.GetValueWidth(), f.cond, f.thn, els);

      assert(result.GetIndexWidth() == f.n.GetIndexWidth());
      result = finishTransformTerm(f.n, result);
      return false;
    }

    if (f.termPhase == Frame::TermPhase::Start)
    {
      f.termPhase = Frame::TermPhase::CollectOperands;
      f.storage = activeParts.size();
    }

    if (f.termPhase == Frame::TermPhase::AfterOperand)
    {
      activeParts.push_back(result);
      f.termPhase = Frame::TermPhase::CollectOperands;
    }

    while (f.i < f.n.Degree())
    {
      const ASTNode& child = f.n[f.i++];

      // The request helper installs the continuation only when it will push,
      // and does so before vector growth can move `f`.
      if (requestTerm(f, Frame::TermPhase::AfterOperand, child))
        return true;
      activeParts.push_back(result);
    }

    const ASTChildren parts = partsFor(f);
    const ASTChildren c = f.n.GetChildren();
    if (c != parts)
      result = nf->CreateArrayTerm(k, f.n.GetIndexWidth(), f.n.GetValueWidth(),
                                   parts);
    else
      result = f.n;
    activeParts.resize(f.storage);

    result = finishTransformTerm(f.n, result);
    return false;
  }

  /* One step of TransformArrayRead, which transforms Array Reads, Read over
   * Writes, Read over ITEs into flattened form.
   *
   * Transform1: Suppose there are two array reads in the input
   * Read(A,i) and Read(A,j) over the same array. Then Read(A,i) is
   * replaced with a symbolic constant, say v1, and Read(A,j) is
   * replaced with the following ITE:
   *
   * ITE(i=j,v1,v2)
   *
  */
  bool stepRead(Frame& f)
  {
    assert(f.job == Frame::Read);
    ASTNode* state = nullptr;
    // A Read allocates persistent slots only when it advances beyond the
    // index phase into a WRITE or ITE continuation. The phase therefore
    // records the presence of state without another flag or sentinel store.
    if (f.ownsReadState())
    {
      assert(f.storage + ReadStateSlots <= activeParts.size());
      state = activeParts.data() + f.storage;
    }
    const ASTNode& term = f.n;
    const unsigned int width = term.GetValueWidth();

    //'term' is of the form READ(arrName, readIndex)
    const ASTNode& arrName = term[0];

    // The tail every path below this point shares.
    auto finishRead = [&](const ASTNode& value)
    {
      assert(BVTypeCheck(value));
      assert(!value.IsNull());
      (*TransformMap)[term] = value;
      result = value;
      return false;
    };

    if (f.readPhase == Frame::ReadPhase::Start)
    {
      if (requestTerm(f, Frame::ReadPhase::AfterIndex, term[1]))
        return true;
    }

    if (f.readPhase == Frame::ReadPhase::AfterIndex)
    {
      // SYMBOL reads and the whole-graph array-equality path finish in this
      // phase, so keep their index local. Allocate persistent Read state only
      // for the WRITE/ITE paths which actually suspend again.
      const ASTNode readIndex = result;

      // With array equality active, every read takes the direct
      // read-abstraction path: mint or reuse the fresh variable for the
      // (array, index) pair, whatever the array
      // term is: variable, write, or if-then-else. Neither its write chain
      // nor its if-then-else structure is expanded here. The lemmas-on-
      // demand consistency checker owns read-over-write and read-over-
      // if-then-else reasoning for these arrays (rules D/U and T-down/T-up),
      // and it needs the structure and the abstraction variables intact.
      {
        ExtensionalityContext* ext = bm->getExtensionalityIfAny();
        if (ext != NULL && ext->activeInSolve())
        {
          if (!ext->arrayGraphFrozen())
            FatalError("array-equality: the array transform ran before the "
                       "complete array graph was frozen",
                       term);
          if (!ext->ownsArray(arrName))
            FatalError("array-equality: a transformed read is absent from the "
                       "complete owned array graph",
                       term);
          if (bm->UserFlags.ackermannisation)
            FatalError("array-equality: eager Ackermannization reached the "
                       "whole-graph read transform");

          ArrType::const_iterator it;
          if ((it = arrayToIndexToRead.find(arrName)) !=
              arrayToIndexToRead.end())
          {
            std::map<ASTNode, ArrayRead>::const_iterator it2;
            if ((it2 = it->second.find(readIndex)) != it->second.end())
            {
              if (it2->second.ite != it2->second.symbol)
                FatalError("array-equality: a whole-graph read reused a legacy "
                           "nested-ITE transformer row",
                           term);
              result = it2->second.ite;
              ext->noteAbstractedRead(term, readIndex, it2->second.symbol);
              (*TransformMap)[term] = result;
              return false;
            }
          }

          // Deterministic per (array, index): repeating a solve re-mints the
          // same abstraction variable, so an incremental round's encoding and
          // lemmas stay attached to the right SAT variables.
          ASTNode CurrentSymbol = bm->CreateDeterministicVariable(
              term.GetIndexWidth(), term.GetValueWidth(), "ext_read", arrName,
              readIndex);

          // Same reason as the read-refinement path below: this variable
          // stands in for the read from here on and is a leaf, so the element
          // format has to travel with it or the element reaches the blaster
          // as a formatless bitvector. Setting a zero width (a non-float
          // array) is a no-op.
          CurrentSymbol.SetExpWidth(term.GetExpWidth());
          CurrentSymbol.SetSigWidth(term.GetSigWidth());

          // See pinRoundingModeCell. A write chain equated with its own base
          // is rewritten rather than abstracted, so the cells it names are
          // reads of the base minted right here, after totalisation -- and
          // the equality it replaced leaves no record for the checker to pin
          // them through either.
          pinRoundingModeCell(arrName, CurrentSymbol);

          result = CurrentSymbol;
          arrayToIndexToRead[arrName].insert(
              make_pair(readIndex, ArrayRead(result, CurrentSymbol)));
          ext->noteAbstractedRead(term, readIndex, CurrentSymbol);
          (*TransformMap)[term] = result;
          return false;
        }
      }

      switch (arrName.GetKind())
      {
        case SYMBOL:
        {
          /* input is of the form: READ(A, readIndex)
           *
           * output is of the from: A1, if this is the first READ over A
           *
           *                        ITE(previous_readIndex=readIndex,A1,A2)
           *
           *                        .....
           */

          {
            ArrType::const_iterator it;
            if ((it = arrayToIndexToRead.find(arrName)) !=
                arrayToIndexToRead.end())
            {
              std::map<ASTNode, ArrayRead>::const_iterator it2;
              if ((it2 = it->second.find(readIndex)) != it->second.end())
              {
                if (recordTouchedReads)
                  touchedReads.push_back(std::make_pair(arrName, readIndex));
                return finishRead(it2->second.ite);
              }
            }
          }

          // Make up a new abstract variable, named deterministically by the
          // (array, index) pair it reads: re-deriving the same read -- in a
          // later solve or an incremental round -- yields the same variable.

          ASTNode CurrentSymbol = bm->CreateDeterministicVariable(
              term.GetIndexWidth(), term.GetValueWidth(),
              "array_" + std::string(arrName.GetName()), readIndex);

          // Reading an array of floats yields a float. The read node derived
          // its format from the array, but this fresh variable stands in for
          // the read from here on and is a leaf, so it has to carry the
          // format itself -- otherwise the element arrives at the blaster as
          // a formatless bitvector.
          CurrentSymbol.SetExpWidth(term.GetExpWidth());
          CurrentSymbol.SetSigWidth(term.GetSigWidth());

          // See pinRoundingModeCell.
          pinRoundingModeCell(arrName, CurrentSymbol);

          ASTNode symbolResult = CurrentSymbol;

          if (!bm->UserFlags.ackermannisation)
          {
            // result is a variable here; it is an ite in the
            // else-branch
          }
          else
          {
            // Full Array transform if we're not doing read refinement.

            // list of array-read indices corresponding to arrName, seen while
            // traversing the AST tree. we need this list to construct the ITEs
            // Only the entries this index can produce a comparison from:
            // constant-against-constant is decided, and walking it is the
            // quadratic cost the estimate deliberately does not charge for.
            const ArrayTransformer::ReadKeys& p =
                ack_pair[arrName].walkFor(readIndex);

            ArrayTransformer::ReadKeys::const_reverse_iterator it2 = p.rbegin();
            ArrayTransformer::ReadKeys::const_reverse_iterator it2end = p.rend();
            for (; it2 != it2end; it2++)
            {
              ASTNode cond = simp->CreateSimplifiedEQ(readIndex, it2->first);
              if (ASTFalse == cond)
                continue;

              if (ASTTrue == cond)
              {
                symbolResult = it2->second;
              }
              else
                symbolResult = simp->CreateSimplifiedTermITE(cond, it2->second,
                                                             symbolResult);
            }

            ack_pair[arrName].add(readIndex, CurrentSymbol);
          }

          assert(arrName.GetType() == ARRAY_TYPE);
          if (recordTouchedReads)
            touchedReads.push_back(std::make_pair(arrName, readIndex));
          arrayToIndexToRead[arrName].insert(
              make_pair(readIndex, ArrayRead(symbolResult, CurrentSymbol)));
          return finishRead(symbolResult);
        }
        case WRITE:
        {
          /* The input to this case is: READ((WRITE A i val) j)
           *
           * The output of this case is: ITE( (= i j) val (READ A j))
           */

          /* 1. arrName or term[0] is infact a WRITE(A,i,val) expression
           *
           * 2. term[1] is the read-index j
           *
           * 3. arrName[0] is the new arrName i.e. A. A can be either a
           SYMBOL or a nested WRITE. no other possibility
           *
           * 4. arrName[1] is the WRITE index i.e. i
           *
           * 5. arrName[2] is the WRITE value i.e. val (val can inturn
           *    be an array read)
           */

          // A read this pair already abstracted reuses its row.
          {
            ChainReadsMap::const_iterator cit = owner.chainReads.find(arrName);
            if (cit != owner.chainReads.end())
            {
              ChainIndexMap::const_iterator rit = cit->second.find(readIndex);
              if (rit != cit->second.end())
              {
                if (recordTouchedReads)
                {
                  owner.touchedChains.push_back(
                      std::make_pair(arrName, readIndex));
                  if (!rit->second.baseArray.IsNull())
                    touchedReads.push_back(
                        std::make_pair(rit->second.baseArray, readIndex));
                }
                return finishRead(rit->second.symbol);
              }
            }
          }

          // Each original read scans its chain once for a cut; the suffix
          // reads the eager expansion itself creates skip the scan (their
          // spine is already covered by the original's mark).
          const bool internalTail = internalTailReads.erase(term) > 0;
          if (!internalTail)
            owner.markLazyChainCut(arrName, readIndex);

          {
            std::map<ASTNode, ASTNodeSet>::const_iterator cit =
                owner.lazyCutTargets.find(arrName);
            // The abstraction pays off when many reads share a chain:
            // the eager expansion is then levels x reads, while the rows
            // and their lemmas stay near-linear. A chain read a handful
            // of times is cheaper expanded -- abstracting it saves little
            // encoding and buys refinement rounds -- so a cut activates
            // only once its base array's qualified reads both exceed a
            // floor and amount to a fair share of the residual depth.
            // The first arrivals stay eager; in the incremental setting
            // the later conjuncts' reads are the ones that matter.
            bool activated = false;
            if (cit != owner.lazyCutTargets.end() &&
                cit->second.find(readIndex) != cit->second.end())
            {
              ASTNode base = arrName;
              while (base.GetKind() == WRITE)
                base = base[0];
              const size_t scans = owner.qualifiedScansOf[base];
              const size_t depth = owner.cutDepthOf[arrName];
              activated = scans > 4 && scans * 4 >= depth;
            }
            if (activated)
            {
              // Collect the residual chain: every level whose write may
              // alias the read, top-down. Provably-disjoint levels are
              // dropped; a provably-hit level ends the walk and stands in
              // for the fall-through (the base is then unreachable and
              // stays null). The walk repeats markLazyChainCut's
              // simplifications, so the two always agree.
              ASTVec rawParts;
              ASTNode base;
              ASTNode w = arrName;
              while (w.GetKind() == WRITE)
              {
                const ASTNode cond = simp->CreateSimplifiedEQ(w[1], readIndex);
                if (cond != ASTFalse)
                {
                  rawParts.push_back(w[1]);
                  rawParts.push_back(w[2]);
                }
                if (cond == ASTTrue)
                  break;
                w = w[0];
              }
              if (w.GetKind() == SYMBOL)
                base = w;
              assert(rawParts.size() >= 2);

              f.storage = activeParts.size();
              activeParts.resize(f.storage + ChainFixedSlots +
                                 rawParts.size());
              state = activeParts.data() + f.storage;
              state[ChainReadIndexSlot] = readIndex;
              state[ChainBaseSlot] = base;
              // Nested transforms grow the arena above these slots, so the
              // level count cannot be recovered from its size later.
              state[ChainCountSlot] =
                  bm->CreateBVConst(32, rawParts.size() / 2);
              for (size_t k = 0; k < rawParts.size(); k++)
                state[ChainFixedSlots + k] = rawParts[k];
              f.i = 0;
              const ASTNode firstRaw = state[ChainFixedSlots];
              if (requestTerm(f, Frame::ReadPhase::ChainLevel, firstRaw))
                return true;
              break;
            }
          }

          f.storage = activeParts.size();
          activeParts.resize(f.storage + ReadStateSlots);
          state = activeParts.data() + f.storage;
          state[ReadIndexSlot] = readIndex;
          if (requestTerm(f, Frame::ReadPhase::AfterWriteIndex, arrName[1]))
            return true;
          break;
        }
        case ITE:
        {
          /* READ((ITE cond thn els) j)
           *
           * is transformed into
           *
           * (ITE cond (READ thn j) (READ els j))
           */

          // pull out the ite from the read // pushes the read through.

          //(ITE cond thn els)
          f.storage = activeParts.size();
          activeParts.resize(f.storage + ReadStateSlots);
          state = activeParts.data() + f.storage;
          state[ReadIndexSlot] = readIndex;
          if (requestFormula(f, Frame::ReadPhase::AfterIteCondition,
                             arrName[0]))
            return true;
          break;
        }
        default:
          FatalError("TransformArray: "
                     "The READ is NOT over SYMBOL/WRITE/ITE",
                     term);
          break;
      }
    }

    assert(state != nullptr);
    if (f.readPhase == Frame::ReadPhase::AfterWriteIndex)
    {
      // Both operands are transformed before the condition is built, as
      // they were: the factory sees them in that order.
      state[WriteIndexSlot] = result;
      if (requestTerm(f, Frame::ReadPhase::AfterWriteValue, arrName[2]))
        return true;
    }

    if (f.readPhase == Frame::ReadPhase::AfterWriteValue)
    {
      state[WriteValueSlot] = result;

      if (ARRAY_TYPE != arrName[0].GetType())
        FatalError("TransformArray: "
                   "An array write is being attempted on a non-array:",
                   term);

      f.cond =
          simp->CreateSimplifiedEQ(state[WriteIndexSlot], state[ReadIndexSlot]);
      assert(BVTypeCheck(f.cond));

      // If the condition is true, it saves iteratively transforming through
      // all the (possibly nested) arrays.
      if (ASTTrue == f.cond)
        return finishRead(state[WriteValueSlot]);

      ASTNode readTerm =
          nf->CreateTerm(READ, width, arrName[0], state[ReadIndexSlot]);
      assert(BVTypeCheck(readTerm));

      // A tail read of an expansion in progress: its spine is covered by
      // the original read's cut scan, so it must not scan again.
      if (readTerm.GetKind() == READ)
        internalTailReads.insert(readTerm);

      // The simplifying node factory may have produced
      // something that's not a READ.
      if (requestTerm(f, Frame::ReadPhase::AfterPushedRead, readTerm))
        return true;
    }

    if (f.readPhase == Frame::ReadPhase::AfterPushedRead)
    {
      const ASTNode readPushedIn = result;
      assert(BVTypeCheck(const_cast<ASTNode&>(readPushedIn)));
      return finishRead(simp->CreateSimplifiedTermITE(
          f.cond, state[WriteValueSlot], readPushedIn));
    }

    if (f.readPhase == Frame::ReadPhase::ChainLevel)
    {
      for (;;)
      {
        state = activeParts.data() + f.storage;
        state[ChainFixedSlots + f.i] = result;
        f.i++;
        const size_t total =
            2 * (size_t)state[ChainCountSlot].GetUnsignedConst();
        if (f.i < total)
        {
          const ASTNode nextRaw = state[ChainFixedSlots + f.i];
          if (requestTerm(f, Frame::ReadPhase::ChainLevel, nextRaw))
            return true;
          continue;
        }

        // Every residual level is transformed: build the row.
        ChainRow row;
        row.index = state[ChainReadIndexSlot];
        row.indexAnchor = owner.anchorForChainTerm(row.index);
        row.baseArray = state[ChainBaseSlot];
        const size_t nLevels = total / 2;
        row.levels.reserve(nLevels);
        for (size_t k = 0; k < nLevels; k++)
        {
          ChainLevel lvl;
          lvl.index = state[ChainFixedSlots + 2 * k];
          lvl.indexAnchor = owner.anchorForChainTerm(lvl.index);
          lvl.value = state[ChainFixedSlots + 2 * k + 1];
          lvl.valueAnchor = owner.anchorForChainTerm(lvl.value);
          row.levels.push_back(lvl);
        }

        if (!row.baseArray.IsNull())
        {
          // The fall-through is the ordinary read abstraction of
          // (base, index): reuse its row, or create it exactly as a direct
          // read would so a later direct read shares it.
          arrTypeMap& baseMap = arrayToIndexToRead[row.baseArray];
          arrTypeMap::const_iterator bit = baseMap.find(row.index);
          if (bit != baseMap.end())
            row.baseReadSymbol = bit->second.symbol;
          else
          {
            ASTNode baseVar = bm->CreateDeterministicVariable(
                term.GetIndexWidth(), term.GetValueWidth(),
                "array_" + std::string(row.baseArray.GetName()), row.index);
            baseVar.SetExpWidth(term.GetExpWidth());
            baseVar.SetSigWidth(term.GetSigWidth());
            baseMap.insert(
                std::make_pair(row.index, ArrayRead(baseVar, baseVar)));
            pinRoundingModeCell(row.baseArray, baseVar);
            row.baseReadSymbol = baseVar;
          }
          if (recordTouchedReads)
            touchedReads.push_back(std::make_pair(row.baseArray, row.index));
        }

        ASTNode readVar = bm->CreateDeterministicVariable(
            term.GetIndexWidth(), term.GetValueWidth(), "chain_read",
            term[0], row.index);
        readVar.SetExpWidth(term.GetExpWidth());
        readVar.SetSigWidth(term.GetSigWidth());
        pinRoundingModeCell(term[0], readVar);
        row.symbol = readVar;

        owner.chainReads[term[0]][row.index] = row;
        if (recordTouchedReads)
          owner.touchedChains.push_back(std::make_pair(term[0], row.index));
        return finishRead(readVar);
      }
    }

    if (f.readPhase == Frame::ReadPhase::AfterIteCondition)
    {
      f.cond = result;

      const ASTNode& thn = arrName[1];
      const ASTNode& els = arrName[2];

      //(READ thn j)
      ASTNode thnRead = nf->CreateTerm(READ, width, thn, state[ReadIndexSlot]);
      assert(BVTypeCheck(thnRead));

      //(READ els j)
      ASTNode elsRead = nf->CreateTerm(READ, width, els, state[ReadIndexSlot]);
      assert(BVTypeCheck(elsRead));

      /* We try to call TransformTerm only if necessary, because it
       * introduces a new symbol for each read. The amount of work we
       * need to do later is based on the square of the number of symbols.
       */
      if (ASTTrue == f.cond || ASTFalse == f.cond)
      {
        if (requestTerm(f, Frame::ReadPhase::AfterIteSelectedBranch,
                        (ASTTrue == f.cond) ? thnRead : elsRead))
          return true;
      }
      else
      {
        // Built now, transformed after the then-read.
        state[ElseReadSlot] = elsRead;
        if (requestTerm(f, Frame::ReadPhase::AfterIteThen, thnRead))
          return true;
      }
    }

    if (f.readPhase == Frame::ReadPhase::AfterIteSelectedBranch)
      return finishRead(result);

    if (f.readPhase == Frame::ReadPhase::AfterIteThen)
    {
      f.thn = result;
      if (requestTerm(f, Frame::ReadPhase::AfterIteElse, state[ElseReadSlot]))
        return true;
    }

    //(ITE cond (READ thn j) (READ els j))
    return finishRead(simp->CreateSimplifiedTermITE(f.cond, f.thn, result));
  }

public:
  explicit TransformDriver(ArrayTransformer& owner)
      : owner(owner), TransformMap(owner.TransformMap), simp(owner.simp),
        bm(owner.bm), nf(owner.nf), ASTTrue(owner.ASTTrue),
        ASTFalse(owner.ASTFalse), ASTUndefined(owner.ASTUndefined),
        arrayToIndexToRead(owner.arrayToIndexToRead), ack_pair(owner.ack_pair),
        recordTouchedReads(owner.recordTouchedReads),
        touchedReads(owner.touchedReads),
        cellSortConstraints(owner.cellSortConstraints)
  {
  }

  ASTNode run(const bool asFormula, const ASTNode& top)
  {
    assert(TransformMap != NULL);
    result = ASTNode();
    stack.clear();
    activeParts.clear();

    const Frame::Job rootJob = asFormula ? Frame::Formula : Frame::Term;
    if (!prepare(rootJob, top))
      return result;

    // One allocation covers the common formula -> term -> read alternation.
    stack.reserve(8);
    if (asFormula)
      stack.emplace_back(top, Frame::FormulaPhase::Start);
    else
      stack.emplace_back(top, Frame::TermPhase::Start);

    while (true)
    {
      Frame& current = stack.back();

      bool descended = false;
      switch (current.job)
      {
        case Frame::Formula:
          descended = stepFormula(current);
          break;
        case Frame::Term:
          descended = stepTerm(current);
          break;
        case Frame::Read:
          descended = stepRead(current);
          break;
      }

      if (descended)
        continue;

      if (current.job == Frame::Read)
      {
        if (current.ownsReadState())
        {
          size_t slots = ReadStateSlots;
          if (current.readPhase == Frame::ReadPhase::ChainLevel)
            slots = ChainFixedSlots +
                    2 * (size_t)activeParts[current.storage + ChainCountSlot]
                            .GetUnsignedConst();
          assert(current.storage + slots == activeParts.size());
          (void)slots;
          activeParts.resize(current.storage);
        }
      }
      stack.pop_back();
      if (stack.empty())
        return result;
    }
  }
};

ASTNode ArrayTransformer::transform(const bool asFormula, const ASTNode& top)
{
  return TransformDriver(*this).run(asFormula, top);
}

/********************************************************
 * TransformFormula()
 *
 * Get rid of ARRAY read/writes
 ********************************************************/
ASTNode ArrayTransformer::TransformFormula(const ASTNode& simpleForm)
{
  return transform(true, simpleForm);
}

ASTNode ArrayTransformer::TransformTerm(const ASTNode& term)
{
  return transform(false, term);
}

// Since these arrayreads are being nuked and recorded in the
// substitutionmap, we have to also record the fact that each
// arrayread (e0 is of the form READ(Arr,const) here is represented
// by a BVCONST (e1). This is necessary for later Leibnitz Axiom
// generation
void ArrayTransformer::FillUp_ArrReadIndex_Vec(const ASTNode& e0,
                                               const ASTNode& e1)
{
  assert(e0.GetKind() == READ);
  assert(e0[0].GetKind() == SYMBOL);
  assert(e0[1].GetKind() == BVCONST);
  assert(e1.GetKind() == BVCONST);
  assert(arrayToIndexToRead[e0[0]].find(e0[1]) ==
         arrayToIndexToRead[e0[0]].end());

  arrayToIndexToRead[e0[0]].insert(make_pair(e0[1], ArrayRead(e1, e1)));

  ack_pair[e0[0]].add(e0[1], e1);
}

} // end of namespace stp

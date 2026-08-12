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
// NB: This is the only function that should be called
// externally. It sets up the cache that the others use.
ASTNode ArrayTransformer::TransformFormula_TopLevel(const ASTNode& form)
{
  runTimes->start(RunTimes::Transforming);

  assert(TransformMap == NULL);
  TransformMap = new ASTNodeMap(100);

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
          ASTNode newV = bm->CreateFreshVariable(0, the_index.GetValueWidth(),
                                                 "STP__IndexVariables");
          equalsNodes.push_back(nf->CreateNode(EQ, the_index, newV));
          replaced.insert(make_pair(the_index, newV));
          it->second.index_symbol = newV;
        }
        assert(it->second.index_symbol.GetValueWidth() ==
               the_index.GetValueWidth());
      }
    }

    runTimes->stop(RunTimes::Transforming);

    if (equalsNodes.size() > 0)
      return nf->CreateNode(AND, result, equalsNodes);
    else
      return result;
  }
  else
  {
    runTimes->stop(RunTimes::Transforming);
    return result;
  }
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
// `job` says which of the three a frame is running and `phase` where in it,
// because most of them suspend at more than one point. Everything else here
// was a local of the function it came from, kept because it has to survive
// the suspension.
struct ArrayTransformer::Frame
{
  enum Job
  {
    Formula,
    Term,
    Read
  };

  enum Phase
  {
    Start,
    Operands,       // a formula's operands, or a term's own children
    TermIteCond,    // ITE term: waiting for the condition
    TermIteOnly,    // ... for the one branch the condition left
    TermIteThen,    // ... for the then-branch, both surviving
    TermIteElse,    // ... for the else-branch
    TermRead,       // READ term: waiting for the array-read transform
    ReadIndex,      // array read: waiting for the read index
    ReadWriteIndex, // read over write: waiting for the write index
    ReadWriteVal,   // ... for the written value
    ReadPushedIn,   // ... for the read pushed under the write
    ReadIteCond,    // read over ITE: waiting for the condition
    ReadIteOnly,    // ... for the one branch the condition left
    ReadIteThen,    // ... for the then-read, both surviving
    ReadIteElse     // ... for the else-read
  };

  Job job;
  Phase phase = Start;
  ASTNode n;

  // Formula and ordinary-term frames use storage for the beginning of their
  // operands in the shared arena. Read frames use it for their state slots in
  // that same arena; those jobs never need both meanings.
  size_t storage = 0;
  size_t i = 0;         // the operand being worked on
  bool waiting = false; // an operand is being transformed below

  // Term ITEs and reads share these. The rest of a slow-path read's
  // continuation lives in the shared arena so every formula and ordinary
  // term does not carry it.
  ASTNode cond;
  ASTNode thn;

  Frame(Job j, ASTNode node) : job(j), n(std::move(node))
  {
  }
};

// TransformFormula, TransformTerm and TransformArrayRead, walked together
// with their frames on the heap. Everything the three did is here in the
// order they did it: the same memo reads and writes, the same node-factory
// calls, and the same decisions about which operand is transformed at all --
// which matters most in the two places that transform only the branch of an
// if-then-else that its condition leaves alive, and tell the extensionality
// context about the one they dropped.
ASTNode ArrayTransformer::transform(const bool asFormula, const ASTNode& top)
{
  assert(TransformMap != NULL);
  static_assert(sizeof(Frame) <= 56,
                "common array-transform frames must remain compact");

  ASTNode result;

  // Decide whether transforming `n` needs a frame. A root which is already
  // answered returns before the stack is constructed; descendant callers
  // use the same checks before pushing a frame.
  auto prepare = [&](const Frame::Job job, const ASTNode& n) -> bool {
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
  };

  const Frame::Job rootJob = asFormula ? Frame::Formula : Frame::Term;
  if (!prepare(rootJob, top))
    return result;

  // Most transforms are shallow. Keep their continuations in one compact
  // allocation instead of a deque's map and fixed-size blocks. A push may
  // move every frame, so a step must return without touching its Frame after
  // a request helper descends.
  std::vector<Frame> stack;
  // One allocation covers the common formula -> term -> read alternation and
  // avoids moving these comparatively large frames while it remains shallow.
  stack.reserve(8);
  stack.emplace_back(rootJob, top);

  // Continuation storage shared by every suspended job. Formula and term
  // frames append their operands; a Read frame reserves four ASTNode slots.
  // Each child owns the suffix beginning at storage and removes it before
  // its result is appended to its parent.
  ASTVec activeParts;

  enum ReadStateSlot : size_t
  {
    ReadIndexSlot,
    WriteIndexSlot,
    WriteValueSlot,
    ElseReadSlot,
    ReadStateSlots
  };
  auto partsFor = [&](const Frame& f) -> ASTChildren {
    // prepare() resolves every leaf without pushing a frame, so a frame
    // reaching reconstruction always owns at least one arena element.
    assert(f.n.Degree() > 0);
    assert(activeParts.size() - f.storage == f.n.Degree());
    return ASTChildren(activeParts.data() + f.storage,
                       activeParts.size() - f.storage);
  };

  // Ask for a formula descendant. Either `prepare` leaves its immediate
  // answer in `result`, or the walk goes below a new frame. Formula and term
  // requests stay separate so their hot paths do not redispatch on Job.
  auto wantFormula = [&](const ASTNode& n,
                         Frame* waitingParent = nullptr) -> bool {
    if (!prepare(Frame::Formula, n))
      return false;
    ASTNode owned = n;
    if (waitingParent != nullptr)
      waitingParent->waiting = true;
    stack.emplace_back(Frame::Formula, std::move(owned));
    return true;
  };

  // The term counterpart. Own the requested node before vector growth
  // invalidates a reference which may point into the current frame.
  auto wantTerm = [&](const ASTNode& n,
                      Frame* waitingParent = nullptr) -> bool {
    if (!prepare(Frame::Term, n))
      return false;
    ASTNode owned = n;
    if (waitingParent != nullptr)
      waitingParent->waiting = true;
    stack.emplace_back(Frame::Term, std::move(owned));
    return true;
  };

  // Read is requested from one place only. Keep its uncommon state-allocation
  // path out of the formula and term helpers used for every operand.
  auto wantRead = [&](const ASTNode& n) -> bool {
    if (!prepare(Frame::Read, n))
      return false;
    ASTNode owned = n;
    stack.emplace_back(Frame::Read, std::move(owned));
    return true;
  };

  // One step of TransformFormula: collect the operands, then rebuild.
  auto stepFormula = [&](Frame& f) -> bool {
    if (f.phase == Frame::Start)
    {
      f.phase = Frame::Operands;
      f.storage = activeParts.size();
    }

    if (f.waiting)
    {
      f.waiting = false;
      activeParts.push_back(result);
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
      const bool descended = op == OperandFormula
                                 ? wantFormula(f.n[i], &f)
                                 : wantTerm(f.n[i], &f);
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
  };

  // One step of TransformTerm. READ hands over to the array-read job, ITE
  // transforms its condition and then only the branch that survives it, and
  // everything else transforms its own children and rebuilds.
  auto stepTerm = [&](Frame& f) -> bool {
    const Kind k = f.n.GetKind();

    if (k == READ)
    {
      if (f.phase == Frame::Start)
      {
        f.phase = Frame::TermRead;
        if (wantRead(f.n))
          return true;
      }
      result = finishTransformTerm(f.n, result);
      return false;
    }

    if (k == ITE)
    {
      if (f.phase == Frame::Start)
      {
        f.phase = Frame::TermIteCond;
        if (wantFormula(f.n[0]))
          return true;
      }

      if (f.phase == Frame::TermIteCond)
      {
        f.cond = result;
        ExtensionalityContext* ext = bm->getExtensionalityIfAny();

        if (ASTTrue == f.cond || ASTFalse == f.cond)
        {
          const bool takeThen = (ASTTrue == f.cond);
          if (ext != NULL && ext->activeInSolve())
            ext->noteEliminatedReadSubtree(takeThen ? f.n[2] : f.n[1]);

          f.phase = Frame::TermIteOnly;
          if (wantTerm(takeThen ? f.n[1] : f.n[2]))
            return true;
        }
        else
        {
          f.phase = Frame::TermIteThen;
          if (wantTerm(f.n[1]))
            return true;
        }
      }

      if (f.phase == Frame::TermIteOnly)
      {
        assert(result.GetIndexWidth() == f.n.GetIndexWidth());
        result = finishTransformTerm(f.n, result);
        return false;
      }

      if (f.phase == Frame::TermIteThen)
      {
        f.thn = result;
        f.phase = Frame::TermIteElse;
        if (wantTerm(f.n[2]))
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

    if (f.phase == Frame::Start)
    {
      f.phase = Frame::Operands;
      f.storage = activeParts.size();
    }

    if (f.waiting)
    {
      f.waiting = false;
      activeParts.push_back(result);
    }

    while (f.i < f.n.Degree())
    {
      const ASTNode& child = f.n[f.i++];

      // The request helper installs the continuation only when it will push,
      // and does so before vector growth can move `f`.
      if (wantTerm(child, &f))
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
  };

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
  auto stepRead = [&](Frame& f) -> bool {
    ASTNode* state = nullptr;
    // A Read allocates persistent slots only when it advances beyond the
    // index phase into a WRITE or ITE continuation. The phase therefore
    // records the presence of state without another flag or sentinel store.
    if (f.phase > Frame::ReadIndex)
    {
      assert(f.storage + ReadStateSlots <= activeParts.size());
      state = activeParts.data() + f.storage;
    }
    const ASTNode& term = f.n;
    const unsigned int width = term.GetValueWidth();

    //'term' is of the form READ(arrName, readIndex)
    const ASTNode& arrName = term[0];

    // The tail every path below this point shares.
    auto finishRead = [&](const ASTNode& value) {
      assert(BVTypeCheck(value));
      assert(!value.IsNull());
      (*TransformMap)[term] = value;
      result = value;
      return false;
    };

    if (f.phase == Frame::Start)
    {
      f.phase = Frame::ReadIndex;
      if (wantTerm(term[1]))
        return true;
    }

    if (f.phase == Frame::ReadIndex)
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

          ASTNode CurrentSymbol = bm->CreateFreshVariable(
              term.GetIndexWidth(), term.GetValueWidth(), "ext_read");

          // Same reason as the read-refinement path below: this variable
          // stands in for the read from here on and is a leaf, so the element
          // format has to travel with it or the element reaches the blaster
          // as a formatless bitvector. Setting a zero width (a non-float
          // array) is a no-op.
          CurrentSymbol.SetExpWidth(term.GetExpWidth());
          CurrentSymbol.SetSigWidth(term.GetSigWidth());

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
                return finishRead(it2->second.ite);
            }
          }

          // Make up a new abstract variable. Build symbolic name
          // corresponding to array read. The symbolic name has 2
          // components: stringname, and a count

          ASTNode CurrentSymbol = bm->CreateFreshVariable(
              term.GetIndexWidth(), term.GetValueWidth(),
              "array_" + std::string(arrName.GetName()));

          // Reading an array of floats yields a float. The read node derived
          // its format from the array, but this fresh variable stands in for
          // the read from here on and is a leaf, so it has to carry the
          // format itself -- otherwise the element arrives at the blaster as
          // a formatless bitvector.
          CurrentSymbol.SetExpWidth(term.GetExpWidth());
          CurrentSymbol.SetSigWidth(term.GetSigWidth());

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
            vector<std::pair<ASTNode, ASTNode>> p = ack_pair[arrName];

            vector<std::pair<ASTNode, ASTNode>>::const_reverse_iterator it2 =
                p.rbegin();
            vector<std::pair<ASTNode, ASTNode>>::const_reverse_iterator it2end =
                p.rend();
            for (; it2 != it2end; it2++)
            {
              ASTNode cond =
                  simp->CreateSimplifiedEQ(readIndex, it2->first);
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

            ack_pair[arrName].push_back(
                make_pair(readIndex, CurrentSymbol));
          }

          assert(arrName.GetType() == ARRAY_TYPE);
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
          f.storage = activeParts.size();
          activeParts.resize(f.storage + ReadStateSlots);
          state = activeParts.data() + f.storage;
          state[ReadIndexSlot] = readIndex;
          f.phase = Frame::ReadWriteIndex;
          if (wantTerm(arrName[1]))
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
          f.phase = Frame::ReadIteCond;
          if (wantFormula(arrName[0]))
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
    if (f.phase == Frame::ReadWriteIndex)
    {
      // Both operands are transformed before the condition is built, as
      // they were: the factory sees them in that order.
      state[WriteIndexSlot] = result;
      f.phase = Frame::ReadWriteVal;
      if (wantTerm(arrName[2]))
        return true;
    }

    if (f.phase == Frame::ReadWriteVal)
    {
      state[WriteValueSlot] = result;

      if (ARRAY_TYPE != arrName[0].GetType())
        FatalError("TransformArray: "
                   "An array write is being attempted on a non-array:",
                   term);

      f.cond = simp->CreateSimplifiedEQ(state[WriteIndexSlot],
                                        state[ReadIndexSlot]);
      assert(BVTypeCheck(f.cond));

      // If the condition is true, it saves iteratively transforming through
      // all the (possibly nested) arrays.
      if (ASTTrue == f.cond)
        return finishRead(state[WriteValueSlot]);

      ASTNode readTerm =
          nf->CreateTerm(READ, width, arrName[0], state[ReadIndexSlot]);
      assert(BVTypeCheck(readTerm));

      // The simplifying node factory may have produced
      // something that's not a READ.
      f.phase = Frame::ReadPushedIn;
      if (wantTerm(readTerm))
        return true;
    }

    if (f.phase == Frame::ReadPushedIn)
    {
      const ASTNode readPushedIn = result;
      assert(BVTypeCheck(const_cast<ASTNode&>(readPushedIn)));
      return finishRead(simp->CreateSimplifiedTermITE(
          f.cond, state[WriteValueSlot], readPushedIn));
    }

    if (f.phase == Frame::ReadIteCond)
    {
      f.cond = result;

      const ASTNode& thn = arrName[1];
      const ASTNode& els = arrName[2];

      //(READ thn j)
      ASTNode thnRead =
          nf->CreateTerm(READ, width, thn, state[ReadIndexSlot]);
      assert(BVTypeCheck(thnRead));

      //(READ els j)
      ASTNode elsRead =
          nf->CreateTerm(READ, width, els, state[ReadIndexSlot]);
      assert(BVTypeCheck(elsRead));

      /* We try to call TransformTerm only if necessary, because it
       * introduces a new symbol for each read. The amount of work we
       * need to do later is based on the square of the number of symbols.
       */
      if (ASTTrue == f.cond || ASTFalse == f.cond)
      {
        f.phase = Frame::ReadIteOnly;
        if (wantTerm((ASTTrue == f.cond) ? thnRead : elsRead))
          return true;
      }
      else
      {
        // Built now, transformed after the then-read.
        state[ElseReadSlot] = elsRead;
        f.phase = Frame::ReadIteThen;
        if (wantTerm(thnRead))
          return true;
      }
    }

    if (f.phase == Frame::ReadIteOnly)
      return finishRead(result);

    if (f.phase == Frame::ReadIteThen)
    {
      f.thn = result;
      f.phase = Frame::ReadIteElse;
      if (wantTerm(state[ElseReadSlot]))
        return true;
    }

    //(ITE cond (READ thn j) (READ els j))
    return finishRead(
        simp->CreateSimplifiedTermITE(f.cond, f.thn, result));
  };

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
      if (current.phase > Frame::ReadIndex)
      {
        assert(current.storage + ReadStateSlots == activeParts.size());
        activeParts.resize(current.storage);
      }
    }
    stack.pop_back();
    if (stack.empty())
      return result;
  }
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

  ack_pair[e0[0]].push_back(make_pair(e0[1], e1));
}

} // end of namespace stp

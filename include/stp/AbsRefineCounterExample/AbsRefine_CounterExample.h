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

#ifndef CTREXAMPLE_H
#define CTREXAMPLE_H

#include "stp/AST/AST.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/ToSATBase.h"

namespace stp
{
// Polarity control for the reified bit-vector equality helper. LEFT_ONLY
// constrains (bits equal -> literal), RIGHT_ONLY constrains
// (literal -> bits equal), BOTH gives the full equivalence.
enum class Polarity
{
  LEFT_ONLY,
  RIGHT_ONLY,
  BOTH
};

// Resolve (or freshly allocate) the SAT variable vector of a SYMBOL.
void getSatVariables(const ASTNode& a, vector<unsigned>& v_a,
                     SATSolver& SatSolver, ToSATBase::ASTNodeToSATVar& satVar);

// Adds clauses constraining a fresh SAT variable to (partially) reify
// the bit-vector equality a = b, and returns that variable.
uint32_t getEquals(SATSolver& SatSolver, const ASTNode& a, const ASTNode& b,
                   ToSATBase::ASTNodeToSATVar& satVar,
                   Polarity polary = Polarity::BOTH);

class FpEncodingContext;
class ArrayReadRefinementProgress;
class UFTheoryAdapter;

class AbsRefine_CounterExample // not copyable
{
private:
  // Handy defs
  ASTNode ASTTrue, ASTFalse, ASTUndefined;

  // Data structure that holds the counterexample
  ASTNodeMap CounterExampleMap;

  // This memo map is used by the ComputeFormulaUsingModel()
  ASTNodeMap ComputeFormulaMap;

  // Ptr to STPManager
  STPMgr* bm;

  // Ptr to Simplifier
  Simplifier* simp;

  // Ptr to ArrayTransformer
  ArrayTransformer* ArrayTransform;

  // Non-owning observer of STP's solve-local source-to-carrier mapping.
  // STP clears this before destroying or replacing the context.
  FpEncodingContext* fpEncodingContext;

  // Non-zero while an already-lowered source expression is being evaluated.
  // Its descendants retain source-sort metadata, but must not be lowered a
  // second time merely because of that metadata.
  unsigned int fpEncodedEvaluationDepth;

  // Non-owning current solve-mode coordinator. STP owns the fresh-query
  // adapter; IncrementalSolver owns the exact-stack adapter.
  UFTheoryAdapter* ufTheoryAdapter;

  FpEncodingContext& requireFpEncodingContext() const;

  // Re-evaluates the query the user actually submitted against the
  // finished model. This must not reconstruct the formula from STPMgr's
  // assertion/query registry: solve-boundary passes (notably opaque
  // array-equality lowering) are local to the root handed to the solve
  // and deliberately do not mutate that public registry.
  //
  // checked_input is the root as submitted, *before* array-equality
  // lowering -- not the semantic root the solve ran on. Passing the
  // semantic root instead would re-ask a question the caller has
  // already had answered, and the memo would answer it from cache.
  //
  // Be precise about what the extra reach buys, because it is less than
  // it looks: an opaque ARRAY_EQ is still present in this root, but it
  // is evaluated through its recorded lowering, which is the value the
  // verdict already rested on. So this walk covers the Boolean skeleton
  // the lowering rebuilt around the equalities -- not the equalities.
  // Their own content is checked separately, by comparing each
  // abstraction variable against the array cells the model publishes
  // (ExtensionalityContext::recheckCertifiedEqualities, called at the
  // end of this function).
  void CheckCounterExample(bool t, const ASTNode& checked_input);

  // Accepts a term and turns it into a constant-term w.r.t
  // The cells the model records for a set of array nodes, keyed by
  // (array, index) with the index normalised to its plain bit-vector
  // spelling.
  //
  // Keyed that way on purpose. A cell is a property of the *value* of
  // its index, but a floating-point constant interns apart from the
  // plain constant with its bits -- so 1.0f and 0x3F800000 are two
  // nodes naming one cell, and looking a cell up by building a READ
  // node asks about the spelling. Whichever spelling the model happened
  // to record under would be found and the other missed, and the miss
  // completes to zero: one array reads a cell the other does not, and
  // two equal arrays are reported as differing.
  typedef std::map<std::pair<ASTNode, ASTNode>, ASTNode> ModelCells;
  void CollectModelCells(const ASTNodeSet& arrays, ModelCells& out);

  // The value the model gives one cell of an array term, without
  // recording anything: the recorded cell if there is one, else the
  // written value if a write at this level hits the index, else the
  // same question one level down, else defaultCellValue. Answers with a
  // plain bitvector constant, for the reason given on
  // TermToConstTermUsingModel below -- its results are compared by
  // node identity.
  ASTNode ReadUsingModel(const ASTNode& arrayTerm,
                         const ASTNode& concreteIndex,
                         const ModelCells& cells);

  // The array-valued nodes an array term is built from -- itself, the
  // base of every write, both branches of every array if-then-else.
  // These are the nodes the model can hold cells against.
  void CollectArrayNodes(const ASTNode& arrayTerm, ASTNodeSet& out) const;

  // counter_example. Always answers with a plain bitvector constant: a
  // float constant interns separately from the bitvector constant with
  // the same bits, and evaluation results are compared (write-hit
  // tests, counterexample-map keys) by node identity, so bits equal
  // must mean nodes equal.
  ASTNode TermToConstTermUsingModel(const ASTNode& term,
                                    bool ArrayReadFlag = true);

private:
  // Which of the three evaluations below a frame of the walk is running.
  enum Job
  {
    EvalFormula,
    EvalTerm,
    EvalExpand
  };

  // Evaluating a formula evaluates its terms, a term its if-then-else
  // condition, and a read over a write the expansion of that write chain and
  // then the terms in it -- once per level of the input, which is the input's
  // choice and can be deeper than the stack holds. So the three are one walk
  // with its frames on the heap rather than three sets of call frames. See
  // DeepDag_Test.cpp.
  class EvaluationDriver;
  ASTNode evaluate(Job job, const ASTNode& n, bool topArrayReadFlag);

public:

  ASTNode Expand_ReadOverWrite_UsingModel(const ASTNode& term,
                                          bool ArrayReadFlag = true);

  void CopySolverMap_To_CounterExample(void);

  // Converts a vector of bools to a BVConst
  ASTNode BoolVectoBVConst(const vector<bool>* w, const unsigned int l);

  // Converts MINISAT counterexample into an AST memotable (i.e. the
  // function populates the datastructure CounterExampleMap)
  void ConstructCounterExample(
      SATSolver& newS,
      const ToSATBase::ASTNodeToSATVar& satVarToSymbol,
      bool internalCandidateRequired = false);

  // Prints MINISAT assigment one bit at a time, for debugging.
  void PrintSATModel(SATSolver& S, ToSATBase::ASTNodeToSATVar& satVarToSymbol);

public:
  AbsRefine_CounterExample(STPMgr* b, Simplifier* s, ArrayTransformer* at)
      : bm(b), simp(s), ArrayTransform(at), fpEncodingContext(NULL),
        fpEncodedEvaluationDepth(0), ufTheoryAdapter(NULL)
  {
    ASTTrue = bm->CreateNode(TRUE);
    ASTFalse = bm->CreateNode(FALSE);
    ASTUndefined = bm->CreateNode(UNDEFINED);
  }

  void setFpEncodingContext(FpEncodingContext* context)
  {
    fpEncodingContext = context;
  }

  void setUFTheoryAdapter(UFTheoryAdapter* adapter)
  {
    ufTheoryAdapter = adapter;
  }
  UFTheoryAdapter* getUFTheoryAdapter() const { return ufTheoryAdapter; }

  // Prints the counterexample to stdout
  void PrintCounterExample(bool t, std::ostream& os = std::cout);
  void PrintCounterExampleSMTLIB2(std::ostream& os);
  void PrintFullCounterExampleSMTLIB2(std::ostream& os);
  void outputLine(std::ostream& os, const ASTNode &f, ASTNode se);
  
  void PrintSMTLIB2(std::ostream& os, const ASTNode& n);

  void ClearCounterExampleMap(void) { CounterExampleMap.clear(); }

  void ClearComputeFormulaMap(void) { ComputeFormulaMap.clear(); }

  // Full incremental encoding-epoch reclamation. Ordinary solves retain the
  // buckets for model reuse; a relief rotation drops a previous model's hash
  // table high-water allocation after that model has been invalidated.
  void ReleaseModelStorage(void)
  {
    ASTNodeMap().swap(CounterExampleMap);
    ASTNodeMap().swap(ComputeFormulaMap);
  }

  // Publish an array observation certified by the array-equality
  // consistency check: READ over a constant index mapped to its
  // concrete value. A different existing value is an integration
  // error, never a choice between two model authorities.
  void InsertIntoCounterExampleMap(const ASTNode& key, const ASTNode& value)
  {
    ASTNodeMap::const_iterator it = CounterExampleMap.find(key);
    if (it != CounterExampleMap.end() && !(it->second == value))
      FatalError("array-equality: certified array observation conflicts with "
                 "an existing counterexample entry",
                 key);
    CounterExampleMap[key] = value;
  }

  // Exact lookup in the materialized SAT assignment. Unlike the general
  // model evaluator, this never invents a default for a symbol that was
  // absent from the bit-blast. The extensionality checker uses it for
  // every scalar name on which a refinement certificate depends.
  ASTNode LookupAssignedValue(const ASTNode& key) const
  {
    ASTNodeMap::const_iterator it = CounterExampleMap.find(key);
    return it == CounterExampleMap.end() ? ASTNode() : it->second;
  }

  // Prints the counterexample to stdout
  void PrintCounterExample_InOrder(bool t);

  // queries the counterexample, and returns the value corresponding
  // to e
  ASTNode GetCounterExample(const ASTNode& e);

  // Model access for the array-equality consistency checker: must work
  // mid-solve on the current candidate, regardless of the ValidFlag
  // left over from an earlier query in incremental use.
  ASTNode ModelValueOfTerm(const ASTNode& t)
  {
    return TermToConstTermUsingModel(t, false);
  }
  ASTNode ModelValueOfFormula(const ASTNode& f)
  {
    return ComputeFormulaUsingModel(f);
  }

  // queries the counterexample, and returns a vector of index-value pairs for e
  vector<std::pair<ASTNode, ASTNode>> GetCounterExampleArray(bool t,
                                                             const ASTNode& e);

  // The observed (index, value) model entries of one array symbol,
  // deduplicated per concrete index and sorted in ascending unsigned
  // index order. Shared by the programmatic model API and the SMT-LIB2
  // model printer so both surfaces expose the same deterministic
  // observations.
  vector<std::pair<ASTNode, ASTNode>>
  GetSortedArrayModelEntries(const ASTNode& arraySym);

  int CounterExampleSize(void) const { return CounterExampleMap.size(); }

  // FIXME: This is bloody dangerous function. Hack attack to take
  // care of requests from users who want to store complete
  // counter-examples in their own data structures.
  ASTNodeMap GetCompleteCounterExample() { return CounterExampleMap; }

  // Computes the truth value of a formula w.r.t counter_example
  ASTNode ComputeFormulaUsingModel(const ASTNode& form);

  // Do two array terms denote the same array in the finished model?
  //
  // Decided from the model alone -- no abstraction variable, no
  // record, no lowering -- so it can answer for an equality the solve
  // never reasoned about, and it is an independent opinion where the
  // solve did. Cells the model records nothing for read as
  // defaultCellValue, which is the completion the model printer and the
  // programmatic model API both apply, so the answer is the one a
  // reader of the printed model would get.
  //
  // The cells at which two array terms can differ are finite and
  // known: every index the model records against an array either term
  // is built from, plus every index written to by a write in either
  // term. Anywhere else both terms read the same default.
  bool ArraysEqualUsingModel(const ASTNode& left, const ASTNode& right);

  // Whether ArraysEqualUsingModel can answer about this array term at
  // all. Ask before asking; see the definition for the one case it
  // cannot.
  bool arrayEqualityIsModelDecidable(const ASTNode& arrayTerm) const;

  // What a cell of this array holds when the model records nothing for
  // it.
  //
  // Every reader of a published model has to answer this identically:
  // the printer emits it as the constant array underneath the observed
  // cells, ReadUsingModel and the read evaluator return it for an index
  // with no entry, and the array-equality checker completes both sides
  // with it before comparing contents. A site that disagrees makes the
  // model contradict itself -- an equality reads false through its
  // lowering's reads while the printed arrays are identical -- and that
  // is invisible until something compares two of the answers. So the
  // value is decided once, here, and every site asks rather than
  // spelling it out.
  //
  // Keyed on the array because it is a property of the element sort,
  // not of the element width: RoundingMode is a one-hot encoding whose
  // all-zero pattern denotes no mode at all, so a five-bit array of
  // modes cannot be completed with the same constant a five-bit array
  // of bitvectors is.
  ASTNode defaultCellValue(const ASTNode& arrayTerm) const;

  // The mode a RoundingMode carrier with nothing behind it denotes.
  // defaultCellValue publishes it for an unobserved cell of an array of
  // modes, and the symbol and read arms of the evaluator publish it for a
  // term the model records nothing for. It is spelled out once here so
  // that a carrier the model *does* record, and no live constraint
  // reached, is completed with the same mode rather than a second choice.
  ASTNode defaultRoundingMode() const;

  // The value to publish for a RoundingMode-sorted term the solve
  // assigned `carrier` bits.
  //
  // Twenty-seven of the carrier's thirty-two patterns denote no mode, and
  // every mode the current formula names is pinned to the five -- by the
  // declaration, by UF lowering, by FpTotalise, by the array transform
  // where it mints a cell. So a carrier that denotes nothing did not
  // escape a pin: it is bits no constraint of this solve reached, a
  // don't-care exactly like the cell no observation covers, and owed the
  // same completion. Anything that does denote a mode is the solve's
  // answer and is returned untouched.
  ASTNode completeRoundingMode(const ASTNode& carrier) const;

  // ComputeFormulaUsingModel for a caller asking a question about the
  // model rather than assembling it: whatever the evaluation would
  // have recorded is rolled back. See the note on ModelQuery in the
  // implementation for why that matters.
  ASTNode QueryFormulaAgainstModel(const ASTNode& form);

  /****************************************************************
   * Array Refinement functions                                   *
   ****************************************************************/
  // original_input is the semantic root this solve ran on, and is what
  // the model is evaluated against to decide the verdict. submitted_input
  // is the root as the user handed it over, before array-equality
  // lowering; it differs only when lowering did something, and it is
  // what --check-counterexample re-evaluates. Callers with no lowered
  // form to distinguish pass the same node twice.
  SOLVER_RETURN_TYPE
  CallSAT_ResultCheck(SATSolver& SatSolver, const ASTNode& modified_input,
                      const ASTNode& original_input,
                      const ASTNode& submitted_input, ToSATBase* tosat,
                      bool refinement);

  SOLVER_RETURN_TYPE
  SATBased_ArrayReadRefinement(SATSolver& newS, const ASTNode& original_input,
                               ToSATBase* tosat,
                               ArrayReadRefinementProgress* progress = NULL);

  void applyAllCongruenceConstraints(SATSolver& SatSolver, ToSATBase* tosat);

#if 0
    SOLVER_RETURN_TYPE
    SATBased_ArrayWriteRefinement(SATSolver& newS,
                                  const ASTNode& orig_input,
                                  ToSATBase *tosat);

    //creates array write axiom only for the input term or formula, if
    //necessary. If there are no axioms to produce then it simply
    //generates TRUE
    ASTNode
    Create_ArrayWriteAxioms(const ASTNode& array_readoverwrite_term,
                            const ASTNode& array_newname);

#endif

  void ClearAllTables(void)
  {
    CounterExampleMap.clear();
    ComputeFormulaMap.clear();
  }

  ~AbsRefine_CounterExample() { ClearAllTables(); }
};

class CompleteCounterExample // not copyable
{
  ASTNodeMap counterexample;
  STPMgr* bv;

public:
  CompleteCounterExample(ASTNodeMap a, STPMgr* beev)
      : counterexample(a), bv(beev)
  {
  }
  ASTNode GetCounterExample(ASTNode e)
  {
    if (BOOLEAN_TYPE == e.GetType() && SYMBOL != e.GetKind())
    {
      FatalError("You must input a term or propositional variables\n", e);
    }
    if (counterexample.find(e) != counterexample.end())
    {
      // The map is the raw model, holding the plain bitvector constants that
      // model evaluation works in. A value handed out carries the sort of
      // what was asked for, as from
      // AbsRefine_CounterExample::GetCounterExample -- so a float term's
      // value can be equated with the term again.
      return bv->LiftSourceValue(counterexample[e], e.GetSourceSort());
    }
    else
    {
      if (SYMBOL == e.GetKind() && BOOLEAN_TYPE == e.GetType())
      {
        return bv->CreateNode(stp::FALSE);
      }

      if (SYMBOL == e.GetKind())
      {
        // Simplified out, so it can take any value. RoundingMode has only five
        // values in its 5-bit carrier, so use a legal deterministic default;
        // ordinary bitvectors and floats retain the all-zero completion.
        ASTNode z = bv->isRoundingModeSortedTerm(e)
                        ? bv->CreateBVConst(
                              5, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN)
                        : bv->CreateZeroConst(e.GetValueWidth());
        return bv->LiftSourceValue(z, e.GetSourceSort());
      }

      return e;
    }
  }
};
} // end of namespace
#endif

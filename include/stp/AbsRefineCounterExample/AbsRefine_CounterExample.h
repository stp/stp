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
Minisat::Var getEquals(SATSolver& SatSolver, const ASTNode& a,
                       const ASTNode& b, ToSATBase::ASTNodeToSATVar& satVar,
                       Polarity polary = Polarity::BOTH);

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

  // Checks if the counterexample is good. In order for the
  // counterexample to be ok, every assert must evaluate to true
  // w.r.t couner_example, and the query must evaluate to
  // false. Otherwise we know that the counter_example is bogus.
  void CheckCounterExample(bool t);

  // Accepts a term and turns it into a constant-term w.r.t
  // counter_example
  ASTNode TermToConstTermUsingModel(const ASTNode& term,
                                    bool ArrayReadFlag = true);

  ASTNode Expand_ReadOverWrite_UsingModel(const ASTNode& term,
                                          bool ArrayReadFlag = true);

  void CopySolverMap_To_CounterExample(void);

  // Converts a vector of bools to a BVConst
  ASTNode BoolVectoBVConst(const vector<bool>* w, const unsigned int l);

  // Converts MINISAT counterexample into an AST memotable (i.e. the
  // function populates the datastructure CounterExampleMap)
  void ConstructCounterExample(SATSolver& newS,
                               ToSATBase::ASTNodeToSATVar& satVarToSymbol);

  // Prints MINISAT assigment one bit at a time, for debugging.
  void PrintSATModel(SATSolver& S, ToSATBase::ASTNodeToSATVar& satVarToSymbol);

public:
  AbsRefine_CounterExample(STPMgr* b, Simplifier* s, ArrayTransformer* at)
      : bm(b), simp(s), ArrayTransform(at)
  {
    ASTTrue = bm->CreateNode(TRUE);
    ASTFalse = bm->CreateNode(FALSE);
    ASTUndefined = bm->CreateNode(UNDEFINED);
  }

  // Prints the counterexample to stdout
  void PrintCounterExample(bool t, std::ostream& os = std::cout);
  void PrintCounterExampleSMTLIB2(std::ostream& os);
  void PrintFullCounterExampleSMTLIB2(std::ostream& os);
  void outputLine(std::ostream& os, const ASTNode &f, ASTNode se);
  
  void PrintSMTLIB2(std::ostream& os, const ASTNode& n);

  void ClearCounterExampleMap(void) { CounterExampleMap.clear(); }

  void ClearComputeFormulaMap(void) { ComputeFormulaMap.clear(); }

  // Publish an array observation certified by the array-equality
  // consistency check: READ over a constant index mapped to its
  // concrete value. Existing entries win.
  void InsertIntoCounterExampleMap(const ASTNode& key, const ASTNode& value)
  {
    if (CounterExampleMap.find(key) == CounterExampleMap.end())
      CounterExampleMap[key] = value;
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

  /****************************************************************
   * Array Refinement functions                                   *
   ****************************************************************/
  SOLVER_RETURN_TYPE
  CallSAT_ResultCheck(SATSolver& SatSolver, const ASTNode& modified_input,
                      const ASTNode& original_input, ToSATBase* tosat,
                      bool refinement);

  SOLVER_RETURN_TYPE
  SATBased_ArrayReadRefinement(SATSolver& newS, const ASTNode& original_input,
                               ToSATBase* tosat);

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
      return counterexample[e];
    }
    else
    {
      if (SYMBOL == e.GetKind() && BOOLEAN_TYPE == e.GetType())
      {
        return bv->CreateNode(stp::FALSE);
      }

      if (SYMBOL == e.GetKind())
      {
        ASTNode z = bv->CreateZeroConst(e.GetValueWidth());
        return z;
      }

      return e;
    }
  }
};
} // end of namespace
#endif

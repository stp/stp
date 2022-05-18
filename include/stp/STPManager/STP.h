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

#ifndef STP_H
#define STP_H

#include "stp/AST/AST.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Parser/LetMgr.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/BVSolver.h"
#include "stp/Simplifier/PropagateEqualities.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Util/Attributes.h"
#include "stp/ToSat/ToSATAIG.h"
#include "stp/Simplifier/NodeDomainAnalysis.h"

namespace stp
{
// FIXME: This needs a better name
class STP
{

  ASTNode sizeReducing(ASTNode input, BVSolver* bvSolver,
                       PropagateEqualities* pe, NodeDomainAnalysis* domain);

  // A copy of all the state we need to restore to a prior expression.
  struct Revert_to
  {
    ASTNodeMap initialSolverMap; // Map from variables to expressions they were
                                 // replaced with.
    ASTNode toRevertTo;          // The original expression.
    ArrayTransformer::ArrType
        backup_arrayToIndexToRead; // array-indices already removed.
  };

  // Accepts query and returns the answer. if query is valid,
  // returns VALID, else returns INVALID. Automatically constructs
  // counterexample for invalid queries, and prints them upon
  // request.
  SOLVER_RETURN_TYPE TopLevelSTPAux(SATSolver& NewSolver,
                                    const ASTNode& modified_input);

  SOLVER_RETURN_TYPE solve_by_sat_solver(SATSolver* newS,
                                         ASTNode original_input);

  SATSolver* get_new_sat_solver();

public:
  STPMgr* bm;
  Simplifier* simp;
  ToSATBase* tosat;
  AbsRefine_CounterExample* Ctr_Example;
  ArrayTransformer* arrayTransformer;
  SubstitutionMap* substitutionMap;

public:
  STP(STPMgr* b)
  {
    bm = b;
    substitutionMap = new stp::SubstitutionMap(bm);
    simp = new Simplifier(bm,substitutionMap);
    arrayTransformer = new ArrayTransformer(bm, simp);
    Ctr_Example = new AbsRefine_CounterExample(bm, simp, arrayTransformer);
    tosat = new ToSATAIG(bm, arrayTransformer);
  }

  STP( const STP& ) = delete; 
  STP& operator=( const STP& ) = delete; 

  ~STP() 
  { 
    ClearAllTables(); 
    deleteObjects();
  }

  // NB doesn't delete the STPMgr.
  void deleteObjects()
  {
    delete Ctr_Example;
    Ctr_Example = NULL;

    delete arrayTransformer;
    arrayTransformer = NULL;

    delete tosat;
    tosat = NULL;

    delete simp;
    simp = NULL;

    delete substitutionMap;
    substitutionMap = NULL;
  }

  // The absolute TopLevel function that invokes STP on the input
  // formula
  DLL_PUBLIC SOLVER_RETURN_TYPE TopLevelSTP(const ASTNode& inputasserts,
                                            const ASTNode& query);

  // calls sizeReducing and the bitblasting simplification.
  ASTNode callSizeReducing(ASTNode simplified_solved_InputToSAT,
                           BVSolver* bvSolver, PropagateEqualities* pe, NodeDomainAnalysis* domain);

  void ClearAllTables(void)
  {
    if (simp != NULL)
      simp->ClearAllTables();
    if (arrayTransformer != NULL)
      arrayTransformer->ClearAllTables();
    if (tosat != NULL)
      tosat->ClearAllTables();
    if (Ctr_Example != NULL)
      Ctr_Example->ClearAllTables();
    // bm->ClearAllTables();
  }
};
} // end of namespace
#endif

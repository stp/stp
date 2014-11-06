// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ********************************************************************/

#ifndef STP_H
#define STP_H

#include "stp/AST/AST.h"
#include "stp/AST/ArrayTransformer.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Simplifier/bvsolver.h"
#include "stp/Simplifier/simplifier.h"
#include "stp/ToSat/ASTNode/ToSAT.h"
#include "stp/Parser/LetMgr.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/Simplifier/PropagateEqualities.h"
#include <boost/utility.hpp>

namespace BEEV
{
  class STP  : boost::noncopyable
  {

    

          ASTNode sizeReducing(ASTNode input, BVSolver* bvSolver, PropagateEqualities *pe);

          // A copy of all the state we need to restore to a prior expression.
          struct Revert_to
          {
            ASTNodeMap initialSolverMap; // Map from variables to expressions they were replaced with.
            ASTNode toRevertTo;          // The original expression.
            ArrayTransformer::ArrType backup_arrayToIndexToRead; // array-indices already removed.
          };

          // Accepts query and returns the answer. if query is valid,
          // returns VALID, else returns INVALID. Automatically constructs
          // counterexample for invalid queries, and prints them upon
          // request.
          SOLVER_RETURN_TYPE TopLevelSTPAux(SATSolver& NewSolver,
                                            const ASTNode& modified_input
                                            );


  public:
ArrayTransformer * arrayTransformer;
    
          // calls sizeReducing and the bitblasting simplification.
          ASTNode callSizeReducing(ASTNode simplified_solved_InputToSAT, BVSolver* bvSolver, PropagateEqualities *pe, const int initial_difficulty_score, int & actualBBSize);


    /****************************************************************
     * Public Data:
     *  
     * Absolute toplevel class. No need to make data private
     ****************************************************************/
    STPMgr * bm;
    Simplifier * simp;
    ToSATBase * tosat;
    AbsRefine_CounterExample * Ctr_Example;

    /****************************************************************
     * Constructor and Destructor                                   *
     ****************************************************************/

    //Constructor
    STP(STPMgr* b,
        Simplifier* s,
        ArrayTransformer * a,
        ToSATBase * ts,
        AbsRefine_CounterExample * ce)
    {
      bm   = b;
      simp = s;
      tosat = ts;
      arrayTransformer = a;
      Ctr_Example = ce;
    }// End of constructor


    //Constructor
    STP(STPMgr* b,
        Simplifier* s,
        BVSolver* bsolv,
        ArrayTransformer * a,
        ToSATBase * ts,
        AbsRefine_CounterExample * ce)    
    {
      bm   = b;
      simp = s;
      tosat = ts;
      delete bsolv; // Remove from the constructor later..
      arrayTransformer = a;
      Ctr_Example = ce;
    }// End of constructor

    ~STP()
    {
      ClearAllTables();
      delete Ctr_Example;
      Ctr_Example = NULL;
      delete arrayTransformer;
      arrayTransformer = NULL;
      delete tosat;
      tosat = NULL;
      delete simp;
      simp = NULL;
      //delete bm;
    }

    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/

    // The absolute TopLevel function that invokes STP on the input
    // formula
    SOLVER_RETURN_TYPE TopLevelSTP(const ASTNode& inputasserts, 
                                   const ASTNode& query);

#if 0
    SOLVER_RETURN_TYPE
    UserGuided_AbsRefine(SATSolver& SatSolver,
			 const ASTNode& original_input);
#endif

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
		//bm->ClearAllTables();
	}
  }; //End of Class STP
} //end of namespace
#endif

// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef STP_H
#define STP_H

#include "../AST/AST.h"
#include "../AST/ArrayTransformer.h"
#include "../STPManager/STPManager.h"
#include "../simplifier/bvsolver.h"
#include "../simplifier/simplifier.h"
#include "../to-sat/ToSAT.h"
#include "../parser/let-funcs.h"
#include "../absrefine_counterexample/AbsRefine_CounterExample.h"

/********************************************************************
 *  This file gives the class description of the STP class          *
 ********************************************************************/

namespace BEEV
{
  class STP {
  public:
    /****************************************************************
     * Public Data:
     *  
     * Absolute toplevel class. No need to make data private
     ****************************************************************/
    STPMgr * bm;
    Simplifier * simp;
    BVSolver * bvsolver;
    ArrayTransformer * arrayTransformer;
    ToSAT * tosat;
    AbsRefine_CounterExample * Ctr_Example;

    /****************************************************************
     * Constructor and Destructor                                   *
     ****************************************************************/

    //Constructor
    STP(STPMgr* b,
	Simplifier* s,
	BVSolver* bsolv,
	ArrayTransformer * a,
	ToSAT * ts,
	AbsRefine_CounterExample * ce)    
    {
      bm   = b;
      simp = s;
      tosat = ts;
      bvsolver = bsolv;
      arrayTransformer = a;
      Ctr_Example = ce;
    }// End of constructor

    ~STP()
    {
      ClearAllTables();	  
    }

    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/

    // The absolute TopLevel function that invokes STP on the input
    // formula
    SOLVER_RETURN_TYPE TopLevelSTP(const ASTNode& inputasserts, 
				   const ASTNode& query)
    {      
      ASTNode q = bm->CreateNode(AND, 
				 inputasserts, 
				 bm->CreateNode(NOT, query));
      return TopLevelSTPAux(q);
    } //End of TopLevelSTP()    

    // Accepts query and returns the answer. if query is valid,
    // returns VALID, else returns INVALID. Automatically constructs
    // counterexample for invalid queries, and prints them upon
    // request.    
    SOLVER_RETURN_TYPE TopLevelSTPAux(const ASTNode& inputasserts_and_query);

    void ClearAllCaches(void);
    
    void ClearAllTables(void);    
  }; //End of Class STP
};//end of namespace
#endif

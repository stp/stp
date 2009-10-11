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


namespace BEEV
{
  class STP {
  public:
    BeevMgr * bm;
    Simplifier * simp;
    BVSolver * bvsolver;
    ArrayTransformer * arrayTransformer;
    ToSAT * tosat;
    AbsRefine_CounterExample * Ctr_Example;

    //Constructor
    STP(BeevMgr* b,
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

    SOLVER_RETURN_TYPE TopLevelSAT(const ASTNode& inputasserts, 
				   const ASTNode& query)
    {      
      ASTNode q = bm->CreateNode(AND, 
				 inputasserts, 
				 bm->CreateNode(NOT, query));
      return TopLevelSATAux(q);
    } //End of TopLevelSAT()    

    // Accepts query and returns the answer. if query is valid,
    // returns VALID, else returns INVALID. Automatically constructs
    // counterexample for invalid queries, and prints them upon
    // request.    
    SOLVER_RETURN_TYPE TopLevelSATAux(const ASTNode& inputasserts_and_query);
  }; //End of Class STP
};//end of namespace
#endif

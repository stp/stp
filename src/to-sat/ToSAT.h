// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef TOSAT_H
#define TOSAT_H
#include <cmath>

#include "ToCNF.h"

#include "../AST/AST.h"
#include "../sat/sat.h"
#include "../AST/RunTimes.h"
#include "../simplifier/bvsolver.h"
#include "../STPManager/STPManager.h"
#include "../simplifier/simplifier.h"

namespace BEEV
{
  class ToSAT {
  private:
    /****************************************************************
     * Private Typedefs and Data                                    *
     ****************************************************************/

    // MAP: This is a map from ASTNodes to MINISAT::Vars.
    //
    // The map is populated while ASTclauses are read from the AST
    // ClauseList returned by CNF converter. For every new boolean
    // variable in ASTClause a new MINISAT::Var is created (these vars
    // typedefs for ints)
    typedef HASHMAP<
    ASTNode, 
    MINISAT::Var, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTtoSATMap;
    ASTtoSATMap _ASTNode_to_SATVar_Map;

    // MAP: This is a map from MINISAT::Vars to ASTNodes
    //
    // Reverse map used in building counterexamples. MINISAT returns a
    // model in terms of MINISAT Vars, and this map helps us convert
    // it to a model over ASTNode variables.
    vector<ASTNode> _SATVar_to_AST_Vector;

    // Ptr to STPManager
    STPMgr * bm;

#if 0
    // Memo table to check the functioning of bitblaster and CNF
    // converter
    ASTNodeMap CheckBBandCNFMemo;

    // Map from formulas to representative literals, for debugging.
    ASTNodeMap RepLitMap;
#endif

    ASTNode ASTTrue, ASTFalse, ASTUndefined;
    
    /****************************************************************
     * Private Member Functions                                     *
     ****************************************************************/

    //looksup a MINISAT var from the minisat-var memo-table. if none
    //exists, then creates one.  Treat the result as const.
    MINISAT::Var LookupOrCreateSATVar(MINISAT::Solver& S, 
                                      const ASTNode& n);

#if 0
    // Evaluates bitblasted formula in satisfying assignment
    ASTNode CheckBBandCNF(MINISAT::Solver& newS, ASTNode form);
    ASTNode CheckBBandCNF_int(MINISAT::Solver& newS, ASTNode form);


    // Looks up truth value of ASTNode SYMBOL in MINISAT satisfying
    // assignment.  Returns ASTTrue if true, ASTFalse if false or
    // undefined.

    ASTNode SymbolTruthValue(MINISAT::Solver &newS, ASTNode form);
#endif

    //Iteratively goes through the Clause Buckets, and calls
      //toSATandSolve()
    bool CallSAT_On_ClauseBuckets(MINISAT::Solver& SatSolver,
                                    ClauseBuckets * cb);

      // Converts the clause to SAT and calls SAT solver
      bool toSATandSolve(MINISAT::Solver& S,
                         ClauseList& cll,
  		       bool add_xor_clauses=false,
  		       bool enable_clausal_abstraction=false);


  public:
    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/
    
    // Constructor
    ToSAT(STPMgr * bm) :
      bm(bm)
#if 0
      ,CheckBBandCNFMemo()
#endif
    {
      ASTTrue      = bm->CreateNode(TRUE);
      ASTFalse     = bm->CreateNode(FALSE);
      ASTUndefined = bm->CreateNode(UNDEFINED);
    }

    // Bitblasts, CNF conversion and calls toSATandSolve()
    bool CallSAT(MINISAT::Solver& SatSolver, 
                 const ASTNode& input);

    //print the STP solver output
    void PrintOutput(SOLVER_RETURN_TYPE ret);

    ASTNode SATVar_to_ASTMap(int i)
    {
      return _SATVar_to_AST_Vector[i];
    }

    void ClearAllTables(void)
    {
      _ASTNode_to_SATVar_Map.clear();
      _SATVar_to_AST_Vector.clear();
    }

    ~ToSAT()
    {
       ClearAllTables();
#if 0
      RepLitMap.clear();
      CheckBBandCNFMemo.clear();
#endif
    }
  }; //end of class ToSAT
}; //end of namespace

#endif

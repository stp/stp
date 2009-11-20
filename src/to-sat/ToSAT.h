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

#include "BitBlast.h"
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

    // Ptr to Simplifier
    Simplifier * simp;

    // Memo table to check the functioning of bitblaster and CNF
    // converter
    ASTNodeMap CheckBBandCNFMemo;

    // Map from formulas to representative literals, for debugging.
    ASTNodeMap RepLitMap;

    ASTNode ASTTrue, ASTFalse, ASTUndefined;
    
    /****************************************************************
     * Private Member Functions                                     *
     ****************************************************************/

    //looksup a MINISAT var from the minisat-var memo-table. if none
    //exists, then creates one.  Treat the result as const.
    MINISAT::Var LookupOrCreateSATVar(MINISAT::Solver& S, 
                                      const ASTNode& n);

    // Evaluates bitblasted formula in satisfying assignment
    ASTNode CheckBBandCNF(MINISAT::Solver& newS, ASTNode form);
    ASTNode CheckBBandCNF_int(MINISAT::Solver& newS, ASTNode form);

    // Looks up truth value of ASTNode SYMBOL in MINISAT satisfying
    // assignment.  Returns ASTTrue if true, ASTFalse if false or
    // undefined.
    ASTNode SymbolTruthValue(MINISAT::Solver &newS, ASTNode form);

  public:
    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/
    
    // Constructor
    ToSAT(STPMgr * bm, Simplifier * s) :
      bm(bm), 
      simp(s),
      CheckBBandCNFMemo()
    {
      ASTTrue      = bm->CreateNode(TRUE);
      ASTFalse     = bm->CreateNode(FALSE);
      ASTUndefined = bm->CreateNode(UNDEFINED);
    }

    // Bitblasts, CNF conversion and calls toSATandSolve()
    bool CallSAT(MINISAT::Solver& SatSolver, 
                 const ASTNode& modified_input,
                 const ASTNode& original_input);

    //Iteratively goes through the Clause Buckets, and calls
    //toSATandSolve()
    bool CallSAT_On_ClauseBuckets(MINISAT::Solver& SatSolver,
                                  ClauseBuckets * cb);
    
    // Converts the clause to SAT and calls SAT solver
    bool toSATandSolve(MINISAT::Solver& S,
                       ClauseList& cll, bool add_xor_clauses=false);
    
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
      _ASTNode_to_SATVar_Map.clear();
      RepLitMap.clear();
      CheckBBandCNFMemo.clear();
      _SATVar_to_AST_Vector.clear();
    }
  }; //end of class ToSAT
}; //end of namespace

#endif

// -*- c++ -*-
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

#ifndef TOSAT_H
#define TOSAT_H

#include "ToCNF.h"

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/ToSATBase.h"

namespace stp
{
class ToSAT : public ToSATBase
{

private:
  /****************************************************************
   * Private Typedefs and Data                                    *
   ****************************************************************/

  // MAP: This is a map from ASTNodes to Variables(uint32_t-s).
  //
  // The map is populated while ASTclauses are read from the AST
  // ClauseList returned by CNF converter. For every new boolean
  // variable in ASTClause a new variable is created
  typedef hash_map<ASTNode, uint32_t, ASTNode::ASTNodeHasher,
                   ASTNode::ASTNodeEqual> ASTtoSATMap;
  ASTtoSATMap _ASTNode_to_SATVar_Map;

  // MAP: This is a map from  ASTNodes to variables(uint32_t-s) for SYMBOLS>
  //
  // Reverse map used in building counterexamples. MINISAT returns a
  // model in terms of MINISAT Vars, and this map helps us convert
  // it to a model over ASTNode variables.
  ASTNodeToSATVar SATVar_to_SymbolIndex;

  int CNFFileNameCounter;
  int benchFileNameCounter;

  /****************************************************************
   * Private Member Functions                                     *
   ****************************************************************/

  // looksup a MINISAT var from the minisat-var memo-table. if none
  // exists, then creates one.  Treat the result as const.
  uint32_t LookupOrCreateSATVar(SATSolver& S, const ASTNode& n);

  // Iteratively goes through the Clause Buckets, and calls
  // toSATandSolve()
  bool CallSAT_On_ClauseBuckets(SATSolver& SatSolver, ClauseBuckets* cb,
                                CNFMgr*& cm);

  // Converts the clause to SAT and calls SAT solver
  bool toSATandSolve(SATSolver& S, ClauseList& cll, bool final, CNFMgr*& cm,
                     bool add_xor_clauses = false,
                     bool enable_clausal_abstraction = false);

  ClauseBuckets* Sort_ClauseList_IntoBuckets(ClauseList* cl,
                                             int clause_bucket_size);

public:
  /****************************************************************
   * Public Member Functions                                      *
   ****************************************************************/

   
  ToSAT(STPMgr* bm) : ToSATBase(bm)
  {
    CNFFileNameCounter = 0;
    benchFileNameCounter = 0;
  }

  // Bitblasts, CNF conversion and calls toSATandSolve()
  bool CallSAT(SATSolver& SatSolver, const ASTNode& input, bool refinement);

  ASTNodeToSATVar& SATVar_to_SymbolIndexMap() { return SATVar_to_SymbolIndex; }

  void ClearAllTables(void)
  {
    _ASTNode_to_SATVar_Map.clear();
    SATVar_to_SymbolIndex.clear();
  }

  ~ToSAT() { ClearAllTables(); }
};
} // end of namespace

#endif

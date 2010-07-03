// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef TOSATAIG_H
#define TOSATAIG_H
#include <cmath>

#include "../AST/AST.h"
#include "../AST/RunTimes.h"
#include "../STPManager/STPManager.h"
#include "../BitBlaster.h"
#include "BBNodeManagerAIG.h"

namespace BEEV
{

  // NB You can't use this with abstraction refinement!!!
  class ToSATAIG : public ToSATBase
  {
  private:

    ASTNodeToSATVar nodeToSATVar;

    // don't assign or copy construct.
    ToSATAIG&  operator = (const ToSATAIG& other);
    ToSATAIG(const ToSATAIG& other);

  public:

    ToSATAIG(STPMgr * bm) :
      ToSATBase(bm)
    {
    }

    void
    ClearAllTables()
    {
      nodeToSATVar.clear();
    }

    // Used to read out the satisfiable answer.
    ASTNodeToSATVar&
    SATVar_to_SymbolIndexMap()
    {
      return nodeToSATVar;
    }

    // Can not be used with abstraction refinement.
    bool
    CallSAT(MINISAT::Solver& satSolver, const ASTNode& input)
    {
      BBNodeManagerAIG mgr;
      BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&mgr);
      set<BBNodeAIG> support;

      BBNodeAIG BBFormula = bb.BBForm(input, support);

      assert(support.size() ==0); // hot handled yet..
      assert(satSolver.nVars() ==0);

      Cnf_Dat_t* cnfData = NULL;

      mgr.toCNF(BBFormula, cnfData, nodeToSATVar);

      bm->GetRunTimes()->start(RunTimes::SendingToSAT);

      for (int i = 0; i < cnfData->nVars; i++)
        satSolver.newVar();

      MINISAT::vec<MINISAT::Lit> satSolverClause;
      for (int i = 0; i < cnfData->nClauses; i++)
        {
          satSolverClause.clear();
          for (int * pLit = cnfData->pClauses[i], *pStop = cnfData->pClauses[i
              + 1]; pLit < pStop; pLit++)
            {
              Var var = (*pLit) >> 1;
              assert(var < satSolver.nVars());
              MINISAT::Lit l(var, (*pLit) & 1);
              satSolverClause.push(l);
            }

          satSolver.addClause(satSolverClause);
          if (!satSolver.okay())
            break;
        }
      bm->GetRunTimes()->stop(RunTimes::SendingToSAT);

      if (bm->UserFlags.output_CNF_flag)
         Cnf_DataWriteIntoFile(cnfData, "output.cnf", 0);

      Cnf_ClearMemory();
      Cnf_DataFree(cnfData);

      bm->GetRunTimes()->start(RunTimes::SATSimplifying);
      if (!satSolver.simplify())
        {
        bm->GetRunTimes()->stop(RunTimes::SATSimplifying);
      return false;
        }
      bm->GetRunTimes()->stop(RunTimes::SATSimplifying);

      bm->GetRunTimes()->start(RunTimes::Solving);
      satSolver.solve();
      bm->GetRunTimes()->stop(RunTimes::Solving);

      if (bm->UserFlags.stats_flag)
        bm->PrintStats(satSolver);

      return satSolver.okay();
    }
  };
}

#endif

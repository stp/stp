#include "ToSATAIG.h"
#include "../../simplifier/constantBitP/ConstantBitPropagation.h"
#include "../../sat/sat.h"

namespace BEEV
{

    // Can not be used with abstraction refinement.
    bool
    ToSATAIG::CallSAT(MINISAT::Solver& satSolver, const ASTNode& input)
    {
      if (cb != NULL  && cb->isUnsatisfiable())
        return false;

      BBNodeManagerAIG mgr;
      BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&mgr,cb);

      bm->GetRunTimes()->start(RunTimes::BitBlasting);
      BBNodeAIG BBFormula = bb.BBForm(input);
      bm->GetRunTimes()->stop(RunTimes::BitBlasting);

      assert(satSolver.nVars() ==0);

      Cnf_Dat_t* cnfData = NULL;

      mgr.toCNF(BBFormula, cnfData, nodeToSATVar);

      // Free the memory in the AIGs.
      BBFormula = BBNodeAIG(); // null node
      mgr.stop();

      // make the result true, see if a contradiction arises.
      /*
      if (cb != NULL)
        {
        cb->setNodeToTrue(input);
        cb->propagate();
        if (cb->isUnsatisfiable())
          return false;
        }
      */

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
         Cnf_DataWriteIntoFile(cnfData, "output_0.cnf", 0);

      Cnf_ClearMemory();
      Cnf_DataFree(cnfData);

      // cryptominisat treats simplify() as protected.
#ifndef CRYPTOMINISAT2
      bm->GetRunTimes()->start(RunTimes::SATSimplifying);
      if (!satSolver.simplify())
        {
        bm->GetRunTimes()->stop(RunTimes::SATSimplifying);
        return false;
        }
      bm->GetRunTimes()->stop(RunTimes::SATSimplifying);
#endif



      bm->GetRunTimes()->start(RunTimes::Solving);
      satSolver.solve();
      bm->GetRunTimes()->stop(RunTimes::Solving);

      if (bm->UserFlags.stats_flag)
        bm->PrintStats(satSolver);

      return satSolver.okay();
    }

}

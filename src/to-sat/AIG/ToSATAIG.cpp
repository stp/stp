#include "ToSATAIG.h"
#include "../../simplifier/constantBitP/ConstantBitPropagation.h"

namespace BEEV
{

    // Can not be used with abstraction refinement.
    bool
    ToSATAIG::CallSAT(SATSolver& satSolver, const ASTNode& input)
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

      bm->GetRunTimes()->start(RunTimes::CNFConversion);
      mgr.toCNF(BBFormula, cnfData, nodeToSATVar,bm->UserFlags);
      bm->GetRunTimes()->stop(RunTimes::CNFConversion);

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

      //Clear out all the constant bit stuff before sending the SAT.
      if (cb != NULL)
    	  cb->clearTables();

      bm->GetRunTimes()->start(RunTimes::SendingToSAT);

      for (int i = 0; i < cnfData->nVars; i++)
        satSolver.newVar();

      SATSolver::vec_literals satSolverClause;
      for (int i = 0; i < cnfData->nClauses; i++)
        {
          satSolverClause.clear();
          for (int * pLit = cnfData->pClauses[i], *pStop = cnfData->pClauses[i
              + 1]; pLit < pStop; pLit++)
            {
              SATSolver::Var var = (*pLit) >> 1;
              assert(var < satSolver.nVars());
              Minisat::Lit l = SATSolver::mkLit(var, (*pLit) & 1);
              satSolverClause.push(l);
            }

          satSolver.addClause(satSolverClause);
          if (!satSolver.okay())
            break;
        }
      bm->GetRunTimes()->stop(RunTimes::SendingToSAT);

      if (bm->UserFlags.output_CNF_flag)
         Cnf_DataWriteIntoFile(cnfData, "output_0.cnf", 0);

      if (bm->UserFlags.output_bench_flag)
        cerr << "Converting to CNF via ABC's AIG package can't yet print out bench format" << endl;

      Cnf_ClearMemory();
      Cnf_DataFree(cnfData);

      if (bm->UserFlags.exit_after_CNF)
      {
        if (bm->UserFlags.quick_statistics_flag)
          bm->GetRunTimes()->print();
        exit(0);
      }

      bm->GetRunTimes()->start(RunTimes::Solving);
      satSolver.solve();
      bm->GetRunTimes()->stop(RunTimes::Solving);

      if(bm->UserFlags.stats_flag)
        satSolver.printStats();

      return satSolver.okay();
    }

}

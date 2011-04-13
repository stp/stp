#include "ToSATAIG.h"
#include "../../simplifier/constantBitP/ConstantBitPropagation.h"
#include "../../simplifier/simplifier.h"

namespace BEEV
{

    bool
    ToSATAIG::CallSAT(SATSolver& satSolver, const ASTNode& input, bool needAbsRef)
    {
      if (cb != NULL  && cb->isUnsatisfiable())
        return false;

      if (simp == NULL)
    	  simp = new Simplifier(bm);

      if (bb== NULL)
    	  bb =  new BitBlaster<BBNodeAIG, BBNodeManagerAIG>(&mgr,cb,simp,bm->defaultNodeFactory,&bm->UserFlags);

      bm->GetRunTimes()->start(RunTimes::BitBlasting);
      BBNodeAIG BBFormula = bb->BBForm(input);
      bm->GetRunTimes()->stop(RunTimes::BitBlasting);

      // It's not incremental.
      delete cb;
      cb = NULL;
      bb->cb = NULL;

      if (!needAbsRef)
      {
    	  delete simp;
    	  simp = NULL;

    	  delete bb;
    	  bb = NULL;

      }

      if (first)
    	  assert(satSolver.nVars() ==0);

      // Oddly the substitution map, which is necessary to output a model is kept in the simplifier.
      // The bitblaster should never enter anything into the solver map.
      //assert(simp.Return_SolverMap()->size() ==0);

      Cnf_Dat_t* cnfData = NULL;

      bm->GetRunTimes()->start(RunTimes::CNFConversion);
      if (first)
    	  {
    	  toCNF.toCNF(BBFormula, cnfData, nodeToSATVar,needAbsRef,mgr);
    	  }
      else
    	  {
    	  assert(needAbsRef);
    	  toCNF.toCNF_renter(BBFormula, cnfData, nodeToSATVar,mgr);
    	  }
      bm->GetRunTimes()->stop(RunTimes::CNFConversion);

      if (!needAbsRef)
      {
    	  // Free the memory in the AIGs.
    	  BBFormula = BBNodeAIG(); // null node
    	  mgr.stop();
      }

      if (bm->UserFlags.output_CNF_flag)
      {
  		stringstream fileName;
  		fileName << "output_" << CNFFileNameCounter++ << ".cnf";
    	Cnf_DataWriteIntoFile(cnfData, (char*)fileName.str().c_str(), 0);
      }
	  first = false;


      bm->GetRunTimes()->start(RunTimes::SendingToSAT);

      // Create a new sat variable for each of the variables in the CNF.
      int satV = satSolver.nVars();
      for (int i = 0; i < cnfData->nVars - satV ; i++)
        satSolver.newVar();


      SATSolver::vec_literals satSolverClause;
      for (int i = 0; i < cnfData->nClauses; i++)
        {
          satSolverClause.clear();
          for (int * pLit = cnfData->pClauses[i], *pStop = cnfData->pClauses[i
              + 1]; pLit < pStop; pLit++)
            {
              SATSolver::Var var = (*pLit) >> 1;
              if (!(var < satSolver.nVars()))
              {
            	  cerr << var << " ";
            	  cerr << satSolver.nVars();
            	  exit(1);
              }
              Minisat::Lit l = SATSolver::mkLit(var, (*pLit) & 1);
              satSolverClause.push(l);
            }

          satSolver.addClause(satSolverClause);
          if (!satSolver.okay())
            break;
        }
      bm->GetRunTimes()->stop(RunTimes::SendingToSAT);

      if (bm->UserFlags.output_bench_flag)
        cerr << "Converting to CNF via ABC's AIG package can't yet print out bench format" << endl;

      if (!needAbsRef)
      {
    	  Cnf_ClearMemory();
    	  Cnf_DataFree(cnfData);
    	  cnfData = NULL;
      }
      else
      {
    	  toCNF.setPrior(cnfData);
      }

      if (bm->UserFlags.exit_after_CNF)
      {
        if (bm->UserFlags.quick_statistics_flag)
          bm->GetRunTimes()->print();

        if (needAbsRef)
          cerr << "Warning: STP is exiting after generating the first CNF. But the CNF"
          "is probably partial which you probably don't want. You probably want to disable"
          "refinement with the \"-r\" command line option." << endl;

        exit(0);
      }

      bm->GetRunTimes()->start(RunTimes::Solving);
      satSolver.solve();
      bm->GetRunTimes()->stop(RunTimes::Solving);

      if(bm->UserFlags.stats_flag)
        satSolver.printStats();

      return satSolver.okay();
    }

    ToSATAIG::~ToSATAIG()
    {
    	delete bb;
    	delete simp;
    	ClearAllTables();
    }


}

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

       if (!first)
       {
    	   assert(input == ASTTrue);
    	   bm->GetRunTimes()->start(RunTimes::Solving);
           satSolver.solve();
           bm->GetRunTimes()->stop(RunTimes::Solving);

           if(bm->UserFlags.stats_flag)
             satSolver.printStats();

           return satSolver.okay();
       }

   	// Shortcut if known. This avoids calling the setup of the CNF generator.
   	// setup of the CNF generator is expensive. NB, these checks have to occur
    // after calling the sat solver (if it's not the first time.)
      if (input == ASTFalse )
   		return false;

      if (input == ASTTrue  )
   		return true;

  	  Simplifier simp(bm);

  	  BBNodeManagerAIG mgr;
  	  BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&mgr,cb,&simp,bm->defaultNodeFactory,&bm->UserFlags);

      bm->GetRunTimes()->start(RunTimes::BitBlasting);
      BBNodeAIG BBFormula = bb.BBForm(input);
      bm->GetRunTimes()->stop(RunTimes::BitBlasting);

      delete cb;
      cb = NULL;
      bb.cb = NULL;

   	  assert(satSolver.nVars() ==0);

   	  bm->GetRunTimes()->start(RunTimes::CNFConversion);
      Cnf_Dat_t* cnfData = NULL;
	  toCNF.toCNF(BBFormula, cnfData, nodeToSATVar,needAbsRef,mgr);
      bm->GetRunTimes()->stop(RunTimes::CNFConversion);

	  // Free the memory in the AIGs.
	  BBFormula = BBNodeAIG(); // null node
	  mgr.stop();

      if (bm->UserFlags.output_CNF_flag)
      {
  		stringstream fileName;
  		fileName << "output_" << CNFFileNameCounter++ << ".cnf";
    	Cnf_DataWriteIntoFile(cnfData, (char*)fileName.str().c_str(), 0);
      }
	  first = false;

      if (bm->UserFlags.exit_after_CNF)
            {
              if (bm->UserFlags.quick_statistics_flag)
                bm->GetRunTimes()->print();

              if (needAbsRef)
                cerr << "Warning: STP is exiting after generating the first CNF. But the CNF"
                " is probably partial which you probably don't want. You probably want to disable"
                " refinement with the \"-r\" command line option." << endl;

              exit(0);
            }

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
              assert ((var < satSolver.nVars()));
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

	  Cnf_ClearMemory();
	  Cnf_DataFree(cnfData);
	  cnfData = NULL;

	  // Minisat doesn't, but simplifying minisat and cryptominsat eliminate variables during their
	  // simplification phases. The problem is that we may later add clauses in that refer to those
	  // simplified-away variables. Here we mark them as frozen which prevents them from being removed.
	  for (ArrayTransformer::ArrType::iterator it = arrayTransformer->arrayToIndexToRead.begin(); it
                != arrayTransformer->arrayToIndexToRead.end(); it++)
            {
                ArrayTransformer::arrTypeMap& atm = it->second;

                for (ArrayTransformer::arrTypeMap::const_iterator it2 = atm.begin(); it2 != atm.end(); it2++)
                    {
                        const ArrayTransformer::ArrayRead& ar = it2->second;
                        ASTNodeToSATVar::iterator it = nodeToSATVar.find(ar.index_symbol);
                        if (it != nodeToSATVar.end())
                            {
                                vector<unsigned>& v = it->second;
                                for (int i=0; i < v.size(); i++)
                                    satSolver.setFrozen(v[i]);
                            }

                        it = nodeToSATVar.find(ar.symbol);
                        if (it != nodeToSATVar.end())
                            {
                                vector<unsigned>& v = it->second;
                                for (int i=0; i < v.size(); i++)
                                    satSolver.setFrozen(v[i]);
                            }
                    }
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
    	ClearAllTables();
    }
}

// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "STP.h"
#include "DifficultyScore.h"
#include "../to-sat/AIG/ToSATAIG.h"
#include "../simplifier/constantBitP/ConstantBitPropagation.h"
#include "../simplifier/constantBitP/NodeToFixedBitsMap.h"
#include "../sat/SimplifyingMinisat.h"
#include "../sat/MinisatCore.h"
#include "../sat/CryptoMinisat.h"
#include "../simplifier/RemoveUnconstrained.h"
#include "../simplifier/FindPureLiterals.h"
#include "../simplifier/EstablishIntervals.h"
#include "../simplifier/UseITEContext.h"
#include "../simplifier/AIGSimplifyPropositionalCore.h"
#include <memory>

namespace BEEV {

   // The absolute TopLevel function that invokes STP on the input
    // formula
  SOLVER_RETURN_TYPE STP::TopLevelSTP(const ASTNode& inputasserts, 
				      const ASTNode& query)
  {      
    ASTNode original_input = bm->CreateNode(AND, 
					    inputasserts, 
					    bm->CreateNode(NOT, query));
    
    //solver instantiated here
//#if defined CRYPTOMINISAT2
    //MINISAT::Solver NewSolver;

    //if(bm->UserFlags.print_cnf_flag)
      //{
	//NewSolver.needLibraryCNFFile(bm->UserFlags.cnf_dump_filename);
      //}
//#endif


    SATSolver *newS;
    if (bm->UserFlags.solver_to_use == UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER)
		newS = new SimplifyingMinisat();
    else if (bm->UserFlags.solver_to_use == UserDefinedFlags::CRYPTOMINISAT_SOLVER)
                    newS = new CryptoMinisat();
    else
      newS = new MinisatCore<Minisat::Solver>();



    SATSolver& NewSolver = *newS;


    if(bm->UserFlags.stats_flag)
      {
	NewSolver.setVerbosity(1);
      }
    
	SOLVER_RETURN_TYPE result;
    if(bm->UserFlags.num_absrefine_flag)
      {
     result =  UserGuided_AbsRefine(NewSolver,
				    original_input);
      }
    else 
      {
	result = TopLevelSTPAux(NewSolver,
			      original_input, original_input);
      }

    delete newS;

    return result;

  } //End of TopLevelSTP()
  

  // These transformations should never increase the size of the DAG.
  ASTNode STP::sizeReducing(ASTNode simplified_solved_InputToSAT, BVSolver* bvSolver)
  {
	    if (bm->UserFlags.isSet("enable-unconstrained","1"))
		{
		  // Remove unconstrained.
		  RemoveUnconstrained r1(*bm);
		  simplified_solved_InputToSAT = r1.topLevel(simplified_solved_InputToSAT, simp);
		  bm->ASTNodeStats("After Removing Unconstrained: ", simplified_solved_InputToSAT);
		}

	    if (bm->UserFlags.isSet("use-intervals","1"))
	    {
	      EstablishIntervals intervals(*bm);
	      simplified_solved_InputToSAT = intervals.topLevel_unsignedIntervals(simplified_solved_InputToSAT );
	      bm->ASTNodeStats("After Establishing Intervals: ", simplified_solved_InputToSAT);
	    }

	    if (bm->UserFlags.bitConstantProp_flag)
		{
		  bm->GetRunTimes()->start(RunTimes::ConstantBitPropagation);
		  SimplifyingNodeFactory nf(*(bm->hashingNodeFactory), *bm);
		  simplifier::constantBitP::ConstantBitPropagation cb(simp, &nf,simplified_solved_InputToSAT);
		  simplified_solved_InputToSAT = cb.topLevelBothWays(simplified_solved_InputToSAT,false);

		  bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);

		  if (cb.isUnsatisfiable())
			simplified_solved_InputToSAT = bm->ASTFalse;

		  bm->ASTNodeStats("After Constant Bit Propagation begins: ",
			  simplified_solved_InputToSAT);
		}

		int initialSize = simp->Return_SolverMap()->size();
        simplified_solved_InputToSAT = simp->CreateSubstitutionMap(simplified_solved_InputToSAT, arrayTransformer);
		if (initialSize != simp->Return_SolverMap()->size())
		{
			simplified_solved_InputToSAT = simp->applySubstitutionMap(simplified_solved_InputToSAT);
			simp->haveAppliedSubstitutionMap();
		    bm->ASTNodeStats("After Propagating Equalities: ", simplified_solved_InputToSAT);
		}

	    // Find pure literals.
		if (bm->UserFlags.isSet("pure-literals","1"))
		{
		  FindPureLiterals fpl;
		  bool changed = fpl.topLevel(simplified_solved_InputToSAT, simp,bm);
		  if (changed)
			{
			  simplified_solved_InputToSAT  = simp->applySubstitutionMap(simplified_solved_InputToSAT);
			  simp->haveAppliedSubstitutionMap();
			  bm->ASTNodeStats("After Pure Literals: ",
							   simplified_solved_InputToSAT);
			}
		}

        if(bm->UserFlags.wordlevel_solve_flag && bm->UserFlags.optimize_flag)
          {
            simplified_solved_InputToSAT =
              bvSolver->TopLevelBVSolve(simplified_solved_InputToSAT,false);
            bm->ASTNodeStats("after solving: ", simplified_solved_InputToSAT);
          }

	   return simplified_solved_InputToSAT;
  }

  //Acceps a query, calls the SAT solver and generates Valid/InValid.
  //if returned 0 then input is INVALID if returned 1 then input is
  //VALID if returned 2 then UNDECIDED
  SOLVER_RETURN_TYPE STP::TopLevelSTPAux(SATSolver& NewSolver,
					 const ASTNode& modified_input,
					 const ASTNode& original_input)
  {


	ASTNode inputToSAT = modified_input;
    ASTNode orig_input = original_input;
    bm->ASTNodeStats("input asserts and query: ", inputToSAT);

    ASTNode simplified_solved_InputToSAT = inputToSAT;
    const bool arrayops = containsArrayOps(original_input);

    DifficultyScore difficulty;
    long initial_difficulty_score = difficulty.score(original_input);
    if (bm->UserFlags.stats_flag)
    	cerr << "Difficulty Initially:" << initial_difficulty_score << endl;

    // A heap object so I can easily control its lifetime.
    BVSolver* bvSolver = new BVSolver(bm,simp);

    simplified_solved_InputToSAT = sizeReducing(inputToSAT,bvSolver);
    //simplified_solved_InputToSAT = sizeReducing(simplified_solved_InputToSAT,bvSolver);

    initial_difficulty_score = difficulty.score(simplified_solved_InputToSAT);
    if (bm->UserFlags.stats_flag)
    	cout << "Difficulty After Size reducing:" << initial_difficulty_score << endl;

    // Copy the solver map incase we need to revert.
    ASTNodeMap initialSolverMap;
    if (!arrayops) // we don't revert for Array problems yet, so don't copy it.
    	{
    	initialSolverMap.insert(simp->Return_SolverMap()->begin(), simp->Return_SolverMap()->end());
    	}
    ASTNode toRevertTo = simplified_solved_InputToSAT;

    //round of substitution, solving, and simplification. ensures that
    //DAG is minimized as much as possibly, and ideally should
    //garuntee that all liketerms in BVPLUSes have been combined.
    bm->SimplifyWrites_InPlace_Flag = false;
    bm->Begin_RemoveWrites = false;
    bm->start_abstracting = false;
    bm->TermsAlreadySeenMap_Clear();
    do
      {
        inputToSAT = simplified_solved_InputToSAT;

        if(bm->UserFlags.optimize_flag) 
          {
            int initialSize = simp->Return_SolverMap()->size();

            simplified_solved_InputToSAT = 
            	simp->CreateSubstitutionMap(simplified_solved_InputToSAT, arrayTransformer);

            // Imagine:
			// The simplifier simplifies (0 + T) to T
			// Then bvsolve introduces (0 + T)
			// Then CreateSubstitutionMap decides T maps to a constant, but leaving another (0+T).
			// When we go to simplify (0 + T) will still be in the simplify cache, so will be mapped to T.
			// But it shouldn't be T, it should be a constant.
			// Applying the substitution map fixes this case.
            //
			if (initialSize != simp->Return_SolverMap()->size())
			{
				simplified_solved_InputToSAT = simp->applySubstitutionMap(simplified_solved_InputToSAT);
				simp->haveAppliedSubstitutionMap();
			}

            bm->ASTNodeStats("after pure substitution: ", 
                             simplified_solved_InputToSAT);

            simplified_solved_InputToSAT = 
              simp->SimplifyFormula_TopLevel(simplified_solved_InputToSAT, 
                                             false);

            bm->ASTNodeStats("after simplification: ", 
                             simplified_solved_InputToSAT);
          }

        if(bm->UserFlags.wordlevel_solve_flag && bm->UserFlags.optimize_flag)
          {
            simplified_solved_InputToSAT = 
              bvSolver->TopLevelBVSolve(simplified_solved_InputToSAT);
            bm->ASTNodeStats("after solving: ", simplified_solved_InputToSAT);
          }
      } 
    while (inputToSAT != simplified_solved_InputToSAT);

    if (bm->UserFlags.bitConstantProp_flag)
      {
        bm->GetRunTimes()->start(RunTimes::ConstantBitPropagation);
        SimplifyingNodeFactory nf(*(bm->hashingNodeFactory), *bm);
        simplifier::constantBitP::ConstantBitPropagation cb(simp, &nf,simplified_solved_InputToSAT);
        simplified_solved_InputToSAT = cb.topLevelBothWays(simplified_solved_InputToSAT);

        bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);

        if (cb.isUnsatisfiable())
          simplified_solved_InputToSAT = bm->ASTFalse;

        bm->ASTNodeStats("After Constant Bit Propagation begins: ",
            simplified_solved_InputToSAT);
      }

    if (bm->UserFlags.isSet("use-intervals","1"))
    {
      EstablishIntervals intervals(*bm);
      simplified_solved_InputToSAT = intervals.topLevel_unsignedIntervals(simplified_solved_InputToSAT );
      bm->ASTNodeStats("After Establishing Intervals: ",
                       simplified_solved_InputToSAT);
    }

    // Find pure literals.
        if (bm->UserFlags.isSet("pure-literals","1"))
        {
          FindPureLiterals fpl;
          bool changed = fpl.topLevel(simplified_solved_InputToSAT, simp,bm);
          if (changed)
            {
              simplified_solved_InputToSAT  = simp->applySubstitutionMap(simplified_solved_InputToSAT);
              simp->haveAppliedSubstitutionMap();
              bm->ASTNodeStats("After Pure Literals: ",
                               simplified_solved_InputToSAT);
            }
        }

        // Simplify using Ite context
        if (bm->UserFlags.optimize_flag &&  bm->UserFlags.isSet("ite-context","1"))
        {
          UseITEContext iteC(bm);
          simplified_solved_InputToSAT  = iteC.topLevel(simplified_solved_InputToSAT);
          bm->ASTNodeStats("After ITE Context: ",
                           simplified_solved_InputToSAT);
        }

        if (bm->UserFlags.isSet("aig-core-simplify","0"))
        {
        	AIGSimplifyPropositionalCore aigRR(bm);
        	simplified_solved_InputToSAT = aigRR.topLevel(simplified_solved_InputToSAT);
            bm->ASTNodeStats("After AIG Core: ",
                             simplified_solved_InputToSAT);
        }


    bm->ASTNodeStats("Before SimplifyWrites_Inplace begins: ", 
                     simplified_solved_InputToSAT);

    bm->SimplifyWrites_InPlace_Flag = true;    
    bm->Begin_RemoveWrites = false;
    bm->start_abstracting = false;
    bm->TermsAlreadySeenMap_Clear();
    do
    {
    	inputToSAT = simplified_solved_InputToSAT;

        if(bm->UserFlags.optimize_flag) 
          {
        	int initialSize = simp->Return_SolverMap()->size();

        	simplified_solved_InputToSAT =
            	simp->CreateSubstitutionMap(simplified_solved_InputToSAT, arrayTransformer);

			if (initialSize != simp->Return_SolverMap()->size())
			{
				simplified_solved_InputToSAT = simp->applySubstitutionMap(simplified_solved_InputToSAT);
				simp->haveAppliedSubstitutionMap();
			}

            bm->ASTNodeStats("after pure substitution: ",
                             simplified_solved_InputToSAT);

            simplified_solved_InputToSAT =
              simp->SimplifyFormula_TopLevel(simplified_solved_InputToSAT, 
                                             false);
            bm->ASTNodeStats("after simplification: ", 
                             simplified_solved_InputToSAT);
          }

        // The word level solver uses the simplifier to apply the rewrites it makes,
        // without optimisations enabled. It will enter infinite loops on some input.
        // Instead it could use the apply function of the substitution map, but it
        // doesn't yet...
        if(bm->UserFlags.wordlevel_solve_flag && bm->UserFlags.optimize_flag)
          {
            simplified_solved_InputToSAT = 
              bvSolver->TopLevelBVSolve(simplified_solved_InputToSAT);
            bm->ASTNodeStats("after solving: ", simplified_solved_InputToSAT);
          }
    } while (inputToSAT != simplified_solved_InputToSAT);

    bm->ASTNodeStats("After SimplifyWrites_Inplace: ", 
                     simplified_solved_InputToSAT);

    if (bm->UserFlags.isSet("enable-unconstrained","1"))
      {
        // Remove unconstrained.
        RemoveUnconstrained r(*bm);
        simplified_solved_InputToSAT = r.topLevel(simplified_solved_InputToSAT, simp);
        bm->ASTNodeStats("After Unconstrained Remove begins: ",
                simplified_solved_InputToSAT);
      }


    bm->TermsAlreadySeenMap_Clear();

    bm->start_abstracting = false;
    bm->SimplifyWrites_InPlace_Flag = false;
    bm->Begin_RemoveWrites = false;


    long final_difficulty_score = difficulty.score(simplified_solved_InputToSAT);
    if (bm->UserFlags.stats_flag)
    {
    	cerr << "Initial Difficulty Score:" << initial_difficulty_score <<endl;
    	cerr << "Final Difficulty Score:" << final_difficulty_score <<endl;
    }


    bool optimize_enabled = bm->UserFlags.optimize_flag;
    if (final_difficulty_score > 1.1 *initial_difficulty_score  && !arrayops && bm->UserFlags.isSet("difficulty-reversion","1"))
    {
    	// If the simplified problem is harder, than the
    	// initial problem we revert back to the initial
    	// problem.

    	if (bm->UserFlags.stats_flag)
    		cerr << "simplification made the problem harder, reverting."<<endl;
    	simplified_solved_InputToSAT = toRevertTo;

    	// I do this to clear the substitution/solver map.
    	// Not sure what would happen if it contained simplifications
    	// that haven't been applied.
    	simp->ClearAllTables();

    	simp->Return_SolverMap()->insert(initialSolverMap.begin(), initialSolverMap.end());
    	initialSolverMap.clear();


    	// The arrayTransformer calls simplify. We don't want
    	// it to put back in all the bad simplifications.
    	bm->UserFlags.optimize_flag = false;
    }

    simplified_solved_InputToSAT =
      arrayTransformer->TransformFormula_TopLevel(simplified_solved_InputToSAT);
    bm->ASTNodeStats("after transformation: ", simplified_solved_InputToSAT);
    bm->TermsAlreadySeenMap_Clear();

    bm->UserFlags.optimize_flag = optimize_enabled;

    SOLVER_RETURN_TYPE res;
    if (bm->UserFlags.arrayread_refinement_flag)
      {
        bm->counterexample_checking_during_refinement = true;
      }

    // We are about to solve. Clear out all the memory associated with caches
    // that we won't need again.
    simp->ClearCaches();
    simp->haveAppliedSubstitutionMap();
    bm->ClearAllTables();


    // Deleting it clears out all the buckets associated with hashmaps etc. too.
    delete bvSolver;
    bvSolver = NULL;

    if(bm->UserFlags.stats_flag)
    	simp->printCacheStatus();

    const bool useAIGToCNF = (!arrayops || !bm->UserFlags.arrayread_refinement_flag || bm->UserFlags.solver_to_use == UserDefinedFlags::MINISAT_SOLVER) && !bm->UserFlags.isSet("traditional-cnf","0");

    const bool maybeRefinement = arrayops && bm->UserFlags.arrayread_refinement_flag;

    simplifier::constantBitP::ConstantBitPropagation* cb = NULL;
    std::auto_ptr<simplifier::constantBitP::ConstantBitPropagation> cleaner;

    if (bm->UserFlags.bitConstantProp_flag)
    {
		bm->ASTNodeStats("Before Constant Bit Propagation begins: ",
			simplified_solved_InputToSAT);

    	bm->GetRunTimes()->start(RunTimes::ConstantBitPropagation);
    	cb = new simplifier::constantBitP::ConstantBitPropagation(simp, bm->defaultNodeFactory,simplified_solved_InputToSAT);
    	cleaner.reset(cb);
		bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);

		if (cb->isUnsatisfiable())
		   simplified_solved_InputToSAT = bm->ASTFalse;
    }

    ToSATAIG toSATAIG(bm,cb);

    ToSATBase* satBase =  useAIGToCNF? ((ToSAT*)&toSATAIG) : tosat;

    // If it doesn't contain array operations, use ABC's CNF generation.
    res =
      Ctr_Example->CallSAT_ResultCheck(NewSolver,
                                       simplified_solved_InputToSAT,
                                       orig_input,
                                       satBase,
                                       maybeRefinement);

    if (SOLVER_UNDECIDED != res)
      {
    	// If the aig converter knows that it is never going to be called again,
    	// it deletes the constant bit stuff before calling the SAT solver.
    	if (toSATAIG.cbIsDestructed())
    		cleaner.release();

    	CountersAndStats("print_func_stats", bm);
        return res;
      }

    assert(arrayops); // should only go to abstraction refinement if there are array ops.
    assert(bm->UserFlags.arrayread_refinement_flag); // Refinement must be enabled too.

    // Unfortunately how I implemented the incremental CNF generator in ABC means that
    // cryptominisat and simplifying minisat may simplify away variables that we later need.

    res = 
      Ctr_Example->SATBased_ArrayReadRefinement(NewSolver,
                                                simplified_solved_InputToSAT, 
                                                orig_input,
                                                satBase);
    if (SOLVER_UNDECIDED != res)
      {
    	if (toSATAIG.cbIsDestructed())
    		cleaner.release();

    	CountersAndStats("print_func_stats", bm);
        return res;
      }

    res = 
      Ctr_Example->SATBased_ArrayWriteRefinement(NewSolver, orig_input,satBase);
    if (SOLVER_UNDECIDED != res)
      {
    	if (toSATAIG.cbIsDestructed())
    		cleaner.release();

    	CountersAndStats("print_func_stats", bm);
        return res;
      }

    res = 
      Ctr_Example->SATBased_ArrayReadRefinement(NewSolver,
                                                simplified_solved_InputToSAT,
                                                orig_input,
                                                satBase);
    if (SOLVER_UNDECIDED != res)
      {
    	if (toSATAIG.cbIsDestructed())
    		cleaner.release();


    	CountersAndStats("print_func_stats", bm);
        return res;
      }

    if(!bm->UserFlags.num_absrefine_flag)
      {
    	FatalError("TopLevelSTPAux: reached the end without proper conclusion:"
		   "either a divide by zero in the input or a bug in STP");
	//bogus return to make the compiler shut up
	return SOLVER_ERROR;
      }
    else
      {
	return res;
      }
  } //End of TopLevelSTPAux

  //UserGuided abstraction refinement
  SOLVER_RETURN_TYPE
  STP::
  UserGuided_AbsRefine(SATSolver& NewSolver,
		       const ASTNode& original_input)
  {
    ASTVec v = bm->GetAsserts_WithKey(0);
    if(v.empty())
      {
	FatalError("UserGuided_AbsRefine: Something is seriously wrong."\
		   "The input set is empty");
      }
    ASTNode sureAddInput = 
      (v.size() == 1) ? v[0] : bm->CreateNode(AND, v); 

    SOLVER_RETURN_TYPE res = SOLVER_UNDECIDED;
    res = TopLevelSTPAux(NewSolver, sureAddInput, original_input);
    if(SOLVER_UNDECIDED != res)
      {
	return res;
      }
    
    //Do refinement here
    if(AND != original_input.GetKind())
      {
	FatalError("UserGuided_AbsRefine: The input must be an AND");
      }

    ASTVec RefineFormulasVec;
    ASTVec RemainingFormulasVec;
    ASTNode asttrue = bm->CreateNode(TRUE);
    ASTNode astfalse = bm->CreateNode(FALSE);
    for(int count=0; count < bm->UserFlags.num_absrefine; count++)
      {
	RemainingFormulasVec.clear();
	RemainingFormulasVec.push_back(asttrue);
	RefineFormulasVec.clear();	
	RefineFormulasVec.push_back(asttrue);
	ASTVec InputKids = original_input.GetChildren();
	for(ASTVec::iterator it = InputKids.begin(), itend = InputKids.end();
	    it!=itend;it++)
	  {
	    Ctr_Example->ClearComputeFormulaMap();
	    if(astfalse == Ctr_Example->ComputeFormulaUsingModel(*it))
	      {
		RefineFormulasVec.push_back(*it);
	      }
	    else
	      {
		RemainingFormulasVec.push_back(*it);
	      }
	  }
	ASTNode RefineFormulas =
	  (RefineFormulasVec.size() == 1) ?
	  RefineFormulasVec[0] : bm->CreateNode(AND, RefineFormulasVec);
	res = TopLevelSTPAux(NewSolver, RefineFormulas, original_input);
	if(SOLVER_UNDECIDED != res)
	  {
	    return res;
	  }
      }

    ASTNode RemainingFormulas = 
      (RemainingFormulasVec.size() == 1) ?
      RemainingFormulasVec[0] : bm->CreateNode(AND, RemainingFormulasVec);
    res = TopLevelSTPAux(NewSolver, RemainingFormulas, original_input);
    
    if(SOLVER_UNDECIDED != res)
      {
	return res;
      }
    
    FatalError("TopLevelSTPAux: reached the end without proper conclusion:"
	       "either a divide by zero in the input or a bug in STP");    
    return SOLVER_ERROR;
  } //End of UserGuided_AbsRefine()
}; //end of namespace

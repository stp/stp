// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "STP.h"
#include "DifficultyScore.h"
#include "../to-sat/AIG/ToSATAIG.h"

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
#if defined CRYPTOMINISAT2
    MINISAT::Solver NewSolver;
#endif

#if defined CRYPTOMINISAT2
    if(bm->UserFlags.print_cnf_flag)
      {
	NewSolver.needLibraryCNFFile(bm->UserFlags.cnf_dump_filename);
      }
#endif

#if defined CORE
	MINISAT::Solver *newS;
    if (bm->UserFlags.solver_to_use == UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER)
		newS = new MINISAT::SimpSolver();
    else if (bm->UserFlags.solver_to_use == UserDefinedFlags::MINISAT_SOLVER)
		newS = new MINISAT::Solver();
    else
    	FatalError("unknown option");

    MINISAT::Solver& NewSolver = *newS;
#endif

    if(bm->UserFlags.stats_flag)
      {
	NewSolver.verbosity = 1;
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

#if defined CORE
    delete newS;
#endif

    return result;

  } //End of TopLevelSTP()
  
  //Acceps a query, calls the SAT solver and generates Valid/InValid.
  //if returned 0 then input is INVALID if returned 1 then input is
  //VALID if returned 2 then UNDECIDED
  SOLVER_RETURN_TYPE STP::TopLevelSTPAux(MINISAT::Solver& NewSolver,
					 const ASTNode& modified_input,
					 const ASTNode& original_input)
  {
    ASTNode inputToSAT = modified_input;
    ASTNode orig_input = original_input;
    bm->ASTNodeStats("input asserts and query: ", inputToSAT);

    ASTNode simplified_solved_InputToSAT = inputToSAT;

    long initial_difficulty_score = DifficultyScore::score(original_input);

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

            simplified_solved_InputToSAT = 
            	simp->CreateSubstitutionMap(simplified_solved_InputToSAT, arrayTransformer);

            //printf("##################################################\n");
            bm->ASTNodeStats("after pure substitution: ", 
                             simplified_solved_InputToSAT);


            simplified_solved_InputToSAT = 
              simp->SimplifyFormula_TopLevel(simplified_solved_InputToSAT, 
                                             false);

            bm->ASTNodeStats("after simplification: ", 
                             simplified_solved_InputToSAT);
          }

        if(bm->UserFlags.wordlevel_solve_flag)
          {
            simplified_solved_InputToSAT = 
              bvsolver->TopLevelBVSolve(simplified_solved_InputToSAT);
            bm->ASTNodeStats("after solving: ", simplified_solved_InputToSAT);
          }

      } 
    while (inputToSAT != simplified_solved_InputToSAT);

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
            simplified_solved_InputToSAT = 
            	simp->CreateSubstitutionMap(simplified_solved_InputToSAT, arrayTransformer);

            bm->ASTNodeStats("after pure substitution: ",
                             simplified_solved_InputToSAT);

            simplified_solved_InputToSAT = 
              simp->SimplifyFormula_TopLevel(simplified_solved_InputToSAT, 
                                             false);
            bm->ASTNodeStats("after simplification: ", 
                             simplified_solved_InputToSAT);
          }
        
        if(bm->UserFlags.wordlevel_solve_flag)
          {
            simplified_solved_InputToSAT = 
              bvsolver->TopLevelBVSolve(simplified_solved_InputToSAT);
            bm->ASTNodeStats("after solving: ", simplified_solved_InputToSAT);
          }
      } while (inputToSAT != simplified_solved_InputToSAT);
    
    bm->ASTNodeStats("After SimplifyWrites_Inplace: ", 
                     simplified_solved_InputToSAT);

    bm->start_abstracting = 
      (bm->UserFlags.arraywrite_refinement_flag) ? true : false;
    bm->SimplifyWrites_InPlace_Flag = false;
    bm->Begin_RemoveWrites = (bm->start_abstracting) ? false : true;
    if (bm->start_abstracting)
      {
        bm->ASTNodeStats("before abstraction round begins: ", 
                         simplified_solved_InputToSAT);
      }

    bm->TermsAlreadySeenMap_Clear();
    if (bm->start_abstracting)
      {
        bm->ASTNodeStats("After abstraction: ", simplified_solved_InputToSAT);
      }
    bm->start_abstracting = false;
    bm->SimplifyWrites_InPlace_Flag = false;
    bm->Begin_RemoveWrites = false;


    long final_difficulty_score = DifficultyScore::score(simplified_solved_InputToSAT);
    if (bm->UserFlags.stats_flag)
    {
    	cerr << "Initial Difficulty Score:" << initial_difficulty_score <<endl;
    	cerr << "Final Difficulty Score:" << final_difficulty_score <<endl;
    }

    const bool arrayops = containsArrayOps(original_input);
    bool optimize_enabled = bm->UserFlags.optimize_flag;
    if (final_difficulty_score > 2 *initial_difficulty_score  && !arrayops)
    {
    	// If the simplified problem is harder, than the
    	// initial problem we revert back to the initial
    	// problem.

    	if (bm->UserFlags.stats_flag)
    		cerr << "simplification made the problem harder, reverting."<<endl;
    	simplified_solved_InputToSAT = original_input;

    	// I do this to clear the substitution/solver map.
    	// Not sure what would happen if it contained simplifications
    	// that haven't been applied.
    	simp->ClearAllTables();

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

    if(bm->UserFlags.stats_flag)
    	simp->printCacheStatus();

    simp->ClearCaches();
    bm->ClearAllTables();
    // Deleting it clears out all the buckets associated with hashmaps etc. too.
    delete bvsolver;
    bvsolver = new BVSolver(bm,simp);

    {
    ToSATAIG toSATAIG(bm);

    // If it doesn't contain array operations, use ABC's CNF generation.
    res = 
      Ctr_Example->CallSAT_ResultCheck(NewSolver, 
                                       simplified_solved_InputToSAT, 
                                       orig_input,
                                       (arrayops ? ((ToSATBase*)tosat): ((ToSATBase*)&toSATAIG))
                                       );
    }

    if (SOLVER_UNDECIDED != res)
      {
        CountersAndStats("print_func_stats", bm);
        return res;
      }

    assert(arrayops); // should only go to abstraction refinement if there are array ops.

    // res = SATBased_AllFiniteLoops_Refinement(NewSolver, orig_input);
    //     if (SOLVER_UNDECIDED != res)
    //       {
    //  CountersAndStats("print_func_stats");
    //         return res;      
    //       }

    res = 
      Ctr_Example->SATBased_ArrayReadRefinement(NewSolver,
                                                simplified_solved_InputToSAT, 
                                                orig_input,
                                                tosat);
    if (SOLVER_UNDECIDED != res)
      {
        CountersAndStats("print_func_stats", bm);
        return res;
      }

    res = 
      Ctr_Example->SATBased_ArrayWriteRefinement(NewSolver, orig_input,tosat);
    if (SOLVER_UNDECIDED != res)
      {
        CountersAndStats("print_func_stats", bm);
        return res;
      }

    res = 
      Ctr_Example->SATBased_ArrayReadRefinement(NewSolver,
                                                simplified_solved_InputToSAT,
                                                orig_input,tosat);
    if (SOLVER_UNDECIDED != res)
      {
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
  UserGuided_AbsRefine(MINISAT::Solver& NewSolver,
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

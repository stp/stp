// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "STP.h"

namespace BEEV {

  //Acceps a query, calls the SAT solver and generates Valid/InValid.
  //if returned 0 then input is INVALID if returned 1 then input is
  //VALID if returned 2 then UNDECIDED
  SOLVER_RETURN_TYPE STP::TopLevelSTPAux(const ASTNode& inputasserts_and_query)
  {
    ASTNode inputToSAT = inputasserts_and_query;
    ASTNode orig_input = inputToSAT;
    bm->ASTNodeStats("input asserts and query: ", inputToSAT);

    ASTNode simplified_solved_InputToSAT = inputToSAT;
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
            bm->GetRunTimes()->start(RunTimes::CreateSubstitutionMap);
            simplified_solved_InputToSAT = 
              arrayTransformer->
	      CreateSubstitutionMap(simplified_solved_InputToSAT);

            bm->GetRunTimes()->stop(RunTimes::CreateSubstitutionMap);
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
            bm->GetRunTimes()->start(RunTimes::CreateSubstitutionMap);
            simplified_solved_InputToSAT = 
              arrayTransformer->
	      CreateSubstitutionMap(simplified_solved_InputToSAT);
            bm->GetRunTimes()->stop(RunTimes::CreateSubstitutionMap);
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

    simplified_solved_InputToSAT = 
      arrayTransformer->TransformFormula_TopLevel(simplified_solved_InputToSAT);
    bm->ASTNodeStats("after transformation: ", simplified_solved_InputToSAT);
    bm->TermsAlreadySeenMap_Clear();

    SOLVER_RETURN_TYPE res;
    
    //solver instantiated here
#ifdef CORE
    MINISAT::Solver newS;
#endif
#ifdef CRYPTOMINISAT
    MINISAT::Solver newS;
#endif
#ifdef SIMP
    MINISAT::SimpSolver newS;
#endif
#ifdef UNSOUND
    MINISAT::UnsoundSimpSolver newS;
#endif

    if (bm->UserFlags.arrayread_refinement_flag)
      {
        bm->counterexample_checking_during_refinement = true;
      }

    res = 
      Ctr_Example->CallSAT_ResultCheck(newS, 
                                       simplified_solved_InputToSAT, 
                                       orig_input);
    if (SOLVER_UNDECIDED != res)
      {
        CountersAndStats("print_func_stats", bm);
        return res;
      }

    // res = SATBased_AllFiniteLoops_Refinement(newS, orig_input);
    //     if (SOLVER_UNDECIDED != res)
    //       {
    //  CountersAndStats("print_func_stats");
    //         return res;      
    //       }

    res = 
      Ctr_Example->SATBased_ArrayReadRefinement(newS,
                                                simplified_solved_InputToSAT, 
                                                orig_input);
    if (SOLVER_UNDECIDED != res)
      {
        CountersAndStats("print_func_stats", bm);
        return res;
      }

    res = 
      Ctr_Example->SATBased_ArrayWriteRefinement(newS, orig_input);
    if (SOLVER_UNDECIDED != res)
      {
        CountersAndStats("print_func_stats", bm);
        return res;
      }

    res = 
      Ctr_Example->SATBased_ArrayReadRefinement(newS,
                                                simplified_solved_InputToSAT,
                                                orig_input);
    if (SOLVER_UNDECIDED != res)
      {
        CountersAndStats("print_func_stats", bm);
        return res;
      }

    FatalError("TopLevelSTPAux: reached the end without proper conclusion:"
               "either a divide by zero in the input or a bug in STP");
    //bogus return to make the compiler shut up
    return SOLVER_ERROR;
  } //End of TopLevelSTPAux
}; //end of namespace

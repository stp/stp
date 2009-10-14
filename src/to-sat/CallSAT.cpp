// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "ToSAT.h"

namespace BEEV
{
  //Call the SAT solver, and check the result before returning. This
  //can return one of 3 values, SOLVER_VALID, SOLVER_INVALID or
  //SOLVER_UNDECIDED
  bool ToSAT::CallSAT(MINISAT::Solver& SatSolver, 
                      const ASTNode& modified_input,
                      const ASTNode& original_input)
  {
    bm->GetRunTimes()->start(RunTimes::BitBlasting);
    BitBlaster BB(bm);
    ASTNode BBFormula = BB.BBForm(modified_input);
    bm->GetRunTimes()->stop(RunTimes::BitBlasting);

    CNFMgr* cm = new CNFMgr(bm);
    ClauseList* cl = cm->convertToCNF(BBFormula);
    if (bm->UserFlags.stats_flag)
      {
        cerr << "Number of clauses:" << cl->size() << endl;
      }
    //PrintClauseList(cout, *cl);
    bool sat = toSATandSolve(SatSolver, *cl);
    cm->DELETE(cl);
    delete cm;
    return sat;
  }
  
  //##################################################
  //##################################################

  /*******************************************************************
   * Helper Functions
   *******************************************************************/

  //This function prints the output of the STP solver
  void ToSAT::PrintOutput(SOLVER_RETURN_TYPE ret)
  {
    bool true_iff_valid = (SOLVER_VALID == ret);

    if (bm->UserFlags.print_output_flag)
      {
        if (bm->UserFlags.smtlib_parser_flag)
          {
            if (true_iff_valid && 
                (input_status == TO_BE_SATISFIABLE))
              {
                cerr << "Warning. Expected satisfiable,"\
		  " FOUND unsatisfiable" << endl;
              }
            else if (!true_iff_valid && 
                     (input_status == TO_BE_UNSATISFIABLE))
              {
                cerr << "Warning. Expected unsatisfiable,"\
		  " FOUND satisfiable" << endl;
              }
          }
      }

    if (true_iff_valid)
      {
        bm->ValidFlag = true;
        if (bm->UserFlags.print_output_flag)
          {
            if (bm->UserFlags.smtlib_parser_flag)
              cout << "unsat\n";
            else
              cout << "Valid.\n";
          }
      }
    else
      {
        bm->ValidFlag = false;
        if (bm->UserFlags.print_output_flag)
          {
            if (bm->UserFlags.smtlib_parser_flag)
              cout << "sat\n";
            else
              cout << "Invalid.\n";
          }
      }
  } //end of PrintOutput()
};//end of namespace

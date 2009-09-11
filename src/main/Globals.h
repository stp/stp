// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#ifndef GLOBALS_H
#define GLOBALS_H

#include <iostream>
#include <sstream>
#include <string>
#include <algorithm>
#include <ctime>
#include <unistd.h>
#include <signal.h>
#include <stdio.h>
#include <unistd.h>
#include <vector>

namespace MINISAT
{
	class Solver;
	typedef int Var;
}

namespace BEEV
{  
  class BeevMgr;
  class ASTNode;
  class ASTInternal;
  class ASTInterior;
  class ASTSymbol;
  class ASTBVConst;
  class BVSolver;

  //some global variables that are set through commandline options. it
  //is best that these variables remain global. Default values set
  //here
  //
  //collect statistics on certain functions
  extern bool stats_flag;
  
  //print DAG nodes
  extern bool print_nodes_flag;
  
  //run STP in optimized mode
  extern bool optimize_flag;
  
  //do sat refinement, i.e. underconstraint the problem, and feed to
  //SAT. if this works, great. else, add a set of suitable constraints
  //to re-constraint the problem correctly, and call SAT again, until
  //all constraints have been added.
  extern bool arrayread_refinement_flag;
  
  //switch to control write refinements
  extern bool arraywrite_refinement_flag;
  
  //check the counterexample against the original input to STP
  extern bool check_counterexample_flag;
  
  //construct the counterexample in terms of original variable based
  //on the counterexample returned by SAT solver
  extern bool construct_counterexample_flag;
  extern bool print_counterexample_flag;
  extern bool print_binary_flag;
  
  //Expands out the finite for-construct completely
  extern bool expand_finitefor_flag;

  //Determines the number of abstraction-refinement loop count for the
  //for-construct
  extern bool num_absrefine_flag;
  extern int num_absrefine;

  //if this option is true then print the way dawson wants using a
  //different printer. do not use this printer.
  extern bool print_arrayval_declaredorder_flag;
  
  //flag to decide whether to print "valid/invalid" or not
  extern bool print_output_flag;
  
  //print the variable order chosen by the sat solver while it is
  //solving.
  extern bool print_sat_varorder_flag;
  
  //turn on word level bitvector solver
  extern bool wordlevel_solve_flag;
  
  //XOR flattening optimizations.
  extern bool xor_flatten_flag;
  
  //this flag indicates that the BVSolver() succeeded
  extern bool toplevel_solved_flag;
  
  //print the input back
  extern bool print_STPinput_back_flag;
  
  //Flag to switch on the smtlib parser
  extern bool smtlib_parser_flag;

  extern bool division_by_zero_returns_one;

  enum inputStatus
    {
      NOT_DECLARED =0, // Not included in the input file / stream
      TO_BE_SATISFIABLE,
      TO_BE_UNSATISFIABLE,
      TO_BE_UNKNOWN // Specified in the input file as unknown.
    };
  extern enum inputStatus input_status;
  
  //return types for the GetType() function in ASTNode class
  enum types
    {
      BOOLEAN_TYPE = 0, BITVECTOR_TYPE, ARRAY_TYPE, UNKNOWN_TYPE
    };

  enum SOLVER_RETURN_TYPE 
    {
      SOLVER_INVALID=0, SOLVER_VALID=1, SOLVER_UNDECIDED=2, SOLVER_ERROR=-100
    };

  //Useful global variables. There are very few them
  extern BeevMgr * GlobalBeevMgr;

  //Empty vector
  extern std::vector<BEEV::ASTNode> _empty_ASTVec;

  //Some global vars for the Main function.
  extern const char * prog;
  extern int linenum;
  extern const char * usage;
  extern std::string helpstring;
  extern const std::string version;
}; //end of namespace BEEV

#endif

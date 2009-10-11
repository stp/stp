/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../STPManager/STP.h"

namespace BEEV
{
  //some global variables that are set through commandline options. it
  //is best that these variables remain global. Default values set
  //here
  //
  //collect statistics on certain functions
  bool stats_flag = false;
  
  //print DAG nodes
  bool print_nodes_flag = false;
  
  //run STP in optimized mode
  bool optimize_flag = true;
  
  //do sat refinement, i.e. underconstraint the problem, and feed to
  //SAT. if this works, great. else, add a set of suitable constraints
  //to re-constraint the problem correctly, and call SAT again, until
  //all constraints have been added.
  bool arrayread_refinement_flag = true;
  
  //flag to control write refinement
  bool arraywrite_refinement_flag = true;
  
  //check the counterexample against the original input to STP
  bool check_counterexample_flag = false;
  
  //construct the counterexample in terms of original variable based
  //on the counterexample returned by SAT solver
  bool construct_counterexample_flag = true;
  bool print_counterexample_flag = false;
  bool print_binary_flag = false;

  //Expands out the finite for-construct completely
  bool expand_finitefor_flag = false;

  //Determines the number of abstraction-refinement loop count for the
  //for-construct
  bool num_absrefine_flag = false;
  int num_absrefine = 0;


  //if this option is true then print the way dawson wants using a
  //different printer. do not use this printer.
  bool print_arrayval_declaredorder_flag = false;
  
  //flag to decide whether to print "valid/invalid" or not
  bool print_output_flag = false;
  
  //print the variable order chosen by the sat solver while it is
  //solving.
  bool print_sat_varorder_flag = false;
  
  //turn on word level bitvector solver
  bool wordlevel_solve_flag = true;
  
  //turn off XOR flattening
  bool xor_flatten_flag = false;
  
  //Flag to switch on the smtlib parser
  bool smtlib_parser_flag = false;
  
  //print the input back
  bool print_STPinput_back_flag = false;

  // If enabled. division, mod and remainder by zero will evaluate to
  // 1.
  bool division_by_zero_returns_one = false;

  bool quick_statistics_flag=false;
  
  enum inputStatus input_status = NOT_DECLARED;

  //global BEEVMGR for the parser. Use exclusively for parsing
  STP     * GlobalSTP;
  STPMgr  * ParserBM;

  void (*vc_error_hdlr)(const char* err_msg) = NULL;
  /** This is reusable empty vector, for representing empty children
      arrays */
  ASTVec _empty_ASTVec;

  //Some global vars for the Main function.
  const char * prog = "stp";
  int linenum  = 1;
  const char * usage = "Usage: %s [-option] [infile]\n";
  std::string helpstring = "\n\n";
}; //end of namespace BEEV

/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/
#ifndef UDEFFLAGS_H
#define UDEFFLAGS_H

#include <map>
#include <string>
#include <cassert>
#include <iostream>
#include <set>

namespace stp
{

/******************************************************************
 * Struct UserDefFlags:
 *
 * Some userdefined variables that are set through commandline
 * options.
 ******************************************************************/

struct UserDefinedFlags // not copyable
{
  UserDefinedFlags(UserDefinedFlags const&) = delete;
  UserDefinedFlags& operator=(UserDefinedFlags const&) = delete;

public:
  UserDefinedFlags()
  {}

  // collect statistics on certain functions
  bool stats_flag = false;

  //collect and delete objects via interface.
  bool cinterface_exprdelete_on_flag = true;

  int64_t timeout_max_conflicts =-1;

  // print DAG nodes
  bool print_nodes_flag = false;

  // the Simplifier functions (which might increase the size).
  bool optimize_flag = true;
  // turn on word level bitvector solver
  bool wordlevel_solve_flag =true;
  // Remove equalities.
  bool propagate_equalities = true;
  // Constant bit propagation enabled.
  bool bitConstantProp_flag = true;
  // AIG rewrites are turned on..
  bool enable_AIG_rewrites_flag = false;
  bool enable_unconstrained= true;
  bool enable_ite_context= true;
  bool enable_aig_core_simplify= false;
  bool enable_use_intervals= true;
  bool enable_pure_literals= true;
  bool enable_always_true = false;
  bool enable_bitblast_simplification = false;
  // If the bit-blaster discovers new constants, should the term simplifier be
  // re-run.
  bool simplify_during_BB_flag = false;
  // given a/b = c, propagates that c<=a even if b may be zero.
  bool cBitP_propagateForDivisionByZero = true;
  bool traditional_cnf = false;
  bool simple_cnf = false; // don't use the good AIG based CNF conversion.

    // eagerly write through the array's function congruence axioms.
  bool ackermannisation = false; 

  // check the counterexample against the original input to STP
  bool check_counterexample_flag = false;

  // construct the counterexample in terms of original variable based
  // on the counterexample returned by SAT solver
  bool print_counterexample_flag = false;
  bool print_binary_flag = false;

  //This is derived from other settings.
  bool construct_counterexample_flag = false;

  // if this option is true then print the way dawson wants using a
  // different printer. do not use this printer.
  bool print_arrayval_declaredorder_flag =false;

  // flag to decide whether to print "valid/invalid" or not
  bool print_output_flag = false;

  // print the input back
  bool print_STPinput_back_flag = false;
  bool print_STPinput_back_C_flag = false;
  bool print_STPinput_back_SMTLIB2_flag =false ;
  bool print_STPinput_back_SMTLIB1_flag =false;
  bool print_STPinput_back_CVC_flag=false;
  bool print_STPinput_back_dot_flag=false;
  bool print_STPinput_back_GDL_flag=false;
  
  bool array_difficulty_reversion = true;
  bool difficulty_reversion = true;


  // output flags
  bool output_CNF_flag = false;
  bool output_bench_flag = false;

  // Flag to switch on the smtlib parser
  bool smtlib1_parser_flag = false;
  bool smtlib2_parser_flag = false;

  bool division_by_zero_returns_one_flag = true;

  bool quick_statistics_flag = false;

  bool exit_after_CNF =false;

  // Available back-end SAT solvers.
  enum SATSolvers
  {
    MINISAT_SOLVER = 0,
    SIMPLIFYING_MINISAT_SOLVER,
    CRYPTOMINISAT5_SOLVER
  };

  #ifdef USE_CRYPTOMINISAT
    enum SATSolvers solver_to_use = CRYPTOMINISAT5_SOLVER;
  #else
    enum SATSolvers solver_to_use = MINISAT_SOLVER;
  #endif

  int num_solver_threads =1;

  bool get_print_output_at_all() const
  {
    return print_STPinput_back_flag || print_STPinput_back_C_flag ||
           print_STPinput_back_SMTLIB2_flag ||
           print_STPinput_back_SMTLIB1_flag || print_STPinput_back_CVC_flag ||
           print_STPinput_back_dot_flag || print_STPinput_back_GDL_flag;
  }

  void disableSimplifications()
  {
    optimize_flag = false;
    enable_unconstrained= false;
    bitConstantProp_flag = false;
    enable_use_intervals = false;
    enable_pure_literals = false;
    enable_always_true = false;
    enable_bitblast_simplification =false;
    wordlevel_solve_flag = false;
    propagate_equalities = false;
  }
};
} // end of namespace

#endif

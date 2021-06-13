/********************************************************************
 * AUTHORS: Vijay Ganesh, Andrew V. Jones
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

#include <cassert>
#include <iostream>
#include <map>
#include <set>
#include <string>

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
  // collect statistics on certain functions
  bool stats_flag;

  //collect and delete objects via interface.
  bool cinterface_exprdelete_on_flag;

  int64_t timeout_max_conflicts;

  int64_t timeout_max_time;

  // print DAG nodes
  bool print_nodes_flag;

  // the Simplifier functions (which might increase the size).
  bool optimize_flag;
  // turn on word level bitvector solver
  bool wordlevel_solve_flag;
  // Remove equalities.
  bool propagate_equalities;
  // Constant bit propagation enabled.
  bool bitConstantProp_flag;
  // AIG rewrites are turned on..
  bool enable_AIG_rewrites_flag;
  bool enable_unconstrained;
  bool enable_flatten = true;
  bool enable_ite_context;
  bool enable_aig_core_simplify;
  bool enable_use_intervals;
  bool enable_pure_literals;
  bool enable_always_true;
  bool enable_bitblast_simplification;
  // If the bit-blaster discovers new constants, should the term simplifier be
  // re-run.
  bool simplify_during_BB_flag;
  // given a/b = c, propagates that c<=a even if b may be zero.
  bool cBitP_propagateForDivisionByZero;
  bool traditional_cnf;
  bool simple_cnf; // don't use the good AIG based CNF conversion.

  // eagerly write through the array's function congruence axioms.
  bool ackermannisation;

  // check the counterexample against the original input to STP
  bool check_counterexample_flag;

  // construct the counterexample in terms of original variable based
  // on the counterexample returned by SAT solver
  bool print_counterexample_flag;
  bool print_binary_flag;

  //This is derived from other settings.
  bool construct_counterexample_flag;

  // if this option is true then print the way dawson wants using a
  // different printer. do not use this printer.
  bool print_arrayval_declaredorder_flag;

  // flag to decide whether to print "valid/invalid" or not
  bool print_output_flag;

  // print the input back
  bool print_STPinput_back_flag;
  bool print_STPinput_back_C_flag;
  bool print_STPinput_back_SMTLIB2_flag;
  bool print_STPinput_back_SMTLIB1_flag;
  bool print_STPinput_back_CVC_flag;
  bool print_STPinput_back_dot_flag;
  bool print_STPinput_back_GDL_flag;

  bool array_difficulty_reversion;
  bool difficulty_reversion;

  // output flags
  bool output_CNF_flag;
  bool output_bench_flag;

  // Flag to switch on the smtlib parser
  bool smtlib1_parser_flag;
  bool smtlib2_parser_flag;

  bool quick_statistics_flag;

  bool exit_after_CNF;

  int num_solver_threads;

  // Available back-end SAT solvers.
  enum SATSolvers
  {
    MINISAT_SOLVER = 0,
    SIMPLIFYING_MINISAT_SOLVER,
    CRYPTOMINISAT5_SOLVER,
    RISS_SOLVER
  };

  enum SATSolvers solver_to_use;

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
    enable_unconstrained = false;
    bitConstantProp_flag = false;
    enable_use_intervals = false;
    enable_pure_literals = false;
    enable_always_true = false;
    enable_bitblast_simplification = false;
    wordlevel_solve_flag = false;
    propagate_equalities = false;
    enable_flatten = false;
  }

  UserDefinedFlags()
  {
    stats_flag = false;
    cinterface_exprdelete_on_flag = true;
    timeout_max_conflicts = -1;
    timeout_max_time = -1; // seconds
    print_nodes_flag = false;
    optimize_flag = true;
    wordlevel_solve_flag = true;
    propagate_equalities = true;
    bitConstantProp_flag = true;
    enable_AIG_rewrites_flag = false;
    enable_unconstrained = true;
    enable_ite_context = true;
    enable_aig_core_simplify = false;
    enable_use_intervals = true;
    enable_pure_literals = true;
    enable_always_true = false;
    enable_bitblast_simplification = false;
    simplify_during_BB_flag = false;
    cBitP_propagateForDivisionByZero = true;
    traditional_cnf = false;
    simple_cnf = false;
    ackermannisation = false;
    check_counterexample_flag = false;
    print_counterexample_flag = false;
    print_binary_flag = false;
    construct_counterexample_flag = false;
    print_arrayval_declaredorder_flag = false;
    print_output_flag = false;
    print_STPinput_back_flag = false;
    print_STPinput_back_C_flag = false;
    print_STPinput_back_SMTLIB2_flag = false;
    print_STPinput_back_SMTLIB1_flag = false;
    print_STPinput_back_CVC_flag = false;
    print_STPinput_back_dot_flag = false;
    print_STPinput_back_GDL_flag = false;
    array_difficulty_reversion = true;
    difficulty_reversion = true;
    output_CNF_flag = false;
    output_bench_flag = false;
    smtlib1_parser_flag = false;
    smtlib2_parser_flag = false;
    quick_statistics_flag = false;
    exit_after_CNF = false;
    num_solver_threads = 1;
    enable_flatten = true;

#ifdef USE_CRYPTOMINISAT
    solver_to_use = CRYPTOMINISAT5_SOLVER;
#else
#ifdef USE_RISS
    solver_to_use = RISS_SOLVER;
#else
    solver_to_use = MINISAT_SOLVER;
#endif
#endif
  }
};
} // end of namespace

#endif

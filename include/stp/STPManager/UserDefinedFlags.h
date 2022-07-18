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
  /* Parsing options */
  bool smtlib1_parser_flag = false;
  bool smtlib2_parser_flag = false;

  /* collect and delete objects via interface. */
  bool cinterface_exprdelete_on_flag = true;

  /* Output details of how the solving went*/
  bool stats_flag = false;
  bool quick_statistics_flag = false;

  /* Control simplification */
  bool optimize_flag = true; // the Simplifier functions (which might increase the size).
  bool wordlevel_solve_flag = true;   // turn on word level bitvector solver
  bool propagate_equalities = true; // Remove equalities.
  bool bitConstantProp_flag = true; // Constant bit propagation enabled.
  bool enable_unconstrained = true;
  bool enable_flatten = false;
  bool enable_ite_context = true;
  bool enable_aig_core_simplify = false;
  bool enable_use_intervals = true;
  bool enable_pure_literals = true;
  bool enable_always_true = false;
  bool enable_split_extracts = true;
  bool enable_sharing_aware_rewriting = false;
  bool enable_merge_same = true;

  int64_t AIG_rewrites_iterations = 0; // Number of iterations of AIG rewrites.
  int64_t bitblast_simplification = 0;
  int64_t size_reducing_fixed_point = 1000000;
  

  bool simplify_to_constants_only = false;

  // given a/b = c, propagates that c<=a even if b may be zero.
  bool cBitP_propagateForDivisionByZero = true;

  bool array_difficulty_reversion = true;
  bool difficulty_reversion = true;


  // eagerly write through the array's function congruence axioms.
  bool ackermannisation = false;

  // construct the counterexample in terms of original variable based
  // on the counterexample returned by SAT solver
  bool print_counterexample_flag = false;
  bool print_binary_flag = false;

  // if this option is true then print the way dawson wants using a
  // different printer. do not use this printer.
  bool print_arrayval_declaredorder_flag = false;

  // flag to decide whether to print "valid/invalid" or not
  bool print_output_flag = false;

  // print the input back
  bool print_STPinput_back_flag = false;
  bool print_STPinput_back_C_flag = false;
  bool print_STPinput_back_SMTLIB2_flag = false;
  bool print_STPinput_back_SMTLIB1_flag = false;
  bool print_STPinput_back_CVC_flag = false;
  bool print_STPinput_back_dot_flag = false;
  bool print_STPinput_back_GDL_flag = false;

  bool print_nodes_flag = false;

  // output flags
  bool output_CNF_flag = false;
  bool output_bench_flag = false;

  /* Bitblasting options */

  // You can select these with any combination you want of true & false.
  bool division_variant_1 = true;
  bool division_variant_2 = true;
  bool division_variant_3 = true;
  bool adder_variant = true;
  bool bbbvle_variant =true;
  bool upper_multiplication_bound = false;
  bool bvplus_variant = true;
  bool conjoin_to_top = true;

  int64_t multiplication_variant = 7;

  // If the bit-blaster discovers new constants, should the term simplifier be
  // re-run.
  bool simplify_during_BB_flag = false;


  /* CNF Generation options */
  bool traditional_cnf = false;
  bool simple_cnf = false; // don't use the good AIG based CNF conversion.

  bool exit_after_CNF = false;

  /* SAT solving options */

  int64_t timeout_max_conflicts = -1;
  int num_solver_threads = 1;
  int64_t timeout_max_time = -1; // seconds

  // check the counterexample against the original input to STP
  bool check_counterexample_flag = false;
  //This is derived from other settings.
  bool construct_counterexample_flag = false;


  // Available back-end SAT solvers.
  enum SATSolvers
  {
    MINISAT_SOLVER = 0,
    SIMPLIFYING_MINISAT_SOLVER,
    CRYPTOMINISAT5_SOLVER,
    RISS_SOLVER,
    CADICAL_SOLVER
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
    wordlevel_solve_flag = false;
    propagate_equalities = false;
    enable_flatten = false;

    bitblast_simplification = 0;
  }

  void disableSizeIncreasingSimplifications()
  {
     simplify_to_constants_only = true;
     enable_ite_context = false;

     // Can't get bigger so we won't need to revert.
     array_difficulty_reversion = false;
     difficulty_reversion = false;
  }



  UserDefinedFlags()
  {

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

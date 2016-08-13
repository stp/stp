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
private:
  std::set<std::string> alreadyOutput;

public:
  // collect statistics on certain functions
  bool stats_flag;

  //collect and delete objects via interface.
  bool cinterface_exprdelete_on_flag;

  int64_t timeout_max_conflicts;

  // print DAG nodes
  bool print_nodes_flag;

  // run STP in optimized mode
  bool optimize_flag;

  // do sat refinement, i.e. underconstrain the problem, and feed to
  // SAT. if this works, great. else, add a set of suitable constraints
  // to re-constraint the problem correctly, and call SAT again, until
  // all constraints have been added.
  bool ackermannisation; // eagerly write through the array's function
                         // congruence axioms.


  // check the counterexample against the original input to STP
  bool check_counterexample_flag;

  // construct the counterexample in terms of original variable based
  // on the counterexample returned by SAT solver
  bool construct_counterexample_flag;
  bool print_counterexample_flag;
  bool print_binary_flag;

  // if this option is true then print the way dawson wants using a
  // different printer. do not use this printer.
  bool print_arrayval_declaredorder_flag;

  // flag to decide whether to print "valid/invalid" or not
  bool print_output_flag;

  // print the variable order chosen by the sat solver while it is
  // solving.
  bool print_sat_varorder_flag;

  // turn on word level bitvector solver
  bool wordlevel_solve_flag;

  bool propagate_equalities;

  // print the input back
  bool print_STPinput_back_flag;
  bool print_STPinput_back_C_flag;
  bool print_STPinput_back_SMTLIB2_flag;
  bool print_STPinput_back_SMTLIB1_flag;
  bool print_STPinput_back_CVC_flag;
  bool print_STPinput_back_dot_flag;
  bool print_STPinput_back_GDL_flag;
  bool get_print_output_at_all() const
  {
    return print_STPinput_back_flag || print_STPinput_back_C_flag ||
           print_STPinput_back_SMTLIB2_flag ||
           print_STPinput_back_SMTLIB1_flag || print_STPinput_back_CVC_flag ||
           print_STPinput_back_dot_flag || print_STPinput_back_GDL_flag;
  }

  // output flags
  bool output_CNF_flag;
  bool output_bench_flag;

  // Flag to switch on the smtlib parser
  bool smtlib1_parser_flag;
  bool smtlib2_parser_flag;

  bool division_by_zero_returns_one_flag;

  bool quick_statistics_flag;

  bool tseitin_are_decision_variables_flag;

  bool bitConstantProp_flag;

  bool cBitP_propagateForDivisionByZero;

  bool exit_after_CNF;

  bool enable_AIG_rewrites_flag;

  bool simplify_during_BB_flag;

  // Available back-end SAT solvers.
  enum SATSolvers
  {
    MINISAT_SOLVER = 0,
    SIMPLIFYING_MINISAT_SOLVER,
    CRYPTOMINISAT5_SOLVER
  };

  enum SATSolvers solver_to_use;
  int num_solver_threads;

  std::map<std::string, std::string> config_options;

  void set(std::string n, std::string v)
  {
    assert(n.size() > 0);
    assert(v.size() > 0);
    assert(config_options.find(n) == config_options.end());
    config_options[n] = v;
  }

  void disableSimplifications()
  {
    optimize_flag = false;
    bitConstantProp_flag = false;
    set("enable-unconstrained", "0");
    set("use-intervals", "0");
    set("pure-literals", "0");
    set("simple-cnf", "1");
    set("always_true", "0");
    set("bitblast-simplification", "0");

    wordlevel_solve_flag = false;
    propagate_equalities = false;
  }

  std::string get(std::string n) { return get(n, ""); }

  // "1" is set.
  bool isSet(std::string n, std::string def) { return (get(n, def) == std::string("1")); }

  std::string get(std::string n, std::string def)
  {
    if (config_options.empty())
      return def;

    std::string result;
    std::map<std::string, std::string>::const_iterator it = config_options.find(n);
    if (it == config_options.end())
      result = def;
    else
      result = it->second;

    if (stats_flag)
      if (alreadyOutput.insert(n).second)
        std::cout << "--config_" << n << "=" << result << std::endl;
    return result;
  }

  // CONSTRUCTOR
  UserDefinedFlags()
  {
    timeout_max_conflicts = -1;

    // collect statistics on certain functions
    stats_flag = false;

    cinterface_exprdelete_on_flag = true;

    // print DAG nodes
    print_nodes_flag = false;

    // run STP in optimized mode
    optimize_flag = true;

    // Do sat refinement, i.e. underconstraint the problem, and feed to
    // SAT. if this works, great. else, add a set of suitable
    // constraints to re-constraint the problem correctly, and call SAT again,
    // until all constraints have been added.
    ackermannisation = false;

    // flag to control write refinement
    // arraywrite_refinement_flag = true;

    // check the counterexample against the original input to STP
    check_counterexample_flag = true;

    // construct the counterexample in terms of original variable based
    // on the counterexample returned by SAT solver
    construct_counterexample_flag = true;
    print_counterexample_flag = false;
    print_binary_flag = false;

    output_CNF_flag = false;
    output_bench_flag = false;

    // if this option is true then print the way dawson wants using a
    // different printer. do not use this printer.
    print_arrayval_declaredorder_flag = false;

    // flag to decide whether to print "valid/invalid" or not
    print_output_flag = false;

    // print the variable order chosen by the sat solver while it is
    // solving.
    print_sat_varorder_flag = false;

    // turn on word level bitvector solver
    wordlevel_solve_flag = true;

    // propagate equalities.
    propagate_equalities = true;

    // Flag to switch on the smtlib parser
    smtlib1_parser_flag = false;
    smtlib2_parser_flag = false;

    // print the input back
    print_STPinput_back_flag = false;
    print_STPinput_back_C_flag = false;
    print_STPinput_back_SMTLIB2_flag = false;
    print_STPinput_back_SMTLIB1_flag = false;
    print_STPinput_back_CVC_flag = false;
    print_STPinput_back_GDL_flag = false;
    print_STPinput_back_dot_flag = false;

    // If enabled. division, mod and remainder by zero will evaluate to
    // 1.
    division_by_zero_returns_one_flag = true;

    quick_statistics_flag = false;

    tseitin_are_decision_variables_flag = true;

    // If cryptominisat is installed, use it as default, otherwise minisat.
#ifdef USE_CRYPTOMINISAT
    solver_to_use = CRYPTOMINISAT5_SOLVER;
#else
    solver_to_use = MINISAT_SOLVER;
#endif

    num_solver_threads = 1;

    // Should constant bit propagation be enabled?
    bitConstantProp_flag = true;

    // given a/b = c, propagates that c<=a even if b may be zero.
    cBitP_propagateForDivisionByZero = true;

    exit_after_CNF = false;

    enable_AIG_rewrites_flag = false;

    // If the bit-blaster discovers new constants, should the term simplifier be
    // re-run.
    simplify_during_BB_flag = false;

  }

};
} // end of namespace

#endif

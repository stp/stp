/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Andrew Teylu
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

#include "main_common.h"

#include <CLI/CLI.hpp>

using namespace stp;
using std::cout;
using std::cerr;
using std::endl;

/********************************************************************
 * MAIN FUNCTION:
 *
 * step 0. Parse the input into an ASTVec.
 * step 1. Do BV Rewrites
 * step 2. Bitblasts the ASTNode.
 * step 3. Convert to CNF
 * step 4. Convert to SAT
 * step 5. Call SAT to determine if input is SAT or UNSAT
 ********************************************************************/

class ExtraMain : public Main
{
public:
  int create_and_parse_options(int argc, char** argv);
  void create_options();
  int parse_options(int argc, char** argv);

  CLI::App app;

  // Pure flags, true when given on the command line.
  bool version = false;
  bool disable_simplifications = false;
  bool switch_word = false;
  bool disable_opt_inc = false;
  bool disable_cbitp = false;
  bool disable_equality = false;
  bool size_reducing_only = false;
  bool use_cvc = false;
  bool use_smtlib1 = false;
  bool use_smtlib2 = false;
  bool use_simplifying_minisat = false;
  bool use_minisat = false;
#ifdef USE_CRYPTOMINISAT
  bool use_cryptominisat = false;
#endif
#ifdef USE_CADICAL
  bool use_cadical = false;
#endif

  // Held as text until parse_options() turns it into UserFlags.search_bias.
  std::string search_bias;
  CLI::Option* search_bias_option = nullptr;

  // Likewise for UserFlags.cadical_factor.
  std::string cadical_factor;
#ifdef USE_CADICAL
  CLI::Option* cadical_factor_option = nullptr;
#endif

  // Likewise for UserFlags.cnf_effort; always mapped, so it carries the
  // default spelling.
  std::string cnf_effort = "medium";

  // Tri-state: UserFlags.interactive_read is only overridden when the
  // option was given, so the value needs its own presence check.
  bool interactive = false;
  CLI::Option* interactive_option = nullptr;
};

int ExtraMain::create_and_parse_options(int argc, char** argv)
{
  create_options();
  int ret = parse_options(argc, argv);
  if (ret != 0)
  {
    return ret;
  }
  return 0;
}

void ExtraMain::create_options()
{
  app.usage("USAGE: stp [options] <input-file>\n"
            " where input is SMTLIB1/2 or CVC depending on options and file "
            "extension");

  // An empty group hides an option from --help; the input file is
  // positional-only.
  app.add_option("file", infile, "input file")->group("");

  const char* const general_group = "Most important options";
  app.set_help_flag("--help,-h", "print this help")->group(general_group);
  app.add_flag("--version", version, "print version number")
      ->group(general_group);

  const char* const simp_group = "Simplifications";

  // A value-taking bool: accepts 1/0, true/false, on/off, as
  // '--flattening false' or '--flattening=false'. capture_default_str()
  // shows the current UserFlags default in --help.
  auto bool_arg = [this](const char* name, bool& var, const char* desc,
                         const char* group) {
    return app.add_option(name, var, desc)->capture_default_str()->group(group);
  };
  auto int64_arg = [this](const char* name, int64_t& var, const char* desc,
                          const char* group) {
    return app.add_option(name, var, desc)->capture_default_str()->group(group);
  };

  app.add_flag("--disable-simplifications", disable_simplifications,
               "disable all simplifications")
      ->group(simp_group);
  app.add_flag("--switch-word,-w", switch_word, "switch off wordlevel solver")
      ->group(simp_group);
  app.add_flag("--disable-opt-inc,-a", disable_opt_inc,
               "disable rewriting simplifier")
      ->group(simp_group);
  app.add_flag("--disable-cbitp", disable_cbitp,
               "disable constant bit propagation")
      ->group(simp_group);
  app.add_flag("--disable-equality", disable_equality,
               "disable equality propagation")
      ->group(simp_group);
  app.add_flag("--size-reducing-only", size_reducing_only,
               "size reducing simplifications only")
      ->group(simp_group);

  bool_arg("--unconstrained-variable-elimination",
           bm->UserFlags.enable_unconstrained,
           "Unconstrained variables are eliminated.", simp_group);

  int64_arg("--aig-rewrite-passes", bm->UserFlags.AIG_rewrites_iterations,
            "Iterations of AIG rewriting to perform", simp_group);

  bool_arg("--flattening", bm->UserFlags.enable_flatten,
           "Enable sharing-aware flattening of >2 arity nodes", simp_group);

  bool_arg("--rewriting", bm->UserFlags.enable_sharing_aware_rewriting,
           "Enable sharing-aware rewriting", simp_group);

  bool_arg("--split-extracts", bm->UserFlags.enable_split_extracts,
           "Create new variables for some extracts", simp_group);

  bool_arg("--ite-context-simplifications", bm->UserFlags.enable_ite_context,
           "Use what is known to be true in an if-then-else node to simplify "
           "the true or false branches",
           simp_group);

  bool_arg("--aig-core-simplification", bm->UserFlags.enable_aig_core_simplify,
           "Simplify the propositional core with AIGs", simp_group);

  bool_arg("--use-intervals", bm->UserFlags.enable_use_intervals,
           "Simplify with interval analysis", simp_group);

  bool_arg("--pure-literals", bm->UserFlags.enable_pure_literals,
           "Pure literals are replaced.", simp_group);

  bool_arg("--merge-same", bm->UserFlags.enable_merge_same,
           "Uses simple boolean algebra rules to combine conjuncts at the top "
           "level",
           simp_group);

  int64_arg("--bit-blast-simplification", bm->UserFlags.bitblast_simplification,
            "Part-way through simplifying, convert to AIGs and look for bits "
            "that the AIGs figure out are true/false or the same as another "
            "node. If the difficulty is less than this number. -1 means "
            "always.",
            simp_group);

  int64_arg("--size-reducing-fixed-point-limit",
            bm->UserFlags.size_reducing_fixed_point,
            "If the number of non-leaf nodes is fewer than this number, run "
            "size-reducing simplifications to a fixed-point. -1 means always.",
            simp_group);

  bool_arg("--simplify-to-constants-only,--simply_to_constants_only",
           bm->UserFlags.simplify_to_constants_only,
           "Use just the simplifications from the potentially size increasing "
           "suite that transform nodes to constants",
           simp_group);

  bool_arg("--difficulty-reversion,--difficulty_reversion",
           bm->UserFlags.difficulty_reversion,
           "Undo size increasing simplifications if they haven't made the "
           "problem simpler",
           simp_group);

  const char* const solver_group = "SAT Solver options";

#ifdef USE_CADICAL
  app.add_flag("--cadical", use_cadical, "use cadical as the solver")
      ->group(solver_group);
  cadical_factor_option =
      app.add_option("--cadical-factor", cadical_factor,
                     "let cadical use bounded variable addition: 'on', 'off', "
                     "or 'auto' (the default, on only for problems with array "
                     "operations). Needs a CaDiCaL 3.x build; otherwise the "
                     "request is declined with a warning")
          ->group(solver_group);
#endif

#ifdef USE_CRYPTOMINISAT
  app.add_flag("--cryptominisat", use_cryptominisat,
               "use cryptominisat as the solver. Only use CryptoMiniSat 5.0 "
               "or above ")
      ->group(solver_group);
  app.add_option("--threads", bm->UserFlags.num_solver_threads,
                 "Number of threads for cryptominisat")
      ->capture_default_str()
      ->group(solver_group);
#endif

#ifdef USE_RISS
  app.add_flag("--riss", "use Riss as the solver")->group(solver_group);
#endif

  app.add_flag("--simplifying-minisat", use_simplifying_minisat,
               "use installed simplifying minisat version as the solver")
      ->group(solver_group);
  app.add_flag("--minisat", use_minisat,
               "use installed minisat version as the solver ")
      ->group(solver_group);
  search_bias_option =
      app.add_option("--search-bias", search_bias,
                     "tune the SAT search towards one answer: 'unsat' (best "
                     "for unsatisfiable / verification workloads), 'sat', or "
                     "'none' (the default, leaving the solver at its own "
                     "settings). Solvers with no such setting ignore it")
          ->group(solver_group);

  const char* const refinement_group = "Refinement options";
  app.add_flag("--ackermanize,-r", bm->UserFlags.ackermannisation,
               "eagerly encode array-read axioms (Ackermannistaion)")
      ->group(refinement_group);
  app.add_flag("--array-equality", bm->UserFlags.enable_array_equality,
               "decide whole-array equality/disequality (extensional arrays) "
               "by lemmas on demand")
      ->group(refinement_group);

  const char* const bb_group = "Bit-blasting options";
  bool_arg("--bb.div-v1", bm->UserFlags.division_variant_1,
           "unsigned division encoding variant 1", bb_group);

  bool_arg("--bb.div-v2", bm->UserFlags.division_variant_2,
           "unsigned division encoding variant 2", bb_group);

  bool_arg("--bb.div-v3", bm->UserFlags.division_variant_3,
           "unsigned division encoding variant 3", bb_group);

  bool_arg("--bb.add-v1", bm->UserFlags.adder_variant,
           "addition encoding variant 1", bb_group);

  bool_arg("--bb.add-v2", bm->UserFlags.bvplus_variant,
           "addition encoding variant 2", bb_group);

  bool_arg("--bb.vle-v1", bm->UserFlags.bbbvle_variant,
           "comparison encoding variant 1", bb_group);

  int64_arg("--bb.mult-variant", bm->UserFlags.multiplication_variant,
            "unsigned multiplication variant", bb_group);

  bool_arg("--bb.mult-v2", bm->UserFlags.upper_multiplication_bound,
           "unsigned multiplication variant 2", bb_group);

  bool_arg("--bb.conjoin-constant", bm->UserFlags.conjoin_to_top,
           "When constant-bit propagation detects a constant bit during AIG "
           "construction, assert the AIG node and replace it, in the AIG, by "
           "the constant bit",
           bb_group);

  bool_arg("--bb.fp-native-cmp", bm->UserFlags.fp_native_cmp,
           "Bit-blast floating-point predicates (comparisons, equalities, "
           "classifications) over already-packed operands natively instead of "
           "via the SymFPU unpacking circuits",
           bb_group);

  bool_arg("--bb.fp-native-arith", bm->UserFlags.fp_native_arith,
           "Bit-blast fp.add and fp.mul under surviving native predicates "
           "with the hand-written packed-operand circuits instead of the "
           "SymFPU unpacking circuits (experimental)",
           bb_group);

  bool_arg("--bb.simplify-during-bb", bm->UserFlags.simplify_during_BB_flag,
           "When bit-blasting discovers that a non-constant child of a term "
           "blasts to an all-constant vector, rebuild the term with that "
           "constant and re-run the word-level term simplifier on it. Has no "
           "effect unless the rewriting simplifier is also on, i.e. not with "
           "--disable-opt-inc or --disable-simplifications",
           bb_group);

  const char* const print_group = "Printing options";
  app.add_flag("--print-stpinput,-b", bm->UserFlags.print_STPinput_back_flag,
               "print STP input back to cout")
      ->group(print_group);
  app.add_flag("--print-back-CVC", bm->UserFlags.print_STPinput_back_CVC_flag,
               "print input in CVC format, then exit")
      ->group(print_group);
  app.add_flag("--print-back-SMTLIB2",
               bm->UserFlags.print_STPinput_back_SMTLIB2_flag,
               "print input in SMT-LIB2 format, then exit")
      ->group(print_group);
  app.add_flag("--print-back-SMTLIB1",
               bm->UserFlags.print_STPinput_back_SMTLIB1_flag,
               "print input in SMT-LIB1 format, then exit")
      ->group(print_group);
  app.add_flag("--print-back-GDL", bm->UserFlags.print_STPinput_back_GDL_flag,
               "print AiSee's graph format, then exit")
      ->group(print_group);
  app.add_flag("--print-back-dot", bm->UserFlags.print_STPinput_back_dot_flag,
               "print dotty/neato's graph format, then exit")
      ->group(print_group);
  app.add_flag("--print-counterex,-p", bm->UserFlags.print_counterexample_flag,
               "print counterexample")
      ->group(print_group);
  app.add_flag("--print-counterexbin,-y", bm->UserFlags.print_binary_flag,
               "print counterexample in binary")
      ->group(print_group);
  app.add_flag("--print-arrayval,-q",
               bm->UserFlags.print_arrayval_declaredorder_flag,
               "print arrayval declared order")
      ->group(print_group);
  app.add_flag("--print-functionstat,-s", bm->UserFlags.stats_flag,
               "print function statistics")
      ->group(print_group);
  app.add_flag("--print-quickstat,-t", bm->UserFlags.quick_statistics_flag,
               "print quick statistics")
      ->group(print_group);
  app.add_flag("--print-nodes,-v", bm->UserFlags.print_nodes_flag,
               "print nodes ")
      ->group(print_group);
  app.add_flag("--print-output,-n", bm->UserFlags.print_output_flag,
               "Print output")
      ->group(print_group);

  const char* const input_group = "Input options";
  app.add_flag("--SMTLIB1,-m", use_smtlib1, "use the SMT-LIB1 format parser")
      ->group(input_group);
  app.add_flag("--SMTLIB2", use_smtlib2, "use the SMT-LIB2 format parser")
      ->group(input_group);
  app.add_flag("--CVC", use_cvc, "use the CVC format parser")
      ->group(input_group);

  const char* const output_group = "Output options";
  app.add_flag("--output-CNF", bm->UserFlags.output_CNF_flag,
               "Save the CNF into output_[0..n].cnf. NOTE: variables cannot "
               "be mapped back, and problems solved by the preprocessing "
               "simplifier alone will not generate any CNF as the SAT solver "
               "is never invoked")
      ->group(output_group);

  const char* const misc_group = "Miscellaneous options";
  app.add_option("--cnf-generation-effort", cnf_effort,
                 "effort spent minimising the CNF: very-low, low, medium, "
                 "high, very-high. Higher is slower to generate but yields a "
                 "smaller CNF")
      ->capture_default_str()
      ->group(misc_group);

  app.add_flag("--exit-after-CNF", bm->UserFlags.exit_after_CNF,
               "exit after the CNF has been generated")
      ->group(misc_group);

  app.add_flag("--parse-only", bm->UserFlags.parse_only,
               "exit after parsing the input, without solving")
      ->group(misc_group);

  interactive_option =
      app.add_option("--interactive", interactive,
                     "read the input a character at a time, as needed when "
                     "driving stp interactively over a pipe. Off reads in "
                     "blocks, which is faster. Default: on when reading from "
                     "stdin, off when reading from a file. SMT-LIB2 only.")
          ->group(misc_group);

  int64_arg("--max-num-confl,--max_num_confl,-g",
            bm->UserFlags.timeout_max_conflicts,
            "Number of conflicts after which the SAT solver gives up. "
            "-1 means never, 0 means give up without searching.",
            misc_group);

  int64_arg("--max-time,--max_time,-k", bm->UserFlags.timeout_max_time,
            "Number of seconds after which the SAT solver gives up. The "
            "budget is for the whole query, not for each call into the SAT "
            "solver. -1 means never, 0 means give up without searching.",
            misc_group);

  app.add_flag("--check-sanity,-d", bm->UserFlags.check_counterexample_flag,
               "construct counterexample and check it")
      ->group(misc_group);
}

int ExtraMain::parse_options(int argc, char** argv)
{
  try
  {
    app.parse(argc, argv);
  }
  catch (const CLI::CallForHelp&)
  {
    cout << app.help();
    exit(0);
  }
  catch (const CLI::ParseError& e)
  {
    cerr << "Error: " << e.what() << endl;
    cerr << "Please give '--help' to get help" << endl;
    exit(-1);
  }

  onePrintBack = bm->UserFlags.get_print_output_at_all();

  if (disable_opt_inc)
  {
    bm->UserFlags.optimize_flag = false;
  }

  if (switch_word)
  {
    bm->UserFlags.wordlevel_solve_flag = false;
  }

  if (disable_cbitp)
  {
    bm->UserFlags.bitConstantProp_flag = false;
  }

  if (interactive_option->count())
  {
    bm->UserFlags.interactive_read = interactive ? 1 : 0;
  }

  if (cnf_effort == "very-low")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_VERY_LOW;
  else if (cnf_effort == "low")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_LOW;
  else if (cnf_effort == "medium")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_MEDIUM;
  else if (cnf_effort == "high")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_HIGH;
  else if (cnf_effort == "very-high")
    bm->UserFlags.cnf_effort = UserDefinedFlags::CNF_EFFORT_VERY_HIGH;
  else
  {
    std::cerr << "Unknown --cnf-generation-effort value '" << cnf_effort
              << "'. Expected one of: very-low, low, medium, high, very-high."
              << std::endl;
    return -1;
  }

  int selected_type = 0;
  if (use_cvc)
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = false;
    bm->UserFlags.smtlib2_parser_flag = false;
  }

  if (use_smtlib2)
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = false;
    bm->UserFlags.smtlib2_parser_flag = true;
  }

  if (use_smtlib1)
  {
    selected_type++;
    bm->UserFlags.smtlib1_parser_flag = true;
    bm->UserFlags.smtlib2_parser_flag = false;
  }

  if (selected_type > 1)
  {
    cerr << "ERROR: You have selected more than one parsing option from "
            "CVC/SMTLIB1/SMTLIB2"
         << endl;
    std::exit(-1);
  }

  if (selected_type == 0)
  {
    bm->UserFlags.smtlib2_parser_flag = true;
  }

  if (use_simplifying_minisat)
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER;
  }

  if (use_minisat)
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::MINISAT_SOLVER;
  }

#ifdef USE_CRYPTOMINISAT
  if (use_cryptominisat)
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::CRYPTOMINISAT5_SOLVER;
  }
#endif

#ifdef USE_CADICAL
  if (use_cadical)
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::CADICAL_SOLVER;
  }
#endif

  if (search_bias_option->count())
  {
    if (search_bias == "sat")
      bm->UserFlags.search_bias = SearchBias::SAT;
    else if (search_bias == "unsat")
      bm->UserFlags.search_bias = SearchBias::UNSAT;
    else if (search_bias == "none")
      bm->UserFlags.search_bias = SearchBias::NONE;
    else
    {
      cerr << "ERROR: --search-bias must be one of 'sat', 'unsat' or 'none'"
           << endl;
      std::exit(-1);
    }
  }

#ifdef USE_CADICAL
  if (cadical_factor_option->count())
  {
    if (cadical_factor == "on")
      bm->UserFlags.cadical_factor = UserDefinedFlags::BVAMode::ON;
    else if (cadical_factor == "off")
      bm->UserFlags.cadical_factor = UserDefinedFlags::BVAMode::OFF;
    else if (cadical_factor == "auto")
      bm->UserFlags.cadical_factor = UserDefinedFlags::BVAMode::AUTO;
    else
    {
      cerr << "ERROR: --cadical-factor must be one of 'on', 'off' or 'auto'"
           << endl;
      std::exit(-1);
    }
  }
#endif

  /*
   * -1 is the only negative value with a meaning ("no limit"); anything more
   * negative than that is a mistake, and silently treating it as unlimited
   * hides it.
   */
  if (bm->UserFlags.timeout_max_conflicts < -1)
  {
    cerr << "ERROR: --max-num-confl must be -1 (no limit) or greater" << endl;
    std::exit(-1);
  }

  if (bm->UserFlags.timeout_max_time < -1)
  {
    cerr << "ERROR: --max-time must be -1 (no limit) or greater" << endl;
    std::exit(-1);
  }

  if (disable_simplifications)
  {
    bm->UserFlags.disableSimplifications();
  }

  if (size_reducing_only)
  {
    bm->UserFlags.disableSizeIncreasingSimplifications();
  }

  if (disable_equality)
  {
    bm->UserFlags.propagate_equalities = false;
  }

  if (selected_type == 0)
  {
    // No parser is explicity requested.
    check_infile_type();
  }

  if (version)
  {
    printVersionInfo();
    exit(0);
  }

  return 0;
}

int main(int argc, char** argv)
{
  ExtraMain main;
  return main.main(argc, argv);
}

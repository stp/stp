/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
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

#include <boost/lexical_cast.hpp>
#include <boost/program_options.hpp>
using boost::lexical_cast;
namespace po = boost::program_options;

#ifdef EXT_HASH_MAP
using namespace __gnu_cxx;
#endif
using namespace stp;
using std::auto_ptr;
using std::cout;
using std::cerr;
using std::endl;

namespace stp
{
void setHardTimeout(int);
}

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
  void try_parsing_options(int argc, char** argv, po::variables_map& vm,
                           po::positional_options_description& pos_options);
  int create_and_parse_options(int argc, char** argv);
  void create_options();
  int parse_options(int argc, char** argv);

  po::options_description cmdline_options;
  po::options_description visible_options;
  po::positional_options_description pos_options;
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

void
ExtraMain::try_parsing_options(int argc, char** argv, po::variables_map& vm,
                               po::positional_options_description& pos_options)
{
  try
  {
    po::store(po::command_line_parser(argc, argv)
                  .options(cmdline_options)
                  .positional(pos_options)
                  .run(),
              vm);

    if (vm.count("help"))
    {
      cout << "USAGE: " << argv[0] << " [options] <input-file>" << endl
           << " where input is SMTLIB1/2 or CVC depending on options and file "
              "extension" << endl;

      cout << cmdline_options << endl;
      exit(0);
    }

    po::notify(vm);
  }
  catch (boost::exception_detail::clone_impl<
      boost::exception_detail::error_info_injector<po::unknown_option>>& c)
  {
    cout << "Some option you gave was wrong. Please give '--help' to get help"
         << endl;
    cout << "Unkown option: " << c.what() << endl;
    exit(-1);
  }
  catch (boost::bad_any_cast& e)
  {
    std::cerr << "ERROR! You probably gave a wrong argument type (Bad cast): "
              << e.what() << endl;

    exit(-1);
  }
  catch (boost::exception_detail::clone_impl<
      boost::exception_detail::error_info_injector<po::invalid_option_value>>&
             what)
  {
    cerr << "Invalid value '" << what.what() << "'"
         << " given to option '" << what.get_option_name() << "'" << endl;

    exit(-1);
  }
  catch (boost::exception_detail::clone_impl<
      boost::exception_detail::error_info_injector<po::multiple_occurrences>>&
             what)
  {
    cerr << "Error: " << what.what() << " of option '" << what.get_option_name()
         << "'" << endl;

    exit(-1);
  }
  catch (boost::exception_detail::clone_impl<
      boost::exception_detail::error_info_injector<po::required_option>>& what)
  {
    cerr << "You forgot to give a required option '" << what.get_option_name()
         << "'" << endl;

    exit(-1);
  }
}

void ExtraMain::create_options()
{
  po::options_description hiddenOptions("Hidden options");
  hiddenOptions.add_options()("file", po::value<string>(&infile), "input file");

  // Declare the supported options.
  po::options_description general_options("Most important options");
  general_options.add_options()("help,h", "print this help")(
      "version", "print version number")("disable-simplify",
                                         "disable all simplifications")(
      "switch-word,w", "switch off wordlevel solver")(
      "disable-opt-inc,a", "disable potentially size-increasing optimisations")(
      "disable-cbitp", "disable constant bit propagation")(
      "disable-equality", "disable equality propagation");

  po::options_description solver_options("SAT Solver options");
  solver_options.add_options()("cryptominisat",
                               "use cryptominisat2 as the solver")
#ifdef USE_CRYPTOMINISAT4
      ("cryptominisat4",
       "use cryptominisat4 as the solver. Only use CryptoMiniSat 4.2 or above.")
#endif
      ("simplifying-minisat", "use simplifying-minisat 2.2 as the solver")(
          "minisat", "use minisat 2.2 as the solver");

  po::options_description refinement_options("Refinement options");
  refinement_options.add_options()(
      "oldstyle-refinement",
      "Do abstraction-refinement outside the SAT solver")(
      "ackermanize,r", po::bool_switch(&(bm->UserFlags.ackermannisation)),
      "eagerly encode array-read axioms (Ackermannistaion)")(
      "flatten,x", po::bool_switch(&(bm->UserFlags.xor_flatten_flag)),
      "flatten XORs");

  po::options_description print_options("Printing options");
  print_options.add_options()(
      "print-stpinput,b",
      po::bool_switch(&(bm->UserFlags.print_STPinput_back_flag)),
      "print STP input back to cout")(
      "print-back-CVC",
      po::bool_switch(&(bm->UserFlags.print_STPinput_back_CVC_flag)),
      "print input in CVC format, then exit")(
      "print-back-SMTLIB2",
      po::bool_switch(&(bm->UserFlags.print_STPinput_back_SMTLIB2_flag)),
      "print input in SMT-LIB2 format, then exit")(
      "print-back-SMTLIB1",
      po::bool_switch((&bm->UserFlags.print_STPinput_back_SMTLIB1_flag)),
      "print input in SMT-LIB1 format, then exit")(
      "print-back-GDL",
      po::bool_switch(&(bm->UserFlags.print_STPinput_back_GDL_flag)),
      "print AiSee's graph format, then exit")(
      "print-back-dot",
      po::bool_switch(&(bm->UserFlags.print_STPinput_back_dot_flag)),
      "print dotty/neato's graph format, then exit")(
      "print-counterex,p",
      po::bool_switch(&(bm->UserFlags.print_counterexample_flag)),
      "print counterexample")(
      "print-counterexbin,y",
      po::bool_switch(&(bm->UserFlags.print_binary_flag)),
      "print counterexample in binary")(
      "print-arrayval,q",
      po::bool_switch(&(bm->UserFlags.print_arrayval_declaredorder_flag)),
      "print arrayval declared order")(
      "print-functionstat,s", po::bool_switch(&(bm->UserFlags.stats_flag)),
      "print function statistics")(
      "print-quickstat,t",
      po::bool_switch(&(bm->UserFlags.quick_statistics_flag)),
      "print quick statistics")(
      "print-nodes,v", po::bool_switch(&(bm->UserFlags.print_nodes_flag)),
      "print nodes ")
      /*("constr-counterex,c",
         po::bool_switch(&(bm->UserFlags.construct_counterexample_flag))
          , "construct counterexample")*/
      ("print-varorder,z",
       po::bool_switch(&(bm->UserFlags.print_sat_varorder_flag)),
       "Print SAT variable order")(
          "print-output,n", po::bool_switch(&(bm->UserFlags.print_output_flag)),
          "Print output");

  po::options_description input_options("Input options");
  input_options.add_options()("SMTLIB1,m", "use the SMT-LIB1 format parser")(
      "SMTLIB2", "use the SMT-LIB2 format parser");

  po::options_description output_options("Output options");
  output_options.add_options()(
      "output-CNF", po::bool_switch(&(bm->UserFlags.output_CNF_flag)),
      "save the CNF into output_[0..n].cnf")(
      "output-bench", po::bool_switch(&(bm->UserFlags.output_bench_flag)),
      "save in ABC's bench format to output.bench");

  po::options_description misc_options("Output options");
  misc_options.add_options()("exit-after-CNF",
                             po::bool_switch(&(bm->UserFlags.exit_after_CNF)),
                             "exit after the CNF has been generated")
#ifndef _MSC_VER
      ("timeout,g", po::value<size_t>(&hardTimeout),
       "timeout (seconds until STP gives up)")
#endif
      ("seed,i", po::value<size_t>(&random_seed),
       "set random seed for STP's satisfiable output. Random_seed is an "
       "integer >= 0")("random-seed",
                       "generate a random number for the SAT solver.")(
          "check-sanity,d", "construct counterexample and check it");

  cmdline_options.add(general_options)
      .add(solver_options)
      .add(refinement_options)
      .add(print_options)
      .add(input_options)
      .add(output_options)
      .add(misc_options)
      .add(hiddenOptions);

  // Register everything except hiddenOptions
  visible_options.add(general_options)
      .add(solver_options)
      .add(refinement_options)
      .add(print_options)
      .add(input_options)
      .add(output_options)
      .add(misc_options);

  pos_options.add("file", 1);
}

int ExtraMain::parse_options(int argc, char** argv)
{
  po::variables_map vm;
  try_parsing_options(argc, argv, vm, pos_options);
  onePrintBack = bm->UserFlags.get_print_output_at_all();

  if (vm.count("disable-size"))
  {
    bm->UserFlags.optimize_flag = false;
  }

  if (vm.count("switch-word"))
  {
    bm->UserFlags.wordlevel_solve_flag = false;
  }

  if (vm.count("disable-cbitp"))
  {
    bm->UserFlags.bitConstantProp_flag = false;
  }

  if (vm.count("SMTLIB2"))
  {
    bm->UserFlags.smtlib2_parser_flag = true;
    bm->UserFlags.division_by_zero_returns_one_flag = true;
    if (bm->UserFlags.smtlib1_parser_flag)
    {
      FatalError("Can't use both the smtlib and smtlib2 parsers");
    }
  }

  if (vm.count("SMTLIB1"))
  {
    bm->UserFlags.smtlib1_parser_flag = true;
    bm->UserFlags.division_by_zero_returns_one_flag = true;
    if (bm->UserFlags.smtlib2_parser_flag)
    {
      FatalError("Can't use both the smtlib and smtlib2 parsers");
    }
  }

  if (vm.count("simplifying-minisat"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER;
  }

  if (vm.count("minisat"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::MINISAT_SOLVER;
  }

  if (vm.count("cryptominisat"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::CRYPTOMINISAT_SOLVER;
  }

#ifdef USE_CRYPTOMINISAT4
  if (vm.count("cryptominisat4"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::CRYPTOMINISAT4_SOLVER;
  }
#endif

  if (vm.count("cryptominisat")
#ifdef USE_CRYPTOMINISAT4
          + vm.count("cryptominisat4")
#endif
          + vm.count("minisat") + vm.count("simplifying-minisat") >
      1)
  {
    cout << "ERROR: You may only give one solver to use: minisat, "
            "simplifying-minisat, or cryptominisat" << endl;
    exit(-1);
  }

  if (vm.count("gauss"))
  {
    if (bm->UserFlags.solver_to_use != UserDefinedFlags::CRYPTOMINISAT_SOLVER)
    {
      cout << "ERROR: you specified a Gaussian elimination length" << endl
           << "       but you didn't ask cryptominisat to be used" << endl;
      exit(-1);
    }
  }

  if (vm.count("oldstyle-refinement"))
  {
    bm->UserFlags.solver_to_use = UserDefinedFlags::MINISAT_SOLVER;
  }

  if (vm.count("disable-simplifications"))
  {
    bm->UserFlags.disableSimplifications();
  }

  if (vm.count("disable-equality"))
  {
    bm->UserFlags.propagate_equalities = false;
  }

  if (vm.count("random-seed"))
  {
    srand(time(NULL));
    bm->UserFlags.random_seed_flag = true;
    bm->UserFlags.random_seed = rand();
  }

  // TODO this is not actually exposed by original main.cpp code
  if (vm.count("hash-nf"))
  {
    bm->defaultNodeFactory = bm->hashingNodeFactory;
  }

#ifndef _MSC_VER
  if (vm.count("timeout"))
  {
    stp::setHardTimeout(hardTimeout);
  }
#endif

  if (vm.count("seed"))
  {
    bm->UserFlags.random_seed_flag = true;
    bm->UserFlags.random_seed = random_seed;
  }

  if (vm.count("constr-check-counterex"))
  {
    bm->UserFlags.construct_counterexample_flag = true;
    bm->UserFlags.check_counterexample_flag = true;
  }

  if (!bm->UserFlags.smtlib1_parser_flag && !bm->UserFlags.smtlib2_parser_flag)
  {
    // No parser is explicity requested.
    check_infile_type();
  }

  if (vm.count("version"))
  {
    cout << "STP version " << get_git_version() << std::endl;
    exit(0);
  }

  return 0;
}

int main(int argc, char** argv)
{
  ExtraMain main;
  return main.main(argc, argv);
}
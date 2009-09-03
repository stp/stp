/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include <iostream>
#include <sstream>
#include <string>
#include <algorithm>
#include <ctime>
#include <unistd.h>
#include <signal.h>
//#include <zlib.h>
#include <stdio.h>
#include "../AST/AST.h"
#include "../sat/core/Solver.h"
#include "../sat/core/SolverTypes.h"
//#include "../sat/VarOrder.h"

#include <unistd.h>

#ifdef EXT_HASH_MAP
  using namespace __gnu_cxx;
#endif

/* GLOBAL FUNCTION: parser
 */
extern int smtparse();
extern int cvcparse();


namespace BEEV
{
extern BEEV::ASTNode SingleBitOne;
extern BEEV::ASTNode SingleBitZero;
}

const string version = "$Id$";

/* GLOBAL VARS: Some global vars for the Main function.
 *
 */
const char * prog = "stp";
int linenum  = 1;
const char * usage = "Usage: %s [-option] [infile]\n";
std::string helpstring = "\n\n";

// Amount of memory to ask for at beginning of main.
static const intptr_t INITIAL_MEMORY_PREALLOCATION_SIZE = 4000000;

/******************************************************************************
 * MAIN FUNCTION:
 *
 * step 0. Parse the input into an ASTVec.
 * step 1. Do BV Rewrites
 * step 2. Bitblasts the ASTNode.
 * step 3. Convert to CNF
 * step 4. Convert to SAT
 * step 5. Call SAT to determine if input is SAT or UNSAT
 ******************************************************************************/
int main(int argc, char ** argv) {
  char * infile;
  extern FILE *cvcin;
  extern FILE *smtin;



  // Grab some memory from the OS upfront to reduce system time when individual
  // hash tables are being allocated

  if (sbrk(INITIAL_MEMORY_PREALLOCATION_SIZE) == ((void *) -1)) {
    // FIXME: figure out how to get and print the real error message.
    BEEV::FatalError("Initial allocation of memory failed.");
  }

  //populate the help string
  helpstring += "version: " + version + "\n\n";
  helpstring +=  "-r  : switch refinement off (optimizations are ON by default)\n";
  helpstring +=  "-w  : switch wordlevel solver off (optimizations are ON by default)\n";
  helpstring +=  "-a  : switch optimizations off (optimizations are ON by default)\n";
  helpstring +=  "-s  : print function statistics\n";
  helpstring +=  "-v  : print nodes \n";
  helpstring +=  "-c  : construct counterexample\n";
  helpstring +=  "-d  : check counterexample\n";
  helpstring +=  "-p  : print counterexample\n";
  helpstring +=  "-y  : print counterexample in binary\n";
  helpstring +=  "-b  : STP input read back\n";
  helpstring +=  "-x  : flatten nested XORs\n";
  helpstring +=  "-h  : help\n";
  helpstring +=  "-m  : use the SMTLIB parser\n";



  for(int i=1; i < argc;i++) {
    if(argv[i][0] == '-') {
      switch(argv[i][1]) {
      case 'a' :
	BEEV::optimize_flag = false;
	break;
      case 'b':
	BEEV::print_STPinput_back_flag = true;
	break;
      case 'c':
	BEEV::construct_counterexample_flag = true;
	break;
      case 'd':
	BEEV::construct_counterexample_flag = true;
	BEEV::check_counterexample_flag = true;
	break;
      case 'h':
	fprintf(stderr,usage,prog);
	cout << helpstring;
	//BEEV::FatalError("");
	return -1;
	break;
      case 'n':
	BEEV::print_output_flag = true;
	break;
      case 'm':
	BEEV::smtlib_parser_flag=true;
	BEEV::division_by_zero_returns_one = true;
	break;
      case 'p':
	BEEV::print_counterexample_flag = true;
	break;
      case 'y':
	BEEV::print_binary_flag = true;
	break;
      case 'q':
	BEEV::print_arrayval_declaredorder_flag = true;
	break;
      case 'r':
	BEEV::arrayread_refinement_flag = false;
	break;
      case 's' :
	BEEV::stats_flag = true;
	break;
      case 'u':
	BEEV::arraywrite_refinement_flag = false;
	break;
      case 'v' :
	BEEV::print_nodes_flag = true;
	break;
      case 'w':
	BEEV::wordlevel_solve_flag = false;
	break;
      case 'x':
	BEEV::xor_flatten_flag = true;
	break;
      case 'z':
	BEEV::print_sat_varorder_flag = true;
	break;
      default:
	fprintf(stderr,usage,prog);
	cout << helpstring;
	//BEEV::FatalError("");
	return -1;
	break;
      }
      if(argv[i][2]) {
	fprintf(stderr, "Multiple character options are not allowed.\n");
	fprintf(stderr, "(for example: -ab is not an abbreviation for -a -b)\n");
	fprintf(stderr,usage,prog);
	cout << helpstring;
	return -1;
      }
    } else {
      infile = argv[i];

      if (BEEV::smtlib_parser_flag)
	{
	  smtin = fopen(infile,"r");
	  if(smtin == NULL)
	    {
	      fprintf(stderr,"%s: Error: cannot open %s\n",prog,infile);
	      BEEV::FatalError("");
	    }
	}
      else
	{
	  cvcin = fopen(infile,"r");
	  if(cvcin == NULL)
	    {
	      fprintf(stderr,"%s: Error: cannot open %s\n",prog,infile);
	      BEEV::FatalError("");
	    }
	}
    }
  }

  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if(0 != c) {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }

  //want to print the output always from the commandline.
  BEEV::print_output_flag = true;
  BEEV::globalBeevMgr_for_parser = new BEEV::BeevMgr();

  BEEV::SingleBitOne = BEEV::globalBeevMgr_for_parser->CreateOneConst(1);
  BEEV::SingleBitZero = BEEV::globalBeevMgr_for_parser->CreateZeroConst(1);

  if (BEEV::smtlib_parser_flag)
    smtparse();
  else
    cvcparse();
}//end of Main

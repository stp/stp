/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-
#include "../AST/AST.h"
#include "../AST/printer/AssortedPrinters.h"

#ifdef EXT_HASH_MAP
using namespace __gnu_cxx;
#endif
using namespace BEEV;

extern int smtparse(void*);
extern int cvcparse(void*);

// Amount of memory to ask for at beginning of main.
static const intptr_t INITIAL_MEMORY_PREALLOCATION_SIZE = 4000000;
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
int main(int argc, char ** argv) {
  char * infile;
  extern FILE *cvcin;
  extern FILE *smtin;

  // Grab some memory from the OS upfront to reduce system time when
  // individual hash tables are being allocated
  if (sbrk(INITIAL_MEMORY_PREALLOCATION_SIZE) == ((void *) -1)) 
    {
      // FIXME: figure out how to get and print the real error
      // message.
      FatalError("Initial allocation of memory failed.");
    }

  //populate the help string
  helpstring += "STP version: " + version + "\n\n";
  helpstring +=  "-a  : switch optimizations off (optimizations are ON by default)\n";
  helpstring +=  "-b  : print STP input back to cout\n";
  helpstring +=  "-c  : construct counterexample\n";
  helpstring +=  "-d  : check counterexample\n";
  helpstring +=  "-e  : expand finite-for construct\n";
  helpstring +=  "-h  : help\n";
  helpstring +=  "-m  : use the SMTLIB parser\n";
  helpstring +=  "-p  : print counterexample\n";
  helpstring +=  "-r  : switch refinement off (optimizations are ON by default)\n";
  helpstring +=  "-s  : print function statistics\n";
  helpstring +=  "-v  : print nodes \n";
  helpstring +=  "-w  : switch wordlevel solver off (optimizations are ON by default)\n";
  helpstring +=  "-x  : flatten nested XORs\n";
  helpstring +=  "-y  : print counterexample in binary\n";

  for(int i=1; i < argc;i++) 
    {
      if(argv[i][0] == '-') 
        {
          switch(argv[i][1]) 
            {
            case 'a' :
              optimize_flag = false;
              break;
            case 'b':
              print_STPinput_back_flag = true;
              break;
            case 'c':
              construct_counterexample_flag = true;
              break;
            case 'd':
              construct_counterexample_flag = true;
              check_counterexample_flag = true;
              break;
	    case 'e':
	      expand_finitefor_flag = true;
	      break;
            case 'h':
              fprintf(stderr,usage,prog);
              cout << helpstring;
              //FatalError("");
              return -1;
              break;
            case 'n':
              print_output_flag = true;
              break;
            case 'm':
              smtlib_parser_flag=true;
              division_by_zero_returns_one = true;
              break;
            case 'p':
              print_counterexample_flag = true;
              break;
            case 'y':
              print_binary_flag = true;
              break;
            case 'q':
              print_arrayval_declaredorder_flag = true;
              break;
            case 'r':
              arrayread_refinement_flag = false;
              break;
            case 's' :
              stats_flag = true;
              break;
            case 'u':
              arraywrite_refinement_flag = false;
              break;
            case 'v' :
              print_nodes_flag = true;
              break;
            case 'w':
              wordlevel_solve_flag = false;
              break;
            case 'x':
              xor_flatten_flag = true;
              break;
            case 'z':
              print_sat_varorder_flag = true;
              break;
            default:
              fprintf(stderr,usage,prog);
              cout << helpstring;
              //FatalError("");
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

          if (smtlib_parser_flag)
            {
              smtin = fopen(infile,"r");
              if(smtin == NULL)
                {
                  fprintf(stderr,"%s: Error: cannot open %s\n",prog,infile);
                  FatalError("");
                }
            }
          else
            {
              cvcin = fopen(infile,"r");
              if(cvcin == NULL)
                {
                  fprintf(stderr,"%s: Error: cannot open %s\n",prog,infile);
                  FatalError("");
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
  print_output_flag = true;
  GlobalBeevMgr = new BeevMgr();
  ASTVec * AssertsQuery = new ASTVec;

  if (smtlib_parser_flag) 
    {
      smtparse((void*)AssertsQuery);
    }
  else 
    {
      cvcparse((void*)AssertsQuery);      
    }
  
  ASTNode asserts = (*(ASTVec*)AssertsQuery)[0];
  ASTNode query   = (*(ASTVec*)AssertsQuery)[1];  
  if(print_STPinput_back_flag) 
    {
      if(smtlib_parser_flag) 
        {
          FatalError("Print back feature for SMT format not yet implemented\n");
        }
      else 
        {
          print_STPInput_Back(asserts, query);
        }
      return 0;
    } //end of PrintBack if

  GlobalBeevMgr->TopLevelSAT(asserts, query);  
  return 0;
}//end of Main

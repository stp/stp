/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-
#include "../AST/AST.h"
#include "../printer/AssortedPrinters.h"
#include "../printer/printers.h"
#include "../STPManager/STPManager.h"
#include "../STPManager/STP.h"

#ifdef EXT_HASH_MAP
using namespace __gnu_cxx;
#endif
using namespace BEEV;

extern int smtparse(void*);
extern int cvcparse(void*);

// callback for SIGALRM.
void handle_time_out(int parameter){
  printf("Timed Out.\n");
  exit(0);
}


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
      FatalError("Initial allocation of memory failed.");
    }


  STPMgr * bm       = new STPMgr();
  Simplifier * simp  = new Simplifier(bm);
  BVSolver* bvsolver = new BVSolver(bm, simp);
  ArrayTransformer * arrayTransformer = new ArrayTransformer(bm, simp);
  ToSAT * tosat      = new ToSAT(bm, simp);
  AbsRefine_CounterExample * Ctr_Example = 
    new AbsRefine_CounterExample(bm, simp, arrayTransformer, tosat);      
  itimerval timeout; 

  ParserBM          = bm;
  GlobalSTP         = 
    new STP(bm, 
            simp, 
            bvsolver, 
            arrayTransformer, 
            tosat, 
            Ctr_Example);
  
  //populate the help string
  helpstring += 
    "STP version: " + version + "\n\n";
  helpstring +=  
    "-a  : switch optimizations off (optimizations are ON by default)\n";
  helpstring +=  
    "-b  : print STP input back to cout\n";
  helpstring +=  
    "-c  : construct counterexample\n";
  helpstring +=  
    "-d  : check counterexample\n";
  helpstring +=  
    "-e  : expand finite-for construct\n";
  helpstring +=  
    "-f  : number of abstraction-refinement loops\n";
  helpstring +=  
    "-g  : timeout (seconds until STP gives up)\n";
  helpstring +=  
    "-h  : help\n";
  helpstring +=  
    "-i <random_seed>  : Randomize STP's satisfiable output. Random_seed is an integer >= 0\n";
  helpstring +=  
    "-m  : use the SMTLIB parser\n";
  helpstring +=  
    "-p  : print counterexample\n";
  helpstring +=  
    "-r  : switch refinement off (optimizations are ON by default)\n";
  helpstring +=  
    "-s  : print function statistics\n";
  helpstring +=  
    "-t  : print quick statistics\n";
  helpstring +=  
    "-v  : print nodes \n";
  helpstring +=  
    "-w  : switch wordlevel solver off (optimizations are ON by default)\n";
  helpstring +=  
    "-x  : flatten nested XORs\n";
  helpstring +=  
    "-y  : print counterexample in binary\n";

  for(int i=1; i < argc;i++)
    {
      if(argv[i][0] == '-')
        {
          if(argv[i][2]) 
            {
              fprintf(stderr, 
                      "Multiple character options are not allowed.\n");
              fprintf(stderr, 
                      "(for example: -ab is not an abbreviation for -a -b)\n");
              fprintf(stderr,usage,prog);
              cout << helpstring;
              return -1;
            }
          switch(argv[i][1])
            {
            case 'a' :
              bm->UserFlags.optimize_flag = false;
              break;
            case 'b':
              bm->UserFlags.print_STPinput_back_flag = true;
              break;
            case 'c':
              bm->UserFlags.construct_counterexample_flag = true;
              break;
            case 'd':
              bm->UserFlags.construct_counterexample_flag = true;
              bm->UserFlags.check_counterexample_flag = true;
              break;
            case 'e':
              bm->UserFlags.expand_finitefor_flag = true;
              break;
            case 'f':
              bm->UserFlags.num_absrefine_flag = true;
              bm->UserFlags.num_absrefine = atoi(argv[++i]);
              break;            
            case 'g':
              signal(SIGVTALRM, handle_time_out);
              timeout.it_interval.tv_usec = 0;
              timeout.it_interval.tv_sec  = 0;
              timeout.it_value.tv_usec    = 0;
              timeout.it_value.tv_sec     = atoi(argv[++i]);
              setitimer(ITIMER_VIRTUAL, &timeout, NULL);
              break;            
            case 'h':
              fprintf(stderr,usage,prog);
              cout << helpstring;
              return -1;
              break;
	    case 'i':
	      bm->UserFlags.random_seed_flag = true;
              bm->UserFlags.random_seed = atoi(argv[++i]);
	      if(!(0 <= bm->UserFlags.random_seed))
		{
		  FatalError("Random Seed should be an integer >= 0\n");
		}
	      break;
	    case 'j':
	      bm->UserFlags.print_cnf_flag = true;
	      break;
            case 'n':
              bm->UserFlags.print_output_flag = true;
              break;
            case 'm':
              bm->UserFlags.smtlib_parser_flag=true;
              bm->UserFlags.division_by_zero_returns_one_flag = true;
              break;
            case 'p':
              bm->UserFlags.print_counterexample_flag = true;
              break;
            case 'q':
              bm->UserFlags.print_arrayval_declaredorder_flag = true;
              break;
            case 'r':
              bm->UserFlags.arrayread_refinement_flag = false;
              break;
            case 's' :
              bm->UserFlags.stats_flag = true;
              break;
            case 't':
              bm->UserFlags.quick_statistics_flag = true;
              break;
            case 'u':
              bm->UserFlags.arraywrite_refinement_flag = false;
              break;
            case 'v' :
              bm->UserFlags.print_nodes_flag = true;
              break;
            case 'w':
              bm->UserFlags.wordlevel_solve_flag = false;
              break;
            case 'x':
              bm->UserFlags.xor_flatten_flag = true;
              break;
            case 'y':
              bm->UserFlags.print_binary_flag = true;
              break;            
            case 'z':
              bm->UserFlags.print_sat_varorder_flag = true;
              break;
            default:
              fprintf(stderr,usage,prog);
              cout << helpstring;
              //FatalError("");
              return -1;
              break;
            }
        } else {          
        infile = argv[i];
        if (bm->UserFlags.smtlib_parser_flag)
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

  //want to print the output always from the commandline.
  bm->UserFlags.print_output_flag = true;
  ASTVec * AssertsQuery = new ASTVec;
  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if(0 != c) {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }
  
  bm->GetRunTimes()->start(RunTimes::Parsing);
  if (bm->UserFlags.smtlib_parser_flag)
    {
      smtparse((void*)AssertsQuery);
    }
  else
    {
      cvcparse((void*)AssertsQuery);
    }
  bm->GetRunTimes()->stop(RunTimes::Parsing);

  if(((ASTVec*)AssertsQuery)->empty())
    {
      FatalError("Input is Empty. Please enter some asserts and query\n");
    }

  if(((ASTVec*)AssertsQuery)->size() != 2)
    {
      FatalError("Input must contain a query\n");
    }

  ASTNode asserts = (*(ASTVec*)AssertsQuery)[0];
  //cout << "asserts: " << asserts << endl;
  ASTNode query   = (*(ASTVec*)AssertsQuery)[1];
  //cout << "query: " << query << endl;

  if(bm->UserFlags.print_STPinput_back_flag)
    {
      if(bm->UserFlags.smtlib_parser_flag)
        {
          // don't pass the query. It's not returned by the smtlib
          // parser.
          printer::SMTLIB_PrintBack(cout, asserts);
        }
      else
        {
          print_STPInput_Back(asserts, query);
        }
      return 0;
    } //end of PrintBack if

  SOLVER_RETURN_TYPE ret = GlobalSTP->TopLevelSTP(asserts, query);
  if (bm->UserFlags.quick_statistics_flag) 
    {
      bm->GetRunTimes()->print();
    }
  (GlobalSTP->tosat)->PrintOutput(ret);
  return 0;
}//end of Main

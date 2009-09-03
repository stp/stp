/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-
#include "../AST.h"
#include "AssortedPrinters.h"
#include "printers.h"

namespace BEEV
{
  /******************************************************************
   * Assorted print routines collected in one place. The code here is
   * different from the one in printers directory. It is possible that
   * there is some duplication.
   *
   * FIXME: Get rid of any redundant code
   ******************************************************************/  

  ostream &ASTNode::LispPrint(ostream &os, int indentation) const
  {
    printer::Lisp_Print(os, *this, indentation);
  }

  ostream &ASTNode::LispPrint_indent(ostream &os, int indentation) const
  {
    printer::Lisp_Print_indent(os, *this, indentation);
  }

  ostream& ASTNode::PL_Print(ostream &os,  int indentation) const
  {
    printer::PL_Print(os, *this, indentation);
  }

  //This is the IO manipulator.  It builds an object of class
  //"LispPrinter" that has a special overloaded "<<" operator.
  inline LispPrinter lisp(const ASTNode &node, int indentation = 0)
  {
    LispPrinter lp(node, indentation);
    return lp;
  } //end of LispPrinter_lisp

  //iomanipulator. builds an object of class "LisPrinter" that has a
  //special overloaded "<<" operator.
  inline LispVecPrinter lisp(const ASTVec &vec, int indentation = 0)
  {
    LispVecPrinter lvp(vec, indentation);
    return lvp;
  } //end of LispVecPrinter_lisp()

  // FIXME: Made non-ref in the hope that it would work better.
  void lp(ASTNode node)
  {
    cout << lisp(node) << endl;
  }

  void lpvec(const ASTVec &vec)
  {
    vec[0].GetBeevMgr().AlreadyPrintedSet.clear();
    LispPrintVec(cout, vec, 0);
    cout << endl;
  }

  // GLOBAL FUNCTION: Prints statistics from the MINISAT Solver
  void BeevMgr::PrintStats(MINISAT::Solver& s)
  {
    if (!stats_flag)
      return;
    double cpu_time = MINISAT::cpuTime();
    uint64_t mem_used = MINISAT::memUsed();
    reportf("restarts              : %llu\n",                      s.starts);
    reportf("conflicts             : %llu   (%.0f /sec)\n",        s.conflicts   , s.conflicts   /cpu_time);
    reportf("decisions             : %llu   (%.0f /sec)\n",        s.decisions   , s.decisions   /cpu_time);
    reportf("propagations          : %llu   (%.0f /sec)\n",        s.propagations, s.propagations/cpu_time);
    reportf("conflict literals     : %llu   (%4.2f %% deleted)\n", s.tot_literals,
            (s.max_literals - s.tot_literals)*100 / (double)s.max_literals);
    if (mem_used != 0)
      reportf("Memory used           : %.2f MB\n", mem_used / 1048576.0);
    reportf("CPU time              : %g s\n", cpu_time);
  } //end of PrintStats()
  
  // Prints Satisfying assignment directly, for debugging.
  void BeevMgr::PrintSATModel(MINISAT::Solver& newS)
  {
    if (!newS.okay())
      FatalError("PrintSATModel: NO COUNTEREXAMPLE TO PRINT", ASTUndefined);
    // FIXME: Don't put tests like this in the print functions.  The print functions
    // should print unconditionally.  Put a conditional around the call if you don't
    // want them to print
    if (!(stats_flag && print_nodes_flag))
      return;

    int num_vars = newS.nVars();
    cout << "Satisfying assignment: " << endl;
    for (int i = 0; i < num_vars; i++)
      {
        if (newS.model[i] == MINISAT::l_True)
          {
            ASTNode s = _SATVar_to_AST[i];
            cout << s << endl;
          }
        else if (newS.model[i] == MINISAT::l_False)
          {
            ASTNode s = _SATVar_to_AST[i];
            cout << CreateNode(NOT, s) << endl;
          }
      }
  } //end of PrintSATModel()


  /* FUNCTION: prints a counterexample for INVALID inputs.  iterate
   * through the CounterExampleMap data structure and print it to
   * stdout
   */
  void BeevMgr::PrintCounterExample(bool t, std::ostream& os)
  {
    //global command-line option
    // FIXME: This should always print the counterexample.  If you want
    // to turn it off, check the switch at the point of call.
    if (!print_counterexample_flag)
      {
        return;
      }

    //input is valid, no counterexample to print
    if (ValidFlag)
      {
        return;
      }

    //if this option is true then print the way dawson wants using a
    //different printer. do not use this printer.
    if (print_arrayval_declaredorder_flag)
      {
        return;
      }

    //t is true if SAT solver generated a counterexample, else it is
    //false
    if (!t)
      {
        cerr << "PrintCounterExample: No CounterExample to print: " << endl;
        return;
      }

    //os << "\nCOUNTEREXAMPLE: \n" << endl;
    ASTNodeMap::iterator it = CounterExampleMap.begin();
    ASTNodeMap::iterator itend = CounterExampleMap.end();
    for (; it != itend; it++)
      {
        ASTNode f = it->first;
        ASTNode se = it->second;

        if (ARRAY_TYPE == se.GetType())
          {
            FatalError("TermToConstTermUsingModel: entry in counterexample is an arraytype. bogus:", se);
          }

        //skip over introduced variables
        if (f.GetKind() == SYMBOL && (_introduced_symbols.find(f) != _introduced_symbols.end()))
          continue;
        if (f.GetKind() == SYMBOL || (f.GetKind() == READ && f[0].GetKind() == SYMBOL && f[1].GetKind() == BVCONST))
          {
            os << "ASSERT( ";
            f.PL_Print(os,0);
            os << " = ";
            if (BITVECTOR_TYPE == se.GetType())
              {
                TermToConstTermUsingModel(se, false).PL_Print(os, 0);
              }
            else
              {
                se.PL_Print(os, 0);
              }
            os << " );" << endl;
          }
      }
    //os << "\nEND OF COUNTEREXAMPLE" << endl;
  } //End of PrintCounterExample


  /* iterate through the CounterExampleMap data structure and print it
   * to stdout. this function prints only the declared array variables
   * IN the ORDER in which they were declared. It also assumes that
   * the variables are of the form 'varname_number'. otherwise it will
   * not print anything. This function was specifically written for
   * Dawson Engler's group (bug finding research group at Stanford)
   */
  void BeevMgr::PrintCounterExample_InOrder(bool t)
  {
    //global command-line option to print counterexample. we do not
    //want both counterexample printers to print at the sametime.
    // FIXME: This should always print the counterexample.  If you want
    // to turn it off, check the switch at the point of call.
    if (print_counterexample_flag)
      return;

    //input is valid, no counterexample to print
    if (ValidFlag)
      return;

    //print if the commandline option is '-q'. allows printing the
    //counterexample in order.
    if (!print_arrayval_declaredorder_flag)
      return;

    //t is true if SAT solver generated a counterexample, else it is
    //false
    if (!t)
      {
        cerr << "PrintCounterExample: No CounterExample to print: " << endl;
        return;
      }

    //vector to store the integer values
    std::vector<int> out_int;
    cout << "% ";
    for (ASTVec::iterator it = _special_print_set.begin(), itend = _special_print_set.end(); it != itend; it++)
      {
        if (ARRAY_TYPE == it->GetType())
          {
            //get the name of the variable
            const char * c = it->GetName();
            std::string ss(c);
            if (!(0 == strncmp(ss.c_str(), "ini_", 4)))
              continue;
            reverse(ss.begin(), ss.end());

            //cout << "debugging: " << ss;
            size_t pos = ss.find('_', 0);
            if (!((0 < pos) && (pos < ss.size())))
              continue;

            //get the associated length
            std::string sss = ss.substr(0, pos);
            reverse(sss.begin(), sss.end());
            int n = atoi(sss.c_str());

            it->PL_Print(cout, 2);
            for (int j = 0; j < n; j++)
              {
                ASTNode index = CreateBVConst(it->GetIndexWidth(), j);
                ASTNode readexpr = CreateTerm(READ, it->GetValueWidth(), *it, index);
                ASTNode val = GetCounterExample(t, readexpr);
                //cout << "ASSERT( ";
                //cout << " = ";
                out_int.push_back(GetUnsignedConst(val));
                //cout << "\n";
              }
          }
      }
    cout << endl;
    for (unsigned int jj = 0; jj < out_int.size(); jj++)
      cout << out_int[jj] << endl;
    cout << endl;
  } //End of PrintCounterExample_InOrder


  void BeevMgr::printCacheStatus()
  {
    cerr << SimplifyMap->size() << endl;
    cerr << SimplifyNegMap->size() << endl;
    cerr << ReferenceCount->size() << endl;
    cerr << TermsAlreadySeenMap.size() << endl;

    cerr << SimplifyMap->bucket_count() << endl;
    cerr << SimplifyNegMap->bucket_count() << endl;
    cerr << ReferenceCount->bucket_count() << endl;
    cerr << TermsAlreadySeenMap.bucket_count() << endl;
  } //printCacheStatus()

  //This function prints the output of the STP solver
  void BeevMgr::PrintOutput(bool true_iff_valid)
  {
    if (print_output_flag)
      {
        if (smtlib_parser_flag)
          {
            if (true_iff_valid && 
		(BEEV::input_status == TO_BE_SATISFIABLE))
              {
                cerr << "Warning. Expected satisfiable, FOUND unsatisfiable" << endl;
              }
            else if (!true_iff_valid && 
		     (BEEV::input_status == TO_BE_UNSATISFIABLE))
              {
                cerr << "Warning. Expected unsatisfiable, FOUND satisfiable" << endl;
              }
          }
      }

    if (true_iff_valid)
      {
        ValidFlag = true;
        if (print_output_flag)
          {
            if (smtlib_parser_flag)
              cout << "unsat\n";
            else
              cout << "Valid.\n";
          }
      }
    else
      {
        ValidFlag = false;
        if (print_output_flag)
          {
            if (smtlib_parser_flag)
              cout << "sat\n";
            else
              cout << "Invalid.\n";
          }
      }
  } //end of PrintOutput()


  void BeevMgr::PrintClauseList(ostream& os, BeevMgr::ClauseList& cll)
  {
    int num_clauses = cll.size();
    os << "Clauses: " << endl << "=========================================" << endl;
    for (int i = 0; i < num_clauses; i++)
      {
        os << "Clause " << i << endl << "-------------------------------------------" << endl;
        LispPrintVecSpecial(os, *cll[i], 0);
        os << endl << "-------------------------------------------" << endl;
      }
  } //end of PrintClauseList()

  //Variable Order Printer: A global function which converts a MINISAT
  //var into a ASTNODE var. It then prints this var along with
  //variable order dcisions taken by MINISAT.
  void Convert_MINISATVar_To_ASTNode_Print(int minisat_var, 
					   int decision_level, int polarity)
  {
    BEEV::ASTNode vv = globalBeevMgr_for_parser->_SATVar_to_AST[minisat_var];
    cout << spaces(decision_level);
    if (polarity)
      {
        cout << "!";
      }
    printer::PL_Print(cout,vv, 0);
    cout << endl;
  }

};//end of namespace BEEV

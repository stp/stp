// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#include "ToSAT.h"
#include "ToSAT.h"
#include "BitBlastNew.h"
#include "../printer/printers.h"
#include <iostream>
#include <fstream>

namespace BEEV
{

  bool isTseitinVariable(const ASTNode& n) {
    if (n.GetKind() == SYMBOL && n.GetType() == BOOLEAN_TYPE) {
      const char * zz = n.GetName();
      if (0 == strncmp("cnf", zz, 3))
        {
          return true;
        }
    }
    return false;
  }

  /* FUNCTION: lookup or create a new MINISAT literal
   * lookup or create new MINISAT Vars from the global MAP
   * _ASTNode_to_SATVar.
   */

  MINISAT::Var 
  ToSAT::LookupOrCreateSATVar(MINISAT::Solver& newSolver, const ASTNode& n)
  {
    ASTtoSATMap::iterator it;
    MINISAT::Var v;

    //look for the symbol in the global map from ASTNodes to ints. if
    //not found, create a S.newVar(), else use the existing one.
    if ((it = _ASTNode_to_SATVar_Map.find(n)) == _ASTNode_to_SATVar_Map.end())
      {
        v = newSolver.newVar();
        _ASTNode_to_SATVar_Map[n] = v;

        //ASSUMPTION: I am assuming that the newSolver.newVar() call increments v
        //by 1 each time it is called, and the initial value of a
        //MINISAT::Var is 0.
        _SATVar_to_AST_Vector.push_back(n);

        // experimental. Don't add Tseitin variables as decision variables.
        if (!bm->UserFlags.tseitin_are_decision_variables_flag && isTseitinVariable(n))
          {
            newSolver.setDecisionVar(v,false);
          }

      }
    else
      v = it->second;
    return v;
  }

  /* FUNCTION: convert ASTClauses to MINISAT clauses and solve.
   * Accepts ASTClauses and converts them to MINISAT clauses. Then
   * adds the newly minted MINISAT clauses to the local SAT instance,
   * and calls solve(). If solve returns unsat, then stop and return
   * unsat. else continue.
   */
  bool ToSAT::toSATandSolve(MINISAT::Solver& newSolver,
                            ClauseList& cll, 
			    bool add_xor_clauses,
			    bool enable_clausal_abstraction)
  {
    CountersAndStats("SAT Solver", bm);
    bm->GetRunTimes()->start(RunTimes::SendingToSAT);

    
    int input_clauselist_size = cll.size();
    if (cll.size() == 0)
      {
        FatalError("toSATandSolve: Nothing to Solve", ASTUndefined);    
      }

    if(bm->UserFlags.random_seed_flag)
      {
#ifdef CRYPTOMINISAT2
	newSolver.setSeed(bm->UserFlags.random_seed);
#endif
      }

	ClauseContainer& cc = *cll.asList();

    //iterate through the list (conjunction) of ASTclauses cll
    ClauseContainer::const_iterator i = cc.begin(), iend = cc.end();
    for (int count=0, flag=0; i != iend; i++)
      {
        //Clause for the SATSolver
        MINISAT::vec<MINISAT::Lit> satSolverClause;
        satSolverClause.capacity((*i)->size());        
        vector<const ASTNode*>::const_iterator j    = (*i)->begin(); 
        vector<const ASTNode*>::const_iterator jend = (*i)->end();      
        //ASTVec  clauseVec;
        //j is a disjunct in the ASTclause (*i)
        for (; j != jend; j++)
          {         
            ASTNode node = **j;
            //clauseVec.push_back(node);
            bool negate = (NOT == node.GetKind()) ? true : false;
            ASTNode n = negate ? node[0] : node;
            MINISAT::Var v = LookupOrCreateSATVar(newSolver, n);
            MINISAT::Lit l(v, negate);
            satSolverClause.push(l);
          }

        // ASTNode theClause = bm->CreateNode(OR, clauseVec);
        //      if(flag 
        //         && ASTTrue == CheckBBandCNF(newSolver, theClause))
        //        {
        //          continue;
        //        }
#if defined CRYPTOMINISAT2
        if(add_xor_clauses)
          {
            newSolver.addXorClause(satSolverClause, false);
          }
        else 
          {
            newSolver.addClause(satSolverClause);
          }
#else
        newSolver.addClause(satSolverClause);
#endif

#if defined CRYPTOMINISAT2
    newSolver.findNormalXors = false;
    newSolver.doSubsumption = false;
    newSolver.verbosity = 0;
    newSolver.doPartHandler = false;
#endif

// 	if(enable_clausal_abstraction && 
// 	   count++ >= input_clauselist_size*CLAUSAL_ABSTRACTION_CUTOFF)
// 	  {
// 	    //Arbitrary adding only x% of the clauses in the hopes of
// 	    //terminating early 
// 	    //      cout << "Percentage clauses added: " 
// 	    //           << percentage << endl;
// 	    bm->GetRunTimes()->stop(RunTimes::SendingToSAT);
// 	    bm->GetRunTimes()->start(RunTimes::Solving);
// 	    newSolver.solve();
// 	    bm->GetRunTimes()->stop(RunTimes::Solving);
// 	    if(!newSolver.okay())
// 	      {
// 		return false;         
// 	      }
// 	    count = 0;
// 	    flag  = 1;
// 	    bm->GetRunTimes()->start(RunTimes::SendingToSAT);
// 	  }

	if (newSolver.okay())
          {
            continue;
          }     
        else
          {
            bm->PrintStats(newSolver);
            bm->GetRunTimes()->stop(RunTimes::SendingToSAT);
            cll.deleteJustVectors();
            return false;
          }     
      } // End of For-loop adding the clauses 

    // output a CNF
    // Because we use the SAT solver incrementally, this may ouput little pieces of the
    // CNF that need to be joined together. Nicer would be to read it out of the solver each time.
    	if (bm->UserFlags.output_CNF_flag && true)
    	{
			#if defined CRYPTOMINISAT2
				cerr << "The -j option will give you the xor clauses that this one doesn't" << endl;
			#endif

    		ofstream file;
    		stringstream fileName;
    		fileName << "output_" << CNFFileNameCounter++ << ".cnf";
    		file.open(fileName.str().c_str());

    		file << "p cnf " << newSolver.nVars() << " " << cll.size() << endl;
    		i = cc.begin(), iend = cc.end();
    		for (; i != iend; i++)
    		{
    			vector<const ASTNode*>::iterator j = (*i)->begin(), jend =
    					(*i)->end();
    			for (; j != jend; j++)
    			{
    				const ASTNode& node = *(*j);
    	            bool negate = (NOT == node.GetKind()) ? true : false;
    	            ASTNode n = negate ? node[0] : node;

    	            ASTtoSATMap::iterator it =  _ASTNode_to_SATVar_Map.find(n);
    	            assert(it != _ASTNode_to_SATVar_Map.end());

    	            MINISAT::Var v = it->second;

    				if (negate)
    					file << -(v + 1) << " ";
    				else
    					file << (v + 1) << " ";
    			}
    			file << "0" << endl;
    		}
    		file.close();

    	}

    // Free the clause list before SAT solving.
    cll.deleteJustVectors();

    bm->GetRunTimes()->stop(RunTimes::SendingToSAT);
    bm->GetRunTimes()->start(RunTimes::Solving);    
    newSolver.solve();
    bm->GetRunTimes()->stop(RunTimes::Solving);
    bm->PrintStats(newSolver);
    if (newSolver.okay())
      return true;
    else
      return false;
  } //end of toSATandSolve()

  //Bucketize clauses into buckets of size 1,2,...CLAUSAL_BUCKET_LIMIT
  static ClauseBuckets * Sort_ClauseList_IntoBuckets(ClauseList * cl)
  {
    ClauseBuckets * cb = new ClauseBuckets();
    ClauseContainer* cc = cl->asList();

    //Sort the clauses, and bucketize by the size of the clauses
    for(ClauseContainer::iterator it = cc->begin(), itend = cc->end();
        it!=itend; it++)
      {
        ClausePtr cptr = *it;
        int cl_size = cptr->size();
        if(cl_size >= CLAUSAL_BUCKET_LIMIT)
          {
            cl_size = CLAUSAL_BUCKET_LIMIT;
          }

        //If no clauses of size cl_size have been seen, then create a
        //bucket for that size
        if(cb->find(cl_size) == cb->end())
          {
            ClauseList * cllist = new ClauseList();
            cllist->push_back(cptr);
            (*cb)[cl_size] = cllist;
          }
        else
          {
            ClauseList * cllist = (*cb)[cl_size];
            cllist->push_back(cptr);
          }
      }

    return cb;
  } //End of SortClauseList_IntoBuckets()

  bool ToSAT::CallSAT_On_ClauseBuckets(MINISAT::Solver& SatSolver,
                                       ClauseBuckets * cb)
  {
    ClauseBuckets::iterator it = cb->begin();
    ClauseBuckets::iterator itend = cb->end();

    bool sat = false;
    for(int count=1;it!=itend;it++, count++)
      {
        ClauseList *cl = (*it).second;
	    sat = toSATandSolve(SatSolver,*cl);

        if(!sat)
          {
            return sat;
          }
      }
    return sat;
  }



  //Call the SAT solver, and check the result before returning. This
  //can return one of 3 values, SOLVER_VALID, SOLVER_INVALID or
  //SOLVER_UNDECIDED
  bool ToSAT::CallSAT(MINISAT::Solver& SatSolver,
                      const ASTNode& input)
  {
    bm->GetRunTimes()->start(RunTimes::BitBlasting);

    ASTNode BBFormula;
    {
    	BitBlasterNew BB(bm);
    	BBNodeSet set;
    	BBFormula = BB.BBForm(input,set);
    	assert(set.size() == 0); // doesn't yet work.
    }

    bm->ASTNodeStats("after bitblasting: ", BBFormula);
    bm->GetRunTimes()->stop(RunTimes::BitBlasting);

    if (bm->UserFlags.output_bench_flag)
    {
		ofstream file;
		stringstream fileName;
		fileName << "output_" << benchFileNameCounter++ << ".bench";
		file.open(fileName.str().c_str());
		printer::Bench_Print(file,BBFormula);
		file.close();
    }

    CNFMgr cm(bm);
    ClauseList* cl = cm.convertToCNF(BBFormula);

    ClauseList* xorcl = cm.ReturnXorClauses();

    ClauseBuckets * cb = Sort_ClauseList_IntoBuckets(cl);
    cl->asList()->clear(); // clause buckets now point to the clauses.
    delete cl;
    bool sat = CallSAT_On_ClauseBuckets(SatSolver, cb);

    for (ClauseBuckets::iterator it = cb->begin(); it != cb->end(); it++)
    	delete it->second;
    delete cb;

    if(!sat)
      {
    	xorcl->deleteJustVectors();
    	delete xorcl;
    	return sat;
      }

#if defined CRYPTOMINISAT2
    if(!xorcl->empty())
      {
        sat = toSATandSolve(SatSolver, *xorcl, true);
      }
#endif


    delete xorcl;
    return sat;
  }

  //##################################################
  //##################################################

  /*******************************************************************
   * Helper Functions
   *******************************************************************/

  //This function prints the output of the STP solver
  void ToSAT::PrintOutput(SOLVER_RETURN_TYPE ret)
  {
    bool true_iff_valid = (SOLVER_VALID == ret);

    if (bm->UserFlags.print_output_flag)
      {
        if (bm->UserFlags.smtlib_parser_flag)
          {
            if (true_iff_valid &&
                (input_status == TO_BE_SATISFIABLE))
              {
                cerr << "Warning. Expected satisfiable,"\
                  " FOUND unsatisfiable" << endl;
              }
            else if (!true_iff_valid &&
                     (input_status == TO_BE_UNSATISFIABLE))
              {
                cerr << "Warning. Expected unsatisfiable,"\
                  " FOUND satisfiable" << endl;
              }
          }
      }

    if (true_iff_valid)
      {
        bm->ValidFlag = true;
        if (bm->UserFlags.print_output_flag)
          {
            if (bm->UserFlags.smtlib_parser_flag)
              cout << "unsat\n";
            else
              cout << "Valid.\n";
          }
      }
    else
      {
        bm->ValidFlag = false;
        if (bm->UserFlags.print_output_flag)
          {
            if (bm->UserFlags.smtlib_parser_flag)
              cout << "sat\n";
            else
              cout << "Invalid.\n";
          }
      }
  } //end of PrintOutput()

#if 0

  // Looks up truth value of ASTNode SYMBOL in MINISAT satisfying
  // assignment.
  ASTNode ToSAT::SymbolTruthValue(MINISAT::Solver &newSolver, ASTNode form)
  {
    MINISAT::Var satvar = _ASTNode_to_SATVar_Map[form];
    if (newSolver.model[satvar] == MINISAT::l_False)
      {
        return ASTFalse;
      }
    else
      {
        // True or undefined.
        return ASTTrue;
      }
  }

  // This function is for debugging problems with BitBlast and
  // especially ToCNF. It evaluates the bit-blasted formula in the
  // satisfying assignment.  While doing that, it checks that every
  // subformula has the same truth value as its representative
  // literal, if it has one.  If this condition is violated, it halts
  // immediately (on the leftmost lowest term).  Use CreateSimpForm to
  // evaluate, even though it's expensive, so that we can use the
  // partial truth assignment.
  ASTNode ToSAT::CheckBBandCNF(MINISAT::Solver& newSolver, ASTNode form)
  {
    // Clear memo table (in case newSolver has changed).
    CheckBBandCNFMemo.clear();
    // Call recursive version that does the work.
    return CheckBBandCNF_int(newSolver, form);
  } //End of CheckBBandCNF()

  // Recursive body CheckBBandCNF
  ASTNode ToSAT::CheckBBandCNF_int(MINISAT::Solver& newSolver, ASTNode form)
  {
    //     cout << "++++++++++++++++" 
    //   << endl 
    //   << "CheckBBandCNF_int form = " 
    //   << form << endl;
    
    ASTNodeMap::iterator memoit = CheckBBandCNFMemo.find(form);
    if (memoit != CheckBBandCNFMemo.end())
      {
        // found it.  Return memoized value.
        return memoit->second;
      }

    ASTNode result; // return value, to memoize.

    Kind k = form.GetKind();
    switch (k)
      {
      case TRUE:
      case FALSE:
        {
          return form;
          break;
        }
      case SYMBOL:
      case BVGETBIT:
        {
          result = SymbolTruthValue(newSolver, form);

          //           cout << "================" 
          //                << endl 
          //                << "Checking BB formula:" 
          //                << form << endl;
          //           cout << "----------------" 
          //                << endl 
          //                << "Result:" << result << endl;
          break;
        }
      default:
        {
          // Evaluate the children recursively.
          ASTVec eval_children;
          ASTVec ch = form.GetChildren();
          ASTVec::iterator itend = ch.end();
          for (ASTVec::iterator it = ch.begin(); it < itend; it++)
            {
              eval_children.push_back(CheckBBandCNF_int(newSolver, *it));
            }
          result = bm->CreateSimpForm(k, eval_children);

          //           cout << "================" 
          //                << endl 
          //                << "Checking BB formula:" << form << endl;
          //           cout << "----------------" 
          //                << endl 
          //                << "Result:" << result << endl;
          
          ASTNode replit_eval;
          // Compare with replit, if there is one.
          ASTNodeMap::iterator replit_it = RepLitMap.find(form);
          if (replit_it != RepLitMap.end())
            {
              ASTNode replit = RepLitMap[form];
              // Replit is symbol or not symbol.
              if (SYMBOL == replit.GetKind())
                {
                  replit_eval = SymbolTruthValue(newSolver, replit);
                }
              else
                {
                  // It's (NOT sym).  Get value of sym and complement.
                  replit_eval = 
                    bm->CreateSimpNot(SymbolTruthValue(newSolver, replit[0]));
                }

              //               cout << "----------------" 
              //                    << endl 
              //                    << "Rep lit: " << replit << endl;
              //               cout << "----------------" 
              //                    << endl 
              //                    << "Rep lit value: " << replit_eval << endl;

              if (result != replit_eval)
                {
                  // Hit the panic button.
                  FatalError("Truth value of BitBlasted formula "\
                             "disagrees with representative literal in CNF.");
                }
            }
          else
            {
              //cout << "----------------" << endl << "No rep lit" << endl;
            }

        }
      }

    return (CheckBBandCNFMemo[form] = result);
  } //end of CheckBBandCNF_int()
#endif
}; //end of namespace BEEV

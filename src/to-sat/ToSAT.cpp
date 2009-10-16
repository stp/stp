// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#include "ToSAT.h"

namespace BEEV
{
  /* FUNCTION: lookup or create a new MINISAT literal
   * lookup or create new MINISAT Vars from the global MAP
   * _ASTNode_to_SATVar.
   */
  MINISAT::Var 
  ToSAT::LookupOrCreateSATVar(MINISAT::Solver& newS, const ASTNode& n)
  {
    ASTtoSATMap::iterator it;
    MINISAT::Var v;

    //look for the symbol in the global map from ASTNodes to ints. if
    //not found, create a S.newVar(), else use the existing one.
    if ((it = _ASTNode_to_SATVar_Map.find(n)) == _ASTNode_to_SATVar_Map.end())
      {
        v = newS.newVar();
        _ASTNode_to_SATVar_Map[n] = v;

        //ASSUMPTION: I am assuming that the newS.newVar() call increments v
        //by 1 each time it is called, and the initial value of a
        //MINISAT::Var is 0.
        _SATVar_to_AST_Vector.push_back(n);
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
  bool ToSAT::toSATandSolve(MINISAT::Solver& newS, ClauseList& cll)
  {
    CountersAndStats("SAT Solver", bm);

    bm->GetRunTimes()->start(RunTimes::SendingToSAT);

    //iterate through the list (conjunction) of ASTclauses cll
    ClauseList::const_iterator i = cll.begin(), iend = cll.end();

    if (i == iend)
      FatalError("toSATandSolve: Nothing to Solve", ASTUndefined);

    //turnOffSubsumption
    // MKK: My understanding is that the rougly equivalent effect is had
    // through setting the second argument of MINISAT::Solver::solve to
    // true
    //newS.turnOffSubsumption();

    // (*i) is an ASTVec-ptr which denotes an ASTclause
    //****************************************
    // *i = vector<const ASTNode*>*
    //****************************************
    for (; i != iend; i++)
      {
        //Clause for the SATSolver
        MINISAT::vec<MINISAT::Lit> satSolverClause;
        satSolverClause.capacity((*i)->size());

        //now iterate through the internals of the ASTclause itself
        vector<const ASTNode*>::const_iterator j = (*i)->begin(); 
        vector<const ASTNode*>::const_iterator jend = (*i)->end();
        
        //j is a disjunct in the ASTclause (*i)
        for (; j != jend; j++)
          {
            ASTNode node = **j;

            bool negate = (NOT == node.GetKind()) ? true : false;
            ASTNode n = negate ? node[0] : node;

            //Lookup or create the MINISAT::Var corresponding to the Booelan
            //ASTNode Variable, and push into sat Solver clause
            MINISAT::Var v = LookupOrCreateSATVar(newS, n);
            MINISAT::Lit l(v, negate);
            satSolverClause.push(l);
          }
        newS.addClause(satSolverClause);
        // clause printing.
        // (printClause<MINISAT::vec<MINISAT::Lit> >)(satSolverClause);
        // cout << " 0 ";
        // cout << endl;

        if (newS.okay())
          {
            continue;
          }
        else
          {
            bm->PrintStats(newS);
            bm->GetRunTimes()->stop(RunTimes::SendingToSAT);
            return false;
          }
      }

    bm->GetRunTimes()->stop(RunTimes::SendingToSAT);

    // if input is UNSAT return false, else return true
    if (!newS.simplify())
      {
        bm->PrintStats(newS);
        return false;
      }

    //PrintActivityLevels_Of_SATVars("Before SAT:",newS);
    //ChangeActivityLevels_Of_SATVars(newS);
    //PrintActivityLevels_Of_SATVars("Before SAT and after initial
    //bias:",newS); newS.solve();

    bm->GetRunTimes()->start(RunTimes::Solving);
    newS.solve();
    bm->GetRunTimes()->stop(RunTimes::Solving);

    //PrintActivityLevels_Of_SATVars("After SAT",newS);

    bm->PrintStats(newS);
    if (newS.okay())
      return true;
    else
      return false;
  } //end of toSATandSolve()

  // Looks up truth value of ASTNode SYMBOL in MINISAT satisfying
  // assignment.  Returns ASTTrue if true, ASTFalse if false or
  // undefined.
  ASTNode ToSAT::SymbolTruthValue(MINISAT::Solver &newS, ASTNode form)
  {
    MINISAT::Var satvar = _ASTNode_to_SATVar_Map[form];
    if (newS.model[satvar] == MINISAT::l_True)
      {
        return ASTTrue;
      }
    else
      {
        // False or undefined.
        return ASTFalse;
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
  ASTNode ToSAT::CheckBBandCNF(MINISAT::Solver& newS, ASTNode form)
  {
    // Clear memo table (in case newS has changed).
    CheckBBandCNFMemo.clear();
    // Call recursive version that does the work.
    return CheckBBandCNF_int(newS, form);
  } //End of CheckBBandCNF()

  // Recursive body CheckBBandCNF FIXME: Modify this to just check if
  // result is true, and print mismatch if not.  Might have a trace
  // flag for the other stuff.
  ASTNode ToSAT::CheckBBandCNF_int(MINISAT::Solver& newS, ASTNode form)
  {
    //    cout << "++++++++++++++++" << endl << "CheckBBandCNF_int form = " <<
    //      form << endl;

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
          // Look up the truth value
          // ASTNode -> Sat -> Truthvalue -> ASTTrue or ASTFalse;
          // FIXME: Could make up a fresh var in undefined case.

          result = SymbolTruthValue(newS, form);

          cout << "================" 
	       << endl 
	       << "Checking BB formula:" 
	       << form << endl;
          cout << "----------------" 
	       << endl 
	       << "Result:" << result << endl;

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
              eval_children.push_back(CheckBBandCNF_int(newS, *it));
            }
          result = bm->CreateSimpForm(k, eval_children);

          cout << "================" 
	       << endl 
	       << "Checking BB formula:" << form << endl;
          cout << "----------------" 
	       << endl 
	       << "Result:" << result << endl;

          ASTNode replit_eval;
          // Compare with replit, if there is one.
          ASTNodeMap::iterator replit_it = RepLitMap.find(form);
          if (replit_it != RepLitMap.end())
            {
              ASTNode replit = RepLitMap[form];
              // Replit is symbol or not symbol.
              if (SYMBOL == replit.GetKind())
                {
                  replit_eval = SymbolTruthValue(newS, replit);
                }
              else
                {
                  // It's (NOT sym).  Get value of sym and complement.
                  replit_eval = 
		    bm->CreateSimpNot(SymbolTruthValue(newS, replit[0]));
                }

              cout << "----------------" 
		   << endl 
		   << "Rep lit: " << replit << endl;
              cout << "----------------" 
		   << endl 
		   << "Rep lit value: " << replit_eval << endl;

              if (result != replit_eval)
                {
                  // Hit the panic button.
                  FatalError("Truth value of BitBlasted formula "\
			     "disagrees with representative literal in CNF.");
                }
            }
          else
            {
              cout << "----------------" << endl << "No rep lit" << endl;
            }

        }
      }

    return (CheckBBandCNFMemo[form] = result);
  } //end of CheckBBandCNF_int()
}; //end of namespace BEEV

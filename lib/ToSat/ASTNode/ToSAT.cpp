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
#include "stp/ToSat/ASTNode/ToSAT.h"
#include "stp/ToSat/BitBlaster.h"
#include "stp/Printer/printers.h"
#include <iostream>
#include <fstream>
#include "stp/ToSat/ASTNode/BBNodeManagerASTNode.h"
#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/ToSat/ASTNode/ClauseList.h"
#include "stp/ToSat/ASTNode/ASTtoCNF.h"

namespace stp
{
using std::endl;

bool isTseitinVariable(const ASTNode& n)
{
  if (n.GetKind() == SYMBOL && n.GetType() == BOOLEAN_TYPE)
  {
    const char* zz = n.GetName();
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

uint32_t ToSAT::LookupOrCreateSATVar(SATSolver& newSolver, const ASTNode& n)
{
  // look for the symbol in the global map from ASTNodes to ints. if
  // not found, create a S.newVar(), else use the existing one.
  ASTtoSATMap::iterator it = _ASTNode_to_SATVar_Map.find(n);
  if ( it != _ASTNode_to_SATVar_Map.end())
    return it->second;

  //We have to create it.
  const uint32_t v = newSolver.newVar();
  _ASTNode_to_SATVar_Map[n] = v;

  // WARNING ASSUMPTION: I am assuming that the newSolver.newVar() call increments v
  // by 1 each time it is called, and the initial value of a
  // uint32_t is 0.

  // Copies the symbol into the map that is used to build the counter example.
  // For boolean we create a vector of size 1.
  if ((n.GetKind() == BOOLEXTRACT && n[0].GetKind() == SYMBOL) ||
      (n.GetKind() == SYMBOL && !isTseitinVariable(n)))
  {
    const ASTNode& symbol = n.GetKind() == BOOLEXTRACT ? n[0] : n;
    const unsigned index =
        n.GetKind() == BOOLEXTRACT ? n[1].GetUnsignedConst() : 0;
    const unsigned width =
        n.GetKind() == BOOLEXTRACT ? symbol.GetValueWidth() : 1;

    if (SATVar_to_SymbolIndex.find(symbol) == SATVar_to_SymbolIndex.end())
    {
      // In the SAT solver these are signed...
      vector<unsigned> vec(width, ~((unsigned)0));
      SATVar_to_SymbolIndex.insert(make_pair(symbol, vec));
    }
    assert(index < width);
    assert(SATVar_to_SymbolIndex[symbol].size() > index);

    SATVar_to_SymbolIndex[symbol][index] = v;
    return v;
  }
}

/* Convert ASTClauses to CNF clauses and solve.
 * Accepts ASTClauses and converts them to CNF clauses. Then
 * adds the newly minted CNF clauses to the local SAT instance,
 * and calls solve(). If solve returns unsat, then stop and return
 * unsat. else continue.
 */
bool ToSAT::toSATandSolve(SATSolver& newSolver, ClauseList& cll, bool final,
                          ASTtoCNF*& cm)
{
  CountersAndStats("SAT Solver", bm);
  bm->GetRunTimes()->start(RunTimes::SendingToSAT);

  if (cll.size() == 0)
  {
    FatalError("toSATandSolve: Nothing to Solve", ASTUndefined);
  }

  if (bm->UserFlags.random_seed_flag)
  {
    newSolver.setSeed(bm->UserFlags.random_seed);
  }

  ClauseContainer& cc = *cll.asList();

  if (bm->UserFlags.output_CNF_flag && true)
  {
    dump_to_cnf_file(newSolver, cll, &cc);
  }

  bool ret = fill_satsolver_with_clauses(cc, newSolver);
  cll.deleteJustVectors();
  if (!ret)
    return false;

  // Remove references to Tseitin variables.
  // Delete the cnf generator.
  if (final)
  {
    ASTVec toDelete;

    ASTtoSATMap::const_iterator it = _ASTNode_to_SATVar_Map.begin();
    for (; it != _ASTNode_to_SATVar_Map.end(); it++)
    {
      ASTNode n = it->first;
      if (!n.IsNull() && isTseitinVariable(n))
        toDelete.push_back(n);
    }

    for (ASTVec::iterator it = toDelete.begin(); it != toDelete.end(); it++)
      _ASTNode_to_SATVar_Map.erase(*it);

    delete cm;
    cm = NULL;
  }

  bm->GetRunTimes()->stop(RunTimes::SendingToSAT);
  bm->GetRunTimes()->start(RunTimes::Solving);
  newSolver.solve(bm->soft_timeout_expired);
  bm->GetRunTimes()->stop(RunTimes::Solving);
  if (bm->UserFlags.stats_flag)
    newSolver.printStats();
  if (newSolver.okay())
    return true;
  else
    return false;
}

bool ToSAT::fill_satsolver_with_clauses(ClauseContainer& cc,
                                        SATSolver& newSolver)
{
  // Clause for the SATSolver
  SATSolver::vec_literals satSolverClause;

  // iterate through the list (conjunction) of ASTclauses cll
  for (ClauseContainer::const_iterator i = cc.begin(), iend = cc.end();
       i != iend; i++)
  {
    satSolverClause.clear();
    for(vector<const ASTNode*>::const_iterator
      j = (*i)->begin(), jend = (*i)->end();
      j != jend; j++)
    {
      ASTNode node = **j;
      bool negate = (NOT == node.GetKind()) ? true : false;
      ASTNode n = negate ? node[0] : node;
      uint32_t v = LookupOrCreateSATVar(newSolver, n);
      Minisat::Lit l = SATSolver::mkLit(v, negate);
      satSolverClause.push(l);
    }

    newSolver.addClause(satSolverClause);

    if (!newSolver.okay()) {
      if (bm->UserFlags.stats_flag)
        newSolver.printStats();
      bm->GetRunTimes()->stop(RunTimes::SendingToSAT);

      return false;
    }
  }

  return true;
}

void ToSAT::dump_to_cnf_file(const SATSolver& newSolver,
                             const ClauseList& cll,
                             const ClauseContainer* cc
                            )
{
  // output a CNF

  // Because we use the SAT solver incrementally, this may ouput little pieces
  // of the CNF that need to be joined together. Nicer would be to read it out
  // of the solver each time.
  std::ofstream file;
  std::stringstream fileName;
  fileName << "output_" << CNFFileNameCounter++ << ".cnf";
  file.open(fileName.str().c_str());

  file << "p cnf " << newSolver.nVars() << " " << cll.size() << endl;
  for(ClauseContainer::const_iterator i = cc->begin(), iend = cc->end();
     i != iend; i++)
  {
    vector<const ASTNode*>::iterator j = (*i)->begin(), jend = (*i)->end();
    for (; j != jend; j++)
    {
      const ASTNode& node = *(*j);
      bool negate = (NOT == node.GetKind()) ? true : false;
      ASTNode n = negate ? node[0] : node;

      ASTtoSATMap::iterator it = _ASTNode_to_SATVar_Map.find(n);
      assert(it != _ASTNode_to_SATVar_Map.end());

      uint32_t v = it->second;

      if (negate)
        file << "-" << (v + 1) << " ";
      else
        file << (v + 1) << " ";
    }
    file << "0" << endl;
  }
  file.close();
}

// Bucketize clauses into buckets of size 1,2,...CLAUSAL_BUCKET_LIMIT
ClauseBuckets* ToSAT::Sort_ClauseList_IntoBuckets(
  ClauseList* cl,
  int clause_bucket_size)
{
  ClauseBuckets* cb = new ClauseBuckets;
  ClauseContainer* cc = cl->asList();

  // Sort the clauses, and bucketize by the size of the clauses
  for (ClauseContainer::iterator it = cc->begin(), itend = cc->end();
       it != itend; it++)
  {
    ClausePtr cptr = *it;
    int cl_size = cptr->size();
    if (cl_size >= clause_bucket_size)
    {
      cl_size = clause_bucket_size;
    }

    // If no clauses of size cl_size have been seen, then create a
    // bucket for that size
    if (cb->find(cl_size) == cb->end())
    {
      ClauseList* cllist = new ClauseList();
      cllist->push_back(cptr);
      (*cb)[cl_size] = cllist;
    }
    else
    {
      ClauseList* cllist = (*cb)[cl_size];
      cllist->push_back(cptr);
    }
  }

  return cb;
} 

bool ToSAT::CallSAT_On_ClauseBuckets(SATSolver& SatSolver, ClauseBuckets* cb,
                                     ASTtoCNF*& cm)
{
  ClauseBuckets::iterator it = cb->begin();
  ClauseBuckets::iterator itend = cb->end();

  bool sat = false;
  for (size_t count = 1; it != itend; it++, count++)
  {
    ClauseList* cl = (*it).second;
    sat = toSATandSolve(SatSolver, *cl, count == cb->size(), cm);

    if (!sat)
    {
      return sat;
    }
  }
  return sat;
}

// Call the SAT solver, and check the result before returning. This
// can return one of 3 values, SOLVER_VALID, SOLVER_INVALID or
// SOLVER_UNDECIDED
bool ToSAT::CallSAT(SATSolver& SatSolver, const ASTNode& input, bool refinement)
{
  bm->GetRunTimes()->start(RunTimes::BitBlasting);

  ASTNode BBFormula;
  {
    BBNodeManagerASTNode nm(bm);
    Simplifier simp(bm);
    BitBlaster<ASTNode, BBNodeManagerASTNode> BB(
        &nm, &simp, bm->defaultNodeFactory, &bm->UserFlags);
    BBFormula = BB.BBForm(input);
  }

  bm->ASTNodeStats("after bitblasting: ", BBFormula);
  bm->GetRunTimes()->stop(RunTimes::BitBlasting);

  if (bm->UserFlags.output_bench_flag)
  {
    std::ofstream file;
    std::stringstream fileName;
    fileName << "output_" << benchFileNameCounter++ << ".bench";
    file.open(fileName.str().c_str());
    printer::Bench_Print(file, BBFormula);
    file.close();
  }

  // The ASTtoCNF is deleted inside the CallSAT_On_ClauseBuckets,
  // just before the final call to the SAT solver.

  ASTtoCNF* to_cnf = new ASTtoCNF(bm);
  ClauseList* cl = to_cnf->convertToCNF(BBFormula);

  ClauseBuckets* cl_buckets = Sort_ClauseList_IntoBuckets(cl, 3);
  cl->asList()->clear(); // clause buckets now point to the clauses.
  delete cl;

  const bool sat = CallSAT_On_ClauseBuckets(SatSolver, cl_buckets, to_cnf);

  if (NULL != to_cnf)
    delete to_cnf;

  return sat;
}

/*******************************************************************
 * Helper Functions
 *******************************************************************/

#if 0

  // Looks up truth value of ASTNode SYMBOL in MINISAT satisfying
  // assignment.
  ASTNode ToSAT::SymbolTruthValue(SATSolver &newSolver, ASTNode form)
  {
    uint32_t satvar = _ASTNode_to_SATVar_Map[form];
    if (newSolver.model[satvar] == SATSolver::l_False)
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
  ASTNode ToSAT::CheckBBandCNF(SATSolver& newSolver, ASTNode form)
  {
    // Clear memo table (in case newSolver has changed).
    CheckBBandCNFMemo.clear();
    // Call recursive version that does the work.
    return CheckBBandCNF_int(newSolver, form);
  } //End of CheckBBandCNF()

  // Recursive body CheckBBandCNF
  ASTNode ToSAT::CheckBBandCNF_int(SATSolver& newSolver, ASTNode form)
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
      case BOOLEXTRACT:
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
                  FatalError("Truth value of BitBlasted formula disagrees with representative literal in CNF.");
                }
            }
          else
            {
              //cout << "----------------" << endl << "No rep lit" << endl;
            }

        }
      }

    return (CheckBBandCNFMemo[form] = result);
  }
#endif

} // end of namespace stp

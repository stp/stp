/********************************************************************
 *
 * BEGIN DATE: Apr, 2012
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

/*
 * Use the Bitblasted encoding as a propagator.
 */

#ifndef BBASPROP_H_
#define BBASPROP_H_

#include "stp/AST/AST.h"
#include "stp/Sat/CryptoMinisat5.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/ToSat/ToSATAIG.h"
#include "stp/ToSat/ToSATBase.h"
#include <unordered_set>

using simplifier::constantBitP::FixedBits;

class BBAsProp
{
public:
  stp::SATSolver::vec_literals assumptions;
  stp::ToSATAIG aig;
  std::unordered_set<unsigned> inputOutput;

  //input1, input2, result
  ASTNode i0, i1, r;
  stp::ToSAT::ASTNodeToSATVar node_to_satvar_map;

  Cnf_Dat_t* cnf;
  ~BBAsProp() 
  { 
    aig.release_cnf_memory(cnf);
  }

  BBAsProp(Kind k, stp::STPMgr* mgr, int bits)
      : aig(mgr, stp::GlobalSTP->arrayTransformer)
  {
    i0 = mgr->CreateSymbol("i0", 0, bits);
    i1 = mgr->CreateSymbol("i1", 0, bits);

    ASTNode eq;
    if (stp::is_Term_kind(k))
    {
      //result is 'bits' width
      ASTNode p = mgr->CreateTerm(k, bits, i0, i1);
      r = mgr->CreateSymbol("r", 0, bits);
      eq = mgr->CreateNode(stp::EQ, p, r);
    }
    else
    {
      //result is true/false
      ASTNode p = mgr->CreateNode(k, i0, i1);
      r = mgr->CreateSymbol("r", 0, 0);
      eq = mgr->CreateNode(stp::IFF, p, r);
    }

    cnf = aig.bitblast(eq, false);
    std::cerr << "Number of clauses:" << cnf->nClauses << std::endl;

    node_to_satvar_map = aig.SATVar_to_SymbolIndexMap();

    inputOutput.clear();
    for (int i = 0; i < bits; i++)
    {
      inputOutput.insert(node_to_satvar_map.find(i0)->second[i]);
      inputOutput.insert(node_to_satvar_map.find(i1)->second[i]); 
    }

    for (int i = 0; i < (stp::is_Term_kind(k)? bits: 1); i++)
    {
      inputOutput.insert(node_to_satvar_map.find(r)->second[i]);      
    }


    {
     stp::CryptoMiniSat5 ss(1);
     aig.add_cnf_to_solver(ss, cnf);
     ss.solveAndDump();
   }


  }

  uint64_t fixed_count_unit_prop_with_assumps()
  {
     stp::CryptoMiniSat5 ss(1);
     aig.add_cnf_to_solver(ss, cnf);
     return ss.getFixedCountWithAssumptions(assumptions, inputOutput);
  }

  void fill_assumps_with(FixedBits& a, FixedBits& b, FixedBits& output)
  {
    assumptions.clear();


    for (int i = 0; i < a.getWidth(); i++)
    {
      if (a[i] == '1')
      {
        assumptions.push(stp::SATSolver::mkLit(
            node_to_satvar_map.find(i0)->second[i], false));
      }
      else if (a[i] == '0')
      {
        assumptions.push(stp::SATSolver::mkLit(
            node_to_satvar_map.find(i0)->second[i], true));
      }

      if (b[i] == '1')
      {
        assumptions.push(stp::SATSolver::mkLit(
            node_to_satvar_map.find(i1)->second[i], false));
      }
      else if (b[i] == '0')
      {
        assumptions.push(stp::SATSolver::mkLit(
            node_to_satvar_map.find(i1)->second[i], true));
      }
    }

    for (int i = 0; i < output.getWidth(); i++)
    {
      if (output[i] == '1')
      {
        assumptions.push(stp::SATSolver::mkLit(
            node_to_satvar_map.find(r)->second[i], false));
      }
      else if (output[i] == '0')
      {
        assumptions.push(
            stp::SATSolver::mkLit(node_to_satvar_map.find(r)->second[i], true));
      }
    }
  }

  void numberClauses()
  {
   // std::cerr << "Number of Clauses:" << ss->nClauses() << std::endl;
  }

};

#endif /* BBASPROP_H_ */

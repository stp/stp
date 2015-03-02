/********************************************************************
 * AUTHORS: Trevor Hansen
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

#include "stp/Sat/MinisatCore.h"
#include "stp/ToSat/AIG/ToSATAIG.h"
#include "stp/ToSat/ASTNode/ToSAT.h"
#include "stp/ToSat/ToSATBase.h"
#include "stp/AST/AST.h"

class BBAsProp
{
public:
  stp::SATSolver::vec_literals assumptions;
  stp::ToSATAIG aig;
  stp::MinisatCore<Minisat::Solver>* ss;
  ASTNode i0, i1, r;
  stp::ToSAT::ASTNodeToSATVar m;

  BBAsProp(Kind k, STPMgr* mgr, int bits)
      : aig(mgr, GlobalSTP->arrayTransformer)
  {

    const bool term = stp::is_Term_kind(k);

    i0 = mgr->CreateSymbol("i0", 0, bits);
    i1 = mgr->CreateSymbol("i1", 0, bits);

    ASTNode p, eq;

    if (term)
    {
      p = mgr->CreateTerm(k, bits, i0, i1);
      r = mgr->CreateSymbol("r", 0, bits);
      eq = mgr->CreateNode(EQ, p, r);
    }
    else
    {
      p = mgr->CreateNode(k, i0, i1);
      r = mgr->CreateSymbol("r", 0, 0);
      eq = mgr->CreateNode(IFF, p, r);
    }

    ss = new MinisatCore<Minisat::Solver>(mgr->soft_timeout_expired);

    aig.CallSAT(*ss, eq, false);
    m = aig.SATVar_to_SymbolIndexMap();
  }

  bool unitPropagate() { return ss->unitPropagate(assumptions); }

  void toAssumptions(FixedBits& a, FixedBits& b, FixedBits& output)
  {
    assumptions.clear();
    int bits = a.getWidth();

    for (int i = 0; i < bits; i++)
    {
      if (a[i] == '1')
      {
        assumptions.push(stp::SATSolver::mkLit(m.find(i0)->second[i], false));
      }
      else if (a[i] == '0')
      {
        assumptions.push(stp::SATSolver::mkLit(m.find(i0)->second[i], true));
      }

      if (b[i] == '1')
      {
        assumptions.push(stp::SATSolver::mkLit(m.find(i1)->second[i], false));
      }
      else if (b[i] == '0')
      {
        assumptions.push(stp::SATSolver::mkLit(m.find(i1)->second[i], true));
      }
    }
    for (int i = 0; i < output.getWidth(); i++)
    {
      if (output[i] == '1')
      {
        assumptions.push(stp::SATSolver::mkLit(m.find(r)->second[i], false));
      }
      else if (output[i] == '0')
      {
        assumptions.push(stp::SATSolver::mkLit(m.find(r)->second[i], true));
      }
    }
  }

  void numberClauses()
  {
    cerr << "Number of Clauses:" << ss->nClauses() << endl;
  }

  int fixedCount()
  {
    return addToClauseCount(i0) + addToClauseCount(i1) + addToClauseCount(r);
  }

  int addToClauseCount(const ASTNode n)
  {
    int result = 0;
    const int bits = std::max(1U, n.GetValueWidth());
    for (int i = bits - 1; i >= 0; i--)
    {
      SATSolver::lbool r = ss->value(m.find(n)->second[i]);

      if (r == ss->true_literal() || r == ss->false_literal())
        result++;
    }
    return result;
  }
};

#endif /* BBASPROP_H_ */

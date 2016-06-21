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
// -*- c++ -*-

#ifndef BVSOLVER_H
#define BVSOLVER_H

#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/Symbols.h"
#include "stp/Simplifier/VariablesInExpression.h"

namespace stp
{

/******************************************************************
 * This class represents the bitvector arithmetic linear solver.
 *
 * The bitvector solver is a partial solver, i.e. it doesn't solve
 * for all variables in the system of equations. it is
 * best-effort. it relies on the SAT solver to be complete.
 *
 * The BVSolver assumes that the input equations are normalized, &
 * have liketerms combined etc.
 *
 * 0. Traverse top-down over the input DAG, looking for a
 * 0. conjunction of equations. if you find one, then for each
 * 0. equation in the conjunction, do the following steps.
 *
 * 1. check for Linearity of the input equation
 *
 * 2. Solve for a "chosen" variable. The variable should occur
 * 2. exactly once and must have an odd coeff. Refer CAV 2007
 * 2. paper on STP for actual solving procedure
 *
 * 4. Outside the solver, Substitute and Re-normalize the input DAG
 ******************************************************************/

class BVSolver // not copyable
{
private:
  // Ptr to toplevel manager that manages bit-vector expressions
  // (i.e. construct various kinds of expressions), and also has
  // member functions that simplify bit-vector expressions
  STPMgr* _bm;

  // Ptr to Simplifier
  Simplifier* _simp;

  //
  ASTNode ASTTrue, ASTFalse, ASTUndefined;

  // choose a suitable var from the term
  ASTNode ChooseMonom(const ASTNode& eq, ASTNode& modifiedterm,
                      ASTNodeSet& checked);
  // accepts an equation and solves for a variable or a monom in it
  ASTNode BVSolve_Odd(const ASTNode& eq);

  // solves equations of the form a*x=t where 'a' is even. Has a
  // return value, unlike the normal BVSolve()
  ASTNode BVSolve_Even(const ASTNode& eq);
  ASTNode CheckEvenEqn(const ASTNode& input, bool& evenflag);

  ASTNode substitute(const ASTNode& eq, const ASTNode& lhs, const ASTNode& rhs,
                     const bool single);

  // takes an even number "in" as input, and returns an odd number
  //(return value) and a power of 2 (as number_shifts by reference),
  // such that in = (odd_number * power_of_2).
  //
  // Refer STP's CAV 2007 (or Clark Barrett's 1998 paper on
  // bit-vector arithmetic published in DAC 1998) paper for precise
  // understanding of the algorithm
  void SplitEven_into_Oddnum_PowerOf2(const ASTNode& in,
                                      unsigned int& number_shifts);

  // Those formulas which have already been solved. If the same
  // formula occurs twice then do not solve the second occurence, and
  // instead drop it
  ASTNodeMap FormulasAlreadySolvedMap;

  // Once a formula has been solved, then update the alreadysolvedmap
  // with the formula, and the solved value. The solved value can be
  // described using the following example: Suppose input to the
  // solver is
  //
  // input key: x = 2 AND y = x + t
  //
  // output value: y = 2 + t
  void UpdateAlreadySolvedMap(const ASTNode& key, const ASTNode& value);

  // This function checks if the key (formula) has already been
  // solved for.
  //
  // If yes it returns TRUE and fills the "output" with the
  // solved-value (call by reference argument),
  //
  // else returns FALSE
  bool CheckAlreadySolvedMap(const ASTNode& key, ASTNode& output);

  VariablesInExpression& vars;

  bool simplify; // Whether to apply the simplifyTerm & simplifyFormula
                 // functions.

  ASTNode simplifyNode(const ASTNode n);

  NodeFactory* nf;

public:
  // constructor
  BVSolver(STPMgr* bm, Simplifier* simp)
      : _bm(bm), _simp(simp), vars(simp->getVariablesInExpression())
  {
    ASTTrue = _bm->CreateNode(TRUE);
    ASTFalse = _bm->CreateNode(FALSE);
    ASTUndefined = _bm->CreateNode(UNDEFINED);
    simplify = true;
    nf = bm->defaultNodeFactory;
  };

  ~BVSolver() { ClearAllTables(); }

  // Top Level Solver: Goes over the input DAG, identifies the
  // equation to be solved, solves them,
  ASTNode TopLevelBVSolve(const ASTNode& a, const bool enable_simplify = true);

  void ClearAllTables(void)
  {
    FormulasAlreadySolvedMap.clear();
  }
};
} // end of namespace stp
#endif

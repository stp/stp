/********************************************************************
 * AUTHORS: Unknown
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

#include "stp/Simplifier/constantBitP/ConstantBitP_MaxPrecision.h"
#include "stp/AST/AST.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/ToSATAIG.h"
#include "stp/ToSat/BitBlaster.h"
#include <memory>

using namespace stp;

namespace simplifier
{

namespace constantBitP
{

//// Help node creation functions.

ASTNode createConstant(int bitWidth, int val, STPMgr* beev)
{
  CBV cbv = CONSTANTBV::BitVector_Create(bitWidth, true);
  int max = bitWidth > ((int)sizeof(int) * 8) ? sizeof(int) * 8 : bitWidth;
  for (int i = 0; i < max; i++)
    if (val & (1u << i))
      CONSTANTBV::BitVector_Bit_On(cbv, i);
  return beev->CreateBVConst(cbv, bitWidth);
}

ASTNode createNode(Kind k, const ASTNode& n1, const ASTNode& n2, STPMgr* beev)
{
  ASTNode result = beev->CreateNode(k, n1, n2);
  BVTypeCheck(result);
  return result;
}

ASTNode createTerm(Kind k, int width, const ASTNode& n1, const ASTNode& n2,
                   const ASTNode& n3, STPMgr* beev)
{
  ASTNode result = beev->CreateTerm(k, width, n1, n2, n3);
  BVTypeCheck(result);
  return result;
}

//////////////////////////////////////////////////

// Concretisation function. Gamma.
void concretise(const ASTNode& variable, const FixedBits& fixed, ASTVec& list,
                STPMgr* beev)
{
  if (BOOLEAN_TYPE == variable.GetType())
  {
    assert(1 == fixed.getWidth());
    assert(fixed.isBoolean());

    if (fixed.isFixed(0))
    {
      ASTNode assert;
      if (!fixed.getValue(0)) // if it's false, try to find a true assignment.
        assert = variable;
      else
        assert = beev->CreateNode(NOT, variable);
      list.push_back(assert);
    }
  }
  else
  {
    assert(BITVECTOR_TYPE == variable.GetType());
    assert(variable.GetValueWidth() == (unsigned)fixed.getWidth());
    for (unsigned i = 0; i < fixed.getWidth(); i++)
    {
      if (fixed.isFixed(i))
      {
        ASTNode oneOrZero =
            createConstant(1, fixed.getValue(i) ? 0 : -1, beev); // NB: swapped.
        ASTNode location = createConstant(32, i, beev);
        ASTNode extract =
            createTerm(BVEXTRACT, 1, variable, location, location, beev);
        ASTNode assert = createNode(EQ, extract, oneOrZero, beev);
        list.push_back(assert);
      }
    }
  }
}

// Concretisation function. Gamma.
void concretise(const ASTNode& variable, const FixedBits& fixed,
                SATSolver::vec_literals& satSolverClause, STPMgr* /*beev*/,
                ToSATBase::ASTNodeToSATVar& map)
{
  if (BOOLEAN_TYPE == variable.GetType())
  {
    assert(1 == fixed.getWidth());
    assert(fixed.isBoolean());

    if (fixed.isFixed(0))
    {
      assert(map.find(variable) != map.end());
      const unsigned v = (map.find(variable)->second)[0];
      // Bits that didn't get encoded into CNF have no SAT variable
      // (marked with ~0 by ToCNFAIG::addVariables). Making a literal from
      // that index corrupts the SAT solver's watch lists.
      if (v != ~((unsigned)0))
        satSolverClause.push(SATSolver::mkLit(v, fixed.getValue(0)));
    }
  }
  else
  {
    assert(BITVECTOR_TYPE == variable.GetType());
    assert(variable.GetValueWidth() == (unsigned)fixed.getWidth());
    for (unsigned i = 0; i < fixed.getWidth(); i++)
    {
      if (fixed.isFixed(i))
      {
        assert(map.find(variable) != map.end());
        const unsigned v = (map.find(variable)->second)[i];
        if (v != ~((unsigned)0)) // See above: the bit wasn't encoded.
          satSolverClause.push(SATSolver::mkLit(v, fixed.getValue(i)));
      }
    }
  }
}

// The bitWidth isn't necessarily the same for all children. e.g. ITE(boolean,
// x-bit, x-bit)
bool maxPrecision(vector<FixedBits*> children, FixedBits& output, Kind kind,
                  STPMgr* beev)
{
  const int numberOfChildren = children.size();

  bool disabledProp = !beev->UserFlags.bitConstantProp_flag;
  bool printOutput = beev->UserFlags.print_output_flag;
  bool checkCounter = beev->UserFlags.check_counterexample_flag;
  bool constructCounter = beev->UserFlags.construct_counterexample_flag;
  beev->UserFlags.bitConstantProp_flag = false;
  beev->UserFlags.print_output_flag = false;
  beev->UserFlags.check_counterexample_flag = false;
  // The refinement loop reads each SAT model back via GetCounterExample;
  // without this flag CallSAT_ResultCheck never constructs the model, every
  // "model" reads as all-zero, and the loop cannot terminate.
  beev->UserFlags.construct_counterexample_flag = true;

  ASTVec initialFixing;

  // Create a variable to represent each input, and one for the output.
  ASTVec variables;
  for (int i = 0; i < numberOfChildren; i++)
  {
    std::stringstream out;
    out << "v_VERY_SPECIALLY_NAMES" << i;

    unsigned valueWidth;

    if (children[i]->isBoolean())
      valueWidth = 0;
    else
      valueWidth = (children[i]->getWidth());

    ASTNode node = beev->CreateSymbol(out.str().c_str(), 0, valueWidth);
    variables.push_back(node);

    // constrain the fixed bits of each input variable not to change.
    concretise(node, *children[i], initialFixing, beev);
  }

  unsigned outputWidth = output.isBoolean() ? 0 : output.getWidth();
  ASTNode outputNode =
      beev->CreateSymbol("result_WITH_SPECIAL_NAME", 0, outputWidth);

  ASTNode expr;
  if (output.isBoolean())
  {
    ASTNode p1 = beev->CreateNode(kind, variables);
    BVTypeCheck(p1);
    expr = createNode(IFF, p1, outputNode, beev);
  }
  else
  {
    ASTNode p1 = beev->CreateTerm(kind, output.getWidth(), variables);
    BVTypeCheck(p1);
    expr = createNode(EQ, p1, outputNode, beev);
  }

  // constrain the input to equal the output.
  BVTypeCheck(expr);

  // constrain the fixed parts of the output node not to change.
  concretise(outputNode, output, initialFixing, beev);

  ASTVec notted;
  for (ASTVec::const_iterator i = initialFixing.begin();
       i != initialFixing.end(); i++)
    notted.push_back(beev->CreateNode(NOT, *i));

  if (notted.size() > 0) // some are specified.
  {
    expr = beev->CreateNode(stp::AND, expr, beev->CreateNode(stp::AND, notted));
  }

  bool first = true;

  SubstitutionMap sm (beev);
  Simplifier simp(beev, &sm );
  ArrayTransformer at(beev, &simp);
  AbsRefine_CounterExample ce(beev, &simp, &at);
  std::unique_ptr<SATSolver> newS_owner(createSATSolver(beev->UserFlags));
  SATSolver& newS = *newS_owner;

  // Exactly, whatever the session's abstraction flags say. The BV abstraction
  // turns CallSAT_ResultCheck into a refinement producer: it can answer
  // SOLVER_UNDECIDED (2) with no arrays involved, returning before the model
  // this loop is about to read is constructed, and the result handling below
  // reads 2 as "error from solver" and aborts. These auxiliary queries are a
  // few bits wide and gain nothing from abstracting anyway.
  //
  // Said to this encoding rather than by clearing the manager's flags and
  // putting them back: that was a manager-wide write for a decision belonging
  // to one lowering, invisible to anything else sharing the manager, and
  // restored only on the paths that reach the bottom of this function.
  ToSATAIG tosat(beev, &at, /*allowAbstraction=*/false);

  SATSolver::vec_literals satSolverClause;

  while (true)
  {

    int result;

    if (first)
    {
      beev->SetQuery(beev->ASTUndefined);
      result = ce.CallSAT_ResultCheck(newS, expr, expr, expr, &tosat, true);
    }
    else
    {
      assert(satSolverClause.size() > 0);
      newS.addClause(satSolverClause);
      satSolverClause.clear();

      beev->SetQuery(beev->ASTUndefined);
      result = ce.CallSAT_ResultCheck(newS, beev->ASTTrue, beev->ASTTrue,
                                      beev->ASTTrue, &tosat, true);
    }

    if (2 == result)
      FatalError("error from solver");
    else if (1 == result)
    {
      break; // UNSAT use the last one..
    }

    if (first)
    {
      // Don't do the meet the first time through. Set the input and output.

      for (int i = 0; i < numberOfChildren; i++)
      {
        ASTNode n = (ce.GetCounterExample(variables[i]));
        *children[i] = FixedBits::concreteToAbstract(n);
        concretise(variables[i], *(children[i]), satSolverClause, beev,
                   tosat.SATVar_to_SymbolIndexMap());
      }

      ASTNode n = (ce.GetCounterExample(outputNode));
      output = FixedBits::concreteToAbstract(n);
      // cerr << resultNode.GetName() << " " << n << endl;
      concretise(outputNode, output, satSolverClause, beev,
                 tosat.SATVar_to_SymbolIndexMap());
    }
    else
    {
      for (int i = 0; i < numberOfChildren; i++)
      {
        ASTNode n = (ce.GetCounterExample(variables[i]));
        // cerr << variables[i].GetName() << " " << n << endl;
        *children[i] =
            FixedBits::meet(FixedBits::concreteToAbstract(n), *children[i]);
        concretise(variables[i], *(children[i]), satSolverClause, beev,
                   tosat.SATVar_to_SymbolIndexMap());
      }

      ASTNode n = (ce.GetCounterExample(outputNode));
      output = FixedBits::meet(FixedBits::concreteToAbstract(n), output);
      // cerr << resultNode.GetName() << " " << n << endl;
      concretise(outputNode, output, satSolverClause, beev,
                 tosat.SATVar_to_SymbolIndexMap());
    }

    first = false;

    if (satSolverClause.size() == 0)
      break; // everything is at top.
  }

  beev->UserFlags.bitConstantProp_flag = !disabledProp;
  beev->UserFlags.print_output_flag = printOutput;
  beev->UserFlags.check_counterexample_flag = checkCounter;
  beev->UserFlags.construct_counterexample_flag = constructCounter;

  return first;
}
}
}

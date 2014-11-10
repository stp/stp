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

#include "stp/ToSat/AIG/ToSATAIG.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/simplifier.h"

namespace BEEV
{

int ToSATAIG::cnf_calls = 0;

bool ToSATAIG::CallSAT(SATSolver& satSolver, const ASTNode& input,
                       bool needAbsRef)
{
  if (cb != NULL && cb->isUnsatisfiable())
    return false;

  if (!first)
  {
    assert(input == ASTTrue);
    bm->GetRunTimes()->start(RunTimes::Solving);
    satSolver.solve();
    bm->GetRunTimes()->stop(RunTimes::Solving);

    if (bm->UserFlags.stats_flag)
      satSolver.printStats();

    return satSolver.okay();
  }

  // Shortcut if known. This avoids calling the setup of the CNF generator.
  // setup of the CNF generator is expensive. NB, these checks have to occur
  // after calling the sat solver (if it's not the first time.)
  if (input == ASTFalse)
    return false;

  if (input == ASTTrue)
    return true;

  Simplifier simp(bm);

  BBNodeManagerAIG mgr;
  BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(
      &mgr, &simp, bm->defaultNodeFactory, &bm->UserFlags, cb);

  bm->GetRunTimes()->start(RunTimes::BitBlasting);
  BBNodeAIG BBFormula = bb.BBForm(input);
  bm->GetRunTimes()->stop(RunTimes::BitBlasting);

  delete cb;
  cb = NULL;
  bb.cb = NULL;

  assert(satSolver.nVars() == 0);

  bm->GetRunTimes()->start(RunTimes::CNFConversion);
  Cnf_Dat_t* cnfData = NULL;
  toCNF.toCNF(BBFormula, cnfData, nodeToSATVar, needAbsRef, mgr);
  bm->GetRunTimes()->stop(RunTimes::CNFConversion);

  // Free the memory in the AIGs.
  BBFormula = BBNodeAIG(); // null node
  mgr.stop();

  if (bm->UserFlags.output_CNF_flag)
  {
    std::stringstream fileName;
    fileName << "output_" << bm->CNFFileNameCounter++ << ".cnf";
    Cnf_DataWriteIntoFile(cnfData, (char*)fileName.str().c_str(), 0);
  }
  first = false;

  if (bm->UserFlags.exit_after_CNF)
  {
    if (bm->UserFlags.quick_statistics_flag)
      bm->GetRunTimes()->print();

    if (needAbsRef)
      cerr << "Warning: STP is exiting after generating the first CNF. But the "
              "CNF"
              " is probably partial which you probably don't want. You "
              "probably want to disable"
              " refinement with the \"-r\" command line option." << endl;

    exit(0);
  }

  bm->GetRunTimes()->start(RunTimes::SendingToSAT);

  // Create a new sat variable for each of the variables in the CNF.
  int satV = satSolver.nVars();
  for (int i = 0; i < cnfData->nVars - satV; i++)
    satSolver.newVar();

  SATSolver::vec_literals satSolverClause;
  for (int i = 0; i < cnfData->nClauses; i++)
  {
    satSolverClause.clear();
    for (int* pLit = cnfData->pClauses[i], *pStop = cnfData->pClauses[i + 1];
         pLit < pStop; pLit++)
    {
      uint32_t var = (*pLit) >> 1;
      assert((var < satSolver.nVars()));
      Minisat::Lit l = SATSolver::mkLit(var, (*pLit) & 1);
      satSolverClause.push(l);
    }

    satSolver.addClause(satSolverClause);
    if (!satSolver.okay())
      break;
  }
  bm->GetRunTimes()->stop(RunTimes::SendingToSAT);

  if (bm->UserFlags.output_bench_flag)
    cerr << "Converting to CNF via ABC's AIG package can't yet print out bench "
            "format" << endl;

  // This releases the memory used by the CNF generator, particularly some data
  // tables.
  // If CNF generation is going to be called lots, we'd rather keep it around.
  // because the datatables are expensive to generate.
  if (cnf_calls == 0)
    Cnf_ClearMemory();

  cnf_calls++;

  Cnf_DataFree(cnfData);
  cnfData = NULL;

  // Minisat doesn't, but simplifying minisat and cryptominsat eliminate
  // variables during their
  // simplification phases. The problem is that we may later add clauses in that
  // refer to those
  // simplified-away variables. Here we mark them as frozen which prevents them
  // from being removed.
  for (ArrayTransformer::ArrType::iterator it =
           arrayTransformer->arrayToIndexToRead.begin();
       it != arrayTransformer->arrayToIndexToRead.end(); it++)
  {
    const ArrayTransformer::arrTypeMap& atm = it->second;

    for (ArrayTransformer::arrTypeMap::const_iterator arr_it = atm.begin();
         arr_it != atm.end(); arr_it++)
    {
      const ArrayTransformer::ArrayRead& ar = arr_it->second;
      ASTNodeToSATVar::iterator it = nodeToSATVar.find(ar.index_symbol);
      if (it != nodeToSATVar.end())
      {
        const vector<unsigned>& v = it->second;
        for (size_t i = 0, size = v.size(); i < size; ++i)
          satSolver.setFrozen(v[i]);
      }

      ASTNodeToSATVar::iterator it2 = nodeToSATVar.find(ar.symbol);
      if (it2 != nodeToSATVar.end())
      {
        const vector<unsigned>& v = it2->second;
        for (size_t i = 0, size = v.size(); i < size; ++i)
          satSolver.setFrozen(v[i]);
      }
    }
  }

  // One modified version of Minisat has an array propagator based solver built
  // in. So this block sends the details of the arrays to it.
  if ((bm->UserFlags.solver_to_use == UserDefinedFlags::MINISAT_PROPAGATORS) &&
      !bm->UserFlags.ackermannisation)
  {
    int array_id = 0; // Is incremented for each distinct array.
    bool found = false;
    for (ArrayTransformer::ArrType::iterator it =
             arrayTransformer->arrayToIndexToRead.begin();
         it != arrayTransformer->arrayToIndexToRead.end(); it++)
    {
      const ArrayTransformer::arrTypeMap& atm = it->second;

      for (ArrayTransformer::arrTypeMap::const_iterator arr_it = atm.begin();
           arr_it != atm.end(); arr_it++)
      {
        const ArrayTransformer::ArrayRead& ar = arr_it->second;

        // Get the the SAT solver variable numbers of the index, but,
        // if it's a constant, use that instead,
        // if we don't have anything, then add some new stuff in.

        ASTNodeToSATVar::iterator it = nodeToSATVar.find(ar.index_symbol);
        SATSolver::vec_literals index;
        Minisat::vec<Minisat::lbool> index_constants;
        const int index_width = arr_it->first.GetValueWidth();
        if (it != nodeToSATVar.end())
        {
          const vector<unsigned>& v = it->second;
          for (int i = 0; i < index_width; i++)
            index.push(SATSolver::mkLit(v[i], false));
        }
        else if (ar.index_symbol.isConstant())
        {
          const CBV c = ar.index_symbol.GetBVConst();
          for (int i = 0; i < index_width; i++)
            if (CONSTANTBV::BitVector_bit_test(c, i))
              index_constants.push((Minisat::lbool)satSolver.true_literal());
            else
              index_constants.push((Minisat::lbool)satSolver.false_literal());
        }
        else
        {

          // The index is ommitted from the problem.

          vector<unsigned> v_a;
          assert(ar.index_symbol.GetKind() == SYMBOL);
          // It was ommitted from the initial problem, so assign it freshly.
          for (size_t i = 0, size = ar.index_symbol.GetValueWidth(); i < size;
               ++i)
          {
            uint32_t v = satSolver.newVar();
            // We probably don't want the variable eliminated.
            satSolver.setFrozen(v);
            v_a.push_back(v);
          }
          nodeToSATVar.insert(make_pair(ar.index_symbol, v_a));

          for (size_t i = 0, size = v_a.size(); i < size; ++i)
          {
            uint32_t var = v_a[i];
            index.push(SATSolver::mkLit(var, false));
          }
        }

        assert((index.size() > 0) ^ (index_constants.size() > 0));

        SATSolver::vec_literals value;
        Minisat::vec<Minisat::lbool> value_constants;
        it = nodeToSATVar.find(ar.symbol);

        if (it != nodeToSATVar.end())
        {
          vector<unsigned>& v = it->second;
          for (size_t i = 0, size = v.size(); i < size; ++i)
          {
            uint32_t var = v[i];
            value.push(SATSolver::mkLit(var, false));
          }
        }
        else if (ar.symbol.isConstant())
        {
          CBV c = ar.symbol.GetBVConst();
          for (size_t i = 0, size = ar.symbol.GetValueWidth(); i < size; ++i)
            if (CONSTANTBV::BitVector_bit_test(c, i))
              value_constants.push((Minisat::lbool)satSolver.true_literal());
            else
              value_constants.push((Minisat::lbool)satSolver.false_literal());
        }
        else
        {
          // The value has been ommitted..
          // I'm not sure this is needed (really).
          vector<unsigned> v_a;

          assert(ar.symbol.GetKind() == SYMBOL);
          // It was ommitted from the initial problem, so assign it freshly.
          for (size_t i = 0, size = ar.symbol.GetValueWidth(); i < size; ++i)
          {
            uint32_t v = satSolver.newVar();
            // We probably don't want the variable eliminated.
            satSolver.setFrozen(v);
            v_a.push_back(v);
          }
          nodeToSATVar.insert(make_pair(ar.symbol, v_a));

          for (size_t i = 0, size = v_a.size(); i < size; ++i)
          {
            uint32_t var = v_a[i];
            value.push(SATSolver::mkLit(var, false));
          }
        }

        satSolver.addArray(array_id, index, value, index_constants,
                           value_constants);
        found = true;
      }
      if (found)
        array_id++;
      found = false;
    }
  }

  // void setHardTimeout(int sec);
  // setHardTimeout(500);

  bm->GetRunTimes()->start(RunTimes::Solving);
  satSolver.solve();
  bm->GetRunTimes()->stop(RunTimes::Solving);

  if (bm->UserFlags.stats_flag)
    satSolver.printStats();

  return satSolver.okay();
}

ToSATAIG::~ToSATAIG()
{
  ClearAllTables();
}
}

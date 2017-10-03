/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Dan Liew, Mate Soos
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
#include "stp/Simplifier/Simplifier.h"

namespace stp
{

THREAD_LOCAL int ToSATAIG::cnf_calls = 0;

bool ToSATAIG::CallSAT(SATSolver& satSolver, const ASTNode& input,
                       bool needAbsRef)
{
  if (cb != NULL && cb->isUnsatisfiable())
    return false;

  if (!first)
  {
    assert(input == ASTTrue);
    return runSolver(satSolver);
  }

  // Shortcut if known. This avoids calling the setup of the CNF generator.
  // setup of the CNF generator is expensive. NB, these checks have to occur
  // after calling the sat solver (if it's not the first time.)
  if (input == ASTFalse)
    return false;

  if (input == ASTTrue)
    return true;

  first = false;
  Cnf_Dat_t* cnfData = bitblast(input, needAbsRef);
  handle_cnf_options(cnfData, needAbsRef);

  assert(satSolver.nVars() == 0);
  add_cnf_to_solver(satSolver, cnfData);

  if (bm->UserFlags.output_bench_flag) {
    cerr << "Converting to CNF via ABC's AIG package can't yet print out bench "
            "format" << endl;
  }
  release_cnf_memory(cnfData);

  mark_variables_as_frozen(satSolver);

  return runSolver(satSolver);
}

void ToSATAIG::release_cnf_memory(Cnf_Dat_t* cnfData)
{
  // This releases the memory used by the CNF generator, particularly some data
  // tables.
  // If CNF generation is going to be called lots, we'd rather keep it around.
  // because the datatables are expensive to generate.
  if (cnf_calls == 0)
    Cnf_ClearMemory();

  Cnf_DataFree(cnfData);
  cnf_calls++;
}

void ToSATAIG::handle_cnf_options(Cnf_Dat_t* cnfData, bool needAbsRef)
{
  if (bm->UserFlags.output_CNF_flag)
  {
    std::stringstream fileName;
    fileName << "output_" << bm->CNFFileNameCounter++ << ".cnf";
    Cnf_DataWriteIntoFile(cnfData, (char*)fileName.str().c_str(), 0);
  }

  if (bm->UserFlags.exit_after_CNF)
  {
    if (bm->UserFlags.quick_statistics_flag)
      bm->GetRunTimes()->print();

    if (needAbsRef) {
      cerr << "Warning: STP is exiting after generating the first CNF."
        << " But the CNF is probably partial which you probably don't want."
        << " You probably want to disable"
        << " refinement with the \"-r\" command line option." << endl;
    }

    exit(0);
  }
}

Cnf_Dat_t* ToSATAIG::bitblast(const ASTNode& input, bool needAbsRef)
{
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

  bm->GetRunTimes()->start(RunTimes::CNFConversion);
  Cnf_Dat_t* cnfData = NULL;
  toCNF.toCNF(BBFormula, cnfData, nodeToSATVar, needAbsRef, mgr);
  bm->GetRunTimes()->stop(RunTimes::CNFConversion);

  // Free the memory in the AIGs.
  BBFormula = BBNodeAIG(); // null node
  mgr.stop();

  return cnfData;
}

void ToSATAIG::add_cnf_to_solver(SATSolver& satSolver, Cnf_Dat_t* cnfData)
{
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
}

void ToSATAIG::mark_variables_as_frozen(SATSolver& satSolver)
{
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
}

bool ToSATAIG::runSolver(SATSolver& satSolver)
{
  bm->GetRunTimes()->start(RunTimes::Solving);
  satSolver.solve(bm->soft_timeout_expired);
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

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

#include "stp/ToSat/ToSATAIG.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include <sstream>

namespace stp
{

THREAD_LOCAL_IE int ToSATAIG::cnf_calls = 0;

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
  {
    // A formula which preprocessing proved true can still own active UF
    // results and argument names.  They are the sole candidate authority for
    // the checker and future congruence lemmas, so the ordinary constant-root
    // shortcut is legal only when there are no such scalars.  Register and
    // solve the disconnected variables here instead of letting the model
    // evaluator invent values for symbols which never reached SAT.
    UFContext* uf = bm->getUFContextIfAny();
    if (uf == NULL || !uf->activeInSolve() || uf->getSolveScalars().empty())
      return true;

    first = false;
    delete cb;
    cb = NULL;
    assert(satSolver.nVars() == 0);
    mark_variables_as_frozen(satSolver);
    return runSolver(satSolver);
  }

  first = false;
  Cnf_Dat_t* cnfData = bitblast(input, needAbsRef);

  // Only an exhausted AIG budget returns NULL: the query has no answer, and
  // `false` alone would be read as UNSAT. Raising the soft-timeout flag is
  // what makes CallSAT_ResultCheck report SOLVER_TIMEOUT instead -- it tests
  // that flag before it tests this return value.
  if (cnfData == NULL)
  {
    bm->soft_timeout_expired = true;
    return false;
  }

  handle_cnf_options(cnfData, needAbsRef);

  assert(satSolver.nVars() == 0);
  add_cnf_to_solver(satSolver, cnfData);

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
    Cnf_ManFree();

  Cnf_DataFree(cnfData);
  cnf_calls++;
}

void ToSATAIG::handle_cnf_options(Cnf_Dat_t* cnfData, bool needAbsRef)
{
  if (bm->UserFlags.output_CNF_flag)
  {
    std::stringstream fileName;
    fileName << "output_" << bm->CNFFileNameCounter++ << ".cnf";
    Cnf_DataWriteIntoFile(cnfData, (char*)fileName.str().c_str(), 0,0,0);
  }

  if (bm->UserFlags.exit_after_CNF)
  {
    if (bm->UserFlags.quick_statistics_flag)
      bm->GetRunTimes()->print();

    if (needAbsRef)
    {
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
  stp::SubstitutionMap sm(bm);
  Simplifier simp(bm, &sm);

  BBNodeManagerAIG mgr;
  mgr.nodeBudget = bm->UserFlags.aig_node_budget;
  BitBlaster bb(&mgr, &simp, bm->defaultNodeFactory, &bm->UserFlags, cb);

  BBNodeAIG BBFormula;

  bm->GetRunTimes()->start(RunTimes::BitBlasting);

  // Only BBForm() and the side-constraint fold below create AIG nodes, so
  // only they can exceed the budget -- ToCNFAIG drives ABC directly and never
  // calls mgr.CreateNode(). Keeping the try that narrow is what lets the
  // handler close RunTimes::BitBlasting unconditionally; RunTimes::stop()
  // FatalErrors on a category mismatch, so a try wide enough to span
  // CNFConversion would abort instead of report.
  try
  {
    BBFormula = bb.BBForm(input);

    // Hand the side constraints over as one variadic AND, so that
    // CreateNode folds them into a log-height tower.
    //
    // Conjoining them one at a time instead -- BBFormula =
    // Aig_And(BBFormula, sc) once per constraint -- leaves an AIG whose
    // depth is the number of constraints, and every AIG -> CNF walk ABC
    // has is a plain recursive DFS: Cnf_ManScanMapping_rec under
    // Cnf_Derive, Cnf_CollectVolume_rec under Cnf_DeriveFast, and so on
    // for the Mf_ManGenerateCnf routes. One frame per link exhausts an
    // 8 MiB stack at around 105k links, and there is one link per bit of
    // each distinct abstracted operand, so a query carrying a few
    // thousand wide equalities took the process out. How many there are
    // is chosen by whoever wrote the input, so no stack size is a fix.
    //
    // The incremental route never had this: syncAbstractions() asserts
    // each constraint as its own permanent unit clause and builds no
    // chain at all.
    const std::vector<BBNodeAIG>& side = bb.sideConstraints();
    if (!side.empty())
    {
      std::vector<BBNodeAIG> conjuncts;
      conjuncts.reserve(side.size() + 1);
      conjuncts.push_back(BBFormula);
      conjuncts.insert(conjuncts.end(), side.begin(), side.end());
      BBFormula = mgr.CreateNode(AND, conjuncts);
    }
  }
  catch (const AIGBudgetExhausted& e)
  {
    bm->GetRunTimes()->stop(RunTimes::BitBlasting);
    if (bm->UserFlags.stats_flag)
      cerr << "AIG node budget exhausted at " << e.nodeCount << " nodes"
           << endl;
    // Say so here, where the reason is known. The no-answer leaves through the
    // same door a clock expiry does -- soft_timeout_expired, so that the whole
    // pipeline unwinds the one way it knows -- and by the time it surfaces
    // nothing can tell the two apart. This is not a clock: more time on the
    // same machine reproduces it exactly, and what a caller can act on is the
    // flag to raise.
    //
    // Phrased alongside the conflict budget's own sentence, and carrying the
    // count it stopped at, which is the one number that says how much higher
    // to set it. AND gates rather than nodes, because that is what the budget
    // counts. -1 rather than 0 is what lifts the limit: 0 is a budget of no
    // gates at all, which gives up before the first one.
    std::ostringstream detail;
    detail << "the AIG node budget set by --aig-node-budget ("
           << bm->UserFlags.aig_node_budget << ") ran out at " << e.nodeCount
           << " AND gates; raise it, or set it to -1 for no limit";
    bm->noteUnknown(UnknownReason::Incomplete, detail.str());
    delete cb;
    cb = NULL;
    bb.cb = NULL;
    mgr.stop();
    return NULL;
  }

  bm->GetRunTimes()->stop(RunTimes::BitBlasting);

  delete cb;
  cb = NULL;
  bb.cb = NULL;

  bm->GetRunTimes()->start(RunTimes::CNFConversion);
  Cnf_Dat_t* cnfData = NULL;
  toCNF.toCNF(BBFormula, cnfData, nodeToSATVar, needAbsRef, mgr);
  bm->GetRunTimes()->stop(RunTimes::CNFConversion);

  // Record what each abstraction stands for, now that CNF conversion has
  // assigned the SAT variable its combinational input carries. Refinement
  // reads these back to compare the candidate against the operands.
  for (const auto& raw : bb.abstractedEQs())
  {
    BVEQAbstraction a;
    a.eqNode = raw.eqNode;
    Aig_Obj_t* pObj = (Aig_Obj_t*)Vec_PtrEntry(
        mgr.aigMgr->vCis, raw.abstractionCI.symbol_index);
    a.abstractionSATVar = cnfData->pVarNums[pObj->Id];
    a.leftSymbol = raw.leftSymbol;
    a.rightSymbol = raw.rightSymbol;
    a.width = std::max(1u, raw.leftSymbol.GetValueWidth());
    abstraction_.equalities().push_back(std::move(a));
  }

  for (const auto& raw : bb.abstractedTerms())
  {
    BVTermAbstraction a;
    a.termNode = raw.termNode;
    a.opKind = raw.opKind;
    for (unsigned i = 0; i < raw.numOperands; i++)
    {
      a.operands[i] = raw.operands[i];
      a.operandNegated[i] = raw.operandNegated[i];
    }
    a.numOperands = raw.numOperands;
    a.width = raw.width;
    if (raw.condCISymbolIndex >= 0)
    {
      Aig_Obj_t* condObj = (Aig_Obj_t*)Vec_PtrEntry(
          mgr.aigMgr->vCis, raw.condCISymbolIndex);
      a.condSATVar = cnfData->pVarNums[condObj->Id];
    }
    abstraction_.terms().push_back(std::move(a));
  }

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
    for (int *pLit = cnfData->pClauses[i], *pStop = cnfData->pClauses[i + 1];
         pLit < pStop; pLit++)
    {
      uint32_t var = (*pLit) >> 1;
      assert((var < satSolver.nVars()));
      SATSolver::Lit l = SATSolver::mkLit(var, (*pLit) & 1);
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
      // A bit that reached no SAT variable is marked with ~0u rather than
      // omitted, so freezing has to skip it: the sentinel is not a variable
      // index, and a backend that acts on setFrozen() writes out of bounds
      // when handed it. The extensionality loop below already guards this.
      const ArrayTransformer::ArrayRead& ar = arr_it->second;
      ASTNodeToSATVar::iterator it = nodeToSATVar.find(ar.index_symbol);
      if (it != nodeToSATVar.end())
      {
        const vector<unsigned>& v = it->second;
        for (size_t i = 0, size = v.size(); i < size; ++i)
          if (v[i] != ~((unsigned)0))
            satSolver.setFrozen(v[i]);
      }

      ASTNodeToSATVar::iterator it2 = nodeToSATVar.find(ar.symbol);
      if (it2 != nodeToSATVar.end())
      {
        const vector<unsigned>& v = it2->second;
        for (size_t i = 0, size = v.size(); i < size; ++i)
          if (v[i] != ~((unsigned)0))
            satSolver.setFrozen(v[i]);
      }
    }
  }

  // The array-equality procedure encodes its refinement lemmas over
  // the SAT variables of its abstraction variables, witness symbols
  // and scalar names; keep those variables from being eliminated.
  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  if (ext != NULL && ext->activeInSolve())
  {
    const std::set<ASTNode>& symbols = ext->getFrozenSymbols();
    for (std::set<ASTNode>::const_iterator it = symbols.begin();
         it != symbols.end(); ++it)
    {
      ASTNodeToSATVar::iterator vit = nodeToSATVar.find(*it);
      if (vit == nodeToSATVar.end())
        continue;
      const vector<unsigned>& v = vit->second;
      for (size_t i = 0, size = v.size(); i < size; ++i)
        if (v[i] != ~((unsigned)0))
          satSolver.setFrozen(v[i]);
    }

    // A lemma-only symbol -- an owned read's abstraction variable or
    // index -- may legally never have reached the bit-blast: the
    // read's only occurrence can itself sit inside another abstracted
    // term. Its semantics live entirely in future refinement lemmas,
    // so fresh SAT variables allocated here, before the first solve,
    // are exactly the unconstrained meaning the blasted formula gives
    // it; the model loop then values them like any other symbol, and
    // the lemmas constrain the same variables the candidate was
    // checked against. Names defined by equations are deliberately
    // not treated this way -- for them a missing vector still fails
    // loudly at lemma encoding.
    const std::set<ASTNode>& lemmaOnly = ext->getLemmaOnlySymbols();
    for (std::set<ASTNode>::const_iterator it = lemmaOnly.begin();
         it != lemmaOnly.end(); ++it)
    {
      if (nodeToSATVar.find(*it) != nodeToSATVar.end())
        continue;
      const unsigned width = it->GetValueWidth();
      vector<unsigned> v(width);
      for (unsigned i = 0; i < width; i++)
      {
        v[i] = satSolver.newVar();
        satSolver.setFrozen(v[i]);
      }
      nodeToSATVar.insert(make_pair(*it, v));
    }
  }

  // The BV abstraction's refinement writes clauses over the abstraction
  // variables and the operand bits in later solve calls, the same way the
  // array machinery above writes its lemmas; a simplifying backend must not
  // eliminate any of them in the meantime. The incremental driver has no
  // counterpart to this call because every backend it admits either
  // restores an eliminated variable on contact or never eliminates one --
  // makeBackend refuses the simplifying MiniSat outright.
  abstraction_.freezeVariables(satSolver, nodeToSATVar);

  // Give every checker-visible scalar one complete mapping in this backend.
  // Connected bits retain their CNF variables; missing/disconnected bits get
  // fresh unconstrained variables, which is exactly their formula semantics.
  // Registration happens after CNF conversion so no second AIG-side meaning
  // can compete with the mapping the checker and lemma encoder both consume.
  UFContext* ufContext = bm->getUFContextIfAny();
  if (ufContext != NULL && ufContext->activeInSolve())
  {
    for (const ASTNode& symbol : ufContext->getSolveScalars())
    {
      if (symbol.GetKind() != SYMBOL)
        FatalError("UF solve-scalar registrar received a non-symbol", symbol);
      const unsigned width = std::max((unsigned)1, symbol.GetValueWidth());
      ASTNodeToSATVar::iterator found = nodeToSATVar.find(symbol);
      if (found == nodeToSATVar.end())
        found = nodeToSATVar
                    .insert(std::make_pair(
                        symbol, vector<unsigned>(width, ~((unsigned)0))))
                    .first;
      if (found->second.size() > width)
        FatalError("UF batch liveness mapping has the wrong width", symbol);
      if (found->second.size() < width)
        found->second.resize(width, ~((unsigned)0));
      for (unsigned bit = 0; bit < width; ++bit)
      {
        if (found->second[bit] == ~((unsigned)0))
          found->second[bit] = satSolver.newVar();
        satSolver.setFrozen(found->second[bit]);
      }
    }
    suggest_uf_scalar_phases(satSolver);
  }

}

// Bias the first candidate so the checker's scalars start out pairwise
// different.
//
// The refinement loop's cost is collisions: two applications whose arguments
// read the same values and whose results do not. Nothing tells the backend
// that spreading unconstrained scalars out is worth anything, so its default
// phase puts many of them on the same value at once and each collision is
// paid for with a lemma and another full solve. Counting the scalars off
// against an increasing value is the same trick Bitwuzla plays for DISTINCT,
// applied to what the congruence checker reads.
//
// This is only a hint: it reorders the search and cannot change which answers
// are reachable, so no soundness argument rests on the choice being good. A
// backend without a phase interface ignores it. Scalars are visited in node
// order rather than the set's, so the same query gets the same hints.
void ToSATAIG::suggest_uf_scalar_phases(SATSolver& satSolver)
{
  if (!bm->UserFlags.uf_phase_hints)
    return;
  UFContext* ufContext = bm->getUFContextIfAny();
  if (ufContext == NULL)
    return;

  std::vector<ASTNode> scalars(ufContext->getSolveScalars().begin(),
                               ufContext->getSolveScalars().end());
  std::sort(scalars.begin(), scalars.end(),
            [](const ASTNode& left, const ASTNode& right)
            { return left.GetNodeNum() < right.GetNodeNum(); });

  // The hints have to land on variables the backend has already declared.
  // CaDiCaL's factoring layer declares lazily -- on a clause, an assumption,
  // or at the start of a solve -- and silently ignores a phase for anything
  // it has not seen, which is every scalar registered above, since those are
  // fresh variables no clause mentions. Declaring is the caller's job, not an
  // advisory hint's: done here, before the first solve, it cannot disturb a
  // model, which is the reason suggestPhase itself must not do it.
  satSolver.declarePendingVariables();

  uint64_t counter = 0;
  for (const ASTNode& symbol : scalars)
  {
    const ASTNodeToSATVar::const_iterator found = nodeToSATVar.find(symbol);
    if (found == nodeToSATVar.end())
      continue;
    const uint64_t value = counter++;
    for (unsigned bit = 0; bit < found->second.size(); ++bit)
    {
      if (found->second[bit] == ~((unsigned)0))
        continue;
      const bool on = bit < 64 && ((value >> bit) & 1ULL) != 0;
      satSolver.suggestPhase(found->second[bit], on);
    }
  }
}

bool ToSATAIG::runSolver(SATSolver& satSolver)
{
  bm->GetRunTimes()->start(RunTimes::Solving);
  bool result = satSolver.solve(bm->soft_timeout_expired);
  bm->GetRunTimes()->stop(RunTimes::Solving);

  if (bm->soft_timeout_expired)
    bm->noteBudgetExhausted(satSolver);

  if (bm->UserFlags.stats_flag)
    satSolver.printStats();

  return result;
}

unsigned ToSATAIG::refineAbstractions(SATSolver& solver)
{
  return abstraction_.refine(solver, nodeToSATVar);
}

ToSATAIG::~ToSATAIG()
{
  ClearAllTables();
}
}

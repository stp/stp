/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Andrew V. Jones
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

#include "stp/STPManager/STP.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/NodeToFixedBitsMap.h"
#include "stp/ToSat/ToSATAIG.h"

#include "stp/Simplifier/NodeDomainAnalysis.h"

#ifdef USE_CRYPTOMINISAT
#include "stp/Sat/CryptoMinisat5.h"
#endif

#ifdef USE_RISS
#include "stp/Sat/Riss.h"
#endif

#ifdef USE_KISSAT
#include "stp/Sat/Kissat.h"
#endif

#include "stp/Sat/MinisatCore.h"
#include "stp/Sat/SimplifyingMinisat.h"

#include "stp/Simplifier/AIGSimplifyPropositionalCore.h"
#include "stp/Simplifier/AlwaysTrue.h"
#include "stp/Simplifier/DifficultyScore.h"
#include "stp/Simplifier/FindPureLiterals.h"
#include "stp/Simplifier/RemoveUnconstrained.h"
#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include "stp/Simplifier/SplitExtracts.h"
#include "stp/Simplifier/UseITEContext.h"
#include "stp/Simplifier/Flatten.h"
#include "stp/Simplifier/StrengthReduction.h"
#include "stp/Simplifier/Rewriting.h"
#include "stp/Simplifier/MergeSame.h"
#include <memory>
using std::cout;

namespace stp
{

const static string cb_message = "After Constant Bit Propagation. ";
const static string bb_message = "After Bitblast simplification. ";
const static string uc_message = "After Removing Unconstrained. ";
const static string int_message = "After Unsigned Interval Analysis. ";
const static string pl_message = "After Pure Literals. ";
const static string bitvec_message = "After Bit-vector Solving. ";
const static string size_inc_message = "After Speculative Simplifications. ";
const static string pe_message = "After Propagating Equalities. ";
const static string domain_message = "After Domain Analysis. ";
const static string se_message = "After Split Extracts. ";

SOLVER_RETURN_TYPE STP::solve_by_sat_solver(SATSolver* newS,
                                            ASTNode original_input)
{
  SATSolver& NewSolver = *newS;
  if (bm->UserFlags.stats_flag)
    NewSolver.setVerbosity(1);

  if (bm->UserFlags.timeout_max_conflicts >= 0)
    newS->setMaxConflicts(bm->UserFlags.timeout_max_conflicts);

  if (bm->UserFlags.timeout_max_time >= 0)
    newS->setMaxTime(bm->UserFlags.timeout_max_time);

  // reset the timeout expired flag for the new check
  bm->soft_timeout_expired = false;

  SOLVER_RETURN_TYPE result = TopLevelSTPAux(NewSolver, original_input);
  return result;
}

SATSolver* STP::get_new_sat_solver()
{
  SATSolver* newS = NULL;
  switch (bm->UserFlags.solver_to_use)
  {
    case UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER:
      newS = new SimplifyingMinisat;
      break;
    case UserDefinedFlags::CRYPTOMINISAT5_SOLVER:
#ifdef USE_CRYPTOMINISAT
      newS = new CryptoMiniSat5(bm->UserFlags.num_solver_threads);
#else
      std::cerr << "CryptoMiniSat5 support was not enabled at configure time."
                << std::endl;
      exit(-1);
#endif
      break;
    case UserDefinedFlags::RISS_SOLVER:
#ifdef USE_RISS
      newS = new RissCore();
#else
      std::cerr << "Riss support was not enabled at configure time."
                << std::endl;
      exit(-1);
#endif
      break;
    case UserDefinedFlags::KISSAT_SOLVER:
#ifdef USE_KISSAT
      newS = new Kissat();
#else
      std::cerr << "Kissat support was not enabled at configure time."
                << std::endl;
      exit(-1);
#endif
      break;
    case UserDefinedFlags::MINISAT_SOLVER:
      newS = new MinisatCore;
      break;
    default:
      std::cerr << "ERROR: Undefined solver to use." << endl;
      exit(-1);
      break;
  };

  return newS;
}

// The absolute TopLevel function that invokes STP on the input
// formula
SOLVER_RETURN_TYPE STP::TopLevelSTP(const ASTNode& inputasserts,
                                    const ASTNode& query)
{

  // Unfortunatey this is a global variable,which the aux function needs to
  // overwrite sometimes.
  bool saved_ack = bm->UserFlags.ackermannisation;

  ASTNode original_input;
  if (query != bm->ASTFalse)
  {
    original_input =
        bm->CreateNode(AND, inputasserts, bm->CreateNode(NOT, query));
  }
  else
  {
    original_input = inputasserts;
  }

  SATSolver* newS = get_new_sat_solver();
  SOLVER_RETURN_TYPE result = solve_by_sat_solver(newS, original_input);
  delete newS;

  bm->UserFlags.ackermannisation = saved_ack;
  return result;
}

ASTNode STP::callSizeReducing(ASTNode inputToSat, 
                              BVSolver* bvSolver,
                              PropagateEqualities* pe,
                              NodeDomainAnalysis* domain
                              )
{
  while (true)
  {
    ASTNode last = inputToSat;
    inputToSat = sizeReducing(last, bvSolver, pe, domain);
    if (last == inputToSat)
      break;
  }

  return inputToSat;
}

// These transformations should never increase the size of the DAG.
ASTNode STP::sizeReducing(ASTNode inputToSat, 
                          BVSolver* bvSolver,
                          PropagateEqualities* pe,
                          NodeDomainAnalysis* domain
                          )
{

  if (bm->UserFlags.propagate_equalities)
  {
    inputToSat = pe->topLevel(inputToSat);
    bm->ASTNodeStats(pe_message.c_str(), inputToSat);
  }
  
  if (bm->UserFlags.enable_unconstrained)
  {
    RemoveUnconstrained r1(*bm);
    inputToSat = r1.topLevel(inputToSat, simp);
    bm->ASTNodeStats(uc_message.c_str(), inputToSat);
  }

  if (bm->UserFlags.enable_use_intervals && bm->UserFlags.bitConstantProp_flag)
  {
    bm->GetRunTimes()->start(RunTimes::StrengthReduction);
    StrengthReduction sr(bm->defaultNodeFactory, &bm->UserFlags);
    inputToSat = sr.topLevel(inputToSat, *domain);
    bm->GetRunTimes()->stop(RunTimes::StrengthReduction);

    bm->ASTNodeStats(domain_message.c_str(), inputToSat);
  }

  if (bm->UserFlags.enable_pure_literals)
  {
    FindPureLiterals fpl;
    fpl.topLevel(inputToSat, simp, bm);
    inputToSat = simp->applySubstitutionMapAtTopLevel(inputToSat);
    bm->ASTNodeStats(pl_message.c_str(), inputToSat);
  }

  if (bm->UserFlags.enable_split_extracts)
  {
    SplitExtracts se(*bm);
    inputToSat = se.topLevel(inputToSat);
    bm->ASTNodeStats(se_message.c_str(), inputToSat);
  }

  if (bm->UserFlags.enable_always_true)
  {
    AlwaysTrue always(bm, bm->defaultNodeFactory);
    inputToSat = always.topLevel(inputToSat);
    bm->ASTNodeStats("After removing always true: ", inputToSat);
  }

  if (bm->UserFlags.enable_merge_same)
  {
    MergeSame ms(bm, bm->defaultNodeFactory);
    inputToSat = ms.topLevel(inputToSat);
    bm->ASTNodeStats("After Merge Same: ", inputToSat);
  }


  if (bm->UserFlags.enable_flatten)
  {
    Flatten flatten(bm,bm->defaultNodeFactory);
    inputToSat = flatten.topLevel(inputToSat);
    bm->ASTNodeStats("After Sharing-aware Flattening: ", inputToSat);
  }

  if (bm->UserFlags.enable_sharing_aware_rewriting)
  {
    Rewriting rewrite(bm,bm->defaultNodeFactory);
    inputToSat = rewrite.topLevel(inputToSat);
    bm->ASTNodeStats("After Sharing-aware rewriting: ", inputToSat);
  }

  // I suspect this could increase the size.
  if (bm->UserFlags.wordlevel_solve_flag)
  {
    inputToSat = bvSolver->TopLevelBVSolve(inputToSat, false);
    bm->ASTNodeStats(bitvec_message.c_str(), inputToSat);
  }

  return inputToSat;
}

// Acceps a query, calls the SAT solver and generates Valid/InValid.
// if returned 0 then input is INVALID if returned 1 then input is
// VALID if returned 2 then UNDECIDED
SOLVER_RETURN_TYPE
STP::TopLevelSTPAux(SATSolver& NewSolver, const ASTNode& original_input)
{
  bm->ASTNodeStats("input asserts and query: ", original_input);

  DifficultyScore difficulty;
  if (bm->UserFlags.stats_flag)
    cerr << "Difficulty Initially:" << difficulty.score(original_input, bm)
         << endl;

  // A heap object so I can easily control its lifetime.
  std::unique_ptr<BVSolver> bvSolver(new BVSolver(bm, simp));
  std::unique_ptr<PropagateEqualities> pe(
      new PropagateEqualities(simp, bm->defaultNodeFactory, bm));

  ASTNode inputToSat = original_input;

  // If the number of array reads is small. We rewrite them through.
  // The bit-vector simplifications are more thorough than the array
  // simplifications. For example,
  // we don't currently do unconstrained elimination on arrays--- but we do for
  // bit-vectors.
  // A better way to do this would be to estimate the number of axioms
  // introduced.
  // TODO: I chose the number of reads we perform this operation at randomly.
  bool removed = false;
  if ((bm->UserFlags.ackermannisation &&
       numberOfReadsLessThan(inputToSat, 50)) ||
      numberOfReadsLessThan(inputToSat, 10))
  {
    // If the number of axioms that would be added it small. Remove them.
    bm->UserFlags.ackermannisation = true;
    inputToSat = arrayTransformer->TransformFormula_TopLevel(inputToSat);
    if (bm->UserFlags.stats_flag)
    {
      cerr << "Have removed array operations" << endl;
    }
    removed = true;
  }

  const bool arrayops = containsArrayOps(inputToSat, bm);
  if (removed)
  {
    assert(!arrayops);
  }

  if (bm->UserFlags.check_counterexample_flag ||
      bm->UserFlags.print_counterexample_flag || (arrayops && !removed))
    bm->UserFlags.construct_counterexample_flag = true;
  else
    bm->UserFlags.construct_counterexample_flag = false;

#ifndef NDEBUG
  bm->UserFlags.construct_counterexample_flag = true;
#endif

  if (bm->UserFlags.enable_flatten)
  {
    Flatten flatten(bm,bm->defaultNodeFactory);
    inputToSat = flatten.topLevel(inputToSat);
    bm->ASTNodeStats("After Sharing-aware Flattening: ", inputToSat);
  }

  if (bm->UserFlags.bitConstantProp_flag)
  {
    bm->GetRunTimes()->start(RunTimes::ConstantBitPropagation);
    simplifier::constantBitP::ConstantBitPropagation cb(
        bm, simp, bm->defaultNodeFactory, inputToSat);
    inputToSat = cb.topLevelBothWays(inputToSat);
    bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);

    if (cb.isUnsatisfiable())
    {
      inputToSat = bm->ASTFalse;
    }

    bm->ASTNodeStats(cb_message.c_str(), inputToSat);
  }

  std::unique_ptr<NodeDomainAnalysis> domain(new NodeDomainAnalysis(bm));

  // Run size reducing just once.
  inputToSat = sizeReducing(inputToSat, bvSolver.get(), pe.get(), domain.get());
  long initial_difficulty_score = difficulty.score(inputToSat, bm);

  // It's helpful to know the initial node size. The difficulty scorer can easily get something similar:
  const long initial_node_size = difficulty.getEvalCount();

  // Fixed point it if it's not too difficult.
  // Currently we discards all the state each time sizeReducing is called,
  // so it's expensive to call.
  if (!arrayops && ( -1 == bm->UserFlags.size_reducing_fixed_point || initial_node_size < bm->UserFlags.size_reducing_fixed_point))
  {
    inputToSat =
        callSizeReducing(inputToSat, bvSolver.get(), pe.get(), domain.get());
  }

  long bitblasted_difficulty = -1;
  // Expensive, so only want to do it once.
  if (bm->UserFlags.bitblast_simplification == -1 || initial_difficulty_score < bm->UserFlags.bitblast_simplification)
  {
    BBNodeManagerAIG bitblast_nodemgr;
    BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(
        &bitblast_nodemgr, simp, bm->defaultNodeFactory, &(bm->UserFlags));
    ASTNodeMap fromTo;
    ASTNodeMap equivs;
    bb.getConsts(inputToSat, fromTo, equivs);

    if (equivs.size() > 0)
    {
      /* These nodes have equivalent AIG representations, so even though they
       * have different
       * word level expressions they are identical semantically. So we pick one
       * of the ASTnodes
       * and replace the others with it.
       * TODO: I replace with the lower id node, sometimes though we replace
       * with much more
       * difficult looking ASTNodes.
      */
      ASTNodeMap cache;
      inputToSat = SubstitutionMap::replace(
          inputToSat, equivs, cache, bm->defaultNodeFactory, false, true);
      bm->ASTNodeStats(bb_message.c_str(), inputToSat);
    }

    if (fromTo.size() > 0)
    {
      ASTNodeMap cache;
      inputToSat = SubstitutionMap::replace(inputToSat, fromTo, cache,
                                            bm->defaultNodeFactory);
      bm->ASTNodeStats(bb_message.c_str(), inputToSat);
    }
    
    bitblasted_difficulty = bitblast_nodemgr.totalNumberOfNodes();
  }


  if (!arrayops || bm->UserFlags.array_difficulty_reversion)
  {
    initial_difficulty_score = difficulty.score(inputToSat, bm);
  }

  if (bitblasted_difficulty != -1 && bm->UserFlags.stats_flag)
    cout << "Initial Bitblasted size:" << bitblasted_difficulty << endl;

  if (bm->UserFlags.stats_flag)
    cout << "Difficulty After Size reducing:" << initial_difficulty_score
         << endl;

  // So we can delete the object and release all the hash-buckets storage.
  std::unique_ptr<Revert_to> revert(new Revert_to());

  if (!arrayops || bm->UserFlags.array_difficulty_reversion)
  {
    revert->initialSolverMap.insert(simp->Return_SolverMap()->begin(),
                                    simp->Return_SolverMap()->end());
    revert->backup_arrayToIndexToRead.insert(
        arrayTransformer->arrayToIndexToRead.begin(),
        arrayTransformer->arrayToIndexToRead.end());
    revert->toRevertTo = inputToSat;
  }

  // round of substitution, solving, and simplification. ensures that
  // DAG is minimized as much as possibly, and ideally should
  // garuntee that all liketerms in BVPLUSes have been combined.
  bm->TermsAlreadySeenMap_Clear();

  ASTNode tmp_inputToSAT;
  do
  {
    tmp_inputToSAT = inputToSat;

    if (bm->soft_timeout_expired)
      return SOLVER_TIMEOUT;

    if (bm->UserFlags.optimize_flag)
    {
      if (bm->UserFlags.propagate_equalities)
      {
        inputToSat = pe->topLevel(inputToSat);
        bm->ASTNodeStats(pe_message.c_str(), inputToSat);
      }


      // Imagine:
      // The simplifier simplifies (0 + T) to T
      // Then bvsolve introduces (0 + T)
      // Then CreateSubstitutionMap decides T maps to a constant, but leaving
      // another (0+T).
      // When we go to simplify (0 + T) will still be in the simplify cache, so
      // will be mapped to T.
      // But it shouldn't be T, it should be a constant.
      // Applying the substitution map fixes this case.
      //

      
      if (bm->UserFlags.simplify_to_constants_only)
      {    
          auto constants = simp->FindConsts_TopLevel(inputToSat, false);

          if (bm->UserFlags.stats_flag)
                cerr << "constants found:" << constants.size() << endl;

          ASTNodeMap cache;
          inputToSat = stp::SubstitutionMap::replace(inputToSat, constants, cache, bm->defaultNodeFactory);
      }
      else
        inputToSat = simp->SimplifyFormula_TopLevel(inputToSat, false);
      
      bm->ASTNodeStats(size_inc_message.c_str(), inputToSat);

      if (bm->UserFlags.wordlevel_solve_flag)
      {
        inputToSat = bvSolver->TopLevelBVSolve(inputToSat, !bm->UserFlags.simplify_to_constants_only);
        bm->ASTNodeStats(bitvec_message.c_str(), inputToSat);
      }
    }
  } while (tmp_inputToSAT != inputToSat);

  if (bm->UserFlags.bitConstantProp_flag)
  {
    bm->GetRunTimes()->start(RunTimes::ConstantBitPropagation);
    simplifier::constantBitP::ConstantBitPropagation cb(
        bm, simp, bm->defaultNodeFactory, inputToSat);
    inputToSat = cb.topLevelBothWays(inputToSat);
    bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);

    if (cb.isUnsatisfiable())
    {
      inputToSat = bm->ASTFalse;
    }

    bm->ASTNodeStats(cb_message.c_str(), inputToSat);
  }

  if (bm->UserFlags.enable_use_intervals && bm->UserFlags.bitConstantProp_flag)
  {
    bm->GetRunTimes()->start(RunTimes::StrengthReduction);
    StrengthReduction sr(bm->defaultNodeFactory, &bm->UserFlags);
    inputToSat = sr.topLevel(inputToSat, *domain);
    bm->GetRunTimes()->stop(RunTimes::StrengthReduction);

    bm->ASTNodeStats(domain_message.c_str(), inputToSat);
  }

  domain.reset(nullptr);

  if (bm->UserFlags.enable_pure_literals)
  {
    FindPureLiterals fpl;
    bool changed = fpl.topLevel(inputToSat, simp, bm);
    if (changed)
    {
      inputToSat = simp->applySubstitutionMapAtTopLevel(inputToSat);
      bm->ASTNodeStats(pl_message.c_str(), inputToSat);
    }
  }

  if (bm->soft_timeout_expired)
    return SOLVER_TIMEOUT;

  if (bm->UserFlags.enable_ite_context)
  {
    UseITEContext iteC(bm);
    inputToSat = iteC.topLevel(inputToSat);
    bm->ASTNodeStats("After ITE Context: ", inputToSat);
  }

  if (bm->UserFlags.enable_aig_core_simplify)
  {
    AIGSimplifyPropositionalCore aigRR(bm);
    inputToSat = aigRR.topLevel(inputToSat);
    bm->ASTNodeStats("After AIG Core: ", inputToSat);
  }

  if (simp->hasUnappliedSubstitutions())
    inputToSat = simp->applySubstitutionMap(inputToSat);

  if (bm->UserFlags.enable_unconstrained)
  {
    RemoveUnconstrained r(*bm);
    inputToSat = r.topLevel(inputToSat, simp);
    bm->ASTNodeStats(uc_message.c_str(), inputToSat);
  }

  bm->TermsAlreadySeenMap_Clear();

  long final_difficulty_score = difficulty.score(inputToSat, bm);

  bool worse = false;
  if (final_difficulty_score > .8 * initial_difficulty_score)
    worse = true;

  // It's of course very wasteful to do this! Later I'll make it reuse the
  // work..We bit-blast again, in order to throw it away, so that we can
  // measure whether the number of AIG nodes is smaller. The difficulty score
  // is sometimes completelywrong, the sage-app7 are the motivating examples.
  // The other way to improve it would be to fix the difficulty scorer!
  if (!worse && (bitblasted_difficulty != -1))
  {
    BBNodeManagerAIG bitblast_nodemgr;
    BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(
        &bitblast_nodemgr, simp, bm->defaultNodeFactory, &(bm->UserFlags));
    bb.BBForm(inputToSat);
    int newBB = bitblast_nodemgr.totalNumberOfNodes();
    if (bm->UserFlags.stats_flag)
      cerr << "Final BB Size:" << newBB << endl;

    if (bitblasted_difficulty < newBB)
      worse = true;
  }

  if (bm->UserFlags.stats_flag)
  {
    cerr << "(3) Initial/Final Difficulty Score:" << initial_difficulty_score << " / " << final_difficulty_score <<  endl;
  }

  bool optimize_enabled = bm->UserFlags.optimize_flag;
  if (worse && (!arrayops || bm->UserFlags.array_difficulty_reversion) &&
      bm->UserFlags.difficulty_reversion)
  {
    // If the simplified problem is harder, than the
    // initial problem we revert back to the initial
    // problem.

    if (bm->UserFlags.stats_flag)
      cerr << "simplification made the problem harder, reverting." << endl;
    inputToSat = revert->toRevertTo;

    // I do this to clear the substitution/solver map.
    // Not sure what would happen if it contained simplifications
    // that haven't been applied.
    simp->ClearAllTables();

    simp->Return_SolverMap()->insert(revert->initialSolverMap.begin(),
                                     revert->initialSolverMap.end());
    revert->initialSolverMap.clear();

    // Copy back what we knew about arrays at the start..
    arrayTransformer->arrayToIndexToRead.clear();
    arrayTransformer->arrayToIndexToRead.insert(
        revert->backup_arrayToIndexToRead.begin(),
        revert->backup_arrayToIndexToRead.end());

    // The arrayTransformer calls simplify. We don't want
    // it to put back in all the bad simplifications.
    bm->UserFlags.optimize_flag = false;
  }
  revert.reset(NULL);

  inputToSat = arrayTransformer->TransformFormula_TopLevel(inputToSat);
  bm->ASTNodeStats("after transformation: ", inputToSat);
  bm->TermsAlreadySeenMap_Clear();

  bm->UserFlags.optimize_flag = optimize_enabled;

  SOLVER_RETURN_TYPE res;

  // We are about to solve. Clear out all the memory associated with caches
  // that we won't need again.
  simp->ClearCaches();
  simp->haveAppliedSubstitutionMap();
  bm->ClearAllTables();

  // Deleting it clears out all the buckets associated with hashmaps etc. too.
  bvSolver.reset(NULL);
  pe.reset(NULL);

  if (bm->UserFlags.stats_flag)
    simp->printCacheStatus();

  const bool maybeRefinement = arrayops && !bm->UserFlags.ackermannisation;

  simplifier::constantBitP::ConstantBitPropagation* cb = NULL;
  std::unique_ptr<simplifier::constantBitP::ConstantBitPropagation> cleaner;

  //TODO should be replaced by the upwards cbitp cache.
  if (bm->UserFlags.bitConstantProp_flag)
  {
    bm->GetRunTimes()->start(RunTimes::ConstantBitPropagation);
    cb = new simplifier::constantBitP::ConstantBitPropagation(
        bm, simp, bm->defaultNodeFactory, inputToSat);
    cleaner.reset(cb);
    bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);

    bm->ASTNodeStats(cb_message.c_str(), inputToSat);

    if (cb->isUnsatisfiable())
      inputToSat = bm->ASTFalse;
  }

  ToSATAIG toSATAIG(bm, cb, arrayTransformer);
  ToSATBase* satBase = bm->UserFlags.traditional_cnf ? tosat : &toSATAIG;

  if (bm->soft_timeout_expired)
    return SOLVER_TIMEOUT;

  NewSolver.enableRefinement(maybeRefinement);

  if (bm->UserFlags.stats_flag)
    bm->print_stats();

  // If it doesn't contain array operations, use ABC's CNF generation.
  res = Ctr_Example->CallSAT_ResultCheck(NewSolver, inputToSat, original_input,
                                         satBase, maybeRefinement);

  if (bm->soft_timeout_expired)
  {
    if (toSATAIG.cbIsDestructed())
      cleaner.release();

    return SOLVER_TIMEOUT;
  }

  if (SOLVER_UNDECIDED != res)
  {
    // If the aig converter knows that it is never going to be called again,
    // it deletes the constant bit stuff before calling the SAT solver.
    if (toSATAIG.cbIsDestructed())
      cleaner.release();

    CountersAndStats("print_func_stats", bm);
    return res;
  }

  // should only go to abstraction refinement if there are array ops.
  assert(arrayops);
  assert(!bm->UserFlags.ackermannisation); // Refinement must be enabled too.

  res = Ctr_Example->SATBased_ArrayReadRefinement(NewSolver, original_input,
                                                  satBase);
  if (SOLVER_UNDECIDED != res)
  {
    if (toSATAIG.cbIsDestructed())
      cleaner.release();

    CountersAndStats("print_func_stats", bm);
    return res;
  }

  FatalError("TopLevelSTPAux: reached the end without proper conclusion:"
             "a bug in STP");
  // bogus return to make the compiler shut up
  return SOLVER_ERROR;
}

} // end of namespace

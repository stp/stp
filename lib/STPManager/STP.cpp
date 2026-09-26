/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Andrew Teylu
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
#include "stp/AbsRefineCounterExample/ArrayReadRefinementProgress.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/FloatBlaster/FpAbstraction.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/Simplifier/EmbeddedConstraints.h"
#include "stp/Simplifier/SkeletonPreproc.h"
#include "stp/UninterpretedFunctions/UFLowering.h"
#include "stp/UninterpretedFunctions/UFPreLowering.h"
#include "stp/UninterpretedFunctions/UFRefinement.h"
#include "stp/UninterpretedFunctions/UFModel.h"
#include "stp/Incremental/IncrementalSolver.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/NodeToFixedBitsMap.h"
#include "stp/ToSat/ToSATAIG.h"

#include "stp/Simplifier/NodeDomainAnalysis.h"

#include "stp/Sat/SATSolverFactory.h"
#include "Lra/LraAtomRegistry.h"
#include "Lra/LraBudgetRefusal.h"
#include "Lra/LraFrontend.h"
#include "Lra/LraCoordinator.h"
#include "Lra/LraSolveContext.h"
#include "Lra/NumberBudget.h"

#include "stp/Simplifier/AIGSimplifyPropositionalCore.h"
#include "stp/Simplifier/DifficultyScore.h"
#include "stp/Simplifier/DistinctOrdering.h"
#include "stp/Simplifier/FindPureLiterals.h"
#include "stp/Simplifier/RemoveUnconstrained.h"
#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include "stp/Simplifier/SplitExtracts.h"
#include "stp/Simplifier/UseITEContext.h"
#include "stp/Simplifier/Flatten.h"
#include "stp/Simplifier/CommonFactor.h"
#include "stp/Simplifier/CommonSubSum.h"
#include "stp/Simplifier/LinearForm.h"
#include "stp/Simplifier/CongruenceCandidates.h"
#include "stp/Simplifier/StrengthReduction.h"
#include "stp/Simplifier/Rewriting.h"
#include "stp/Simplifier/MergeSame.h"
#include "stp/Util/DagWalk.h"
#include <limits>
#include <memory>
#include <map>
#include <set>
using std::cout;

namespace stp
{

const static string cb_message = "After Constant Bit Propagation. ";
const static string uc_message = "After Removing Unconstrained. ";
const static string pl_message = "After Pure Literals. ";
const static string bitvec_message = "After Bit-vector Solving. ";
const static string size_inc_message = "After Speculative Simplifications. ";
const static string pe_message = "After Propagating Equalities. ";
const static string domain_message = "After Domain Analysis. ";
const static string se_message = "After Split Extracts. ";

STP::STP(STPMgr* b)
{
  bm = b;
  substitutionMap = new stp::SubstitutionMap(bm);
  simp = new Simplifier(bm, substitutionMap);
  arrayTransformer = new ArrayTransformer(bm, simp);
  Ctr_Example = new AbsRefine_CounterExample(bm, simp, arrayTransformer);
  batchUFView.reset(new LoweredApplicationView());
  batchUFAdapter.reset(new UFBatchAdapter(bm));
  tosat = new ToSATAIG(bm, arrayTransformer);
}

STP::~STP()
{
  ClearAllTables();
  deleteObjects();
}

void STP::ClearAllTables(void)
{
  QueryPhaseScope cleanup(bm->query_timing, QueryPhase::QueryCleanup);
  // The counterexample goes with them, so there is no longer a model to read.
  // Whoever decides the next query says so again.
  queryAnswered = false;

  if (simp != NULL)
    simp->ClearAllTables();
  if (arrayTransformer != NULL)
    arrayTransformer->ClearAllTables();
  if (tosat != NULL)
    tosat->ClearAllTables();
  if (Ctr_Example != NULL)
  {
    Ctr_Example->ClearAllTables();
    Ctr_Example->setFpEncodingContext(NULL);
    Ctr_Example->setFpAbstraction(NULL);
  }
  if (bm != NULL)
    bm->setFpAbstraction(NULL);
  fpAbstraction.reset();
  fpEncodingContext.reset();
  *batchUFView = LoweredApplicationView();
  if (batchUFAdapter)
    batchUFAdapter->clear();
  if (Ctr_Example != NULL)
    Ctr_Example->setUFTheoryAdapter(NULL);
  if (bm != NULL && bm->getUFContextIfAny() != NULL)
    bm->getUFContextIfAny()->releaseSolveProtection();
  // bm->ClearAllTables();
}

SOLVER_RETURN_TYPE STP::solve_by_sat_solver(SATSolver* newS,
                                            ASTNode original_input,
                                            const ASTNodeMap&
                                                arrayEqualityRewrites,
                                            std::chrono::steady_clock::time_point
                                                deadline)
{
  SATSolver& NewSolver = *newS;
  if (bm->UserFlags.stats_flag)
    NewSolver.setVerbosity(1);

  applySolveBudgets(NewSolver, bm->UserFlags, deadline);

  // reset the timeout expired flag for the new check
  bm->soft_timeout_expired = false;
  bm->clearUnknown();
  if (NewSolver.timeLimitExpired())
  {
    bm->InvalidateRealModel();
    bm->soft_timeout_expired = true;
    bm->noteBudgetExhausted(NewSolver);
    return bm->unknownResult();
  }

  SOLVER_RETURN_TYPE result =
      TopLevelSTPAux(NewSolver, original_input, arrayEqualityRewrites);
  return result;
}

IncrementalSolver* STP::getIncrementalSolver()
{
  if (incrementalSolver == nullptr)
  {
    // The abstraction under the driver runs the batch candidate check on
    // every solve, and that check's ordinary replay is the certifier of
    // last resort. With lazy array reads the replay can reject a candidate
    // that no seeded read axiom, chain lemma, or record release explains
    // -- a completeness gap of the lazily seeded tables that the exact
    // driver's search happens never to reach -- so a session under the
    // floating-point abstraction takes the eager array expansion, where
    // every measured session answers every check. Decided here, before the
    // first piece is prepared, so the whole session sees one array strategy.
    if (bm->UserFlags.fp_abstraction &&
        bm->UserFlags.fp_abstraction_incremental &&
        !bm->UserFlags.ackermannisation)
    {
      if (bm->UserFlags.stats_flag)
        std::cerr << "Note: --fp-abstraction under the incremental driver "
                     "expands arrays eagerly (--ackermanize)."
                  << std::endl;
      bm->UserFlags.ackermannisation = true;
    }
    incrementalSolver =
        new IncrementalSolver(bm, Ctr_Example, simp, arrayTransformer);
  }
  return incrementalSolver;
}

void STP::resetIncrementalSolver()
{
  delete incrementalSolver;
  incrementalSolver = nullptr;
}

SATSolver* STP::get_new_sat_solver()
{
  SATSolver* newS = createSATSolver(bm->UserFlags);
  applySearchBias(*newS, bm->UserFlags, true);
  return newS;
}

// The absolute TopLevel function that invokes STP on the input
// formula
// Decide one query, twice if the first run cannot say whose refutation it
// reached.
//
// --uf-inject-args puts injectivity into the encoding, which the query never
// asserted, so an unsat over it may be the assumption's rather than the
// query's. Normally the solver settles that itself: the implications sit
// behind an assumption the search can be asked about and, if the refutation
// used it, withdrawn -- two searches on one encoding, no second pipeline run.
// See STPMgr::solveRetractingInjectivity.
//
// What that cannot cover is a refutation reached before the solver was ever
// asked. Preprocessing works on the strengthened formula, so a formula it
// proves false may have been proved false with the assumption's help, and
// there is no assumption trail to interrogate afterwards. Nor is there a
// cheaper question to ask than the one below: run the query again with the
// flag off, and report what that says. bm->uf_injectivity_assumed is exactly
// the "nobody established this" record -- both resolvers clear it -- so this
// second run happens only in the case the first run could not close.
SOLVER_RETURN_TYPE STP::TopLevelSTP(const ASTNode& inputasserts,
                                    const ASTNode& query)
{
  // One deadline for preprocessing, the floating-point restarts, restarted
  // UF rounds, and the injectivity fallback. A later public query starts
  // anew.
  const auto started = std::chrono::steady_clock::now();
  QueryTiming timing(started);
  QueryTimingReport timing_report(bm->query_timing,
      bm->UserFlags.stats_flag ? &timing : nullptr, std::cerr);
  const auto deadline = started +
      std::chrono::seconds(bm->UserFlags.timeout_max_time >= 0
                               ? bm->UserFlags.timeout_max_time : 0);
  const PreparationControl preparation(
      bm->UserFlags.timeout_max_time >= 0
          ? deadline : PreparationControl::Clock::time_point::max(),
      bm->preparation_control);
  const PreparationScope preparation_scope(bm->preparation_control, preparation);
  const bool original_inject_args = bm->UserFlags.uf_inject_args;
  bm->soft_timeout_expired = false;
  bm->clearUnknown();
  fpAbstractionExact.clear();
  fpAbstractionRestarts = 0;
  fpAbstractionPreviouslyAbstracted = 0;
  try
  {
    SOLVER_RETURN_TYPE first = topLevelSTPOnce(inputasserts, query, deadline);
    // A floating-point release by restart (FpAbstraction::restartRequested):
    // the run ended undecided with the operations to lower exactly noted,
    // and the pipeline runs again over the same formula with them held out
    // of the abstraction. Each run releases at least one more, so this ends.
    // The same table clearing as the UF second run below, for the same
    // reason. Every run shares the query's one deadline.
    while (fpAbstraction != NULL && fpAbstraction->restartRequested())
    {
      const std::set<ASTNode>& requests = fpAbstraction->releaseRequests();
      fpAbstractionExact.insert(requests.begin(), requests.end());
      fpAbstractionPreviouslyAbstracted = fpAbstraction->applications().size();
      ++fpAbstractionRestarts;
      if (bm->UserFlags.stats_flag)
        std::cerr << "FpAbstraction: releasing " << requests.size()
                  << " operation(s) exactly by running the pipeline again ("
                  << fpAbstractionExact.size() << " exact in total)"
                  << std::endl;
      bm->ClearAllTables();
      ClearAllTables();
      skeletonAsked = false;
      first = topLevelSTPOnce(inputasserts, query, deadline);
    }
    if (first != SOLVER_UNSATISFIABLE || bm->uf_injectivity_assumed == 0)
      return first;

    if (bm->UserFlags.stats_flag)
      std::cerr << "UF: refuted before the search could be asked about the "
                << "injectivity assumption, deciding the query without it"
                << std::endl;

    const bool saved = bm->UserFlags.uf_inject_args;
    bm->UserFlags.uf_inject_args = false;
    // A second run of the pipeline is a second solve, and every solve reaches
    // topLevelSTPOnce over tables nobody has written yet: the SMT-LIB2 frontend
    // clears them in Cpp_interface::resetSolver, the C API in vc_query, and the
    // single-query tool has never run anything. This one is reached from inside
    // the driver, so nothing did it here, and the run inherits the first run's
    // substitution map, array-transform tables and bit-blasting cache.
    //
    // The substitution map is the one that bites rather than merely wastes:
    // RemoveUnconstrained's array rules meet a symbol the first run already
    // substituted and call UpdateSubstitutionMapFewChecks, whose whole contract
    // is that its caller has established the symbol is not in the map. Same
    // clearing as the frontends do, and in the same place relative to the solve
    // -- before it, so the first run's answer is complete and the second run's
    // model is built over its own encoding.
    bm->ClearAllTables();
    ClearAllTables();
    const SOLVER_RETURN_TYPE second = topLevelSTPOnce(inputasserts, query, deadline);
    bm->UserFlags.uf_inject_args = saved;
    bm->clearInjectivityAssumed();
    skeletonAsked = false;
    return second;
  }
  catch (const PreparationInterrupted& stopped)
  {
    QueryPhaseScope cleanup(bm->query_timing, QueryPhase::QueryCleanup);
    bm->UserFlags.uf_inject_args = original_inject_args;
    bm->InvalidateRealModel();
    bm->ClearAllTables();
    ClearAllTables();
    bm->clearInjectivityAssumed();
    skeletonAsked = false;
    bm->soft_timeout_expired = true;
    bm->noteUnknown(UnknownReason::Timeout);
    if (bm->UserFlags.stats_flag)
    {
      const auto finished = std::chrono::steady_clock::now();
      std::cerr << "Preparation timeout: stage=" << preparationStageName(stopped.stage)
                << " query_ns=" << std::chrono::duration_cast<std::chrono::nanoseconds>(
                       stopped.noticed - started).count()
                << " cleanup_ns=" << std::chrono::duration_cast<std::chrono::nanoseconds>(
                       finished - stopped.noticed).count() << '\n';
    }
    return bm->unknownResult();
  }
}

namespace
{

// Whether `root` holds a multiplication, division or remainder that
// --bv-term-abstraction would abstract: at or above `width` bits. The signed
// forms count, since the bit-blaster lowers them to the unsigned circuits.
bool containsWideArithmetic(const ASTNode& root, unsigned width)
{
  bool found = false;
  ASTNodeSet visited;
  walkPreOrder(root, [&](const ASTNode& n) -> bool {
    if (found || !visited.insert(n).second)
      return false;
    switch (n.GetKind())
    {
      case BVMULT:
      case BVDIV:
      case BVMOD:
      case SBVDIV:
      case SBVREM:
      case SBVMOD:
        if (n.GetValueWidth() >= width)
          found = true;
        break;
      default:
        break;
    }
    return !found;
  });
  return found;
}

} // namespace

SOLVER_RETURN_TYPE STP::topLevelSTPOnce(const ASTNode& inputasserts,
                                        const ASTNode& query,
                                        std::chrono::steady_clock::time_point
                                            deadline)
{
  // Candidate construction and publication are separate decisions.
  // TopLevelSTPAux may force construction for array/UF
  // refinement, but nothing after this solve may interpret that as an SMT-LIB
  // get-model/get-value request.
  const bool constructForCaller = bm->UserFlags.callerRequestedModel();
  // Preparation can unwind at any checkpoint, including before the ordinary
  // return path. Restore query-local policy on every exit.
  struct RestoreFlags
  {
    UserDefinedFlags& flags;
    bool construct, ack, abstract, optimize;
    UserDefinedFlags::CNFEffort cnf;
    uint32_t schemas;
    ~RestoreFlags()
    {
      flags.construct_counterexample_flag = construct;
      flags.ackermannisation = ack;
      flags.bv_term_abstraction = abstract;
      flags.optimize_flag = optimize;
      flags.cnf_effort = cnf;
      flags.bv_term_abstraction_schema_groups = schemas;
    }
  } restore{bm->UserFlags, constructForCaller, bm->UserFlags.ackermannisation,
            bm->UserFlags.bv_term_abstraction, bm->UserFlags.optimize_flag,
            bm->UserFlags.cnf_effort,
            bm->UserFlags.bv_term_abstraction_schema_groups};

  // A public check never inherits a model from an earlier epoch.  The
  // coordinator installs a replacement only after every same-candidate gate
  // succeeds.
  bm->InvalidateRealModel();
  bm->checkPreparation(PreparationStage::Boundary);
  if (bm->UserFlags.timeout_max_time >= 0 &&
      std::chrono::steady_clock::now() >= deadline)
  {
    bm->soft_timeout_expired = true;
    bm->noteUnknown(UnknownReason::Timeout);
    return bm->unknownResult();
  }

  // One encoding context per actual solve. Keep it after this function
  // returns so counterexample/get-value requests reuse the exact mappings
  // that introduced unspecified-value arrays and lowered the solved formula.
  Ctr_Example->setFpEncodingContext(NULL);
  fpEncodingContext.reset(new FpEncodingContext(bm));
  Ctr_Example->setFpEncodingContext(fpEncodingContext.get());

  // The same lifetime for the floating-point abstraction: one per solve,
  // alive with the model afterwards, registered with the manager only for
  // the solve that abstracted something (TopLevelSTPAux).
  Ctr_Example->setFpAbstraction(NULL);
  bm->setFpAbstraction(NULL);
  fpAbstraction.reset();

  ASTNode original_input;
  ASTNodeMap arrayEqualityRewrites;
  if (query != bm->ASTFalse)
  {
    original_input =
        bm->CreateNode(AND, inputasserts, bm->CreateNode(NOT, query));
  }
  else
  {
    original_input = inputasserts;
  }

  // Order fully symmetric distincts before anything else looks at the
  // formula. It runs here, on this solve's own assembled root, rather than
  // in the parser: only the whole formula shows whether the operands really
  // do occur nowhere else, and re-deciding it per solve is what keeps a
  // later assert from inheriting an ordering it never earned.
  if (bm->UserFlags.distinct_ordering && bm->has_distinct)
  {
    size_t ordered = 0;
    original_input = applyDistinctOrdering(bm, original_input, &ordered);
    if (ordered > 0 && bm->UserFlags.stats_flag)
      std::cerr << "Ordered " << ordered << " symmetric distinct group(s)."
                << std::endl;
  }

  // Whatever the optional symmetry pass did not consume now acquires its
  // ordinary pairwise semantics. This is deliberately after completed-root
  // ordering and before UF, FP, array, or generic preprocessing.
  if (bm->has_distinct)
  {
    original_input = lowerDistinct(bm, original_input);
    if (containsKind(original_input, DISTINCT))
      FatalError("DISTINCT crossed the batch completed-root lowering barrier",
                 original_input);
  }

  // Durable UF nodes stay visible through frontend substitution and query
  // assembly. This is their one batch lowering boundary: before FP
  // totalisation, opaque array equality, or any ordinary preprocessor. Keep
  // the submitted root in batchUFView and pass only its semantic replacement
  // plus query-local naming definitions onward.
  *batchUFView = LoweredApplicationView();
  ASTNodeMap batchUFHandleAliases;
  // Each batch query builds its encoding from nothing, so what the last one
  // assumed says nothing about this one.
  bm->clearInjectivityAssumed();
  skeletonAsked = false;
  if (bm->UserFlags.enable_uninterpreted_functions)
  {
    bm->checkPreparation(PreparationStage::UFLowering);
    // While an application is still a term, push the query's own top-level
    // equalities through it; once lowered, its arguments are protected from
    // exactly this. Gated on the general simplification switches as well as
    // its own, and skipped outright for a root with no application, which
    // has nothing to gain and is the common case.
    const UFPreLoweringChoice ufChoice =
        containsKind(original_input, UF_APPLY)
            ? chooseUFPreLowering(*bm, original_input)
            : UFPreLoweringChoice();
    if (ufChoice.propagate)
    {
      const bool askSkeleton = ufChoice.askSkeleton;
      UFPreLowering pre(bm);
      UFPreLoweringStats preStats;
      original_input = pre.propagate(original_input, &preStats, askSkeleton,
                                     &batchUFHandleAliases);
      pre.report(preStats);
      // The skeleton has been asked; sizeReducing need not ask it again.
      if (askSkeleton)
        skeletonAsked = true;
    }
    UFLowering lowerer(bm);
    *batchUFView = lowerer.lowerCompletedRoot(
        original_input, UFSolveScope::batch(++batchUFScopeGeneration));
    bm->checkPreparation(PreparationStage::UFLowering);
    batchUFView->handleAliases = batchUFHandleAliases;
    original_input = batchUFView->semanticRootWithDefinitions(bm);
    if (containsKind(original_input, UF_APPLY))
      FatalError("UF_APPLY crossed the batch completed-root lowering barrier",
                 original_input);
  }
  else if (bm->getUFContextIfAny() != NULL)
    bm->getUFContextIfAny()->releaseSolveProtection();

  batchUFAdapter->beginQuery(batchUFView.get());
  Ctr_Example->setUFTheoryAdapter(batchUFView->active()
                                      ? batchUFAdapter.get()
                                      : NULL);

  // A UF solve abstracts its wide arithmetic unless told otherwise; see
  // UserDefinedFlags::uf_bv_term_abstraction. Decided on the word-level root,
  // before floating-point lowering can introduce products of its own, and
  // for this solve only: the general flag and the CNF rung it selects are
  // put back afterwards, so a later plain bit-vector query in the same
  // session is encoded exactly as it always was.
  const bool savedTermAbstraction = bm->UserFlags.bv_term_abstraction;
  const uint32_t savedSchemaGroups =
      bm->UserFlags.bv_term_abstraction_schema_groups;
  if (batchUFView->active())
  {
    typedef UserDefinedFlags::UFAbstractionMode Mode;
    const Mode mode = bm->UserFlags.uf_bv_term_abstraction;
    bool abstractTerms = savedTermAbstraction;
    if (mode == Mode::ON)
      abstractTerms = true;
    else if (mode == Mode::OFF)
      abstractTerms = false;
    else if (!abstractTerms)
      abstractTerms = containsWideArithmetic(
          original_input, bm->UserFlags.bv_abstraction_width);
    if (abstractTerms != savedTermAbstraction)
    {
      bm->UserFlags.bv_term_abstraction = abstractTerms;
      if (bm->UserFlags.stats_flag)
        std::cerr << "UF: " << (abstractTerms ? "abstracting" : "not abstracting")
                  << " wide arithmetic for this solve "
                  << "(--uf-bv-term-abstraction)" << std::endl;
    }
    // The division facts the corpus needs; see
    // UserDefinedFlags::uf_quotient_threshold_schemas.
    if (abstractTerms && bm->UserFlags.uf_quotient_threshold_schemas &&
        !bm->UserFlags.bv_term_abstraction_schema_groups_explicit &&
        !bvSchemaGroupEnabled(savedSchemaGroups,
                              BVSchemaGroup::QUOTIENT_THRESHOLDS))
    {
      bm->UserFlags.bv_term_abstraction_schema_groups |=
          bvSchemaGroupBit(BVSchemaGroup::QUOTIENT_THRESHOLDS);
      if (bm->UserFlags.stats_flag)
        std::cerr << "UF: admitting the quotient-threshold schemas for this "
                  << "solve (--uf-quotient-threshold-schemas)" << std::endl;
    }
  }

  // The latch is the same kind of cheap fast-negative the lowering test below
  // uses, widened to cover RoundingMode -- which carries no format, so it
  // never reaches noteFloatingPoint, and which is exactly why this test could
  // not use has_floating_point. Without a negative every pure bit-vector
  // query walked its whole DAG asking each node for its source sort.
  const bool input_uses_floating_point_theory =
      bm->has_floating_point_theory &&
      containsFloatingPointTheory(original_input, bm);
  // Mixed FP/LRA input must reach exact Real preregistration in its original
  // submitted form.  Defer FP totalisation to TopLevelSTPAux, immediately
  // after the coordinator has replaced only its Real predicates.  Pure FP
  // and every feature-off path retain the established ordering here.
  const bool defer_fp_until_after_lra_preregistration =
      lra::Frontend::containsRealSyntax(original_input) ||
      !bm->AllRealSymbols().empty();

  // Make the partial floating-point operations total, canonicalise the
  // indexes of float-indexed arrays, and pin every rounding mode the formula
  // names to the five legal encodings -- before the formula is used for
  // anything. See FpTotalise. This is query-local: an unused or popped FP
  // term must not send a later pure-BV query through an FP-only pass.
  // RoundingMode-element arrays and RoundingMode symbols can each appear
  // without a single float node, hence the broader source-theory test.
  if (input_uses_floating_point_theory &&
      !defer_fp_until_after_lra_preregistration)
  {
    original_input = fpEncodingContext->prepare(original_input);
    fpEncodingContext->copyArrayEqualityRewrites(arrayEqualityRewrites);
  }

  // Lazy congruence for the fully-Real declarations. Eager expansion states
  // every pair before the first solve, and each pair it states is an equality
  // atom, which is a row and a slack variable in the tableau -- quadratic in
  // the applications, and paid whether or not the search ever needed it.
  //
  // A committed model can be asked instead. Group a declaration's
  // applications by the exact values of their arguments, and any two in one
  // group that carry different results have just shown that this pair, and
  // only this pair, needed stating. Add those and solve again.
  //
  // Each round adds at least one constraint the previous model violated, so no
  // round repeats another's work and the pairs available to state are finite:
  // in the worst case this converges on exactly the eager constraint set, and
  // in practice it stops after a round or two having stated almost none of it.
  //
  // The solve below takes the rounds on itself, extending its LRA context in
  // place and keeping its SAT solver -- see TopLevelSTPAux. This loop is the
  // fallback for when it cannot, which is when the theory propagator holds
  // the context: then the next round is a whole new solve over the original
  // query and everything earned so far.
  SOLVER_RETURN_TYPE result;
  ASTVec earnedCongruence;
  lazyCongruence = LazyCongruenceState();
  unsigned restarts = 0;
  for (;;)
  {
    ASTNode round_input = original_input;
    if (!earnedCongruence.empty())
    {
      ASTVec conjuncts;
      conjuncts.reserve(earnedCongruence.size() + 1);
      conjuncts.push_back(original_input);
      conjuncts.insert(conjuncts.end(), earnedCongruence.begin(),
                       earnedCongruence.end());
      round_input = bm->CreateNode(AND, conjuncts);
    }

    std::unique_ptr<SATSolver, QueryTimedDelete<SATSolver>> newS(
        get_new_sat_solver(), {bm->query_timing, QueryPhase::SolverCleanup});
    result = solve_by_sat_solver(newS.get(), round_input, arrayEqualityRewrites,
                                 deadline);
    newS.reset();

    // Only a satisfiable answer rests on a model, and only a model can break
    // congruence. An unsatisfiable one rests on the constraints stated so far,
    // every one of which the query entails.
    if (result != SOLVER_INVALID || !batchUFView->active())
      break;
    const ASTVec fresh = nextLazyCongruenceRound(bm, Ctr_Example, *batchUFView,
                                                 lazyCongruence);
    if (fresh.empty())
      break;
    earnedCongruence.insert(earnedCongruence.end(), fresh.begin(),
                            fresh.end());
    ++restarts;
  }
  // Install both parts of the combined interpretation before indexing UF
  // observations: an argument can be scalar-valued, or a Real ite whose
  // condition needs the counterexample. The counterexample outlives this
  // model; query invalidation discards both before a later solve.
  if (result == SOLVER_INVALID && bm->HasRealModel())
  {
    try
    {
      AbsRefine_CounterExample* counterexample = Ctr_Example;
      STPMgr* manager = bm;
      bm->SetRealConditionOracle(
          [counterexample, manager](const ASTNode& condition) {
            const ASTNode decided =
                counterexample->ModelValueOfFormula(condition);
            if (decided == manager->ASTTrue) return true;
            if (decided == manager->ASTFalse) return false;
            throw std::runtime_error(
                "Real ite condition did not evaluate to a Boolean constant");
          });
      bm->SetRealScalarKeyOracle(
          [counterexample, manager](const ASTNode& argument) {
            std::string key;
            if (!UFModel::scalarModelKey(manager, counterexample, argument,
                                         argument.GetSourceSort(), key))
              throw std::runtime_error(
                  "Real function argument has no concrete scalar model value");
            return key;
          });
      if (batchUFView->active())
        bm->PublishRealApplicationValues(batchUFView->handleToResult);
    }
    catch (const std::exception& failure)
    {
      bm->InvalidateRealModel();
      if (!lra::gaveUpOnABudget(failure))
        return SOLVER_ERROR;
      bm->noteUnknown(UnknownReason::Incomplete,
                      std::string("could not publish the exact function model: ") +
                          failure.what());
      return bm->unknownResult();
    }
  }

  if (bm->UserFlags.stats_flag && batchUFView->active())
    std::cerr << "UF lazy congruence: rounds=" << lazyCongruence.rounds
              << " lemmas=" << lazyCongruence.lemmas
              << " expanded=" << lazyCongruence.expanded.size()
              << " restarts=" << restarts << std::endl;

  // Raw: whether an unsat here is the query's is TopLevelSTP's question, and
  // it has a second run to answer it with.
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

  if (bm->UserFlags.skeleton_preproc && !skeletonAsked)
  {
    skeletonAsked = true;
    // What the Boolean structure settles on its own, conjoined to the query
    // so that the passes below can act on it. Every fact is already implied
    // -- this makes it visible, which is the whole point: a forced equality
    // is one PropagateEqualities can substitute, where the same equality
    // buried inside an implication is not.
    bool skeletonUnsat = false;
    SkeletonPreproc skeleton(bm);
    ASTVec facts = skeleton.derive(inputToSat, skeletonUnsat);
    if (skeletonUnsat)
      return bm->CreateNode(FALSE); // the structure alone refutes the query
    if (!facts.empty())
    {
      facts.push_back(inputToSat);
      inputToSat = bm->defaultNodeFactory->CreateNode(AND, facts);
      bm->ASTNodeStats("After Skeleton Preprocessing: ", inputToSat);
    }
  }

  if (bm->UserFlags.embedded_constraints)
  {
    EmbeddedConstraints ec(bm);
    inputToSat = ec.topLevel(inputToSat);
    bm->ASTNodeStats("After Embedded Constraints: ", inputToSat);
  }

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
    inputToSat = se.topLevel(inputToSat, simp);
    bm->ASTNodeStats(se_message.c_str(), inputToSat);
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

  // Take the factor several of a sum's products have in common out of the
  // sum. Flattening runs first because the extraction reads the n-ary
  // products it builds, and both belong here rather than beside the
  // same-kind extraction later: everything after the difficulty snapshot is
  // reverted together unless the round takes a fifth off the score, which a
  // few percent of multiplications removed does not reach on its own.
  if (bm->UserFlags.enable_common_factor)
  {
    CommonFactor factor(bm, bm->defaultNodeFactory);
    inputToSat = factor.topLevel(inputToSat);
    bm->ASTNodeStats("After Common Factor Extraction: ", inputToSat);
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
namespace
{
// The predicate now lives in Lra/LraBudgetRefusal.h, so that this and the C
// interface cannot drift apart about which layers count as a budget refusal.
bool lraGaveUpOnABudget(const std::exception& thrown)
{
  return lra::gaveUpOnABudget(thrown);
}
} // namespace

SOLVER_RETURN_TYPE
STP::TopLevelSTPAux(SATSolver& NewSolver, const ASTNode& original_input,
                    const ASTNodeMap& arrayEqualityRewrites)
{
  QueryPhaseScope query_work(bm->query_timing, QueryPhase::Other);
  if (bm->has_distinct && containsKind(original_input, DISTINCT))
    FatalError("DISTINCT reached ordinary batch preprocessing", original_input);
  if (bm->UserFlags.enable_uninterpreted_functions &&
      containsKind(original_input, UF_APPLY))
    FatalError("UF_APPLY reached ordinary batch preprocessing",
               original_input);

  // Lowering has installed the current view's protected/registered scalars.
  // Activate them for exactly the preprocessing, SAT and refinement window;
  // retained batch model data remains readable after this scope closes.
  UFContext* ufSolveContext =
      batchUFView->active() ? bm->getUFContextIfAny() : NULL;
  UFContext::SolveScope ufSolveScope(ufSolveContext);

  std::unique_ptr<lra::LraCoordinator, QueryTimedDelete<lra::LraCoordinator>>
      lraCoordinator(nullptr, {bm->query_timing, QueryPhase::LraCleanup});
  ASTNode preregistered_input = original_input;
  ASTNode submitted_counterexample_input = original_input;
  if (lra::Frontend::containsRealSyntax(original_input) ||
      !bm->AllRealSymbols().empty())
  {
    try
    {
      // The Real arguments of the uninterpreted applications, for every
      // model to keep apart. Each one starts at zero and nothing in the
      // lowered formula moves it, so without this they all collide on the
      // first model and congruence has to spend a round telling them apart.
      std::vector<ASTNode> spreadSymbols;
      for (const LoweredApplicationRecord& record : batchUFView->applications)
        for (const ASTNode& actual : record.namedActuals)
          if (actual.GetKind() == SYMBOL &&
              actual.GetSourceSort().kind() == SourceSort::Kind::Real)
            spreadSymbols.push_back(actual);
      ASTNode lra_input = original_input;
      if (NewSolver.timeLimitExpired())
      {
        bm->soft_timeout_expired = true;
        bm->noteBudgetExhausted(NewSolver);
        return bm->unknownResult();
      }
      bm->checkPreparation(PreparationStage::LraPreregistration);
      lraCoordinator.reset(new lra::LraCoordinator(
          *bm, NewSolver, lra_input, spreadSymbols));
      bm->checkPreparation(PreparationStage::LraCore);
      if (!lraCoordinator->ready())
        return SOLVER_ERROR;
      preregistered_input = lraCoordinator->booleanFormula();
      submitted_counterexample_input = preregistered_input;
    }
    catch (const PreparationInterrupted&)
    {
      throw; // The public query boundary owns timeout reporting and cleanup.
    }
    catch (const std::exception& thrown)
    {
      bm->InvalidateRealModel();
      // Building the LRA problem does exact arithmetic at four layers, and
      // each one refuses in its own currency: the number budget itself, the
      // frontend's normalisation, the atom registry, the solve context that
      // hands the core its rows. Every one of them can run out on a query
      // that is perfectly well formed, and none of that is an error in STP.
      //
      // SOLVER_ERROR said it was. It is this interface's "the call was
      // malformed", it is the one verdict that carries no reason, and it
      // leaves the raw internal value on a C boundary documented to answer
      // 0, 1, 2 or 3 -- so a caller could neither find out what happened nor
      // reliably tell it apart from an answer. Give up the way the rest of
      // the solver gives up instead, and keep SOLVER_ERROR for the failures
      // that really are ours.
      if (!lraGaveUpOnABudget(thrown))
        return SOLVER_ERROR;
      bm->noteUnknown(
          UnknownReason::Incomplete,
          std::string("the exact linear arithmetic solver could not build "
                      "this query within its resource budget: ") +
              thrown.what());
      return bm->unknownResult();
    }
  }

  const bool lraActive = lraCoordinator != nullptr;
  // The Real path's Boolean skeleton is the shape on which the fast CNF
  // generator is the slow one; see the flag.
  bm->UserFlags.cnf_auto_real_path = lraActive;

  // ARRAY_EQ remains a normal, traversable AST node through query assembly
  // and macro/function substitution. Lower it only now, at the complete-query
  // boundary and before any ordinary simplifier or array transform runs.
  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  if (ext != NULL)
    ext->beginSolve();

  //
  // Nothing here runs without the option. ARRAY_EQ has exactly one
  // producer -- the hashing factory, which every front end's node
  // creation bottoms out in -- and it refuses to build one while the
  // option is off, so a query that never enabled it cannot contain one
  // and does not have to be walked to find that out. A second check
  // here would defend a state its own enforcement point already makes
  // unreachable, at the price of a whole-DAG traversal on every solve
  // STP performs.
  // The rewrite map is subject to the same argument: floating-point
  // preparation records an entry only for a node that was already an
  // ARRAY_EQ, so a non-empty map means one was built, which means the
  // option was on.
  std::unique_ptr<PropagateEqualities> pe(
      new PropagateEqualities(simp, bm->defaultNodeFactory, bm));

  ASTNode semantic_input =
      preregistered_input;
  ASTNodeMap effective_array_equality_rewrites = arrayEqualityRewrites;
  if (lraActive && bm->has_floating_point_theory &&
      containsFloatingPointTheory(original_input, bm))
  {
    semantic_input = fpEncodingContext->prepare(semantic_input);
    effective_array_equality_rewrites.clear();
    fpEncodingContext->copyArrayEqualityRewrites(
        effective_array_equality_rewrites);
  }
  if (bm->UserFlags.enable_array_equality)
  {
    const bool hasOpaqueEquality =
        containsKind(original_input, ARRAY_EQ) ||
        !effective_array_equality_rewrites.empty();

    // A definitional equality -- a symbol equated with an array term at
    // the top level, (= A (store B i v)) -- substitutes the symbol away
    // outright, which is strictly cheaper than abstracting the equality
    // and refining it with lemmas. Run the propagator once before
    // lowering so those equalities never reach abstraction; whatever
    // remains (negated, nested, or non-definitional equalities) lowers
    // as before. This is the only point in the solve where the
    // propagator can see an ARRAY_EQ at all.
    if (!lraActive && hasOpaqueEquality && bm->UserFlags.optimize_flag &&
        bm->UserFlags.propagate_equalities)
    {
      semantic_input = pe->topLevel(semantic_input);
      bm->ASTNodeStats(pe_message.c_str(), semantic_input);
    }

    // The same argument for unconstrained elimination, and it is the
    // only window where its array rules can do anything: an equality
    // with an unconstrained operand is a free Boolean, so it settles
    // here rather than costing a record, a witness pair and a refinement
    // loop. Afterwards the operands sit under witness reads whose shape
    // ExtensionalityContext has to recognise, and the rules turn
    // themselves off (RemoveUnconstrained::arrayRules).
    //
    // This is what the "unconstrained" benchmarks of Brummayer's
    // dissertation ask for. Their arrays are each used once and the
    // selector bits come from wide divisions that no model needs, so
    // reaching abstraction at all means bit-blasting an unsatisfiable
    // amount of dead arithmetic.
    if (!lraActive && hasOpaqueEquality && bm->UserFlags.optimize_flag &&
        bm->UserFlags.enable_unconstrained)
    {
      RemoveUnconstrained r(*bm);
      semantic_input = r.topLevel(semantic_input, simp);
      bm->ASTNodeStats(uc_message.c_str(), semantic_input);
    }

    if (ext == NULL && hasOpaqueEquality)
    {
      ext = bm->getExtensionality();
      ext->beginSolve();
    }
    // Reuse an existing context object when present; beginSolve() above has
    // cleared all generated records. The lowering pass builds fresh
    // solve-local records and computes an empty active set when this root has
    // no equality.
    if (ext != NULL)
      semantic_input =
          ext->lowerArrayEqualities(semantic_input,
                                    effective_array_equality_rewrites);
  }

  bm->ASTNodeStats("input asserts and query: ", semantic_input);

  // has_floating_point is deliberately only a manager-lifetime fast-negative
  // hint. A float built in a popped scope (or never asserted at all) must not
  // send this query through the lowering pass. Do not reset the hint on pop:
  // public AST handles may retain the old node and use it in a later query.
  const bool input_has_floating_point =
      bm->has_floating_point && containsFloatingPoint(original_input, bm);

  DifficultyScore difficulty;
  if (bm->UserFlags.stats_flag)
    cerr << "Difficulty Initially:" << difficulty.score(semantic_input, bm)
         << endl;

  // A heap object so I can easily control its lifetime.
  std::unique_ptr<BVSolver> bvSolver(new BVSolver(bm, simp));

  ASTNode inputToSat = semantic_input;

  // Array equality (lemmas on demand, Brummayer & Biere JSAT 2009):
  // with at least one array equality reachable from the current root, conjoin
  // exactly its active dependency closure's witness constraints. These are
  // preprocessing step 1 of the paper: a fresh index lambda with two virtual
  // reads witnessing inequality. The anchors keep each operand reachable and
  // carry it through the same preprocessing as the rest of the formula so its
  // current form can be recovered. Array-valued ITEs remain structural and
  // are handled directly by the consistency checker's T rules. A query with
  // no active array equality stays on STP's ordinary array path.
  bool extActive = ext != NULL && ext->active();
  // Releases the record-table seal on every exit from this function.
  ExtensionalityContext::SolveScope extScope(ext);
  if (extActive)
  {
    inputToSat = ext->prepareInitialFormula(inputToSat);
    extActive = ext->active();
  }

  // Record anchors keep equality operands live even when no array operation
  // is reachable from the lowered Boolean root, so active extensionality
  // counts as array operations for the refinement machinery.
  bool arrayops = containsArrayOps(inputToSat, bm) || extActive;

  // If the number of array reads is small. We rewrite them through.
  // The bit-vector simplifications are more thorough than the array
  // simplifications. For example,
  // we don't currently do unconstrained elimination on arrays--- but we do for
  // bit-vectors.
  // A better way to do this would be to estimate the number of axioms
  // introduced.
  // TODO: I chose the number of reads we perform this operation at randomly.
  bool removed = false;
  const int arrayReadLimit = bm->UserFlags.ackermannisation ? 50 : 10;
  // The read count is a proxy for what the transform builds, and on its own a
  // poor one: a read over a chain of WRITEs becomes one ITE per link, so nine
  // reads over a deep store chain expand into tens of thousands of nodes and
  // take 48x longer than leaving them to read refinement. Ask what the
  // expansion would actually cost as well, so the flat-array queries this
  // threshold was tuned for still take it and the deep-chain ones do not.
  // Give each read admitted by the count policy twenty structural expansion
  // units before preferring refinement. This is a safety threshold, not a
  // prediction of total solver work.
  constexpr uint64_t arrayEagerCostPerRead = 20;
  const uint64_t arrayEagerCostLimit =
      static_cast<uint64_t>(arrayReadLimit) * arrayEagerCostPerRead;
  if (arrayops &&
      !extActive && // array equality needs the refinement loop
      numberOfReadsLessThan(inputToSat, arrayReadLimit) &&
      arrayEagerCostLessThan(inputToSat, arrayEagerCostLimit))
  {
    // If the number of axioms that would be added it small. Remove them.
    bm->UserFlags.ackermannisation = true;
    inputToSat = arrayTransformer->TransformFormula_TopLevel(inputToSat);
    if (bm->UserFlags.stats_flag)
    {
      cerr << "Have removed array operations" << endl;
    }
    removed = true;

    // With ackermannisation on, the transform removes every array
    // operation.
    arrayops = false;
    assert(!containsArrayOps(inputToSat, bm));
  }

  // Bounded variable addition is decided here rather than at solver
  // construction because AUTO wants the post-simplification answer: the
  // Ackermannisation above can remove every array operation, and arrayops
  // is only final from this point on. The solver has not yet been handed a
  // clause, which is the only window in which it accepts the setting. ON is
  // the default, so a decline (no CaDiCaL 3.x behind the build, or a
  // different backend) is only worth a warning when ON was asked for by
  // name; a declined AUTO is just the heuristic not applying.
  //
  // ON is a bit-vector default: the measurement behind it (a 0.76-0.80
  // geometric mean of wall clock on hard QF_BV, -12.5% total wall over 42k
  // easy ones) never saw a Real query, and the shape it was fitted on is not
  // the shape the Real path produces. What BVA is handed there is a wide,
  // shallow conjunction of small clauses over opaque atoms, one per Real
  // predicate. Over all 3 037 SMT-LIB QF_LRA and QF_UFLRA files, each run
  // under both settings back to back on one binary, factoring costs seven
  // files (2 650 solved against 2 657) and 2.8% of the CPU the 1 000 both
  // settle spend, at a 0.983 geometric mean. No answer disagreed.
  //
  // Its cost is concentrated rather than broad, and only part of the win is
  // work removed. Sampling 47 hard files puts factoring at a mean 0.4% of
  // the profile and at nothing at all on 26 of them, but at 20-23% on the
  // LassoRanker queries where it does engage -- and of the eleven files
  // turning it off newly solves, four carry a share that large while the
  // rest sit near zero and simply get a different, luckier search out of the
  // smaller encoding. Both halves point the same way here; only the first
  // half would survive a change to CaDiCaL's search.
  //
  // So an active Real solve that did not name the flag takes the AUTO rule
  // instead of the ON default. AUTO rather than OFF because a Real query can
  // still carry array operations, and surviving arrays are exactly the shape
  // AUTO was fitted to keep BVA for; on the QF_LRA/QF_UFLRA sets, which have
  // none, the two coincide and the measurement above is of this code. An
  // explicit --cadical-factor is honoured as before, on either path.
  UserDefinedFlags::BVAMode bvaMode = bm->UserFlags.cadical_factor;
  if (lraActive && !bm->UserFlags.cadical_factor_explicit &&
      bvaMode == UserDefinedFlags::BVAMode::ON)
    bvaMode = UserDefinedFlags::BVAMode::AUTO;

  enableBVAIfWanted(
      NewSolver, bm->UserFlags,
      bvaMode == UserDefinedFlags::BVAMode::ON ||
          (bvaMode == UserDefinedFlags::BVAMode::AUTO && arrayops),
      true);

  // Recomputed per query, never latched: every input is available here,
  // including the C API's direct request, so a query that happens to need a
  // candidate model cannot leave construction switched on for the rest of
  // the session.
  bm->UserFlags.construct_counterexample_flag =
      lraActive ||
      bm->UserFlags.modelConstructionRequired(
          (arrayops && !removed) || batchUFView->active() ||
          bm->UserFlags.fp_abstraction);

  // Ahead of everything that reads the term structure: constant bit
  // propagation's fixed-point map, the difficulty score, the sub-sum
  // extraction and the blaster all describe whatever tree they are handed,
  // and a combination that has been given its canonical spelling is a
  // combination they see once rather than twice.
  if (!lraActive && bm->UserFlags.enable_linear_form)
  {
    LinearForm linear(bm, bm->defaultNodeFactory,
                      bm->UserFlags.linear_form_addend_limit < 0
                          ? std::numeric_limits<size_t>::max()
                          : static_cast<size_t>(
                                bm->UserFlags.linear_form_addend_limit));
    inputToSat = linear.topLevel(inputToSat);
    bm->ASTNodeStats("After Linear Canonical Form: ", inputToSat);
  }

  // Before the passes that read the term structure, so that an equality
  // proved here is one they can act on: constant bit propagation, the
  // difficulty score and the blaster all describe whatever tree they are
  // handed, and two applications a proved equality collapses are an
  // application they see once.
  //
  // After the canonicaliser above, where both are asked for. A pair that
  // differs only in how its combination is spelled is one that pass has
  // already made a single node, so what is left to propose here is the
  // pairs a spelling does not account for -- and each of those costs a
  // sub-solve, where the canonical form costs a rewrite.
  if (!lraActive && bm->UserFlags.enable_congruence_candidates)
  {
    CongruenceCandidates congruence(
        bm, bm->defaultNodeFactory,
        bm->UserFlags.congruence_candidate_limit < 0
            ? std::numeric_limits<size_t>::max()
            : static_cast<size_t>(bm->UserFlags.congruence_candidate_limit),
        bm->UserFlags.congruence_candidate_conflicts);

    ASTVec facts = congruence.derive(inputToSat);
    if (!facts.empty())
    {
      facts.push_back(inputToSat);
      inputToSat = bm->defaultNodeFactory->CreateNode(AND, facts);
      bm->ASTNodeStats("After Congruence Candidates: ", inputToSat);
    }
  }

  // Flattening is structural -- nested conjunctions and disjunctions become
  // one n-ary node -- so it is sound over the opaque atoms an active Real
  // solve has put in the formula, and it is what keeps a formula nested as
  // deep as an unrolled trace from reaching the CNF layer as a chain the
  // bit-blaster's recursion has to follow level by level.
  if (bm->UserFlags.enable_flatten)
  {
    Flatten flatten(bm,bm->defaultNodeFactory);
    inputToSat = flatten.topLevel(inputToSat);
    bm->ASTNodeStats("After Sharing-aware Flattening: ", inputToSat);
  }

  if (!lraActive && bm->UserFlags.bitConstantProp_flag)
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

  // LRA keeps the preregistered Boolean skeleton intact through the word-level
  // pipeline.  Legacy simplifiers are allowed to assign pure/unconstrained
  // Boolean symbols and remember those assignments only in model-replay
  // tables; an opaque theory atom must instead remain in the SAT candidate so
  // a verified no-good can constrain the same literal on the next round.
  if (!lraActive)
    inputToSat =
        sizeReducing(inputToSat, bvSolver.get(), pe.get(), domain.get());

  // Difficulty reversion asks whether the word-level simplifiers left the
  // formula harder than they found it, and puts it back if they did. An
  // active Real solve runs none of them -- every pass between the two scores
  // is behind !lraActive -- so both scores are the same node's, the test
  // reads X > 0.8X, and the revert fires on every solve to restore what
  // nothing changed. It costs the scorer's walk of the whole DAG, it makes
  // the simplifier drop its tables a few hundred lines before the solve
  // drops them anyway, and under -s it reports "simplification made the
  // problem harder" about a query that was never simplified. None of the
  // state it touches -- the solver map, the read registry, optimize_flag --
  // is read again on this path before it is cleared or restored. So do not
  // run the apparatus rather than pay for it to do nothing.
  const bool difficultyReversionApplies = !lraActive;

  int64_t initial_difficulty_score =
      difficultyReversionApplies ? difficulty.score(inputToSat, bm) : 0;

  // It's helpful to know the initial node size. The difficulty scorer can easily get something similar:
  const int64_t initial_node_size = difficulty.getEvalCount();

  // Fixed point it if it's not too difficult.
  // Currently we discards all the state each time sizeReducing is called,
  // so it's expensive to call.
  if (!lraActive && !arrayops &&
      (-1 == bm->UserFlags.size_reducing_fixed_point ||
       initial_node_size < bm->UserFlags.size_reducing_fixed_point))
  {
    inputToSat =
        callSizeReducing(inputToSat, bvSolver.get(), pe.get(), domain.get());
  }

  // Lower floating-point operations before the first pass that invokes the
  // bit-blaster. From here on the formula is a packed-bit circuit: float
  // symbols, constants and reads retain sort metadata for model
  // reconstruction. The only FP operations that survive are the predicates
  // over packed-view operands -- the four ordering comparisons, the two
  // equalities (fp.eq and = on floats) and the seven classifications --
  // which the bit-blaster encodes natively over the packed bits
  // (BBcompareFP, BBeqFP, BBclassifyFP); every downstream pass already has
  // arms for these kinds because they used to reach it before lowering
  // existed.
  //
  // This remains after all of the size-reducing passes above. In particular,
  // RemoveUnconstrained must see a float symbol rather than its exposed bits.
  //
  // See FloatBlast for why this is a pass of its own: doing it inside
  // simplification meant building floating-point nodes over bitvector
  // children and stamping a float format on them to make them type check,
  // and that stamp landed on hash-consed nodes the input still used as plain
  // bitvectors.
  // Floating-point abstraction (--fp-abstraction): immediately before the
  // lowering commits an operation to its circuit, replace the admitted
  // operations by same-sort surrogates and conjoin their proxy definitions
  // and rule tiers. The result is lowered like any other formula; the
  // surrogates are packed views of bit-vector symbols, so nothing here
  // builds a SymFPU operation. See FpAbstraction.
  bool fpAbstractionActive = false;
  // Declined on an LRA solve: the exact linear Real coordinator owns that
  // solve's candidate check and refinement loop, and one owner is enough.
  if (input_has_floating_point && bm->UserFlags.fp_abstraction && !lraActive)
  {
    fpAbstraction.reset(new FpAbstraction(bm, fpAbstractionExact,
                                          fpAbstractionRestarts,
                                          fpAbstractionPreviouslyAbstracted));
    const ASTNode abstracted = fpAbstraction->abstract(inputToSat);
    if (fpAbstraction->active())
    {
      inputToSat = abstracted;
      fpAbstractionActive = true;
      bm->setFpAbstraction(fpAbstraction.get());
      Ctr_Example->setFpAbstraction(fpAbstraction.get());
      // The shared counterexample machinery may still carry the driver's
      // array-route repair gate; the batch replay certifies.
      Ctr_Example->setFpRepairAllowed(true);
      bm->ASTNodeStats("After floating-point abstraction: ", inputToSat);
    }
    else
      fpAbstraction.reset();
  }

  if (input_has_floating_point)
  {
    bm->checkPreparation(PreparationStage::Encoding);
    inputToSat = fpEncodingContext->lowerPrepared(inputToSat);
    bm->ASTNodeStats("After floating-point lowering: ", inputToSat);

    // Everything downstream works on the lowered form, so the snapshot that
    // difficulty reversion later compares against has to describe that form
    // rather than the much smaller word-level FP syntax. Retaken here because
    // the recompute below is skipped for array problems.
    if (difficultyReversionApplies)
      initial_difficulty_score = difficulty.score(inputToSat, bm);
  }

  if (difficultyReversionApplies &&
      (!arrayops || bm->UserFlags.array_difficulty_reversion))
  {
    initial_difficulty_score = difficulty.score(inputToSat, bm);
  }

  if (bm->UserFlags.stats_flag && difficultyReversionApplies)
    cout << "Difficulty After Size reducing:" << initial_difficulty_score
         << endl;

  // So we can delete the object and release all the hash-buckets storage.
  std::unique_ptr<Revert_to> revert(new Revert_to());

  if (difficultyReversionApplies &&
      (!arrayops || bm->UserFlags.array_difficulty_reversion))
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
      return bm->unknownResult();

    if (!lraActive && bm->UserFlags.optimize_flag)
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

          // These replacements are not recorded in the solver map, so
          // a symbol the array-equality procedure depends on must not
          // be replaced away.
          UFContext* ufContext = bm->getUFContextIfAny();
          if (extActive ||
              (ufContext != NULL && ufContext->activeInSolve()))
            for (ASTNodeMap::iterator cit = constants.begin();
                 cit != constants.end();)
            {
              if (cit->first.GetKind() == SYMBOL &&
                  ((extActive && ext->isProtected(cit->first)) ||
                   (ufContext != NULL &&
                    ufContext->isProtected(cit->first))))
                cit = constants.erase(cit);
              else
                ++cit;
            }

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

  if (!lraActive && bm->UserFlags.bitConstantProp_flag)
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

  if (!lraActive && bm->UserFlags.enable_use_intervals &&
      bm->UserFlags.bitConstantProp_flag)
  {
    bm->GetRunTimes()->start(RunTimes::StrengthReduction);
    StrengthReduction sr(bm->defaultNodeFactory, &bm->UserFlags);
    inputToSat = sr.topLevel(inputToSat, *domain);
    bm->GetRunTimes()->stop(RunTimes::StrengthReduction);

    bm->ASTNodeStats(domain_message.c_str(), inputToSat);
  }

  domain.reset(nullptr);

  if (!lraActive && bm->UserFlags.enable_pure_literals)
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
    return bm->unknownResult();

  if (!lraActive && bm->UserFlags.enable_ite_context)
  {
    UseITEContext iteC(bm);
    inputToSat = iteC.topLevel(inputToSat);
    bm->ASTNodeStats("After ITE Context: ", inputToSat);
  }

  if (!lraActive && bm->UserFlags.enable_aig_core_simplify)
  {
    AIGSimplifyPropositionalCore aigRR(bm);
    inputToSat = aigRR.topLevel(inputToSat);
    bm->ASTNodeStats("After AIG Core: ", inputToSat);
  }

  if (!lraActive && simp->hasUnappliedSubstitutions())
    inputToSat = simp->applySubstitutionMap(inputToSat);

  // Extract sub-terms shared between same-kind applications of each
  // associative-commutative operator, ahead of unconstrained-variable
  // elimination: a pair of otherwise-unused variables occurring only inside
  // the shared node makes that node collapsible there. This also keeps the
  // extraction ahead of the ConstantBitPropagation object built below,
  // whose fixed-point map must describe the exact tree handed to ToSATAIG.
  // BVOR is absent because the node factory lowers it to BVNOT/BVAND at
  // creation, so its sharing is BVAND sharing by the time this runs.
  if (!lraActive && bm->UserFlags.enable_common_subsum)
  {
    for (const Kind k : {BVPLUS, BVMULT, BVXOR, BVAND, XOR, AND, OR})
    {
      CommonSubSum cse(bm, bm->defaultNodeFactory, k);
      inputToSat = cse.topLevel(inputToSat);
    }
    bm->ASTNodeStats("After Common Sub-term Extraction: ", inputToSat);
  }

  if (!lraActive && bm->UserFlags.enable_unconstrained)
  {
    RemoveUnconstrained r(*bm);
    inputToSat = r.topLevel(inputToSat, simp);
    bm->ASTNodeStats(uc_message.c_str(), inputToSat);
  }

  bm->TermsAlreadySeenMap_Clear();

  int64_t final_difficulty_score = difficulty.score(inputToSat, bm);
  bm->expected_blast_ands = final_difficulty_score;

  // Simplification has to have taken a fifth off the score to count as having
  // helped. Written as an assignment now that the AIG node count is gone: it
  // was the second of the two things that could set this.
  const bool worse = difficultyReversionApplies &&
                     final_difficulty_score > .8 * initial_difficulty_score;

  if (bm->UserFlags.stats_flag && difficultyReversionApplies)
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

    // Variable-to-constant assignments discovered during the discarded
    // simplification can't make the problem harder, so they are re-applied
    // to the reverted formula.
    ASTNodeMap keptConstants;
    for (const auto& e : *simp->Return_SolverMap())
      if (e.first.GetKind() == SYMBOL && e.second.isConstant() &&
          revert->initialSolverMap.find(e.first) ==
              revert->initialSolverMap.end())
        keptConstants.insert(e);

    inputToSat = revert->toRevertTo;
    bm->expected_blast_ands = initial_difficulty_score;

    // I do this to clear the substitution/solver map.
    // Not sure what would happen if it contained simplifications
    // that haven't been applied.
    simp->ClearAllTables();

    simp->Return_SolverMap()->insert(revert->initialSolverMap.begin(),
                                     revert->initialSolverMap.end());
    revert->initialSolverMap.clear();

    if (keptConstants.size() > 0)
    {
      if (bm->UserFlags.stats_flag)
        cerr << "Re-applying " << keptConstants.size()
             << " discovered constants." << endl;
      ASTNodeMap cache;
      inputToSat = SubstitutionMap::replace(inputToSat, keptConstants, cache,
                                            bm->defaultNodeFactory);
      simp->Return_SolverMap()->insert(keptConstants.begin(),
                                       keptConstants.end());
      bm->ASTNodeStats("after reverting: ", inputToSat);
    }

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

  // A pre-view pass may already have proved the formula false. In that
  // case no candidate or bound graph is needed; any satisfiable active
  // candidate is required below to have passed preparation and binding.
  const bool extPrepared = extActive && !inputToSat.isConstant();
  if (extPrepared)
  {
    // Array equality: final preparation, immediately before the one
    // main array transform. Recover the current equality operands,
    // collect and freeze the complete array graph (including retained
    // array-valued if-then-elses), and conjoin the naming equations that
    // give future lemma leaves SAT variables.
    inputToSat = ext->prepare(inputToSat);
    bm->ASTNodeStats("after extensionality preparation: ", inputToSat);
  }

  // ARRAY_EQ is a user-facing, solve-boundary node only.  Check the exact
  // root handed to the ordinary array transformer so that no future
  // preparation rewrite can accidentally leak opaque equality semantics
  // into code which has no case for it.  This barrier is worth its walk,
  // but only where the node it looks for can exist: with the option off
  // the factory never built one, so a query that never enabled the
  // feature pays nothing.
  if (bm->UserFlags.enable_array_equality &&
      containsKind(inputToSat, ARRAY_EQ))
    FatalError("array-equality: an opaque equality reached the final array "
               "transformation boundary",
               inputToSat);

  // extPrepared implies extActive, and an active registry counts as array
  // operations above -- so a prepared registry always reaches this transform.
  // bindAfterTransform below reads the map only this call populates, so
  // skipping it for a prepared registry would silently bind no reads.
  assert(!extPrepared || arrayops);

  if (arrayops)
  {
    inputToSat = arrayTransformer->TransformFormula_TopLevel(inputToSat);
    bm->ASTNodeStats("after transformation: ", inputToSat);
  }
  bm->TermsAlreadySeenMap_Clear();

  if (extPrepared)
    ext->bindAfterTransform(arrayTransformer);

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

  // The bit-vector abstractions are refined from candidate models too, so a
  // query carrying one needs the refinement machinery kept alive even with no
  // array operation in it.
  const bool maybeRefinement =
      lraActive || (arrayops && !bm->UserFlags.ackermannisation) ||
      bm->UserFlags.bv_eq_abstraction ||
      bm->UserFlags.bv_term_abstraction || batchUFView->active() ||
      fpAbstractionActive;

  simplifier::constantBitP::ConstantBitPropagation* cb = NULL;
  std::unique_ptr<simplifier::constantBitP::ConstantBitPropagation> cleaner;

  //TODO should be replaced by the upwards cbitp cache.
  if (!lraActive && bm->UserFlags.bitConstantProp_flag)
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
  // The encoder may consume CB before CNF conversion. Match that handoff
  // on every exit, including cancellation after it has already deleted CB.
  struct ReleaseConsumedCB
  {
    std::unique_ptr<simplifier::constantBitP::ConstantBitPropagation>& owner;
    ToSATAIG& encoder;
    ~ReleaseConsumedCB() { if (encoder.cbIsDestructed()) owner.release(); }
  } release_consumed_cb{cleaner, toSATAIG};
  QueryCleanupOnExit query_cleanup(bm->query_timing, QueryPhase::QueryCleanup);
  // Whether the refinement below is only the uninterpreted-function loop,
  // which lets the lowering choose its CNF rung from the estimate rather
  // than fall back to the size-based ABC rung meant for array refinement.
  // The bit-vector abstractions choose their own rung ahead of this.
  toSATAIG.setUFOnlyRefinement(
      batchUFView->active() && !(arrayops && !bm->UserFlags.ackermannisation) &&
      !extActive);
  ToSATBase* satBase = &toSATAIG;
  const auto reportBVAbstractionRecords = [&]() {
    if (bm->UserFlags.quick_statistics_flag)
      toSATAIG.reportBVAbstractionRecords(std::cerr);
    if (fpAbstractionActive &&
        (bm->UserFlags.stats_flag || bm->UserFlags.quick_statistics_flag))
      fpAbstraction->reportStatistics(std::cerr);
  };


  if (lraCoordinator != nullptr)
  {
    for (const ASTNode& atom : lraCoordinator->opaqueAtoms())
      toSATAIG.protectSymbol(atom);
    lraCoordinator->setLegacyArrayRefinementEnabled(
        arrayops && !extActive && !bm->UserFlags.ackermannisation);

    // Keep the whole transformed abstraction retractable while a candidate
    // is being inspected.  A theory no-good is inserted only after this
    // assumption has been released; the following same-solver call asserts
    // it again.  Thus root-level abstraction UNSAT is reported by solve(),
    // never misclassified as an addClause failure on a strict backend.
    if (!inputToSat.isConstant())
    {
      const ASTNode& activation = lraCoordinator->solveActivation();
      inputToSat = bm->CreateNode(
          IMPLIES, activation, inputToSat);
      if (!NewSolver.supportsAssumptions() ||
          !toSATAIG.setRequiredSolveAssumption(activation))
      {
        lraCoordinator->failClosed(
            "active LRA solve requires common SAT assumptions");
        return SOLVER_ERROR;
      }
    }
  }

  if (bm->soft_timeout_expired)
    return bm->unknownResult();

  NewSolver.enableRefinement(maybeRefinement);

  if (bm->UserFlags.stats_flag)
    bm->print_stats();

  // If it doesn't contain array operations, use ABC's CNF generation.
  // semantic_input decides the verdict; original_input -- the same query
  // with its opaque array equalities still in place -- is what
  // --check-counterexample re-evaluates, so the check covers the Boolean
  // skeleton the lowering rebuilt rather than repeating the question
  // just answered. The equalities themselves are checked against the
  // published array cells, not re-evaluated here.
  // Snapshotted before the first solve: that call refines the bit-vector
  // abstractions too, and the driver's loop below reads the count to decide
  // whether the round it is looking at made progress.
  uint64_t abstractionsRefined = satBase->abstractionRefinements();

  bm->checkPreparation(PreparationStage::Encoding);
  res = Ctr_Example->CallSAT_ResultCheck(
      NewSolver, inputToSat, semantic_input,
      submitted_counterexample_input,
      satBase, maybeRefinement
      , lraCoordinator.get()
      );
  ++lazyCongruence.rounds;

  // A satisfiable answer over an uninterpreted Real function is provisional
  // until its model has been read for congruence. The pairs it breaks are
  // stated to the same solve: the coordinator registers their atoms and
  // rebuilds its exact core, the lemma is encoded into the SAT solver that
  // has been running all along -- with every clause it has learned -- and
  // the search resumes. Each round states something the previous model
  // violated, so this ends.
  const auto lazyCongruenceRound = [&]() -> bool {
    if (res != SOLVER_INVALID || lraCoordinator == nullptr ||
        !batchUFView->active() || !bm->UserFlags.uf_lazy_in_place)
      return false;
    const ASTVec fresh = nextLazyCongruenceRound(bm, Ctr_Example, *batchUFView,
                                                 lazyCongruence);
    if (fresh.empty())
      return false;
    const ASTNode lemma = fresh.size() == 1 ? fresh[0]
                                            : bm->CreateNode(AND, fresh);
    const lra::ExtensionOutcome extended =
        lraCoordinator->extendWithFormula(lemma, *satBase);
    lraCoordinator->rethrowPreparationInterruption();
    if (extended != lra::ExtensionOutcome::Extended)
    {
      // Give the lemmas back either way: this round did not state them.
      for (const ASTNode& item : fresh)
        lazyCongruence.earned.erase(item);
      lazyCongruence.lemmas -= fresh.size();
      if (extended == lra::ExtensionOutcome::Declined)
        // The coordinator would not take it on and nothing moved. The
        // caller's restart loop finds the lemmas again and states them from
        // the top over a new solve.
        return false;
      // The extension began and could not finish. It has already dropped the
      // committed model the restart loop re-derives its lemmas from, so that
      // loop would find nothing to state and return this round's `sat` -- for
      // a query whose congruence this round has just shown to be broken.
      // There is no answer here, only which kind of no-answer it is.
      if (extended == lra::ExtensionOutcome::ResourceLimit)
      {
        bm->noteUnknown(
            UnknownReason::Incomplete,
            std::string("the exact linear arithmetic solver could not take on "
                        "a congruence lemma within its resource budget: ") +
                lraCoordinator->failureDetail());
        res = bm->unknownResult();
      }
      else
        res = SOLVER_ERROR;
      return false;
    }
    batchUFAdapter->invalidateCertifiedModel();
    Ctr_Example->ClearAllTables();
    bm->checkPreparation(PreparationStage::Encoding);
    res = Ctr_Example->CallSAT_ResultCheck(
        NewSolver, bm->ASTTrue, semantic_input, submitted_counterexample_input,
        satBase, true, lraCoordinator.get());
    ++lazyCongruence.rounds;
    return true;
  };
  while (lazyCongruenceRound())
  {
  }

  if (bm->soft_timeout_expired)
  {
    reportBVAbstractionRecords();
    return bm->unknownResult();
  }

  if (SOLVER_UNDECIDED != res)
  {
    // The counters are cumulative over the checker's lifetime, so a batch
    // query decided before the refinement loop still has rounds to report
    // -- earlier queries' rounds. Both decision exits report, or a later
    // query would silently drop the line the driver prints for it.
    if (ext != NULL)
      ext->reportLemmaStats();
    reportBVAbstractionRecords();
    CountersAndStats("print_func_stats", bm);
    return res;
  }

  // An undecided result belongs to an active array, bit-vector abstraction,
  // floating-point abstraction, UF, or LRA refinement owner.
  assert(arrayops || toSATAIG.hasBVEQAbstractions() ||
         toSATAIG.hasBVTermAbstractions() || batchUFView->active() ||
         fpAbstractionActive || lraActive);
  // Refinement must be enabled too, unless an abstraction, UF, or LRA owns
  // the round.
  assert(toSATAIG.hasBVEQAbstractions() || toSATAIG.hasBVTermAbstractions() ||
         batchUFView->active() || fpAbstractionActive || lraActive ||
         !bm->UserFlags.ackermannisation);

  // Refinement driver. Every owner that retained a candidate-blocking
  // lemma is drained before the next solve, rather than the first one
  // that has something: the round has to leave no certificate behind.
  // The bit-vector abstractions are refined inside CallSAT_ResultCheck,
  // ahead of the checkers, so a round that refined one arrives here with
  // nothing pending and the raised count is what says the search has
  // somewhere to go. Encoding only the abstraction's clauses and
  // re-solving instead would present the array checker with a second
  // candidate while its certificate for the first was still pending --
  // which the checker refuses outright, and is right to: dropping the
  // certificate would lose the conflict.
  //
  // In an active equality solve the extensionality checker owns the
  // complete array graph, so each undecided candidate must carry a
  // pending theory lemma and legacy read refinement is never entered.
  // Without an active equality, retain STP's ordinary read-refinement
  // path unchanged.
  ArrayReadRefinementProgress lraReadRefinementProgress;
  while (true)
  {
    const uint64_t refinedNow = satBase->abstractionRefinements();
    bool progress = refinedNow != abstractionsRefined;
    abstractionsRefined = refinedNow;

    if (lraCoordinator != nullptr && lraCoordinator->hasPendingLraClause())
    {
      if (!lraCoordinator->encodePendingLraClause())
        return SOLVER_ERROR;
      bm->checkPreparation(PreparationStage::Encoding);
      res = Ctr_Example->CallSAT_ResultCheck(
          NewSolver, bm->ASTTrue, semantic_input,
          submitted_counterexample_input, satBase, true,
          lraCoordinator.get());
    }
    else if (lraCoordinator != nullptr &&
             lraCoordinator->legacyArrayRefinementPending())
    {
      const bool encoded = Ctr_Example->AddArrayReadRefinementForCandidate(
          NewSolver, satBase, &lraReadRefinementProgress);
      if (!encoded)
      {
        lraCoordinator->failClosed(
            "ordinary mismatch produced no legacy array-read refinement");
        return SOLVER_ERROR;
      }
      lraCoordinator->noteLegacyArrayRefinementEncoded();
      if (!lraCoordinator->ready())
        return SOLVER_ERROR;
      Ctr_Example->ClearAllTables();
      bm->checkPreparation(PreparationStage::Encoding);
      res = Ctr_Example->CallSAT_ResultCheck(
          NewSolver, bm->ASTTrue, semantic_input,
          submitted_counterexample_input, satBase, true,
          lraCoordinator.get());
    }
    else
    {
      if (extActive)
      {
        // An undecided candidate the bit-vector abstraction did not account
        // for is still a checker's, and one of them still owes a lemma for
        // it -- or the floating-point abstraction does, which refutes a
        // candidate the array checker has already accepted.
        if (!progress && !ext->hasPendingLemma() &&
            !(batchUFView->active() && batchUFAdapter->hasPendingLemma()) &&
            !(fpAbstractionActive && (fpAbstraction->hasPendingLemma() ||
                                      fpAbstraction->restartRequested())))
          FatalError("array-equality: an active refinement round has neither "
                     "a decision nor a pending theory lemma");
        if (ext->hasPendingLemma())
        {
          ext->encodePendingLemmas(NewSolver, satBase);
          progress = true;
        }
      }
      if (batchUFView->active() && batchUFAdapter->hasPendingLemma())
      {
        batchUFAdapter->encodePendingLemmas(NewSolver, satBase);
        progress = true;
      }
      // A floating-point release that is to be made by running the pipeline
      // again (FpAbstraction::restartRequested): this run is over, and
      // TopLevelSTP starts the next with the operation lowered exactly.
      if (fpAbstractionActive && fpAbstraction->restartRequested())
      {
        if (toSATAIG.cbIsDestructed())
          cleaner.release();
        reportBVAbstractionRecords();
        return SOLVER_UNDECIDED;
      }
      // A floating-point candidate the exact evaluator refuted: its value
      // lemma, shape lemma or exact release is pending, and is a
      // definitional fact about the operation, so it joins whatever else
      // this round installs.
      if (fpAbstractionActive && fpAbstraction->hasPendingLemma())
      {
        fpAbstraction->encodePendingLemmas(NewSolver, satBase);
        progress = true;
      }

      if (progress)
      {
        bm->checkPreparation(PreparationStage::Encoding);
        res = Ctr_Example->CallSAT_ResultCheck(
            NewSolver, bm->ASTTrue, semantic_input,
            submitted_counterexample_input,
            satBase, true
            , lraCoordinator.get()
            );
      }
      else
      {
        if (lraCoordinator != nullptr)
        {
          lraCoordinator->failClosed(
              "LRA coordinator reached refinement without a pending owner");
          return SOLVER_ERROR;
        }
        if (!arrayops)
          FatalError("refinement reached undecided without a pending "
                     "candidate-blocking lemma");
        res = Ctr_Example->SATBased_ArrayReadRefinement(
            NewSolver, semantic_input, satBase);
      }
    }

    while (lazyCongruenceRound())
    {
    }

    if (SOLVER_UNDECIDED != res)
    {
      if (ext != NULL)
        ext->reportLemmaStats();
      reportBVAbstractionRecords();
      CountersAndStats("print_func_stats", bm);
      return res;
    }

    if (bm->soft_timeout_expired)
    {
      reportBVAbstractionRecords();
      return bm->unknownResult();
    }

    if (!toSATAIG.hasBVEQAbstractions() && !toSATAIG.hasBVTermAbstractions() &&
        !extActive && !batchUFView->active() && !fpAbstractionActive)
    {
      if (lraCoordinator != nullptr)
        continue;
      break;
    }
  }

  FatalError("TopLevelSTPAux: reached the end without proper conclusion:"
             "a bug in STP");
  // bogus return to make the compiler shut up
  return SOLVER_ERROR;
}

} // end of namespace

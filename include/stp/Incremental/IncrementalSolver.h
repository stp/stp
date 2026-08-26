/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
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

#ifndef INCREMENTALSOLVER_H_
#define INCREMENTALSOLVER_H_

#include "stp/AST/AST.h"
#include "stp/Globals/Globals.h"
#include <cstdint>
#include <memory>

// The incremental solving driver; docs/incremental-solving.rst tells the
// full story.
//
// One SAT solver, one AIG, and one CNF encoding persist across ordinary
// checks within an encoding epoch.
// Everything encoded is a conservative extension -- fresh Tseitin variables
// and definitional clauses -- so it stays valid for that epoch; what changes
// between check-sats is only which root literals are asserted. A base-level
// (level 0)
// conjunct becomes a permanent unit clause; a conjunct at any pushed level
// has its root literal *assumed* per solve, so a pop retracts it by simply
// not assuming it any more. Learned clauses therefore survive both check-sats
// and pops by construction. A memory-relief rebuild rotates the complete
// semantic/AIG epoch and reconstructs only the live stack, bounding dead
// historical state; SAT-only policy rebuilds retain the AIG epoch.
// Whole-formula, satisfiability-only rewrites such as DISTINCT ordering also
// ride one assumed completed root. Their occurrence guards are re-evaluated
// against every active snapshot, so a later assertion retracts a symmetry
// choice without requiring clause deletion.
//
// The whole input language is covered -- plain bit-vectors, arrays (lazy
// refinement or --ackermanize), floating point, and --array-equality --
// canHandle() below is the seam should a future construct need excluding.

namespace stp
{

class STPMgr;
class AbsRefine_CounterExample;
class Simplifier;
class ArrayTransformer;

class IncrementalSolver
{
public:
  // `batchSimp` and `batchAT` are the batch pipeline's Simplifier and
  // ArrayTransformer -- the objects `ce` reads eliminated-variable
  // definitions and array read records from when it builds and checks
  // models. The driver seeds them from its own persistent stores
  // just-in-time (its substitutions at model construction, its read
  // registry around array work); the batch pipeline always clears both
  // (resetSolver) before using them itself.
  IncrementalSolver(STPMgr* bm, AbsRefine_CounterExample* ce,
                    Simplifier* batchSimp, ArrayTransformer* batchAT);
  ~IncrementalSolver();

  IncrementalSolver(const IncrementalSolver&) = delete;
  IncrementalSolver& operator=(const IncrementalSolver&) = delete;

  // Should a session that did NOT explicitly ask for the driver be using it
  // by now? One policy, for every frontend: the SMT-LIB2 reader and the C
  // API disagreed for as long as each carried its own copy, and the C API's
  // copy was a literal that `--incremental-auto-engage-at` could not reach,
  // so the documented override was inert for embedders.
  //
  // `configuredThreshold` is UserDefinedFlags::incremental_auto_engage_at:
  // negative selects the measured per-logic default, 0 disables automatic
  // engagement entirely, and N engages on the Nth real check. `solvesRun`
  // is how many real checks this session has already made, so the Nth check
  // asks with N-1. `delayedBvLogic` selects the longer default: pure
  // QF_BV/QF_ABV repay the driver's persistent encoding later than other
  // logics do, and a caller that cannot know its logic -- the C API has no
  // set-logic -- passes false and gets the shorter one.
  //
  // Explicit forcing (--incremental, vc_setFlags 'i') bypasses this
  // entirely; that is the caller's decision, not this policy's.
  static bool automaticEngagementReady(int64_t configuredThreshold,
                                       bool delayedBvLogic, size_t solvesRun);

  // Whether this solve is a forced FIRST engagement: the session explicitly
  // asked for the driver (--incremental, vc_setFlags 'i') AND has made no
  // real check yet. Four policies in the driver key on it -- a speculative
  // whole-stack block, a skipped constant-bit bootstrap, a pure-literal pass
  // over a base-only stack, and the scoped-preprocessing gate.
  //
  // Deliberately NOT derivable inside the driver as `engagedSolves == 0`.
  // That says only "this driver object has not solved before", which is also
  // true of the automatic path's first engaged solve -- and THAT solve has
  // had batch-preprocessed predecessors, so it must keep the search shape
  // they left. The difference is a session fact only a frontend can see, and
  // the three ways it comes apart are all reachable: resetAssertions()
  // destroys the driver without resetting the frontend's counter, the C API's
  // 'i' flag can arrive after batch queries have already run, and a
  // canHandle() refusal bumps the counter without engaging.
  //
  // `solvesRun` is checks already made, as above; the first check asks with 0.
  static bool forcedFirstSolve(bool forcedFromStart, size_t solvesRun);

  // Whether every assertion currently on the stack is inside the fragment
  // this driver encodes. Every construct the frontends can produce is
  // covered, so this answers TRUE today and exists as the seam should a
  // future one need excluding; it does no work and caches nothing.
  // `assertionsSMT2` is what Cpp_interface::checkSat receives: one
  // conjunction per assertion level, base level first.
  bool canHandle(const ASTVec& assertionsSMT2);

  // Solve the current stack: encode what is new, assume what is retractable,
  // and leave everything else in place for the next call. On sat, the
  // counterexample tables are populated exactly as the batch path would.
  //
  // With `assumeLastLevelPerConjunct` the LAST level's conjuncts are
  // assumed one root literal each instead of grouped under an activation
  // literal -- check-sat-assuming passes its assumptions as that level and
  // wants per-assumption failure granularity for get-unsat-assumptions.
  // `firstForcedIncrementalSolve` is set only by a frontend explicitly
  // forced incremental from its first real solve. It enables first-engagement
  // policies which automatic (third-solve) engagement does not need: an
  // oversized, initially empty cross-level propagation engine may be left
  // unbuilt until the next solve, and an exact-stack array block receives the
  // batch pipeline's cheap size-reducing prefix. A multi-level plain-BV stack
  // may use the same scoped block when the trial at least halves its DAG; a
  // base-only BV formula instead receives a one-time pure-literal pass before
  // any permanent clause exists.
  //
  // The parser's assertion stack remains canonical and is supplied as a
  // complete snapshot. The driver reconciles it into one versioned scope
  // ledger which owns stability, promotion, active preprocessing/model state
  // and independent processed-prefix cursors (CBP may not run on every
  // route). The assumption set is still recomputed from the snapshot against
  // permanent content-addressed encodings; no SAT clause deletion or frontend
  // push/pop hook is required. Base-level conjuncts become permanent units,
  // which is sound because reset/reset-assertions destroys this object.
  SOLVER_RETURN_TYPE checkSat(const ASTVec& assertionsSMT2,
                              bool assumeLastLevelPerConjunct = false,
                              bool firstForcedIncrementalSolve = false);

  // The unsat story of the most recent checkSat, valid until the next one.
  // hasAssumptionGranularity: the last level was assumed per conjunct and
  // the backend reported which assumptions failed -- then
  // lastUnsatAssumptionConjuncts() is the (possibly empty: the
  // unsatisfiability may not need the assumptions at all) subset of that
  // level's conjuncts in the core. Without granularity a caller must fall
  // back to reporting every assumption, which is always a correct core.
  // lastUnsatCoreLevels() is the set of pushed-level indices (into the
  // checkSat argument vector) whose assumed literals the refutation used;
  // an extensionality round is assumed as one block literal, so it
  // reports every level.
  bool lastSolveWasUnsat() const;
  bool lastUnsatHasAssumptionGranularity() const;
  std::vector<ASTNode> lastUnsatAssumptionConjuncts() const;
  std::vector<size_t> lastUnsatCoreLevels() const;

  // A sat answer defers counterexample construction unless something
  // reads the model at solve time: the SAT model stays live until the
  // next solve or clause addition, and the driver touches neither
  // between user commands. The model readers (get-value, get-model, the
  // C API's counterexample calls) call this first; answers nobody
  // samples never pay for construction. Idempotent and cheap when
  // nothing is pending.
  void materializePendingModel();

  // Test-only inspection: the (array, index) rows the last refinement-driven
  // check-sat seeded into the batch-side read table. The invariant under
  // test is that rows introduced by popped conjuncts never appear, however
  // many of them the persistent registry keeps: a popped row's defining
  // equations are guarded by a root literal that is no longer assumed, so
  // its SAT variables float, and one such row in the counterexample tables
  // makes the model checker reject every candidate.
  std::vector<std::pair<ASTNode, ASTNode>> seededReadsForTesting() const;

  struct EncodingEpochStats
  {
    uint64_t generation = 0;
    size_t aigAndNodes = 0;
    size_t rootEncodings = 0;
    size_t bitBlastedSymbols = 0;
    size_t semanticCacheEntries = 0;
  };

  // Test-only inspection of the resettable encoding store. A relief test
  // uses this to distinguish a real AIG/semantic rotation from a SAT-only
  // restart whose logically cleared vectors still retain their high-water
  // allocations.
  EncodingEpochStats encodingEpochStatsForTesting() const;

  // Public only so the ToSATBase adapter in the implementation file can
  // name it; the definition never leaves IncrementalSolver.cpp.
  struct Impl;

private:
  // The bodies of the two public entry points above, split out so that the
  // profile bracket and the pending-model latch enclose every path through
  // them -- both bodies return from many places.
  SOLVER_RETURN_TYPE checkSatBody(const ASTVec& assertionsSMT2,
                                  bool assumeLastLevelPerConjunct,
                                  bool firstForcedIncrementalSolve,
                                  const ASTNode& assumptionScopedRoot,
                                  size_t orderedDistincts);

  void buildPendingModel();

  // Latched by the first checkSat() of a session that set
  // UserDefinedFlags::aig_node_budget. The driver's AIG is persistent --
  // it outlives the check that grew it and is read again by every later
  // one -- so a check cannot walk away from a half-built encoding the way
  // the batch blaster can, and the cap is not enforced here. Say so once,
  // rather than letting a memory cap look as if it were in force.
  bool budgetNotEnforcedWarned = false;

  std::unique_ptr<Impl> impl;
};

} // namespace stp

#endif

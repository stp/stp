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

#ifndef INCREMENTALSOLVERIMPL_H_
#define INCREMENTALSOLVERIMPL_H_

// The incremental driver's private implementation header: the Impl
// state machine, the file-local helper classes it is built from, and
// the ToSATBase adapter the refinement machinery drives. Included only
// by the driver's own translation units (IncrementalSolver.cpp and the
// topic files beside it) -- nothing outside lib/Incremental may include
// it. One class, several files, exactly so the topic files can define
// Impl's route-specific methods next to their own concerns.

#include "stp/Incremental/IncrementalSolver.h"
#include "stp/ToSat/BVAbstractionRefiner.h"

#include "IncrementalLifetimeState.h"

#include "stp/Incremental/IncrementalCBP.h"
#include "stp/Incremental/IncrementalCnfEncoder.h"
#include "stp/Incremental/IncrementalPolicy.h"
#include "stp/Incremental/IncrementalProfile.h"
#include "stp/Incremental/IncrementalScopeState.h"
#include "stp/Incremental/IncrementalWalks.h"

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayReadRefinementProgress.h"
#include "stp/AbsRefineCounterExample/ArrayTransformer.h"
#include "stp/Simplifier/FindPureLiterals.h"
#include "stp/Simplifier/PropagateEqualities.h"
#include "stp/Simplifier/RemoveUnconstrained.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/FloatBlaster/FpEncodingContext.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/BitBlaster.h"
#include "stp/ToSat/ToSATBase.h"

#ifdef USE_MINISAT
#include "stp/Sat/MinisatCore.h"
#endif

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <limits>
#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace stp
{


// Narrow a configured limit to what an index type can hold. The clamp is
// vacuous where size_t is 64 bits wide and load-bearing where it is 32 --
// STP builds and tests an i386 leg -- so it goes through std::min rather
// than an explicit comparison that one of the two platforms can prove is
// always false.
inline size_t clampToSize(const uint64_t value)
{
  return static_cast<size_t>(
      std::min<uint64_t>(value, std::numeric_limits<size_t>::max()));
}


template <class Container> void releaseContainer(Container& container)
{
  Container empty;
  container.swap(empty);
}

// One resettable word-to-AIG encoding epoch. BitBlaster memo entries contain
// BBNodeAIG pointers owned by the manager, and the Simplifier is referenced by
// the blaster, so one object owns their lifetime and resets them in dependency
// order. Ordinary check-sats keep this object intact; only memory relief
// rotates it.
class AigEncodingEpoch
{
  STPMgr* bm;
  std::unique_ptr<SubstitutionMap> substitutionMap;
  std::unique_ptr<Simplifier> simplifier;
  std::unique_ptr<BBNodeManagerAIG> nodeManager;
  std::unique_ptr<BitBlaster> bitBlaster;

public:
  explicit AigEncodingEpoch(STPMgr* bm_) : bm(bm_) { reset(); }

  void reset()
  {
    bitBlaster.reset();
    nodeManager.reset();
    simplifier.reset();
    substitutionMap.reset();

    substitutionMap.reset(new SubstitutionMap(bm));
    simplifier.reset(new Simplifier(bm, substitutionMap.get()));
    nodeManager.reset(new BBNodeManagerAIG());
    bitBlaster.reset(new BitBlaster(nodeManager.get(), simplifier.get(),
                                    bm->defaultNodeFactory,
                                    &bm->UserFlags, NULL));
  }

  BBNodeManagerAIG& nodes() { return *nodeManager; }
  const BBNodeManagerAIG& nodes() const { return *nodeManager; }
  BitBlaster& blaster() { return *bitBlaster; }
  size_t aigAndNodes() const
  {
    return static_cast<size_t>(nodeManager->totalNumberOfNodes());
  }
};

// The one retraction mechanism is SAT assumptions, so the backend must
// support them. Plain MiniSat stands in for the ones that cannot: the
// simplifying MiniSat eliminates variables, and a later batch of definitional
// clauses may mention an eliminated variable again, which it cannot cope
// with -- the same reason cvc5 turns SatELite off under incremental solving.
inline SATSolver* makeBackend(UserDefinedFlags& uf, bool warn)
{
  SATSolver* s = NULL;
  if (uf.solver_to_use == UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER)
  {
    if (warn)
      std::cerr << "Warning: the simplifying MiniSat cannot retract "
                   "assumptions safely; incremental solving uses plain "
                   "MiniSat instead."
                << std::endl;
#ifdef USE_MINISAT
    s = new MinisatCore;
#else
    // Let the central factory issue its standard, precise diagnostic for a
    // solver that was not compiled in.
    return createSATSolver(uf);
#endif
  }
  else
    s = createSATSolver(uf);

  if (!s->supportsAssumptions())
  {
    delete s;
    std::cerr << "ERROR: the selected SAT backend does not support "
                 "incremental assumptions"
              << std::endl;
    exit(-1);
  }

  // Match the batch solver's configuration. Some backends only accept the
  // bias while they are still empty, so it belongs here for both the initial
  // solver and every relief rebuild. Warn once for the session, not once per
  // rebuild.
  applySearchBias(*s, uf, warn);
  return s;
}

typedef std::unordered_map<ASTNode, int, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    NodeToLitMap;

// What the driver knows about a conjunct's content: whether its source DAG
// contains array operations, whether its prepared form contains them (which
// decides the refinement machinery), whether it touches floating point
// (which decides totalisation and lowering), and whether it carries an opaque
// whole-array equality (which routes the entire check-sat through the
// extensionality block). All node-local, permanent properties.
struct Fragment
{
  bool sourceArrays;
  bool arrays;
  bool fp;
  bool arrayEq;
};
typedef std::unordered_map<ASTNode, Fragment, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    NodeToFragmentMap;

// Split a level's conjunction into its top-level conjuncts. The level node
// is rebuilt (and re-simplified) by the node factory on every check-sat, so
// the split set -- not the node -- is the stable notion of the level's
// content.
//
// Nested ANDs are as deep as the input makes them -- a chain of define-funs
// inlined at parse time reaches tens of thousands of levels -- so the walk
// keeps its position on the heap rather than on the call stack.
inline void splitConjuncts(const ASTNode& n, const ASTNode& trueNode, ASTVec& out)
{
  ASTVec pending(1, n);
  while (!pending.empty())
  {
    const ASTNode cur = pending.back();
    pending.pop_back();

    if (cur == trueNode)
      continue;

    if (cur.GetKind() == AND)
    {
      // Pushed in reverse so they come back off in the order the recursion
      // visited them. `out` is the conjunct list a level is encoded and
      // assumed in, and a level's content must not depend on how this walk
      // is organised.
      for (size_t i = cur.Degree(); i > 0; i--)
        pending.push_back(cur[i - 1]);
      continue;
    }

    out.push_back(cur);
  }
}

struct IncrementalSolver::Impl
{
  enum class RebuildReason
  {
    Relief,
    Promotion,
    Inprobing,
    Trail
  };

  // The per-check and running-session measurement records; the structs,
  // the scoped timer filling their duration fields, and the report
  // printer live in IncrementalProfile.{h,cpp}.
  typedef IncrementalCheckProfile CheckProfile;
  typedef IncrementalSessionProfile SessionProfile;

  STPMgr* bm;
  AbsRefine_CounterExample* ce;
  Simplifier* batchSimp;
  ArrayTransformer* batchAT;

  // The single owner of current scope identity, semantic transactions,
  // promotion state and preprocessing-consumer cursors. Content-addressed
  // encoding caches remain below; whether their roots participate in this
  // check belongs here.
  IncrementalScopeState scopes;

  // Optional, fitted performance decisions are read only through this
  // profile. The persistent assumption/refinement mechanism and resource
  // epoch rotation do not depend on them.
  const IncrementalPolicy policy;

  std::unique_ptr<SATSolver> solver;

  // The bit-blaster wants a Simplifier; give it an inert one of its own, as
  // ToSATAIG::bitblast does, so no batch-pipeline substitution state can
  // leak into the persistent encoding.
  AigEncodingEpoch encoding;

  // The DAG-walk utilities and their epoch-scoped memos (per-node symbol
  // sets, capped size counts); see IncrementalWalks.h. Thin forwarders
  // below keep the call sites reading as they always have.
  IncrementalWalks walks;

  // The incremental Tseitin encoder over the persistent solver; owns the
  // AIG-to-variable table and the shared TRUE variable
  // (IncrementalCnfEncoder.h). Thin forwarders below keep call sites
  // unchanged; its binding generation is what validates the adapter's
  // cached symbol map.
  IncrementalCnfEncoder cnf;

  // ── Bit-vector abstraction: --bv-eq-abstraction, --bv-term-abstraction ──
  //
  // The persistent bit-blaster abstracts on this route exactly as the batch
  // lowering does, which leaves this route owing the same CEGAR loop: an
  // abstracted equality or operation is a free input, so a candidate is an
  // assignment of the stack only once every abstraction in it has been
  // checked against the operands underneath and, where they disagree,
  // pinned. Without an owner the checks never happened, and models that
  // falsify an asserted formula, and downstream theory checkers reading
  // values no equation ever constrained, both followed.
  //
  // Nothing this adds is retractable, and nothing needs to be. Every clause
  // it emits -- the operand proxies' defining biconditionals and the pinning
  // lemmas alike -- says only what a variable means in terms of AIG bits the
  // encoding already carries, which holds under any set of assumptions.
  BVAbstractionRefiner bvAbstraction;

  // How much of the blaster's growing state has been taken across. Reset
  // together with the SAT backend: a fresh solver holds none of the clauses
  // these produced, and none of the variables they were written over, so the
  // records have to be harvested and refined again from nothing.
  size_t harvestedEQAbstractions = 0;
  size_t harvestedTermAbstractions = 0;
  size_t assertedSideConstraints = 0;

  // conjunct -> root literal (2*var + sign). Epoch-persistent: the encoding
  // of a formula is a definition, valid in every context using this AIG/SAT
  // epoch.
  NodeToLitMap rootLitOf;

  // conjunct -> fragment facts. Node-local properties cached for this
  // encoding epoch; relief drops dead node keys as well as their circuits.
  NodeToFragmentMap fragmentCache;

  // The read registry, persistent across ordinary check-sats in an encoding
  // epoch: array -> index ->
  // ArrayRead, exactly the batch ArrayTransformer's table. The transformer
  // consults it before minting an abstraction variable, so seeding it from
  // here before every transform gives one canonical read symbol per
  // (array, index) for that epoch -- which is what makes refinement axioms
  // (congruence over those symbols) valid permanent clauses in its SAT
  // instances. A relief rotation discards registry and clauses together.
  // Entries from popped scopes stay: their axioms are tautologies of the
  // abstraction, so clauses already learned over them remain valid. They
  // are NOT harmless everywhere, though -- their defining equations were
  // encoded under root literals that are no longer assumed, so their SAT
  // variables float, and seedActiveReads below must keep them out of the
  // per-solve batch tables.
  //
  // Under --ackermanize the registry also carries the reads of each array in
  // encounter order. That new-versus-existing shape is monotone, so
  // persisting the list keeps pair coverage across check-sats: any two reads
  // are related by whichever was encoded later. A popped read remains a sound
  // unconstrained observation of the array.
  ArrayTransformer::Registry arrayRegistry;

  // The (array, index) reads each ENCODING contains, keyed exactly as
  // rootLitOf is -- the raw conjunct on the ordinary path, the rewritten
  // node on the pushed-definitions path -- so per-solve batch tables can
  // be restricted to the reads of the encodings actually assumed this
  // round. (Keying by the raw conjunct would go quietly wrong under
  // pushed definitions: different conjuncts, or one conjunct under
  // different rounds' definitions, can share one rewritten-node entry
  // whose encode never re-runs, and a rewrite that touches an index
  // expression mints a different registry row for the same syntactic
  // read.) Reads of popped encodings have unconstrained anchor/value SAT
  // variables -- their defining equations are guarded by root literals no
  // longer assumed -- and one such row in the counterexample tables
  // shadows an active cell with a floating value, makes the checker
  // reject every candidate, and refinement cannot converge.
  std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>> readsOfEncoded;

  IncrementalSymbolMapCache symbolMapCache;

  // Constructed on first array use (its class is defined below Impl).
  std::unique_ptr<ToSATBase> adapter;

  // Created on first floating-point use; see fpContext().
  std::unique_ptr<FpEncodingContext> fpCtx;

  // Nodes the block cache's determinism depends on. STP garbage-collects
  // unreferenced interior nodes and re-mints their numbers, and the
  // deterministic generated names are keyed on node numbers -- so every
  // stage of a round's spine (raw conjunction, prepared, lowered) is
  // pinned here. Without this, an identical re-pushed stack rebuilds the
  // freed spine under fresh numbers and the whole chain diverges.
  // (The per-conjunct caches never had the problem: their keys hold their
  // nodes by construction.)
  ASTNodeSet exactStackKeepAlive;

  // The exact-stack block cache needs one stable encoding policy per raw
  // active conjunction. Array-equality rounds revisit this map: automatic
  // engagement keeps its first stack raw and preprocesses genuinely new
  // stacks. Explicit first engagement preprocesses immediately. The
  // first-check BV escape below only lands here after its preprocessing trial
  // has collapsed enough to be accepted. Re-visiting any stored stack must
  // keep the same transformed root, refinement lemmas and learned clauses.
  std::map<ASTNode, bool> exactScopedPreprocessOf;

  // Base-level conjuncts already asserted as permanent units.
  ASTNodeSet level0Asserted;

  // ---- Per-conjunct preparation with guarded elimination ----
  //
  // Each pushed conjunct is prepared -- substituted under the context of
  // the base store and the definitions below and before it, then run
  // through the batch equality-propagation and simplification passes --
  // and definitions the propagator harvests fall into two classes. A
  // variable PRIVATE to the conjunct's level -- mentioned by no base
  // conjunct, no other live level, no already-prepared conjunct of its
  // own level, and never bit-blasted -- is genuinely eliminated: its
  // definition leaves the formula, is recorded here, and is replayed
  // into the model channel whenever a model is built while the level is
  // live. Later conjuncts of the same level are safe by construction:
  // the definition joins the context, so their uses are substituted
  // away. Everything else keeps the old semantics: the definition is
  // re-conjoined, so a shared or already-encoded variable's equation is
  // never lost (the freeze rule).
  //
  // The elimination is guarded against the future by screening: before
  // anything is prepared or encoded, every piece of never-seen raw
  // content has its symbols checked against the variables that live
  // cache entries eliminated, and a mention invalidates those entries --
  // they re-prepare with the variable now shared, re-conjoining its
  // definition. Stale encodings of a dropped entry's conjuncts stay in
  // rootLitOf, which is sound: an encoding is a definition of its
  // formula, valid forever; only the conjunct-to-formula mapping
  // changes.
  typedef PreprocessingTransaction PreparedPiece;
  // Keyed by the context-substituted conjunct (the T1 discipline: the
  // key is the rewritten node, so the same conjunct under different live
  // definitions prepares separately and a re-pushed stack hits).
  std::map<ASTNode, PreparedPiece> preparedPieceOf;

  // var -> cache keys of entries that eliminated it, for screening.
  std::map<ASTNode, std::vector<ASTNode>> eliminationUsers;

  // Raw content whose symbols have already been screened.
  ASTNodeSet screenedContent;

  // Symbols of every base-level conjunct ever asserted; grown as the
  // base grows, consulted by the privacy check.
  ASTNodeSet baseSymbols;


  // Keys this driver has seeded into the batch Simplifier's SolverMap
  // (the model-evaluation channel), so the next solve can withdraw them.
  ASTNodeSet seededModelKeys;

  // Base-level definitions eliminated by the rebuild-boundary global
  // pass. The base is permanent, so these are permanent too: seeded into
  // the model channel every solve, and restored the moment any later
  // content mentions their variable (see screenNewContent). What
  // restoration means depends on provenance. An equation the propagator
  // harvested is IMPLIED by the base, so the equation itself returns. A
  // definition the unconstrained-variable pass recorded is only a
  // WITNESS -- a value chosen to satisfy the dropped constraint, in no
  // way implied -- so asserting it would wrongly pin the variable
  // against whatever the new content wants; the original raw conjuncts
  // that mentioned the variable return instead (complete, because a
  // variable eliminated as unconstrained occurred in exactly one).
  typedef ScopedElimination BaseElimination;
  std::map<ASTNode, BaseElimination> baseEliminatedDefs;

  // Witness originals can be shared by several eliminated variables. The
  // first later mention recursively restores all of them, so remember which
  // roots this backend epoch has already asserted rather than submitting the
  // same permanent unit once per variable.
  ASTNodeSet restoredBaseRoots;

  // The re-simplified base conjuncts a rebuild produced, awaiting
  // encoding: the rebuild itself must not add clauses, because the fresh
  // backend's configuration window (bounded variable addition) has to be
  // decided first.
  ASTVec pendingRebuiltBase;

  // Newly submitted structural clauses, owned by the formula key whose
  // encoding first introduced them. The retained total comes directly from
  // SATSolver::submittedClauses(); ownership says which part of that total a
  // live assertion stack would need after a rebuild.
  std::map<ASTNode, uint64_t> clauseMassOf;

  // Theory clauses are globally valid within an encoding epoch -- the read
  // registry is canonical there, so a congruence axiom over its symbols stays
  // true for every later stack in the epoch -- but counting them live forever
  // would hide refinement-heavy dead growth from the relief valve. They are
  // charged instead to the solve that emitted them, keyed by that solve's
  // whole-stack conjunction. A relief rotation discards registry and clauses
  // together.
  //
  // Be clear about what that policy actually does, because it is not the
  // middle ground it reads as. The key is the entire live stack, so ANY change
  // to it -- one push of an unrelated level -- yields a fresh key whose mass is
  // zero, and every lemma ever emitted stops counting at once. Mass survives
  // only for a bit-identical repeated stack. So the two cases are "repeat the
  // same query" and "drop it all", with nothing in between, and a session that
  // refines while its stack moves measures its own live mass short by the
  // whole refinement total.
  //
  // Measured, on a 250-level read-heavy QF_ABV churn session forced to the
  // valve (--incremental-reencode-limit 8000, 125x tighter than the default):
  // this costs exactly one relief rebuild that the true live mass would not
  // have permitted, and 646 of 6800 refinement clauses re-derived after it.
  // Total time is a wash across three interleaved pairs -- the rebuild
  // compacts what it discards. Counting the lemmas permanently live instead
  // removes the rebuild and then never relieves at all on that session, which
  // is the failure this policy exists to prevent. Attributing mass to the live
  // read rows is the fix that would be right, and it needs always-on per-row
  // clause accounting: the only per-row liveness that exists today is a
  // profiling counter, and feeding that into the valve is precisely the
  // profiler-changes-the-schedule defect fixed in 635b3b04. Left as it is,
  // deliberately, with the cost stated rather than the behaviour misdescribed.
  //
  // One entry per distinct stack solved since the last rebuild, and each pins
  // its conjunction node: the map grows with the session's shape, not its
  // depth. Bounding it would change the repeated-query policy above, so it is
  // a known cost, not an oversight.
  std::map<ASTNode, uint64_t> refinementMassOf;
  // Refinement clauses currently carried by the backend. Unlike the optional
  // profiling counters this is always maintained: the late-FP trail policy
  // uses it to avoid throwing away a substantial refined search state.
  uint64_t currentRefinementClauseMass = 0;

  // The actual AIG root encoded under each formula key. Newly submitted
  // clause deltas are a cheap live-mass estimate, but not an exact one: a
  // current root can reuse a large cone first introduced by a now-popped key.
  // Retain the roots and lazily walk their unique live cone only when the
  // cheap estimate would otherwise permit relief. Only the most recent solve
  // is retained: it is the one a false rebuild on a persistent live stack
  // must protect, while keeping every growing root vector would itself take
  // quadratic memory. Popped historical content should not prevent relief.
  std::map<ASTNode, Aig_Obj_t*> aigRootOf;
  IncrementalPendingLiveCone pendingLiveCone;

  // Permanent-for-this-backend-epoch mass: base root units and definitions,
  // plus promoted units. A promoted level's retraction forces a rebuild, so
  // its units really are live until the epoch ends.
  uint64_t baseLiveMass = 0;
  // Roots and unit clauses which are permanent in this backend epoch. Keeping
  // the roots separate lets the lazy exact walk take their structural union
  // with the current assumed roots rather than either missing shared clauses
  // or counting shared clauses twice.
  std::vector<Aig_Obj_t*> permanentAigRoots;
  uint64_t permanentUnitMass = 0;
  // Activation implications are live only while their activation literal is
  // assumed. Retired implications and their false pins deliberately remain
  // outside this map and therefore count as reclaimable dead mass.
  std::unordered_map<int, uint64_t> activationMassOf;

  uint64_t currentLiveClauseMass = 0;
  // The largest live mass any solve has used since the last rebuild:
  // the valve's denominator. Comparing against the PEAK working set --
  // not the last solve's, which may be momentarily tiny -- gives the
  // trigger hysteresis: after a rebuild the tracked mass starts at
  // roughly the working set, so the next fire needs 4x growth again.
  uint64_t maxLiveClauseMass = 0;

  // AST roots deliberately pinned by semantic caches in this encoding epoch.
  // The running charge is an inexpensive, conservative sum of per-root DAG
  // sizes; once it reaches the configured floor, semanticReliefReached()
  // walks the exact retained and live unions before authorizing rotation.
  IncrementalSemanticEpochAccounting semanticEpoch;

  // Probe-based inprocessing retirement (see the trigger in
  // checkSatBody): how many solves this driver has run, and
  // whether the persistent solver now runs with inprobing off.
  size_t engagedSolves = 0;
  bool inprobingRetired = false;
  // Few-solve sessions profit from inprobing (they are one big search);
  // many-solve sessions over a FIXED base pay its whole-encoding re-runs
  // at every solve. A growing permanent base gives inprocessing genuinely
  // new work and can depend on its elimination to prove later queries, so
  // AUTO also waits for level zero to be stable throughout this window.
  // The measured fixed-base corpora split cleanly: the hurt class has 1-2
  // solves, the win class 20+.
  static const size_t inprobingRetireSolves = 8;
  // ... and only when the encoding is big enough for inprobing to cost
  // anything: retirement pays a rebuild, and on a small solver that is
  // pure overhead (a ten-millisecond session measured 10x slower from a
  // rebuild whose savings were nothing). The winning sessions retire
  // with fifty thousand variables and up.
  static const unsigned long inprobingRetireMinVars = 20000;

  // Definitions with replacements larger than this are never inlined:
  // they stay asserted equations, and their variable keeps the sharing.
  static const size_t defInlineCap = 200;

  // Formulas over this size skip the whole-level grouping AND the
  // equality-propagation pass: on the deep define-fun chains PE's
  // rewriting explodes the shared DAG (measured ten million clauses out
  // of seven conjuncts), while the plain simplifier has always handled
  // them.
  static const size_t bigFormulaCap = 20000;

  // A tiny exact-stack block cannot create the clause cliffs this first-solve
  // escape targets, while changing its assumption/search shape costs visible
  // milliseconds across the corpus's smallest queries. Keep those on the
  // ordinary per-level path even if a toy formula happens to halve.
  static const size_t firstStackCollapseMinNodes = 128;
  static const int64_t firstStackMinReencodeLimit = 1000000;

  // DAG node count up to `cap`; used to pick the preparation granularity.
  static size_t dagSizeUpTo(const ASTNode& n, size_t cap)
  {
    return IncrementalWalks::dagSizeUpTo(n, cap);
  }

  // The memoised variant against the epoch-scoped big-formula memo; the
  // rationale for memoising lives with the memo (IncrementalWalks.h).
  size_t dagSizeUpToBigMemo(const ASTNode& n, size_t cap)
  {
    return walks.dagSizeUpToBigMemo(n, cap);
  }

  size_t semanticCacheLimit() const
  {
    const int64_t configured =
        bm->UserFlags.incremental_semantic_cache_limit;
    if (configured <= 0)
      return 0;
    return clampToSize(static_cast<uint64_t>(configured));
  }

  void chargeSemanticRoot(const ASTNode& root)
  {
    semanticEpoch.charge(root, semanticCacheLimit());
  }

  void stageSemanticLiveStack(const ASTVec& rawStack,
                              const ASTVec& encodedRoots)
  {
    semanticEpoch.stage(rawStack, encodedRoots);
  }

  bool semanticReliefReached()
  {
    return semanticEpoch.reliefReached(semanticCacheLimit());
  }

  // CBP's cost follows the sum of the level DAGs it feeds (a shared node in
  // two levels is deliberately visited twice by the scoped engine). Bound
  // the estimate itself by the policy limit: as soon as the next level
  // crosses it, finishing that walk cannot change the decision.
  bool cbpStackExceeds(const ASTVec& levels, size_t limit)
  {
    size_t total = 0;
    for (const ASTNode& level : levels)
    {
      const size_t remaining = limit - total;
      const size_t nodes = dagSizeUpTo(level, remaining);
      if (nodes > remaining)
        return true;
      total += nodes;
    }
    return false;
  }

  // ── Session-persistent constant-bit propagation over the live prefix ──
  //
  // One IncrementalCBP persists across stack changes. Divergence rolls its
  // engine and caller overlay back to the longest common prefix (see Cross-call
  // reuse below); reset/re-feed remains available as a diagnostic oracle. It
  // is fed each live level's RAW word-level conjunction in stack order, each
  // level's conjunction assumed true while that prefix is active. Facts
  // discovered while feeding level L depend only on levels <= L --
  // the pushed-definition context's prefix discipline, for the same
  // reason: rewritten forms stay stable as the stack grows
  // underneath, and a fact can never outlive a level it was drawn
  // from. Adoption happens BEFORE piece preparation, keying and the
  // array transform: the adopted form flows into the piece machinery
  // content-keyed like any other conjunct (a different stack derives
  // a different form, so a stale strengthened encoding is unreachable
  // by construction), and the transformer and read registry see
  // folded indices exactly the way pushed-definition folds have
  // always reached them. This is what per-level preparation is
  // structurally blind to: a read whose write-chain indices are fixed
  // by ANOTHER level's content only collapses when the fixings cross
  // the levels (the Industrial_Control_C family: ite(flag,c1,c2)
  // write indices whose flags other levels pin, chaseRead stopping at
  // every maybe-equal index, and the transformer expanding the
  // surviving chains quadratically).
  std::unique_ptr<IncrementalCBP> callCbp;
  // node -> constant, accumulated across the fed levels. EXTRACT
  // and CONCAT never enter it: their total fixing can rest on a
  // PARTIALLY fixed operand, so no total pinning fact exists to
  // justify replacing them. Nothing carrying an array operation
  // enters either: reads and writes belong to the read registry, and
  // a substituted-away read leaves its rows behind with no encoded
  // anchor (the target family's indices are ite(flag,const,const) --
  // array-free -- so the exclusion costs it nothing).
  ASTNodeMap callCbpSubst;
  // Fixings of THIS level's own fed conjuncts, parked while the level
  // rewrites (level-granularity slot protection, see cbpFeedLevel)
  // and restored for deeper levels by cbpFinishLevel.
  std::vector<std::pair<ASTNode, ASTNode>> callCbpDeferred;
  // Which substitution-domain nodes' pinning facts are already
  // appended this call, and which nodes are fed conjuncts (their own
  // levels assert them; no fact needed).
  ASTNodeSet callCbpFactEmitted;
  ASTNodeSet callCbpFedConjuncts;
  size_t callCbpFed = 0;
  size_t callCbpAdopted = 0;
  size_t callCbpReplayed = 0;
  size_t cbpEpochAdopted = 0;
  size_t cbpBarrenDivergences = 0;
  bool cbpEverFixed = false;

  // Whether the engine has ever DERIVED a fixing, as opposed to recording the
  // truth of a conjunct that was fed to it.
  //
  // Every fed level is asserted, so its conjunction and each of its top-level
  // conjuncts are fixed to TRUE by assumption alone -- and a Boolean symbol
  // asserted bare is both a fed conjunct and a symbol. Counting those made the
  // flag true after the first array-free feed, before the engine had derived
  // anything, which inverted the retirement tiers: the short leash for a
  // session whose fixing map stays empty became unreachable for exactly the
  // pop-per-query sessions it was measured on, and they served out the long
  // one instead.
  void noteEngineDerivedFixing(const ASTNode& n)
  {
    if (callCbpFedConjuncts.find(n) == callCbpFedConjuncts.end())
      cbpEverFixed = true;
  }
  bool cbpFedArrays = false;
  bool callCbpOff = false;
  bool callCbpConflict = false;
  // A session that ever overflows the feed cap stops paying for the
  // prepass at all: repeatedly inspecting and feeding replacement
  // suffixes near that cap is a steady tax on deep hundred-solve
  // sessions with nothing adopted to show for it. The same retirement
  // fires on evidence of futility: a session whose stack keeps
  // diverging with no adoption to show for its suffix propagation is
  // the KLEE-class pop-per-query shape,
  // where the prefix never stabilises and the fixings never come.
  // The evidence is per-tier, because adoption timing says little on
  // its own (measured: the Industrial specimen's first adoption is
  // near solve 115, after ~20 divergences, and those four late folds
  // are the entire 40x -- while the KLEE-class b64 diverges 997
  // times with the fixing map EMPTY at every single one). A session
  // whose engine has NEVER derived one fixing retires after a short
  // barren run; a session with fixings but no adoption yet gets a
  // leash long enough that a pop-bounded session cannot exhaust it.
  bool cbpSessionRetired = false;
  // Refusing a level for want of capacity is NOT that judgement. The cap
  // measures the live stack, and the charge against it is refunded when a
  // level pops (cbpRollbackCallerTo), so a retirement keyed on it must be
  // refunded too: otherwise one deep excursion turns the pass off for a
  // session that spends the rest of its life at depth two. Latched at the
  // fed-level count that was refused, and released once the stack falls
  // back below it.
  static const size_t noFeedCapRefusal = std::numeric_limits<size_t>::max();
  size_t cbpOverFeedCapAt = noFeedCapRefusal;
  bool cbpOverFeedCap() const { return cbpOverFeedCapAt != noFeedCapRefusal; }
  static const size_t cbpRetireBarrenNeverFixed = 8;
  static const size_t cbpRetireBarrenFixed = 64;
  // The substitution stays small: it exists for the cross-level few
  // (the target family's whole map is 48 entries), and a giant
  // constant-rich feed can legitimately fix a hundred thousand nodes
  // whose folding the pieces' own passes already perform. Harvesting
  // stops at the cap; what is left unharvested costs folds, never
  // soundness.
  static const size_t cbpHarvestCap = 4096;
  // The engine's fed content is bounded; raw word-level stacks are
  // parse-folded and small (the target family's whole stack is under
  // five thousand nodes), so a stack past this size is the deep
  // KLEE-class session the cap exists to protect. What is charged against
  // it is what the engine RETAINS for the live stack -- see cbpFeedLevel.
  size_t cbpFeedCap() const
  {
    const int64_t configured = bm->UserFlags.incremental_cbp_feed_cap;
    return configured < 1 ? 1 : static_cast<size_t>(configured);
  }

  // ── Cross-call reuse ──────────────────────────────────────────────
  //
  // The engine state after feeding levels 0..L is a pure function of
  // those levels' conjunctions. A divergence (a pop, a changed level, or
  // base growth) rolls the engine and its caller-side semantic overlay back
  // to the longest common prefix, then feeds only the replacement suffix.
  // Rewrites are memoised by the scope ledger with one stronger property: an
  // entry records outputs as derived at BUILD time, when the accumulated
  // substitution held exactly the entry's own prefix. Replaying under a
  // deeper stack can therefore never leak a deeper fact upward. Keeping that
  // memo beside scope identity also means CBP is no longer a second owner of
  // the assertion stack.

  struct CbpSubstUndo
  {
    ASTNode key;
    ASTNode oldValue;
    bool existed;

    CbpSubstUndo(const ASTNode& key_, const ASTNode& oldValue_, bool existed_)
        : key(key_), oldValue(oldValue_), existed(existed_)
    {
    }
  };

  struct CbpCallerCheckpoint
  {
    size_t substUndo;
    size_t fedConjunctsAdded;
    size_t factsAdded;
    size_t fedBefore;
    bool fedArraysBefore;
    // Trailed for completeness: feedLevel latches both, so an undo of that
    // feed owes their restoration. The one call site happens to reassign them
    // immediately afterwards, which makes the restore unobservable today --
    // but a trail that only covers the state whose restoration is currently
    // load-bearing is a trap for the next caller.
    bool offBefore;
    bool conflictBefore;
  };

  // Caller-side undo payload parallels the CBP consumer cursor owned by
  // `scopes`. The semantic identity and memo live there; only mechanics of
  // undoing this implementation's maps remain here.
  std::vector<CbpCallerCheckpoint> cbpCallerCheckpoints;
  std::vector<CbpSubstUndo> cbpSubstUndo;
  std::vector<ASTNode> cbpFedConjunctsAdded;
  std::vector<ASTNode> cbpFactsAdded;
  ASTNodeSet cbpSubstTrailedThisLevel;
  bool cbpCallerLevelOpen = false;
  // Levels below this replay their memo this call (set at call
  // start): their prefix is unchanged, so their recorded outputs are
  // exactly what recomputation would derive.
  size_t cbpMemoStable = 0;

  void cbpBeginCallerLevel(size_t fedBefore);

  void cbpTrailSubstitution(const ASTNode& key);

  void cbpAssignSubstitution(const ASTNode& key, const ASTNode& value);

  void cbpEraseSubstitution(const ASTNode& key);

  void cbpInsertFedConjunct(const ASTNode& node);

  bool cbpInsertFactDomain(const ASTNode& node);

  size_t cbpRollbackCallerTo(size_t levels);

  void cbpReset();

  // Budget-bounded containment probe; the harvest's rationale for the
  // bound lives with the walk (IncrementalWalks.h).
  static bool reachesAnyOf(const ASTNode& n, const ASTNodeSet& syms)
  {
    return IncrementalWalks::reachesAnyOf(n, syms);
  }

  // Feed one live level's raw conjunction to the engine and collect
  // the newly fixed nodes into the substitution. An already-fed level
  // (the stable prefix of a persisting session) is a no-op: its
  // fixings are in the map and its rewrites replay from the memo. The
  // level's own fed conjuncts' fixings are DEFERRED until
  // cbpFinishLevel: a conjunct must never rewrite under its own
  // assumption-of-truth (substituting a fed conjunct's TRUE into its
  // own slot erases the constraint -- the circularity measured as a
  // refinement livelock the moment it was admitted), and parking the
  // whole level's entries keeps every sibling rewrite safe too.
  // Occurrences inside DEEPER levels' conjuncts still fold, justified
  // without a pinning fact by the fed conjunct's own asserted slot.
  void cbpFeedLevel(size_t level, const ASTNode& levelConjunction);

  // Restore the fed-conjunct fixings cbpFeedLevel parked, once the
  // level's own conjuncts are past rewriting.
  void cbpFinishLevel();

  // Rewrite one conjunct under the constants accumulated from levels
  // <= its own. Adoption follows the trial policy's spirit: constant
  // folds only ever shrink (the substitution replaces a subterm by a
  // leaf), so any strict shrink is admitted; a same-size or grown
  // result means the factory rewrote the spine into a novel shape on
  // the way -- the shuffle class the trial gates exist to refuse --
  // and the conjunct keeps its raw-keyed form and all the sharing
  // that comes with it. Every replaced node's pinning fact (node ==
  // constant; the node itself or its negation for Booleans) is
  // collected into factsOut and asserted alongside this level's
  // conjuncts, so the substitution loses nothing and the models the
  // refinement loop validates stay models of the raw stack. Fed
  // conjuncts are exempt: their own levels assert them for at least
  // as long as any adopter lives.
  ASTNode cbpAdopt(const ASTNode& conjunct,
                   std::vector<ScopedFact>& factsOut);

  // Every floating-point OPERATION node of `n` (kind-categorised FP, so
  // constants and plain carriers stay out), for the substitution gate
  // below.
  void collectFpOperations(const ASTNode& n, ASTNodeSet& out)
  {
    ASTNodeSet visited;
    std::vector<ASTNode> pending(1, n);
    while (!pending.empty())
    {
      const ASTNode cur = pending.back();
      pending.pop_back();
      if (!visited.insert(cur).second)
        continue;
      if (is_FP_kind(cur.GetKind()))
        out.insert(cur);
      for (unsigned i = 0; i < cur.Degree(); i++)
        pending.push_back(cur[i]);
    }
  }

  // Would adopting `substituted` in place of `original` hand the blaster a
  // floating-point operation it has not seen in the original -- a NOVEL
  // VARIANT of a circuit rather than a fold? Substituting into a
  // floating-point operation's arguments rebuilds the whole symfpu
  // circuit for the new argument syntax: thousands of clauses that
  // duplicate an operation the raw-keyed encodings already carry, and
  // the search must then re-derive their equivalence bit by bit through
  // both copies (a family of generated variant-push queries measured
  // 0.3s raw against a deterministic 45s-to-timeout with the variants).
  // A substitution that FOLDS an operation away -- the floating-point-
  // computed array index collapsing to a constant, which is what the
  // floating-point harvest exists for -- removes FP nodes and introduces
  // none, and passes this gate untouched.
  bool introducesNovelFpOperations(const ASTNode& original,
                                   const ASTNode& substituted)
  {
    if (substituted == original || !bm->has_floating_point_theory)
      return false;
    if (!containsFloatingPointTheory(substituted, bm))
      return false;
    ASTNodeSet originalOps;
    collectFpOperations(original, originalOps);
    ASTNodeSet substitutedOps;
    collectFpOperations(substituted, substitutedOps);
    for (const ASTNode& op : substitutedOps)
      if (originalOps.find(op) == originalOps.end())
        return true;
    return false;
  }

  // Per-node symbol sets (epoch-memoised) and the multi-root union walk;
  // both live in IncrementalWalks.h with their machinery.
  const ASTNodeSet& symbolsOf(const ASTNode& n) { return walks.symbolsOf(n); }

  void addSymbolsOf(const ASTVec& roots, ASTNodeSet& out)
  {
    walks.addSymbolsOf(roots, out);
  }

  // Screen a piece of raw content that has never been seen: any symbol it
  // mentions that some cached entry eliminated invalidates that entry.
  void screenNewContent(const ASTNode& raw)
  {
    if (!screenedContent.insert(raw).second)
    {
      if (profile.enabled)
        profile.screenCached++;
      return;
    }
    if (profile.enabled)
      profile.screenNew++;
    if (eliminationUsers.empty() && baseEliminatedDefs.empty())
      return;
    for (const ASTNode& s : symbolsOf(raw))
    {
      std::map<ASTNode, std::vector<ASTNode>>::iterator it =
          eliminationUsers.find(s);
      if (it != eliminationUsers.end())
      {
        const std::vector<ASTNode> keys = it->second;
        for (const ASTNode& key : keys)
          dropPreparedLevel(key);
      }
      // A permanently eliminated base variable that new content mentions
      // gets its constraint back as permanent units -- the base only
      // grows, so re-conjoining later is sound -- and leaves the replay
      // set, so its value comes from its bits again. An implied equation
      // returns as itself; a witness definition must NOT be asserted
      // (it would pin the variable to one chosen value), so the original
      // conjuncts that mentioned the variable return instead. The
      // restored content is screened first: it may mention OTHER
      // eliminated variables, whose constraints must return with it or
      // the restoration would be weaker than the original.
      std::map<ASTNode, BaseElimination>::iterator bit =
          baseEliminatedDefs.find(s);
      if (bit != baseEliminatedDefs.end())
      {
        ASTVec restore;
        if (bit->second.witness)
          restore = bit->second.originals;
        else
          restore.push_back(
              definitionEquation(bit->first, bit->second.value));
        baseEliminatedDefs.erase(bit);
        for (const ASTNode& r : restore)
        {
          screenNewContent(r);
          if (!restoredBaseRoots.insert(r).second)
            continue;
          const int lit = rootLit(r);
          SATSolver::vec_literals unit;
          unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
          addClause(unit);
          baseLiveMass = addMass(baseLiveMass,
                                 addMass(clauseMassOf[r], 1));
          recordPermanentRoot(r);
        }
      }
    }
  }

  void dropPreparedLevel(const ASTNode& key)
  {
    std::map<ASTNode, PreparedPiece>::iterator it = preparedPieceOf.find(key);
    if (it == preparedPieceOf.end())
      return;
    if (profile.enabled)
      profile.preparationInvalidations++;
    for (const ASTNode& v : it->second.eliminatedVariables)
    {
      std::map<ASTNode, std::vector<ASTNode>>::iterator ui =
          eliminationUsers.find(v);
      if (ui == eliminationUsers.end())
        continue;
      std::vector<ASTNode>& keys = ui->second;
      keys.erase(std::remove(keys.begin(), keys.end(), key), keys.end());
      if (keys.empty())
        eliminationUsers.erase(ui);
    }
    preparedPieceOf.erase(it);
  }

  // ── Where each symbol occurs in the live pushed stack ────────────────
  //
  // Both eliminability questions are occurrence queries over the live
  // levels: "does any level other than this one name v?" and "does any
  // level BELOW this one name context key u?". Answering either by scanning
  // the stack costs O(depth) per candidate, and both are asked once per
  // candidate per level, so the session cost grew as the cube of the stack
  // depth on a stack whose levels each contribute a definition.
  //
  // One pass over the live levels answers both in constant time. The levels'
  // symbol sets are already memoised, so this is set iteration rather than
  // DAG walking, and it is rebuilt per call because the stack is the only
  // thing that defines it.
  struct LevelOccurrence
  {
    size_t levels = 0;   // how many live pushed levels name the symbol
    size_t deepest = 0;  // the largest such level index
  };
  typedef std::unordered_map<ASTNode, LevelOccurrence, ASTNode::ASTNodeHasher,
                             ASTNode::ASTNodeEqual>
      LevelOccurrenceMap;
  LevelOccurrenceMap levelOccurrences;
  bool levelOccurrencesBuilt = false;
  // The level currently being asked about, and its symbol set: every
  // candidate of a level repeats the same lookup otherwise.
  const ASTNodeSet* ownLevelSymbols = NULL;
  size_t ownLevelSymbolsIdx = std::numeric_limits<size_t>::max();

  // Built on first use rather than per solve: a stack whose preparations
  // harvest no definition and whose context stays empty never asks either
  // question, and the pass is proportional to the live levels' symbol sets,
  // which is not free on a symbol-rich stack.
  void invalidateLevelOccurrences()
  {
    levelOccurrencesBuilt = false;
    ownLevelSymbols = NULL;
    ownLevelSymbolsIdx = std::numeric_limits<size_t>::max();
  }

  void ensureLevelOccurrences(const ASTVec& stack)
  {
    if (levelOccurrencesBuilt)
      return;
    levelOccurrencesBuilt = true;
    levelOccurrences.clear();
    for (size_t j = 1; j < stack.size(); j++)
      for (const ASTNode& s : symbolsOf(stack[j]))
      {
        LevelOccurrence& use = levelOccurrences[s];
        use.levels++;
        use.deepest = j;
      }
  }

  // Does any live pushed level other than `levelIdx` name `v`?
  bool namedByAnotherLevel(const ASTNode& v, size_t levelIdx,
                           const ASTVec& stack)
  {
    ensureLevelOccurrences(stack);
    LevelOccurrenceMap::const_iterator it = levelOccurrences.find(v);
    if (it == levelOccurrences.end())
      return false;
    size_t elsewhere = it->second.levels;
    if (levelIdx < stack.size())
    {
      if (levelIdx != ownLevelSymbolsIdx)
      {
        ownLevelSymbols = &symbolsOf(stack[levelIdx]);
        ownLevelSymbolsIdx = levelIdx;
      }
      if (ownLevelSymbols->find(v) != ownLevelSymbols->end())
        elsewhere--;
    }
    return elsewhere > 0;
  }

  // Whether `v` belongs to one conjunct of level `levelIdx` alone:
  // mentioned by no base conjunct, no other live level's raw content, at
  // most ONE raw conjunct of its own level (its defining one -- the context
  // is level-uniform, so a same-level use elsewhere would keep a reference
  // to the variable), and never bit-blasted.
  //
  // This is only half of eliminability. The other half -- that the context
  // can be made to substitute the variable away in the levels below -- is
  // ctxInlinable, and preparePiece requires both.
  bool levelPrivate(const ASTNode& v, size_t levelIdx, const ASTVec& stack,
                    const std::map<ASTNode, size_t>& conjunctCountOf,
                    const ASTNodeSet& protectedSymbols)
  {
    if (encoding.nodes().symbolToBBNode.find(v) !=
        encoding.nodes().symbolToBBNode.end())
      return false;
    if (baseSymbols.find(v) != baseSymbols.end())
      return false;
    if (protectedSymbols.find(v) != protectedSymbols.end())
      return false;
    std::map<ASTNode, size_t>::const_iterator cnt = conjunctCountOf.find(v);
    if (cnt != conjunctCountOf.end() && cnt->second > 1)
      return false;
    return !namedByAnotherLevel(v, levelIdx, stack);
  }

  // The re-conjoined form of a definition the privacy check refused.
  ASTNode definitionEquation(const ASTNode& var, const ASTNode& def)
  {
    if (def == bm->ASTTrue)
      return var;
    if (def == bm->ASTFalse)
      return bm->defaultNodeFactory->CreateNode(NOT, var);
    if (var.GetType() == BOOLEAN_TYPE)
      return bm->defaultNodeFactory->CreateNode(IFF, var, def);
    return bm->defaultNodeFactory->CreateNode(EQ, var, def);
  }

  // Can this definition be inlined into the pushed-definition context, and
  // what would go in?
  //
  // This is the OTHER half of eliminability, and it must be decided in the
  // same place as privacy. Eliminating a definition deletes its equation and
  // leaves the variable's occurrences to be substituted away by the context;
  // if the context entry is then declined -- because expansion reintroduces
  // the variable, or the body is too big to inline -- the occurrences in
  // deeper levels stay and nothing constrains them. Deciding the two
  // together makes "eliminated" mean "substituted away everywhere" by
  // construction, which is what the encode-boundary assertion in rootLit
  // checks.
  //
  // A variable the context already binds needs nothing further: its
  // occurrences are already substituted away.
  // `ctx` is not const because replace() canonicalises the map as it runs,
  // expanding entries through each other; that is welcome and is what the
  // re-join has always relied on.
  bool ctxInlinable(const ASTNode& var, const ASTNode& def, ASTNodeMap& ctx,
                    ASTNode& expandedOut)
  {
    if (ctx.find(var) != ctx.end())
    {
      expandedOut = ASTNode();
      return true;
    }
    ASTNode expanded = def;
    if (!ctx.empty())
    {
      ASTNodeMap cache;
      expanded =
          SubstitutionMap::replace(expanded, ctx, cache, bm->defaultNodeFactory);
    }
    if (expanded.GetKind() != TRUE && expanded.GetKind() != FALSE &&
        bm->VarSeenInTerm(var, expanded))
      return false;
    if (dagSizeUpTo(expanded, defInlineCap) > defInlineCap)
      return false;
    expandedOut = expanded;
    return true;
  }

  const PreparedPiece&
  preparePiece(const ASTNode& replaced, size_t levelIdx, const ASTVec& stack,
               const std::map<ASTNode, size_t>& conjunctCountOf,
               const ASTNodeSet& protectedSymbols, ASTNodeMap& ctx)
  {
    ScopedProfileTimer preparationTimer(profile.enabled, profile.prepareNs);
    std::map<ASTNode, PreparedPiece>::iterator hit =
        preparedPieceOf.find(replaced);
    if (hit != preparedPieceOf.end())
    {
      // Revalidate cached eliminations against the complete current scope.
      // Usually screenNewContent invalidates an entry before a new mention
      // can make its variable shared.  Raw nodes are screened only once,
      // however, and an entry eliminating one of their symbols may be
      // created after that first screening while the node is popped.  A
      // later re-push must not reuse that now-non-private elimination.
      // Privacy only. Inlinability is settled by the caller, which needs the
      // expansion anyway, so checking it here as well would pay for the same
      // substitution twice on every cache hit.
      bool privateStill = true;
      for (const ASTNode& v : hit->second.eliminatedVariables)
      {
        if (!levelPrivate(v, levelIdx, stack, conjunctCountOf,
                          protectedSymbols))
        {
          privateStill = false;
          break;
        }
      }
      if (privateStill)
      {
        if (profile.enabled)
          profile.preparationHits++;
        return hit->second;
      }
      dropPreparedLevel(replaced);
    }
    if (profile.enabled)
      profile.preparationMisses++;

    // The batch front pipeline, on the conjunct alone: harvest defining
    // equations (PropagateEqualities fills the scratch SolverMap and
    // removes them from the formula), substitute them through, simplify.
    // sigma0 is applied HERE, inside the cache: its entries are permanent
    // truths, so a preparation made under an older, smaller sigma0 stays
    // sound forever -- which is exactly what lets the cache key ignore it
    // and survive base growth (the retractable pushed definitions, whose
    // staleness would NOT be sound, are in the key).
    SubstitutionMap scratchSm(bm);
    Simplifier scratch(bm, &scratchSm);
    ASTNode out = replaced;
    if (!sigma0.empty())
    {
      ASTNodeMap cache;
      out =
          SubstitutionMap::replace(out, sigma0, cache, bm->defaultNodeFactory);
    }
    // The equality-propagation-and-simplify pipeline is a TRIAL, run on
    // its own scratch state. Its result is NOVEL nodes: adopting it
    // forfeits every bit-blast-memo hit the raw form's subterms would
    // have had, across this solve's siblings and every later one. Only
    // meaningful COLLAPSE pays for that -- the families this exists for
    // shrink by orders of magnitude -- so a result that explodes or
    // merely shuffles (same-size rewrites measured 25x the clauses
    // purely through lost sharing) is discarded wholesale, formula and
    // harvested definitions together, and the piece passes through
    // untouched: rootLit's raw-keyed preparation, which has always
    // handled those, does the rest.
    // Only meaningful COLLAPSE pays for novelty, and that is the whole
    // criterion: the result must halve, or be the identical node (a
    // no-op trial costs nothing to "adopt"). There used to be a flat
    // 200-node floor here so small pieces could adopt freely -- and on
    // small dense floating-point conjuncts it admitted same-size
    // SHUFFLES (108 nodes to 105), whose novel forms both forfeit the
    // bit-blast memo's sharing and can be strictly harder to search: a
    // family the batch pipeline solves in a second ran to timeout,
    // deterministically, on shuffled forms of near-identical size.
    // Measured unclipped. `out` has just been expanded under sigma0, whose
    // replacements carry no inlining cap, so a piece that arrived under the
    // granularity gate can leave it far above bigFormulaCap -- and a clipped
    // count saturates there, turning "must at least halve" into a fixed
    // ten-thousand-node ceiling that a legitimately large collapse cannot
    // meet. This is the cache-miss path, so the walk is paid once per
    // distinct piece, against passes that walk it anyway.
    const size_t before = dagSizeUpTo(out, std::numeric_limits<size_t>::max());
    const size_t budget = before / 2;
    {
      SubstitutionMap trialSm(bm);
      Simplifier trial(bm, &trialSm);
      ASTNode trialOut = out;
      bool rejectedBeforeSimplify = false;
      if (bm->UserFlags.propagate_equalities)
      {
        PropagateEqualities pe(&trial, bm->defaultNodeFactory, bm);
        trialOut = pe.topLevel(trialOut);
      }
      if (trial.hasUnappliedSubstitutions())
        trialOut = trial.applySubstitutionMap(trialOut);
      // The gate must also bound the TRIAL's own cost: simplifying a
      // propagation-exploded intermediate can take minutes before any
      // post-hoc check would see it.
      if (dagSizeUpTo(trialOut, budget) > budget)
      {
        rejectedBeforeSimplify = true;
        trialOut = out;
      }
      else
        trialOut = trial.SimplifyFormula_TopLevel(trialOut, false);
      // Unconstrained-variable elimination is deliberately NOT run on
      // pieces: a piece's untouchable set would have to protect every
      // symbol visible outside it, and with cross-level cascades off
      // limits the pass measured as pure graph-build overhead with no
      // collapse anywhere in the slowdown corpus (the collapses PE can
      // see, it already gets). The base conjunction at a rebuild
      // boundary is the one place a global pass is sound and free of
      // the reuse penalty; see rebuildEncodings.
      if (!rejectedBeforeSimplify &&
          (trialOut == out || dagSizeUpTo(trialOut, budget) <= budget))
      {
        if (profile.enabled)
        {
          if (trialOut == out)
            profile.preparationNoop++;
          else
            profile.preparationCollapsed++;
        }
        out = trialOut;
        DenseNodeMap* harvested = trial.Return_SolverMap();
        for (DenseNodeMap::const_iterator it = harvested->begin();
             it != harvested->end(); ++it)
          scratchSm.Return_SolverMap()->insert(*it);
      }
      else if (profile.enabled)
        profile.preparationRejected++;
    }

    PreparedPiece pl(PreprocessingMode::PerLevel, replaced);
    ASTVec keep;
    DenseNodeMap* defs = scratch.Return_SolverMap();
    for (DenseNodeMap::const_iterator it = defs->begin(); it != defs->end();
         ++it)
    {
      const ASTNode& var = it->first;
      const ASTNode& def = it->second;
      // Non-symbol entries (a read the map resolved, say) and every
      // non-private variable keep today's semantics: the definition is
      // asserted, never lost. So does a definition too big to inline:
      // elimination is only sound if later uses are substituted away,
      // and substituting a big replacement destroys the sharing its
      // variable provides.
      //
      // An array-carrying BODY is refused too, exactly as the equality
      // harvests refuse it (recogniseDefinition): an eliminated body is
      // replayed through the model channel, where a read belongs to a
      // registry row no active encoding anchors, and it joins the
      // pushed-definition context, whose cycle check
      // (STPMgr::VarSeenInTerm) does not look inside read-over-write
      // terms. Keeping the equation asserted costs only the rewrite.
      ASTNode inlined;
      if (var.GetKind() != SYMBOL || var.GetIndexWidth() != 0 ||
          !levelPrivate(var, levelIdx, stack, conjunctCountOf,
                        protectedSymbols) ||
          dagSizeUpTo(def, defInlineCap) > defInlineCap ||
          containsArrayOps(def, bm) ||
          !ctxInlinable(var, def, ctx, inlined))
      {
        keep.push_back(definitionEquation(var, def));
        continue;
      }
      pl.addElimination(var, def);
    }

    if (!keep.empty())
    {
      keep.push_back(out);
      out = bm->defaultNodeFactory->CreateNode(AND, keep);
    }
    splitConjuncts(out, bm->ASTTrue, pl.conjuncts);

#ifndef NDEBUG
    // Recording an elimination while any retained conjunct still mentions
    // its variable would leave live backend bits alongside model-only
    // metadata.  Adopted substitutions must remove every such use.
    for (const ASTNode& v : pl.eliminatedVariables)
      for (const ASTNode& c : pl.conjuncts)
        assert(symbolsOf(c).find(v) == symbolsOf(c).end());
#endif

    for (const ASTNode& v : pl.eliminatedVariables)
      eliminationUsers[v].push_back(replaced);

    return preparedPieceOf.insert(std::make_pair(replaced, pl))
        .first->second;
  }

  // Substitutions harvested from base-level equations: x -> t for a
  // base-level conjunct (= x t), plus TRUE/FALSE for unit boolean
  // conjuncts. The base level only grows, so this map is monotone and
  // needs no backtracking. An entry's defining equation normally encodes
  // to TRUE under its own entry -- a genuine elimination, with the
  // variable's model value replayed by evaluating the definition -- and
  // that is sound exactly while every encoded occurrence of the variable
  // is substituted away. Two raw-encoding routes can break that
  // completeness: a frozen late definition (mustKeepRaw) whose right-hand
  // side names the variable, and an exact-stack block carrying the raw
  // base. restoreDroppedSigma0 re-asserts the defining conjunct as a
  // permanent unit before either may mint bits; after that, rewriting
  // under the entry is plain simplification of an asserted equation.
  //
  // SubstitutionMap::replace expands entries through each other as it runs
  // ((x -> y) plus (y -> 5) becomes (x -> 5), mutating the map); every
  // rewritten entry is still a permanent truth, so that canonicalisation
  // is welcome. It is also why rewrite caches are per use, never shared
  // across calls: a cache entry can predate an expansion.
  ASTNodeMap sigma0;

  // Defining equations that must reach the solver as real constraints.
  // A variable whose bits were already encoded in an EARLIER check-sat is
  // frozen (z3's rule: a symbol the backend has seen must not be
  // eliminated): its defining equation would otherwise rewrite itself to
  // TRUE under its own entry, and the existing SAT variables would lose
  // the constraint -- sat where unsat lies that way. Such an equation is
  // encoded un-rewritten; the sigma0 entry still simplifies everything
  // encoded afterwards, which is sound exactly because the equation is
  // asserted.
  ASTNodeSet mustKeepRaw;

  // The raw defining conjunct behind each sigma0 entry, and the entries
  // whose equation is NOT asserted in the current backend epoch (it
  // encoded to TRUE under its own entry; the model replays the value by
  // evaluation). Such a variable must never acquire live SAT bits: every
  // encoded occurrence was substituted away, so bits could only arrive
  // through a route that encodes RAW content -- a frozen late definition
  // whose right-hand side names the variable, or an exact-stack block
  // carrying the raw base -- and bits without the equation are
  // unconstrained: sat where unsat lies that way, and models that
  // contradict the raw stack. restoreDroppedSigma0 is the guard: before
  // any formula is encoded, each dropped variable it mentions gets its
  // defining conjunct back as a permanent unit (always sound -- the base
  // only grows), encoded raw via mustKeepRaw so it cannot erase itself
  // under its own entry. A relief rotation clears mustKeepRaw and its
  // fresh epoch re-encodes every equation to TRUE again, so it re-drops
  // every entry and restoration repeats on demand.
  std::map<ASTNode, ASTNode> sigma0DefiningConjunctOf;
  ASTNodeSet sigma0Dropped;

  // One activation literal per distinct set of root literals a pushed
  // level has ever solved with. Assuming the activation literal asserts
  // exactly those roots through persistent implications, shrinking the
  // assumption set from one literal per conjunct to one per level. The
  // key is the sorted root vector itself -- not the level's formula --
  // because under pushed-level definitions the same formula can encode to
  // different roots in different rounds; identical roots are the only
  // thing that makes reusing the implications sound.
  //
  // Entries age: one not assumed for actLitRetireAge solves is retired --
  // its literal is PINNED false by a permanent unit, which satisfies the
  // implications outright (so the solver stops carrying them) and fixes
  // the variable so it is never decided again. This is cvc5's popped-
  // variable treatment, sound here for exactly one variable class: an
  // activation variable's ONLY clauses are its implications, all
  // satisfied by the pin, so the pin can transmit no semantics. (Pinning
  // an ENCODING variable this way would violate its Tseitin definitional
  // clauses, which no activation unit guards -- that is why eviction
  // stops at activation literals.) A retired root set that recurs simply
  // mints a fresh activation variable.
  struct ActLitEntry
  {
    int lit = 0;
    uint64_t lastUsed = 0;
  };
  std::map<std::vector<int>, ActLitEntry> actLitOf;
  static const uint64_t actLitRetireAge = 16;

  // Every literal that ever carried a level (or an extensionality block)
  // as an assumption, with the solve that last assumed it. The ones not
  // assumed by the current call are retracted content, and
  // hintRetractedLevels steers the decision heuristic away from them;
  // entries not assumed for actLitRetireAge solves fall off the list
  // (hints are advice, so forgetting one is always sound), which keeps
  // the per-solve hinting cost bounded on long sessions.
  std::unordered_map<int, uint64_t> everAssumedLits;

  // Per-call bookkeeping for unsat answers: which level each assumed
  // literal carried, and -- when the caller asked for the last level to be
  // assumed one conjunct at a time (check-sat-assuming wants per-assumption
  // failure granularity) -- which conjunct each of its literals stands
  // for. Consumed by the unsat-assumption accessors; rebuilt every call.
  std::vector<std::pair<int, size_t>> assumedLitLevels;
  std::vector<std::pair<int, ASTNode>> lastLevelLitConjuncts;
  bool lastUnsat;
  bool lastUnsatCoarse;     // ext rounds: one block literal, no granularity
  bool lastLevelIndividual; // the per-conjunct mode actually ran

  // A sat answer whose counterexample nobody has read yet; see
  // materializePendingModel. Cleared at the top of every solve.
  bool modelPending;

  // Trail reuse is a size gamble: on sessions of many small queries the
  // saved per-solve re-descent dominates (the issue #483 KLEE files, 36%
  // and 19% faster at ~11k variables), while on large instances the kept
  // trail suppresses the fresh restarts the search needs. Floating point is
  // a useful early-session predictor of that phase-sensitive class. A late
  // transition is more specific: source array+FP Vector sessions benefit
  // from a short observation window and eventual retirement, while the
  // corresponding array-free BVFP sessions recover several solves by
  // keeping their established trail. A state which remains below the
  // ~11k-variable class where reuse first measured useful is cheap to
  // rebuild; a growing array state is kept until trail and inprobing
  // retirement can share the existing 20k-variable rebuild boundary.
  // Substantial carried refinement state is protected until the independent
  // size belt. These are measured policy boundaries; none changes semantics.
  bool trailReuseAllowed;
  static const unsigned long trailReuseVarLimit = 100000;
  static const size_t trailReuseFpRetireSolves = 7;
  static const size_t trailReuseLateArrayFpProbeSolves = 3;
  static const unsigned long trailReuseEstablishedVarFloor = 10000;
  static const uint64_t trailReuseRefinementClauseFloor = 500;
  bool sourceArraysSeen = false;
  size_t lateArrayFpSolvesWithTrail = 0;
  std::vector<int> lastFailedLits;
  size_t lastLevelCount;

  // A granular core is trustworthy only if every literal that could fail is
  // one this call can attribute. The accessors go the other way -- they keep
  // the failed literals they can find in assumedLitLevels and
  // lastLevelLitConjuncts, and silently drop the rest -- so an assumed
  // literal missing from those tables does not widen the reported core, it
  // narrows it. The extensionality block literal is exactly such a literal
  // (assumed, deliberately unrecorded), and a round that assumed one would
  // report a core too shallow, letting the frontend cache unsat at a level
  // that is satisfiable. Those rounds are routed to coarse today; this is
  // the statement of why that routing is load-bearing, and it re-establishes
  // the conclusion rather than trusting the routing, because coarse is
  // always a correct answer and a wrong unsat is not.
  void recordUnsat(const SATSolver::vec_literals& assumptions,
                   size_t levelCount, bool coarse)
  {
    if (!coarse)
    {
      std::unordered_set<int> attributable;
      for (const std::pair<int, size_t>& ll : assumedLitLevels)
        attributable.insert(ll.first);
      for (int i = 0; i < assumptions.size() && !coarse; i++)
        coarse = attributable.count(assumptions[i].x) == 0;
      assert(!coarse && "granular unsat with an unattributable assumption");
    }
    lastUnsat = true;
    lastUnsatCoarse = coarse;
    lastLevelCount = levelCount;
    if (!coarse)
      solver->unsatAssumptions(assumptions, lastFailedLits);
  }

  // ── Unit promotion of stable prefixes ─────────────────────────────
  //
  // A pushed level asserted via an assumption pays for its
  // retractability at every solve: the backend re-decides the
  // assumption trail, and none of the level's clauses may take part in
  // root-level preprocessing, because the solver must stay correct for
  // calls that drop the assumption. A level that has sat IDENTICAL at
  // the same depth for many consecutive solves is paying for a
  // retraction that never comes -- the measured gap is large (the same
  // instance solved 40.7s under its session's assumptions against
  // 12.7s with those assumptions as units) -- so a stable PREFIX of
  // the stack is promoted to permanent units. Prefix-only, mirroring
  // stack discipline; never the deepest level (the churn point, and
  // check-sat-assuming's per-assumption frame). The price is paid on
  // retraction instead: any change to a promoted level starts the
  // solver over (rebuildEncodings), and each such demotion DOUBLES the
  // stability threshold for the session, so a session that keeps
  // popping its prefix stops being gambled on.
  //
  // Unsat-core soundness: a promoted level's content is asserted
  // unconditionally, so every refutation may silently rest on it. The
  // failed-assumption story therefore floors every core at the
  // promoted depth (lastUnsatCoreLevels), and the frontend's verdict
  // cache can never record an unsat above a promoted level that may
  // have carried it.
  size_t promoteAfterSolves = 8;

  // Track per-level stability against the last call's stack, and start
  // the solver over if a PROMOTED level changed or vanished -- its
  // units no longer describe the stack. Runs before any routing, so
  // extensionality rounds see a coherent solver too.
  void updateStackStability(const ASTVec& assertionsSMT2)
  {
    const IncrementalScopeState::ReconcileResult reconciliation =
        scopes.reconcile(assertionsSMT2);
    if (reconciliation.promotedPrefixRetracted)
    {
      promoteAfterSolves *= 2;
      if (bm->UserFlags.stats_flag)
        std::cerr << "Incremental: promoted prefix retracted, solver "
                     "restarted (threshold now "
                  << promoteAfterSolves << " solves)" << std::endl;
      rebuildEncodings(assertionsSMT2, RebuildReason::Promotion);
    }

    for (size_t i = 0; i < assertionsSMT2.size(); i++)
    {
      const bool same = i < reconciliation.commonPrefix;
      // This is a session classification, so a source array level remains
      // evidence after it is popped. Inspect only new/replaced levels: an
      // unchanged level was already screened on the call where it arrived.
      // Inspect the raw node directly, preventing totalisation's internal
      // arrays from setting this. Deliberately avoid fragment() here: memory
      // relief immediately follows reconciliation and must compare the
      // previous epoch snapshot before current-query cache roots are charged.
      if (!sourceArraysSeen && !same)
        sourceArraysSeen = containsArrayOps(assertionsSMT2[i], bm);
    }
  }

  bool baseStableForInprobingRetirement() const
  {
    return scopes.size() > 0 &&
           scopes.stableSolves(0) >= inprobingRetireSolves;
  }

  // The AUTO-mode evidence that probe inprocessing has turned from a one-off
  // win into a recurring tax: a session long enough to have paid for it
  // repeatedly, a base that has stopped moving underneath it, and an encoding
  // big enough for probing to be the dominant per-solve cost.
  //
  // Three sites have to agree on this and each wrote it out in full: whether
  // to retire now, whether a rebuild happening anyway can absorb the
  // retirement, and whether to take it as that rebuild lands. Three copies of
  // a five-term conjunction over two fitted constants is three chances for
  // them to drift, and the third site exists precisely because the first two
  // disagreeing by one solve cost a measured 2x on a double rebuild.
  bool inprobingRetirementEarned() const
  {
    return policy.adaptiveBackendConfiguration() &&
           bm->UserFlags.incremental_inprobing ==
               UserDefinedFlags::BVAMode::AUTO &&
           solver->supportsInprobingControl() &&
           engagedSolves > inprobingRetireSolves &&
           baseStableForInprobingRetirement() &&
           solver->nVars() >= inprobingRetireMinVars;
  }

  // Whether the bounded-variable-addition decision has been taken for the
  // current backend instance. rebuildEncodings resets it: the fresh solver
  // reopens the configuration window. The warning latch is per session --
  // a rebuild does not deserve a repeat of the warning.
  bool bvaDecided;
  bool bvaWarned;

  // Clause submissions are counted by SATSolver so direct theory-refinement
  // clients cannot bypass the accounting. Keep the mass of retired backend
  // epochs separately: profiles report work over the whole driver lifetime,
  // while retained/liveness decisions use only the current solver's count.
  uint64_t retiredClauseSubmissions = 0;

  // Generation of the resettable semantic/AIG encoding store. SAT-only
  // configuration rebuilds do not advance it; a relief rebuild does.
  uint64_t encodingEpochGeneration = 0;

  uint64_t lifetimeClauseSubmissions() const
  {
    return addMass(retiredClauseSubmissions, solver->submittedClauses());
  }

  // Per-call counters printed under -s.
  uint64_t encodesThisCall;
  CheckProfile profile;
  SessionProfile sessionProfile;
  ProfileClock::time_point profileStarted;
  uint64_t profileClausesBefore = 0;

  // The ordinary check-sat path is deliberately staged here rather than
  // represented by a mutable solve-plan object. Each stage owns the local
  // bookkeeping it creates and exposes only the value the next stage needs.
  void maintainBackendForCheck(const ASTVec& assertionsSMT2);
  bool tryExactStackRoute(const ASTVec& assertionsSMT2,
                          bool assumeLastLevelPerConjunct,
                          bool firstForcedIncrementalSolve,
                          SOLVER_RETURN_TYPE& result);
  void synchronizeCbpPrefix(const ASTVec& assertionsSMT2,
                            bool firstForcedIncrementalSolve);
  void encodeBaseLevel(const ASTVec& assertionsSMT2,
                       bool firstForcedIncrementalSolve);
  size_t prepareAndEncodePushedLevels(
      const ASTVec& assertionsSMT2, bool assumeLastLevelPerConjunct,
      SATSolver::vec_literals& assumptions);

  Impl(STPMgr* bm_, AbsRefine_CounterExample* ce_, Simplifier* batchSimp_,
       ArrayTransformer* batchAT_)
      : bm(bm_), ce(ce_), batchSimp(batchSimp_), batchAT(batchAT_),
        policy(bm_->UserFlags.incremental_core_only),
        solver(makeBackend(bm_->UserFlags, true)), encoding(bm_),
        walks(bm_->ASTFalse), cnf(solver.get()), bvAbstraction(bm_),
        lastUnsat(false), lastUnsatCoarse(false),
        lastLevelIndividual(false), modelPending(false),
        trailReuseAllowed(!policy.coreOnly()), lastLevelCount(0),
        bvaDecided(false),
        bvaWarned(false), encodesThisCall(0)
  {
    // Refinement adds clauses between solve calls; tell backends that need
    // to know (CryptoMiniSat skips its startup simplification).
    solver->enableRefinement(true);

    // The driver's assumption order is prefix-stable across calls --
    // assumptions are emitted in assertion stack order, and push/pop only
    // ever change the suffix -- which is exactly what lets a backend keep
    // the shared trail between solves instead of re-descending from the
    // root every call. Size-gated: see trailReuseAllowed.
    if (trailReuseAllowed)
      solver->enableTrailReuse();

    // Lucky-phase probing re-tries trivial whole assignments over the
    // entire clause database at every solve call. The driver's solver is
    // many-solve by definition, so that is a recurring tax (measured a
    // third of small variant-push sessions); the batch pipeline's
    // single-solve instances keep it.
    if (policy.adaptiveBackendConfiguration())
      solver->disableLuckyPhases();
  }

  void beginProfile(size_t levels)
  {
    if (!bm->UserFlags.incremental_profile)
    {
      profile.enabled = false;
      return;
    }
    profile = CheckProfile();
    profile.enabled = true;
    profile.check = sessionProfile.checks + 1;
    profile.levels = levels;
    profileClausesBefore = lifetimeClauseSubmissions();
    profileStarted = ProfileClock::now();
  }

  void finishProfile()
  {
    if (!profile.enabled)
      return;

    profile.totalNs = std::chrono::duration_cast<std::chrono::nanoseconds>(
                          ProfileClock::now() - profileStarted)
                          .count();
    profile.clauses = lifetimeClauseSubmissions() - profileClausesBefore;
    profile.retainedClauses = retainedClauseMass();
    profile.liveClauses = currentLiveClauseMass;
    profile.peakLiveClauses = maxLiveClauseMass;
    sessionProfile.add(profile);

    printIncrementalProfile(std::cerr, profile, sessionProfile,
                            policy.coreOnly(), retainedClauseMass(),
                            currentLiveClauseMass, maxLiveClauseMass);
  }

  int varOfAig(Aig_Obj_t* regular) const { return cnf.varOf(regular); }

  void addClause(SATSolver::vec_literals& c) { cnf.addClause(c); }

  static uint64_t addMass(uint64_t a, uint64_t b)
  {
    const uint64_t limit = std::numeric_limits<uint64_t>::max();
    return b > limit - a ? limit : a + b;
  }

  uint64_t retainedClauseMass() const { return solver->submittedClauses(); }

  void recordPeakLiveClauseMass(uint64_t mass)
  {
    // Ownership can conservatively count one shared clause through two live
    // roots. It may delay relief, but it must never manufacture more live
    // retained mass than the backend actually received.
    mass = std::min(mass, retainedClauseMass());
    maxLiveClauseMass = std::max(maxLiveClauseMass, mass);
  }

  void recordLiveClauseMass(uint64_t mass)
  {
    mass = std::min(mass, retainedClauseMass());
    currentLiveClauseMass = std::max(currentLiveClauseMass, mass);
    recordPeakLiveClauseMass(mass);
  }

  bool clauseReliefSizeReached() const
  {
    return bm->UserFlags.incremental_reencode_limit > 0 &&
           (int64_t)solver->nVars() >=
               bm->UserFlags.incremental_reencode_limit;
  }

  bool reliefRatioReached() const
  {
    // Equivalent to retained >= 4 * (peak + 1), without overflowing the
    // multiplication or peak+1 at the uint64_t boundary.
    return maxLiveClauseMass != std::numeric_limits<uint64_t>::max() &&
           maxLiveClauseMass + 1 <= retainedClauseMass() / 4;
  }

  uint64_t refinementMass(const ASTNode& owner) const
  {
    std::map<ASTNode, uint64_t>::const_iterator it =
        refinementMassOf.find(owner);
    return it == refinementMassOf.end() ? 0 : it->second;
  }

  uint64_t accountRefinementClauses(const ASTNode& owner,
                                    uint64_t submittedBefore)
  {
    const uint64_t submittedAfter = solver->submittedClauses();
    assert(submittedAfter >= submittedBefore);
    const uint64_t delta = submittedAfter - submittedBefore;
    if (delta == 0)
      return 0;
    refinementMassOf[owner] = addMass(refinementMassOf[owner], delta);
    currentRefinementClauseMass =
        addMass(currentRefinementClauseMass, delta);
    if (profile.enabled)
      profile.refinementClauses =
          addMass(profile.refinementClauses, delta);
    return delta;
  }

  uint64_t activeActivationMass(
      const SATSolver::vec_literals& assumptions) const
  {
    uint64_t mass = 0;
    for (int i = 0; i < assumptions.size(); i++)
    {
      std::unordered_map<int, uint64_t>::const_iterator it =
          activationMassOf.find((int)assumptions[i].x);
      if (it != activationMassOf.end())
        mass = addMass(mass, it->second);
    }
    return mass;
  }

  Aig_Obj_t* aigRoot(const ASTNode& key) const
  {
    std::map<ASTNode, Aig_Obj_t*>::const_iterator it = aigRootOf.find(key);
    assert(it != aigRootOf.end());
    return it->second;
  }

  void recordPermanentRoot(const ASTNode& key)
  {
    permanentAigRoots.push_back(aigRoot(key));
    permanentUnitMass = addMass(permanentUnitMass, 1);
  }

  static void normalizeAigRoots(std::vector<Aig_Obj_t*>& roots)
  {
    std::sort(roots.begin(), roots.end(), [](Aig_Obj_t* a, Aig_Obj_t* b) {
      return Aig_ObjId(Aig_Regular(a)) < Aig_ObjId(Aig_Regular(b));
    });
    roots.erase(std::unique(roots.begin(), roots.end(),
                            [](Aig_Obj_t* a, Aig_Obj_t* b) {
                              return Aig_ObjId(Aig_Regular(a)) ==
                                     Aig_ObjId(Aig_Regular(b));
                            }),
                roots.end());
  }

  // Exact number of clauses ensureEncoded() submitted for the unique AIG
  // nodes reachable from the permanent-root prefix and current roots: three
  // per AND and one for the shared TRUE variable when a cone reaches the
  // constant. CIs allocate variables but no clauses. Every root has already
  // been encoded in this backend epoch.
  uint64_t encodedAigConeMass(
      const std::vector<Aig_Obj_t*>& currentRoots,
      size_t permanentRootCount)
  {
    assert(permanentRootCount <= permanentAigRoots.size());
    std::unordered_set<unsigned> seen;
    std::vector<Aig_Obj_t*> pending;
    pending.reserve(permanentRootCount + currentRoots.size());
    pending.insert(pending.end(), permanentAigRoots.begin(),
                   permanentAigRoots.begin() + permanentRootCount);
    pending.insert(pending.end(), currentRoots.begin(), currentRoots.end());
    uint64_t mass = 0;
    while (!pending.empty())
    {
      Aig_Obj_t* node = Aig_Regular(pending.back());
      pending.pop_back();
      if (!seen.insert(Aig_ObjId(node)).second)
        continue;
      assert(varOfAig(node) != -1);
      if (Aig_ObjIsConst1(node))
      {
        mass = addMass(mass, 1);
        continue;
      }
      if (Aig_ObjIsCi(node))
        continue;
      assert(Aig_ObjIsAnd(node));
      mass = addMass(mass, 3);
      pending.push_back(Aig_ObjFanin0(node));
      pending.push_back(Aig_ObjFanin1(node));
    }
    return mass;
  }

  // Record a solve's cheap live estimate now and retain enough of its actual
  // AIG roots to repair that estimate lazily if it would later authorize a
  // rebuild. `nonStructuralMass` is the exact live unit/activation/theory
  // share; the cone walk supplies only structural clauses.
  void stageLiveConeMass(std::vector<Aig_Obj_t*> currentRoots,
                         uint64_t cheapLiveMass,
                         uint64_t nonStructuralMass)
  {
    // The value that drives the relief decision is the same in both modes.
    // It used to be the cheap ownership estimate normally and an exact cone
    // union under --incremental-profile, which meant the profiler changed
    // WHEN rebuilds fire: exact is never below the estimate, so a profiled
    // run raised the peak and rebuilt later, or not at all. Every number
    // taken with the profiler then described a configuration production does
    // not run, including the rebuild counters the tests assert on.
    recordLiveClauseMass(cheapLiveMass);

    const bool stage = clauseReliefSizeReached();
    if (profile.enabled || stage)
      normalizeAigRoots(currentRoots);

    if (profile.enabled)
    {
      // Reported, never fed back: instrumentation observes the exact working
      // set without moving the schedule it is there to observe.
      profile.exactLiveClauses = addMass(
          encodedAigConeMass(currentRoots, permanentAigRoots.size()),
          nonStructuralMass);
    }

    // A pending exact walk is only useful once the variable floor has been
    // crossed. Coalesce to this solve's snapshot: retaining every historical
    // root vector on a growing ordinary stack would be quadratic memory, and
    // stale popped stacks are precisely the content relief should reclaim.
    if (stage)
    {
      pendingLiveCone.replace(currentRoots, permanentAigRoots.size(),
                              nonStructuralMass);
    }
    else
      pendingLiveCone.clear();
  }

  // Pay pending whole-cone walks only when the cheap ownership estimate would
  // otherwise authorize a rebuild. Newest first repairs a monotonically
  // growing live stack with one walk; stop immediately once the recovered
  // high-water mark disproves relief. The staging side has already coalesced
  // history to the last solve, so this is at most one full-cone walk.
  void expandPendingLiveConeMass()
  {
    if (!pendingLiveCone.active())
      return;
    const uint64_t structural = encodedAigConeMass(
        pendingLiveCone.roots(), pendingLiveCone.permanentRoots());
    const uint64_t live =
        addMass(structural, pendingLiveCone.nonStructural());
    // This snapshot belongs to the previous solve. Discovering its exact cone
    // repairs the epoch's historical high-water mark, but must not report that
    // old working set as live in the check about to start.
    recordPeakLiveClauseMass(live);
    pendingLiveCone.clear();
  }

  void addBinary(int lit_a, int lit_b) { cnf.addBinary(lit_a, lit_b); }

  void ensureEncoded(Aig_Obj_t* regular) { cnf.ensureEncoded(regular); }

  // Harvest a base-level substitution from a conjunct, if it defines one.
  // The conjunct itself is still encoded and asserted regardless, which is
  // what makes every use of the entry sound forever.
  // Recognise a defining conjunct: SYMBOL / (not SYMBOL) as a boolean unit,
  // or an equation with a symbol on one side. FALSE when the conjunct
  // defines nothing usable; the guards are shared by both harvests.
  bool recogniseDefinition(const ASTNode& c, ASTNode& var, ASTNode& term,
                           bool allowFp = false)
  {
    if (c.GetKind() == SYMBOL)
    {
      var = c;
      term = bm->ASTTrue;
    }
    else if (c.GetKind() == NOT && c[0].GetKind() == SYMBOL)
    {
      var = c[0];
      term = bm->ASTFalse;
    }
    else if ((c.GetKind() == EQ || c.GetKind() == IFF) && c.Degree() == 2)
    {
      if (c[0].GetKind() == SYMBOL)
      {
        var = c[0];
        term = c[1];
      }
      else if (c[1].GetKind() == SYMBOL)
      {
        var = c[1];
        term = c[0];
      }
      else
        return false;
    }
    else
      return false;

    if (var == term)
      return false;

    // Only plain bit-vector/boolean definitions. An array-typed symbol is
    // not a substitutable value; and the replacement must not smuggle
    // theory content -- array reads, opaque equalities -- into conjuncts
    // whose transform decisions (raw-conjunct properties) were already
    // made without it. A floating-point body is allowed where the caller
    // re-checks the substituted conjunct for totalisation (the pushed
    // harvest): these definitions are how a query's FP-computed array
    // indices ever fold to constants, and refusing them leaves every
    // read symbolic for the refinement loop to disentangle.
    if (var.GetIndexWidth() != 0)
      return false;
    if (!allowFp && bm->has_floating_point_theory &&
        containsFloatingPointTheory(term, bm))
      return false;
    if (containsArrayOps(term, bm))
      return false;
    if (bm->UserFlags.enable_array_equality && containsKind(term, ARRAY_EQ))
      return false;
    if (term.GetKind() != TRUE && term.GetKind() != FALSE &&
        bm->VarSeenInTerm(var, term))
      return false;

    return true;
  }

  void harvestSigma0(const ASTNode& c)
  {
    ASTNode var, term;
    if (!recogniseDefinition(c, var, term))
      return;
    if (sigma0.find(var) != sigma0.end())
      return;

    // Expand the replacement through what is already known, once. Chains
    // that stay partially expanded are fine: every equation remains
    // asserted, so partial rewriting is merely less simplification.
    ASTNodeMap cache;
    ASTNode expanded = SubstitutionMap::replace(term, sigma0, cache,
                                                bm->defaultNodeFactory);

    // recogniseDefinition occurs-checked the RAW replacement; expansion
    // can smuggle the variable back in (m = a is innocent until a = f(m)
    // is already known, when it expands to m = f(m)). A self-referential
    // entry makes replace() recurse forever, so it is refused -- the
    // equation is still asserted, so refusing only costs rewriting. With
    // every stored entry expanded and occurs-free at insertion, an
    // entry's replacement can only mention variables that were undefined
    // when it was stored, so no chain of entries can loop.
    if (expanded.GetKind() != TRUE && expanded.GetKind() != FALSE &&
        bm->VarSeenInTerm(var, expanded))
      return;

    // Frozen: the variable's bits already live in the solver, so this
    // equation must constrain them for real (see mustKeepRaw). Otherwise
    // the equation encodes to TRUE under its own entry -- a genuine
    // elimination -- and the entry is recorded as dropped, so a later
    // raw-encoding route restores the equation before minting the
    // variable's bits (see restoreDroppedSigma0).
    if (encoding.nodes().symbolToBBNode.find(var) !=
        encoding.nodes().symbolToBBNode.end())
      mustKeepRaw.insert(c);
    else
      sigma0Dropped.insert(var);
    sigma0DefiningConjunctOf[var] = c;

    sigma0[var] = expanded;
  }

  // A definition found at a PUSHED level. It holds only while its level is
  // live, so nothing about it may persist: entries go into a per-call map,
  // the defining conjunct is remembered so it is never rewritten under its
  // own entry (it stays assumed, which is what makes using the entry
  // sound), and the rewritten conjuncts are cached by their REWRITTEN node
  // -- a formula-level key, valid whenever the same rewrite recurs, and
  // simply not reached in rounds where the definition is gone.
  void harvestPushed(const ASTNode& c, ASTNodeMap& sigmaP,
                     ASTNodeSet& sources, bool& fpLatch)
  {
    ASTNode var, term;
    if (!recogniseDefinition(c, var, term, /*allowFp=*/true))
      return;
    if (sigma0.find(var) != sigma0.end())
      return;
    if (sigmaP.find(var) != sigmaP.end())
      return;

    // Same discipline as harvestSigma0, against the map this entry will
    // actually be used in: the caller replaces under sigma0 MERGED with
    // sigmaP, so the replacement is expanded under both (sigma0 first --
    // sigmaP replacements are already sigma0-expanded, so one pass each
    // suffices) and refused if its own variable reappears. A pushed
    // m = a against a base a = f(m) is exactly the moo.smt2 cycle split
    // across levels.
    ASTNodeMap cache0, cacheP;
    ASTNode expanded = SubstitutionMap::replace(term, sigma0, cache0,
                                                bm->defaultNodeFactory);
    expanded = SubstitutionMap::replace(expanded, sigmaP, cacheP,
                                        bm->defaultNodeFactory);
    if (expanded.GetKind() != TRUE && expanded.GetKind() != FALSE &&
        bm->VarSeenInTerm(var, expanded))
      return;

    // Inlining economics: substituting a definition duplicates its
    // replacement at every use, and each copy re-blasts a cone the
    // variable used to share through one encoding. A big replacement is
    // therefore never chained -- the equation stays asserted and the
    // variable keeps the sharing (a deep-chain definition inlined into a
    // deep-chain user measured ten MILLION clauses for seven conjuncts).
    if (dagSizeUpTo(expanded, defInlineCap) > defInlineCap)
      return;

    sigmaP[var] = expanded;
    sources.insert(c);
    if (!fpLatch && bm->has_floating_point_theory &&
        containsFloatingPointTheory(expanded, bm))
      fpLatch = true;
  }

  // Assertion-local, equivalence-preserving simplification; the shared
  // one-shot entry point guarantees the empty substitution map, so
  // everything it does to this one conjunct is a plain equivalence.
  // Measurably worth it on multi-round workloads; sharing a Simplifier
  // across conjuncts measured slower, so this stays per call.
  ASTNode simplifyAlone(const ASTNode& n)
  {
    return Simplifier::simplifyAlone(bm, n);
  }

  // What actually gets encoded for a conjunct: the conjunct rewritten under
  // the base-level substitutions and then simplified on its own. Keyed by
  // the ORIGINAL conjunct in rootLitOf, so reuse is untouched; encoding
  // under an older, smaller sigma0 stays sound because sigma0 entries are
  // permanent truths.
  ASTNode prepareConjunct(const ASTNode& c)
  {
    if (!bm->UserFlags.optimize_flag)
      return c;

    ASTNode out = c;
    if (!sigma0.empty() && mustKeepRaw.find(c) == mustKeepRaw.end())
    {
      // replace() rebuilds every touched node through the (simplifying)
      // node factory, so the node-local rewrite rules already run over the
      // substituted result as it is built.
      ASTNodeMap cache;
      out =
          SubstitutionMap::replace(out, sigma0, cache, bm->defaultNodeFactory);
    }

    return simplifyAlone(out);
  }

  // Enforce the elimination invariant at the encode boundary: a sigma0
  // variable whose defining equation was dropped may not acquire SAT
  // bits. A formula raw enough to still mention one (a frozen late
  // definition's right-hand side, an exact-stack block carrying the raw
  // base) first gets that variable's defining conjunct back as a
  // permanent unit, encoded raw (mustKeepRaw) with its stale eliminated
  // encoding evicted. Restoring one equation can expose another dropped
  // variable inside its own right-hand side; the recursion through
  // rootLit's encode runs this same guard, and each step removes its
  // variable from the dropped set before encoding, so the chain
  // terminates and a definition never restores itself twice.
  void restoreDroppedSigma0(const ASTNode& toEncode)
  {
    if (sigma0Dropped.empty())
      return;
    for (const ASTNode& s : symbolsOf(toEncode))
    {
      if (sigma0Dropped.erase(s) == 0)
        continue;
      const ASTNode conj = sigma0DefiningConjunctOf.at(s);
      mustKeepRaw.insert(conj);
      // The conjunct's cached encoding is the eliminated TRUE form; evict
      // it so the re-encode below produces the raw equation.
      rootLitOf.erase(conj);
      const int lit = rootLit(conj);
      SATSolver::vec_literals unit;
      unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
      addClause(unit);
      baseLiveMass = addMass(baseLiveMass, addMass(clauseMassOf[conj], 1));
      recordPermanentRoot(conj);
      if (bm->UserFlags.stats_flag)
        std::cerr << "Incremental: restored an eliminated base definition "
                     "before its variable was encoded raw"
                  << std::endl;
    }
  }

  // Lower, transform and bit-blast a fully rewritten word-level formula
  // into the persistent solver, returning its root literal. Everything
  // emitted is a conservative extension; every actual encode is counted
  // for the per-call statistics. `key` is the node this encoding is cached
  // under in rootLitOf -- the raw conjunct on the ordinary path, the
  // rewritten node on the pushed-definitions path -- and the registry rows
  // the transform visits are recorded under the same key, so a later cache
  // hit finds its rows by the node it hit with.
  int encodePrepared(const ASTNode& key, ASTNode toEncode, const Fragment& frag)
  {
    ScopedProfileTimer encodingTimer(profile.enabled, profile.encodeNs);
    restoreDroppedSigma0(toEncode);
#ifndef NDEBUG
    // Vacuous right after the guard above by construction; it stays
    // because it re-states the boundary contract independently of the
    // guard's internals, so a future early-exit or cap added there fails
    // here instead of encoding unconstrained bits.
    for (const ASTNode& s : symbolsOf(toEncode))
      assert(sigma0Dropped.find(s) == sigma0Dropped.end() &&
             "encoding raw content over a dropped base definition");
#endif
    if (frag.fp)
      toEncode = fpContext()->lowerPrepared(toEncode);

    if (frag.arrays)
    {
      ArrayTransformer::TransformResult transformed =
          batchAT->TransformFormulaWithRegistry(toEncode, arrayRegistry);
      toEncode = transformed.formula;
      readsOfEncoded[key].swap(transformed.touchedReads);
      assert(!containsArrayOps(toEncode, bm));
      totalizeRegistrySymbols();

      // The transformer conjoins a read's index-binding equation
      // (index-expression = index-symbol) only when it CREATES the
      // registry row. Under the persistent registry that first creation
      // may live in another conjunct entirely -- another level's, even a
      // popped one -- and a conjunct encoded against a hit row would use
      // an anchor nothing in the current solve binds: the index floats,
      // the abstraction over-approximates wildly, and refinement crawls
      // through the garbage (a family the batch pipeline solves in a
      // second ran to timeout exactly this way once piece preparation
      // separated bindings from their users). Every conjunct therefore
      // re-conjoins the bindings of every row it touches; for rows whose
      // binding is already inside, the AND simply deduplicates.
      if (!bm->UserFlags.ackermannisation && !readsOfEncoded[key].empty())
      {
        ASTVec binds;
        for (const std::pair<ASTNode, ASTNode>& ai : readsOfEncoded[key])
        {
          ArrayTransformer::ArrType::const_iterator ait =
              arrayRegistry.reads.find(ai.first);
          if (ait == arrayRegistry.reads.end())
            continue;
          ArrayTransformer::arrTypeMap::const_iterator rit =
              ait->second.find(ai.second);
          if (rit == ait->second.end())
            continue;
          const ASTNode& indexSym = rit->second.index_symbol;
          if (ai.second == indexSym || indexSym.IsNull())
            continue;
          binds.push_back(
              bm->defaultNodeFactory->CreateNode(EQ, ai.second, indexSym));
        }
        if (!binds.empty())
        {
          binds.push_back(toEncode);
          toEncode = bm->defaultNodeFactory->CreateNode(AND, binds);
        }
      }
    }

    const uint64_t clausesPre = solver->submittedClauses();
    bm->GetRunTimes()->start(RunTimes::BitBlasting);
    BBNodeAIG root = encoding.blaster().BBForm(toEncode);
    bm->GetRunTimes()->stop(RunTimes::BitBlasting);

    bm->GetRunTimes()->start(RunTimes::CNFConversion);
    Aig_Obj_t* regular = Aig_Regular(root.n);
    ensureEncoded(regular);
    const int lit = 2 * varOfAig(regular) + (Aig_IsComplement(root.n) ? 1 : 0);
    bm->GetRunTimes()->stop(RunTimes::CNFConversion);

    // Clause mass per encoding key feeds the relief valve's deadness
    // measure: the valve compares the mass of everything encoded against
    // the mass the live stack actually uses.
    const uint64_t delta = solver->submittedClauses() - clausesPre;
    clauseMassOf[key] = delta;
    aigRootOf[key] = regular;

    encodesThisCall++;
    return lit;
  }

  // Bit-blast a conjunct (once, memoised across the session by the
  // persistent BitBlaster) and encode its circuit; the returned literal
  // asserts it. Array reads are abstracted through the seeded registry
  // first, so the encoded form is pure bit-vector and the abstraction
  // variables are canonical for the session.
  int rootLit(const ASTNode& conjunct)
  {
    chargeSemanticRoot(conjunct);
#ifndef NDEBUG
    // The encode boundary is where the elimination invariant is finally
    // observable: a variable whose defining equation this solve dropped must
    // not appear in anything the solve encodes. Checked here rather than only
    // inside preparePiece because the hazard is a DEEPER level -- rewritten
    // through the pushed-definition context -- naming a variable an earlier
    // level eliminated, which the per-piece check cannot see.
    for (const ASTNode& s : symbolsOf(conjunct))
      assert(scopes.activeEliminatedVariables().find(s) ==
                 scopes.activeEliminatedVariables().end() &&
             "encoding a conjunct over an eliminated variable");
#endif
    NodeToLitMap::const_iterator it = rootLitOf.find(conjunct);
    if (it != rootLitOf.end())
    {
      if (profile.enabled)
        profile.rootHits++;
      return it->second;
    }
    if (profile.enabled)
      profile.rootMisses++;
    const Fragment* frag = NULL;
    ASTNode toEncode = conjunct;
    {
      ScopedProfileTimer preparationTimer(profile.enabled, profile.prepareNs);
      frag = &fragment(conjunct);

      // Totalise partial floating-point operations and pin rounding modes
      // before the formula is used for anything, as the batch pipeline does;
      // the word-level rewriting runs on the totalised form, and lowering to
      // the packed circuit comes after it.
      if (frag->fp)
        toEncode = fpContext()->prepare(toEncode);

      toEncode = prepareConjunct(toEncode);
    }

    const int lit = encodePrepared(conjunct, toEncode, *frag);
    rootLitOf[conjunct] = lit;
    return lit;
  }

  const Fragment& fragment(const ASTNode& n)
  {
    chargeSemanticRoot(n);
    NodeToFragmentMap::const_iterator it = fragmentCache.find(n);
    if (it != fragmentCache.end())
      return it->second;

    Fragment f;
    f.fp =
        bm->has_floating_point_theory && containsFloatingPointTheory(n, bm);
    f.arrayEq =
        bm->UserFlags.enable_array_equality && containsKind(n, ARRAY_EQ);
    f.sourceArrays = containsArrayOps(n, bm);

    // Arrayness must be judged on the form that will be encoded: totalising
    // a partial floating-point operation (fp.to_ubv of a NaN, say) can
    // introduce reads of an unspecified-value array into a conjunct that
    // had no arrays at all. Judged on the raw conjunct, the introduced READ
    // reached the bit-blaster, and the refinement loop -- which is what
    // enforces congruence between unspecified results at equal indices --
    // was skipped. This costs a second totalisation of the node: the
    // encoding-epoch context memoises each CHANGED subterm, so rootLit's
    // later call re-uses those rewrites rather than re-deriving them, but it
    // does re-walk the root to rebuild the spine and re-collect the
    // rounding-mode side conditions. A root-level memo was tried and measured neutral --
    // SAT time dominates every floating-point session it would help -- and
    // was dropped rather than carry a per-root cache for nothing.
    ASTNode basis = n;
    if (f.fp)
      basis = fpContext()->prepare(n);
    f.arrays = basis == n ? f.sourceArrays : containsArrayOps(basis, bm);

    return fragmentCache.insert(std::make_pair(n, f)).first->second;
  }

  SOLVER_RETURN_TYPE exactStackCheckSat(const ASTVec& assertionsSMT2,
                                        bool firstForcedIncrementalSolve,
                                        bool requireScopedCollapse = false,
                                        bool* scopedAccepted = NULL);
  SOLVER_RETURN_TYPE
  solvePlainExactStack(const ASTVec& assertionsSMT2,
                       const SATSolver::vec_literals& assumptions,
                       const ASTNode& inputToSat, Aig_Obj_t* blockRegular);
  ToSATBase* ensureAdapter();

  // The encoding-epoch floating-point context. Its totalisation
  // re-conjoins every side condition (rounding-mode pinning in particular)
  // onto each call's own result -- by design, precisely so the guarantee
  // is independent of the assertion stack -- so per-conjunct preparation
  // over one persistent context is self-contained: a conjunct's lowered
  // form carries its own conditions and retracts with it.
  FpEncodingContext* fpContext()
  {
    if (!fpCtx)
      fpCtx.reset(new FpEncodingContext(bm));
    return fpCtx.get();
  }

  // Publish this epoch's floating-point context to the model machinery,
  // before any model this driver produced can be read. Unconditional, and
  // that is the whole point of it having a name.
  //
  // A NULL context there has to mean exactly one thing -- no solve has run --
  // because that is what every reader of it takes it to mean: the fatal in
  // requireFpEncodingContext, and the "the question cannot be put" answer
  // arrayEqualityIsModelDecidable gives. Installing only when this epoch
  // happened to lower a float makes NULL mean two things at once, and the
  // model machinery has no way to tell them apart. It read the second as the
  // first, and took abort() out of a legal C API call over a float term the
  // assertion stack never mentioned -- which is answerable, and which the
  // batch driver answers, from the context it builds per solve whether or not
  // that solve had a float anywhere in it (STP.cpp, TopLevelSTP).
  //
  // What it costs on a stack with no float in it is one context per encoding
  // epoch: two small allocations over empty caches, made once and reused by
  // every check-sat of the epoch -- less than the batch side already pays,
  // which is one per solve.
  void publishFpContext() { ce->setFpEncodingContext(fpContext()); }

  // Give every bit of a symbol a CNF variable, allocating unconstrained
  // ones where the encoded cones never needed the bit. The refinement
  // machinery encodes congruence axioms straight over the bit variables of
  // the registry's symbols (getEquals), with no notion of "this bit never
  // reached the solver" -- and an unconstrained fresh variable is exactly
  // the meaning the blasted formula gives an unused bit, the same argument
  // ToSATAIG makes for lemma-only extensionality symbols.
  void totalizeSymbol(const ASTNode& s)
  {
    // Eager-Ackermann registry rows carry no index symbol at all.
    if (s.IsNull() || s.GetKind() != SYMBOL)
      return;
    const unsigned width = std::max((unsigned)1, s.GetValueWidth());
    for (unsigned i = 0; i < width; i++)
    {
      BBNodeAIG bit = encoding.nodes().CreateSymbol(s, i);
      ensureEncoded(Aig_Regular(bit.n));
    }
  }

  // What the last refinement-driven check-sat seeded into the batch-side
  // ── Incrementally maintained active-read seeding ──────────────────
  // Reference counts over the (array, index) row KEYS the active cone
  // touches (several keys can touch one row), and the exact row list
  // each key folded (so unfolds mirror folds even if the key's
  // recorded rows change in between). Base keys queue in
  // pendingBaseSeed as they are first asserted and fold exactly once.
  // Deliberately keys only, never row values: the registry's row
  // structs are re-read fresh at every seeding, exactly as the old
  // full rebuild did -- a fold-time copy went stale against later
  // registry updates and the model check tripped the refinement
  // no-progress guard on the divergence.
  std::map<std::pair<ASTNode, ASTNode>, size_t> seededRowRef;
  std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>> foldedRowsOf;
  std::vector<ASTNode> pendingBaseSeed;

  // The PUSHED keys seedActiveReads last folded, sorted by node number; base
  // keys fold monotonically and need no fingerprint.
  std::vector<ASTNode> lastSeededKeys;

  // Seed the batch-side read table with only the reads of the given
  // (active) encodings, drawn from the persistent registry. The keys are
  // whatever this round's literals were cached under: base-level conjuncts
  // and, for the pushed levels, the prepared conjuncts that were assumed.
  // Fold one encoded key's registry rows into the maintained table.
  // The rows actually folded are remembered against the key, so a later
  // unfold decrements exactly what this fold incremented even if the
  // key's recorded rows change in between (a re-encode overwrites
  // readsOfEncoded).
  void foldKeyReads(const ASTNode& key)
  {
    if (foldedRowsOf.find(key) != foldedRowsOf.end())
      return;
    if (profile.enabled)
      profile.readKeysFolded++;
    std::vector<std::pair<ASTNode, ASTNode>>& folded = foldedRowsOf[key];
    std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>>::
        const_iterator rit = readsOfEncoded.find(key);
    if (rit == readsOfEncoded.end())
      return;
    for (const std::pair<ASTNode, ASTNode>& ai : rit->second)
    {
      seededRowRef[ai]++;
      folded.push_back(ai);
    }
  }

  void unfoldKeyReads(const ASTNode& key)
  {
    std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>>::iterator fit =
        foldedRowsOf.find(key);
    if (fit == foldedRowsOf.end())
      return;
    if (profile.enabled)
      profile.readKeysUnfolded++;
    for (const std::pair<ASTNode, ASTNode>& ai : fit->second)
    {
      std::map<std::pair<ASTNode, ASTNode>, size_t>::iterator rr =
          seededRowRef.find(ai);
      if (rr != seededRowRef.end() && --rr->second == 0)
        seededRowRef.erase(rr);
    }
    foldedRowsOf.erase(fit);
  }

  void seedActiveReads(const std::vector<ASTNode>& pushedActiveKeys)
  {
    ScopedProfileTimer readTimer(profile.enabled, profile.readSeedNs);
    // The seeded table is maintained INCREMENTALLY. Base keys arrive
    // through pendingBaseSeed as they are first asserted and fold
    // exactly once -- the base never retracts, so they never unfold.
    // Pushed keys fold and unfold by set difference against the last
    // solve, with per-row reference counts arbitrating rows that
    // several keys touch. Rebuilding the filtered table from the whole
    // ever-grown base every refinement-driven solve was measured at 42%
    // of a KLEE-style session by its thousandth query; the difference
    // walk below touches only what changed.
    std::vector<ASTNode> sortedPushed = pushedActiveKeys;
    std::sort(sortedPushed.begin(), sortedPushed.end(),
              [](const ASTNode& a, const ASTNode& b)
              { return a.GetNodeNum() < b.GetNodeNum(); });
    sortedPushed.erase(std::unique(sortedPushed.begin(), sortedPushed.end()),
                       sortedPushed.end());

    // No skip-if-unchanged fast path: the refinement machinery mutates
    // the batch-side table during its rounds, and every refinement
    // entry must start from a freshly materialised one -- the old
    // full-rebuild code re-assigned on effectively every solve and its
    // correctness silently leaned on that. Materialisation is O(live
    // rows) here, so re-assigning every time costs nothing worth
    // gambling against.
    for (const ASTNode& k : pendingBaseSeed)
      foldKeyReads(k);
    pendingBaseSeed.clear();

    // Two sorted walks: keys leaving the pushed set unfold, keys
    // entering it fold. A key that is ALSO a base conjunct never
    // unfolds -- its base assertion is permanent, and unfolding the
    // shared entry would strip the base's rows with it.
    for (const ASTNode& k : lastSeededKeys)
      if (level0Asserted.find(k) == level0Asserted.end() &&
          !std::binary_search(sortedPushed.begin(), sortedPushed.end(), k,
                              [](const ASTNode& a, const ASTNode& b)
                              { return a.GetNodeNum() < b.GetNodeNum(); }))
        unfoldKeyReads(k);
    for (const ASTNode& k : sortedPushed)
      if (foldedRowsOf.find(k) == foldedRowsOf.end())
        foldKeyReads(k);

    // Materialise the table for the refcounted row keys with FRESH
    // registry values -- O(live rows), not O(ever-asserted base).
    ArrayTransformer::ArrType fresh;
    for (std::map<std::pair<ASTNode, ASTNode>, size_t>::const_iterator it =
             seededRowRef.begin();
         it != seededRowRef.end(); ++it)
    {
      const std::pair<ASTNode, ASTNode>& ai = it->first;
      ArrayTransformer::ArrType::const_iterator ait =
          arrayRegistry.reads.find(ai.first);
      if (ait == arrayRegistry.reads.end())
        continue;
      ArrayTransformer::arrTypeMap::const_iterator iit =
          ait->second.find(ai.second);
      if (iit == ait->second.end())
        continue;
      fresh[ai.first].insert(*iit);
    }
    batchAT->arrayToIndexToRead = fresh;
    lastSeededKeys.swap(sortedPushed);
    if (profile.enabled)
      profile.readRowsLive = seededRowRef.size();
  }

  // Every read row's value and index symbol of one table, totalised.
  void totalizeReadTable(const ArrayTransformer::ArrType& table)
  {
    ScopedProfileTimer registryTimer(profile.enabled, profile.registryNs);
    for (ArrayTransformer::ArrType::const_iterator it = table.begin();
         it != table.end(); ++it)
    {
      for (ArrayTransformer::arrTypeMap::const_iterator rit =
               it->second.begin();
           rit != it->second.end(); ++rit)
      {
        totalizeSymbol(rit->second.symbol);
        totalizeSymbol(rit->second.index_symbol);
      }
    }
  }

  void totalizeRegistrySymbols()
  {
    // Only the refinement machinery encodes axioms over registry symbols,
    // and --ackermanize never refines.
    if (bm->UserFlags.ackermannisation)
      return;
    totalizeReadTable(arrayRegistry.reads);
  }

  // The same guarantee for the rows an extensionality round refines over.
  // Those rows live in the batch transformer's per-round table, not in the
  // persistent registry -- the round transforms on a fresh table by design
  // -- so totalizeRegistrySymbols cannot cover them. Idempotent (the bit
  // creation is memoised), so calling it before every refinement entry is
  // cheap, and necessary: the checker's lemma encodings can add rows
  // mid-round.
  void totalizeBatchRegistrySymbols()
  {
    totalizeReadTable(batchAT->arrayToIndexToRead);
  }

  size_t semanticCacheEntryCount() const
  {
    size_t rows = 0;
    for (ArrayTransformer::ArrType::const_iterator it =
             arrayRegistry.reads.begin();
         it != arrayRegistry.reads.end(); ++it)
      rows += it->second.size();
    return semanticEpoch.retainedRootCount() + fragmentCache.size() + rows +
           readsOfEncoded.size() +
           arrayRegistry.ackPairs.size() + exactStackKeepAlive.size() +
           exactScopedPreprocessOf.size() + preparedPieceOf.size() +
           eliminationUsers.size() + screenedContent.size() +
           walks.cacheEntryCount() + scopedBlockOf.size();
  }

  // Release all state whose validity/reuse is tied to the word-to-AIG
  // encoding epoch. This is deliberately stronger than a SAT-only policy
  // restart: every holder of an AIG pointer is already empty when this runs,
  // and only the current raw assertion ledger plus permanent base facts
  // survive to reconstruct the next epoch.
  void rotateEncodingEpoch()
  {
    assert(policy.rotateEncodingEpochForRelief());
    const size_t oldAigNodes = encoding.aigAndNodes();
    const size_t oldRoots = rootLitOf.size();
    const size_t oldSemanticEntries = semanticCacheEntryCount();

    // CBP retains at most one processed prefix, but that prefix can belong to
    // a route which has since been bypassed by exact-stack solves. Relief is
    // the point at which even that dead prefix and its vector high-water
    // storage must go.
    cbpReset();
    scopes.releaseEpochStorage();
    cbpMemoStable = 0;

    ExtensionalityContext* ext = bm->getExtensionalityIfAny();
    if (ext != NULL)
      ext->releaseSolveStorage();

    // The old model has already been invalidated by entry into this check.
    // Withdraw shared model-channel seeds before dropping the ASTs they pin.
    if (batchSimp != NULL)
    {
      DenseNodeMap* channel = batchSimp->Return_SolverMap();
      for (const ASTNode& key : seededModelKeys)
        channel->erase(key);
    }
    releaseContainer(seededModelKeys);
    ce->ReleaseModelStorage();

    // ArrayTransformer's maps free their nodes on clear, but its per-run
    // scratch vector retains the largest exact block it has seen.
    batchAT->ReleaseRunStorage();

    if (fpCtx)
      ce->setFpEncodingContext(NULL);
    fpCtx.reset();
    adapter.reset();
    symbolMapCache.releaseStorage();

    releaseContainer(fragmentCache);
    arrayRegistry.releaseStorage();
    releaseContainer(readsOfEncoded);
    releaseContainer(exactStackKeepAlive);
    releaseContainer(exactScopedPreprocessOf);
    releaseContainer(preparedPieceOf);
    releaseContainer(eliminationUsers);
    releaseContainer(screenedContent);
    walks.releaseEpochStorage();
    releaseContainer(scopedBlockOf);
    releaseContainer(levelOccurrences);
    invalidateLevelOccurrences();
    releaseContainer(restoredBaseRoots);
    releaseContainer(pendingRebuiltBase);
    releaseContainer(clauseMassOf);
    releaseContainer(refinementMassOf);
    releaseContainer(baseEliminatedDefs);
    // This set records equations frozen only because their variables had AIG
    // bits in the retiring epoch. In the fresh epoch sigma0 can substitute
    // them from the start, so carrying the freeze would be stale policy.
    releaseContainer(mustKeepRaw);
    // With the freezes gone, the fresh epoch's base re-encode eliminates
    // every defining equation again, so every sigma0 entry is dropped
    // until a raw route in the new epoch restores it.
    releaseContainer(sigma0Dropped);
    for (std::map<ASTNode, ASTNode>::const_iterator it =
             sigma0DefiningConjunctOf.begin();
         it != sigma0DefiningConjunctOf.end(); ++it)
      sigma0Dropped.insert(it->first);

    releaseContainer(callCbpSubst);
    releaseContainer(callCbpDeferred);
    releaseContainer(callCbpFactEmitted);
    releaseContainer(callCbpFedConjuncts);
    releaseContainer(cbpCallerCheckpoints);
    releaseContainer(cbpSubstUndo);
    releaseContainer(cbpFedConjunctsAdded);
    releaseContainer(cbpFactsAdded);
    releaseContainer(cbpSubstTrailedThisLevel);

    // clear() leaves the high-water allocation behind for vectors and hash
    // tables. These were made logically empty by the backend reset; swap now
    // makes the relief boundary reclaim their storage as well.
    cnf.releaseStorage();
    releaseContainer(rootLitOf);
    releaseContainer(aigRootOf);
    releaseContainer(permanentAigRoots);
    pendingLiveCone.releaseStorage();
    releaseContainer(actLitOf);
    releaseContainer(everAssumedLits);
    releaseContainer(activationMassOf);
    releaseContainer(lastSeededKeys);
    releaseContainer(seededRowRef);
    releaseContainer(foldedRowsOf);
    releaseContainer(pendingBaseSeed);
    releaseContainer(assumedLitLevels);
    releaseContainer(lastLevelLitConjuncts);
    releaseContainer(lastFailedLits);
    semanticEpoch.releaseStorage();

    encoding.reset();
    ++encodingEpochGeneration;
    if (profile.enabled)
      profile.encodingEpochResets++;
    if (bm->UserFlags.stats_flag)
      std::cerr << "Incremental: encoding epoch reset (generation "
                << encodingEpochGeneration << ", released " << oldAigNodes
                << " AIG nodes, " << oldRoots << " roots, "
                << oldSemanticEntries << " semantic cache entries)"
                << std::endl;
  }

  // Rebuild the SAT side from nothing. Policy-only rebuilds preserve the
  // semantic/AIG store and cheaply re-CNF the live roots. A relief rebuild
  // additionally rotates that store above, so dead historical circuits and
  // semantic caches no longer accumulate for the life of the session.
  // (The finer-grained alternative -- pinning popped variables away from
  // the decision heuristics, as cvc5's CaDiCaL propagator does -- needs
  // the propagator interface and is not portable across our backends.)
  // Steer the decision heuristic away from retracted content: every
  // literal that has ever carried a level or a block is hinted toward
  // its falsifying value while it is not among this call's assumptions.
  // A popped level's literal is unconstrained, and a backend whose
  // default phase is positive would otherwise keep pulling the dead
  // level's cone into the search until the heuristic learns better.
  // Search advice only -- it cannot change a verdict, and assumed
  // literals need no hint because assumptions are forced, not decided.
  void hintRetractedLevels(const SATSolver::vec_literals& assumptions)
  {
    if (!policy.retractionSearchHints())
      return;
    std::unordered_set<int> current;
    for (int i = 0; i < assumptions.size(); i++)
      current.insert(assumptions[i].x);

    for (std::unordered_map<int, uint64_t>::const_iterator it =
             everAssumedLits.begin();
         it != everAssumedLits.end(); ++it)
    {
      if (current.count(it->first))
        continue;
      solver->suggestPhase(it->first >> 1, (it->first & 1) != 0);
    }
  }

  // Retire stale retraction bookkeeping: pin activation literals whose
  // root set has not been assumed for actLitRetireAge solves (see the
  // declaration for why the pin is sound for this variable class and no
  // other), and forget equally stale hint entries. Must run after the
  // backend's configuration window is decided -- the pins are clauses.
  void retireStaleActivation()
  {
    size_t pinned = 0;
    for (std::map<std::vector<int>, ActLitEntry>::iterator it =
             actLitOf.begin();
         it != actLitOf.end();)
    {
      if (engagedSolves - it->second.lastUsed <= actLitRetireAge)
      {
        ++it;
        continue;
      }
      const int lit = it->second.lit;
      SATSolver::vec_literals unit;
      unit.push(SATSolver::mkLit(lit >> 1, (lit & 1) == 0));
      addClause(unit);
      everAssumedLits.erase(lit);
      activationMassOf.erase(lit);
      it = actLitOf.erase(it);
      pinned++;
    }

    for (std::unordered_map<int, uint64_t>::iterator it =
             everAssumedLits.begin();
         it != everAssumedLits.end();)
    {
      if (engagedSolves - it->second > actLitRetireAge)
        it = everAssumedLits.erase(it);
      else
        ++it;
    }

    if (pinned > 0 && bm->UserFlags.stats_flag)
      std::cerr << "Incremental: pinned " << pinned
                << " retired activation literals" << std::endl;
  }

  void rebuildEncodings(const ASTVec& assertionsSMT2, RebuildReason reason)
  {
    ScopedProfileTimer timer(profile.enabled, profile.rebuildNs);
    if (profile.enabled)
    {
      profile.rebuilds++;
      switch (reason)
      {
        case RebuildReason::Relief:
          profile.rebuildRelief++;
          break;
        case RebuildReason::Promotion:
          profile.rebuildPromotion++;
          break;
        case RebuildReason::Inprobing:
          profile.rebuildInprobing++;
          break;
        case RebuildReason::Trail:
          profile.rebuildTrail++;
          break;
      }
    }
    // The fresh solver has no promoted units; a still-stable prefix
    // re-promotes on the next call's tail, recording what it pins then.
    scopes.clearPromotions();

    retiredClauseSubmissions =
        addMass(retiredClauseSubmissions, solver->submittedClauses());
    solver.reset(makeBackend(bm->UserFlags, false));
    solver->enableRefinement(true);
    if (trailReuseAllowed)
      solver->enableTrailReuse();
    if (inprobingRetired)
    {
      solver->disableInprobing();
      // The rest of the recurring-inprocessing tax goes with it, on the
      // same measured session class: bounded variable elimination
      // re-eliminates restored variables every solve on a churning
      // persistent encoding, and clause shrinking taxes every conflict
      // of a many-solve session (interleaved on f84c6e97: retirement
      // alone 7.7s, with elimination and shrinking retired 5.0s; the
      // deep 1ccb771c class and the small variant-push sessions
      // measured neutral).
      solver->disableEliminationAndShrinking();
    }
    if (policy.adaptiveBackendConfiguration())
      solver->disableLuckyPhases();
    bvaDecided = false;

    if (reason == RebuildReason::Relief)
      rotateEncodingEpoch();

    cnf.reset(solver.get());
    symbolMapCache.invalidate();
    // The fresh backend holds none of the abstraction's pinning clauses and
    // none of the variables they named, and its proxy constraints were
    // units that only syncAbstractions re-asserts. Forget what refinement
    // had established so that every record is taken across again -- from a
    // rotated epoch there are none left to take, and from a policy rebuild
    // the blaster still has them all.
    bvAbstraction.clear();
    harvestedEQAbstractions = 0;
    harvestedTermAbstractions = 0;
    assertedSideConstraints = 0;
    rootLitOf.clear();
    actLitOf.clear();
    everAssumedLits.clear();
    // Folding records describe readsOfEncoded from the OLD backend epoch.
    // Re-encoding can overwrite a key with a different row set (for example
    // after new permanent substitutions fold an index), so rebuild the
    // active-row view transactionally and queue every permanent key again.
    batchAT->ClearAllTables();
    lastSeededKeys.clear();
    seededRowRef.clear();
    foldedRowsOf.clear();
    clauseMassOf.clear();
    // Reclamation, not invalidation; see reclaimSymbolSets.
    walks.reclaimSymbolSets();
    refinementMassOf.clear();
    currentRefinementClauseMass = 0;
    aigRootOf.clear();
    pendingLiveCone.clear();
    activationMassOf.clear();
    baseLiveMass = 0;
    permanentAigRoots.clear();
    permanentUnitMass = 0;
    currentLiveClauseMass = 0;
    maxLiveClauseMass = 0;
    // Content screened before this rebuild must be screened again: the
    // base pass below may eliminate a variable that only popped levels
    // mention, and a re-push of such a level after the rebuild has to
    // re-assert the equation -- the memo would skip it.
    screenedContent.clear();
    restoredBaseRoots.clear();
    // Epoch-scoped, like the roots above: the eliminations below belong to
    // the epoch that recorded them, and the pass that repopulates them may
    // not run for this one. Clearing here rather than only inside the pass
    // keeps a stale claim from surviving into a fresh epoch that re-asserts
    // the raw base.
    baseEliminatedDefs.clear();

    // Every permanent raw base root is re-encoded in the fresh epoch. This
    // assignment belongs after full rotation, which releases the old
    // vector's high-water storage.
    pendingBaseSeed.assign(level0Asserted.begin(), level0Asserted.end());

    // Re-materialising the base is needed whatever ended the epoch;
    // re-SIMPLIFYING it is only worth its price when the epoch ended because
    // the encoding had grown too big. Two of the four reasons -- retiring
    // inprocessing and retiring trail reuse -- are pure SAT-backend
    // configuration latches that want a fresh solver and nothing else, and
    // running a whole-base constant-bit, equality, simplification and
    // unconstrained pass for them is unbudgeted work nobody asked for:
    // measured at 18ms for a 3,001-conjunct base of trivial constraints, and
    // it scales with the base. Promotion demotion is likewise about
    // retraction, not size.
    resimplifyBaseAtRebuild(
        assertionsSMT2,
        reason == RebuildReason::Relief && policy.semanticPreprocessing());
  }

  // A forced base-only first solve has no earlier batch round to simplify its
  // complete permanent formula. Pure Boolean literals are a particularly
  // cheap part of that missing work, and the Goel hardware family consists of
  // thousands of clauses which this pass reduces to TRUE. This is deliberately
  // narrower than the rejected recurring base-preprocessing prototype: it
  // runs once, only before any driver clause exists, and only for array/FP-free
  // base content. A later assertion which mentions a chosen literal restores
  // every original base conjunct that used it through screenNewContent().
  bool preprocessForcedFirstBase(const ASTVec& rawBase, ASTVec& toEncode)
  {
    toEncode = rawBase;
    if (rawBase.empty() || !bm->UserFlags.optimize_flag ||
        !bm->UserFlags.enable_pure_literals)
      return false;

    for (const ASTNode& c : rawBase)
    {
      const Fragment& f = fragment(c);
      if (f.arrays || f.arrayEq || f.fp)
        return false;
    }

    ASTVec ordered = rawBase;
    std::sort(ordered.begin(), ordered.end());
    ASTNode out = ordered.size() == 1
                      ? ordered[0]
                      : bm->defaultNodeFactory->CreateNode(AND, ordered);
    PreprocessingTransaction transaction(PreprocessingMode::PermanentBase,
                                         out);

    SubstitutionMap passSm(bm);
    Simplifier pass(bm, &passSm);
    FindPureLiterals pure;
    if (!pure.topLevel(out, &pass, bm))
      return false;
    out = pass.applySubstitutionMapAtTopLevel(out);

    DenseNodeMap* defs = pass.Return_SolverMap();
    std::map<ASTNode, size_t> eliminationIndex;
    for (DenseNodeMap::const_iterator it = defs->begin(); it != defs->end();
         ++it)
    {
      if (it->first.GetKind() != SYMBOL ||
          it->first.GetType() != BOOLEAN_TYPE)
        continue;
      eliminationIndex[it->first] = transaction.eliminated.size();
      transaction.addElimination(it->first, it->second, true);
    }
    if (transaction.eliminated.empty())
      return false;

    // The raw base was screened before these eliminations existed. Any
    // original saved as a witness must be eligible for a fresh recursive
    // screen when one eliminated variable brings it back, so its other
    // eliminated variables are restored at the same time.
    for (const ASTNode& c : ordered)
    {
      bool saved = false;
      for (const ASTNode& s : symbolsOf(c))
      {
        std::map<ASTNode, size_t>::const_iterator e =
            eliminationIndex.find(s);
        if (e == eliminationIndex.end())
          continue;
        transaction.eliminated[e->second].originals.push_back(c);
        saved = true;
      }
      if (saved)
        screenedContent.erase(c);
    }

    splitConjuncts(out, bm->ASTTrue, transaction.conjuncts);

    // Commit the transformed formula and every witness replay together.
    // Before this point the trial has made no persistent semantic change.
    for (const ScopedElimination& e : transaction.eliminated)
      baseEliminatedDefs[e.symbol] = e;
    toEncode = transaction.conjuncts;
    if (profile.enabled)
    {
      profile.basePreprocesses++;
      profile.baseEliminations += transaction.eliminated.size();
    }
    if (bm->UserFlags.stats_flag)
      std::cerr << "Incremental: first base pure-literal pass, "
                << ordered.size() << " conjuncts -> " << toEncode.size()
                << ", " << transaction.eliminated.size() << " eliminated"
                << std::endl;
    return true;
  }

  // The rebuild boundary is the one place a GLOBAL pass over the base is
  // both sound and free: everything re-encodes from scratch anyway, so
  // novel rewritten forms forfeit no bit-blast sharing, and the base
  // never retracts, so cross-conjunct rewriting inside it carries no
  // retraction hazard -- this is the whole-formula constant propagation
  // and unconstrained-variable elimination the driver otherwise forgoes
  // per query. Pushed levels stay out of it: their symbols form the
  // untouchable set, and their content is prepared per level as always.
  // level0Asserted deliberately keeps its RAW keys, so the per-solve
  // base loop keeps skipping conjuncts the pass already covers; the
  // simplified replacements wait in pendingRebuiltBase for the encoding
  // point after the backend's configuration window is decided.
  void resimplifyBaseAtRebuild(const ASTVec& assertionsSMT2, bool simplify)
  {
    pendingRebuiltBase.clear();
    if (level0Asserted.empty())
      return;

    // Raw base conjuncts, in deterministic order.
    ASTVec base(level0Asserted.begin(), level0Asserted.end());
    std::sort(base.begin(), base.end());
    for (const ASTNode& c : base)
      pendingRebuiltBase.push_back(c);

    if (!simplify || !bm->UserFlags.optimize_flag)
      return;
    // Arrays keep the historical per-conjunct path: eliminating within
    // an array-carrying base would put reads into the replay channel the
    // refinement loop evaluates. An active extensionality session
    // likewise keeps its own choreography.
    ExtensionalityContext* ext = bm->getExtensionalityIfAny();
    if (ext != NULL)
      return;
    for (const ASTNode& c : base)
    {
      const Fragment& f = fragment(c);
      if (f.arrays || f.arrayEq)
        return;
    }

    ASTNode conj = base.size() == 1
                       ? base[0]
                       : bm->defaultNodeFactory->CreateNode(AND, base);
    PreprocessingTransaction transaction(PreprocessingMode::PermanentBase,
                                         conj);

    // Budget it. This is the same PropagateEqualities + applySubstitutionMap
    // + constant-bit propagation the trial path runs, and the trial path is
    // gated on cost; here it was not gated at all, and the rebuild it belongs
    // to has no budget of its own either. Measured at 9.4 s on a
    // 23,294-conjunct base -- a base that size is exactly the one the pass
    // cannot digest, and skipping it re-encodes the raw base, which is the
    // path an array base and the three non-size rebuild reasons already take.
    // Measure the conjunction, not the sum over conjuncts: base conjuncts
    // share structure, and summing their sizes bills a shared cone once per
    // conjunct that mentions it.
    const int64_t configuredLimit =
        bm->UserFlags.incremental_base_resimplify_limit;
    const size_t resimplifyLimit =
        configuredLimit < 0 ? 0 : static_cast<size_t>(configuredLimit);
    if (dagSizeUpToBigMemo(conj, resimplifyLimit) > resimplifyLimit)
    {
      if (bm->UserFlags.stats_flag)
        std::cerr << "Incremental: base re-simplification skipped (base over "
                  << resimplifyLimit << " nodes)" << std::endl;
      return;
    }

    // This pass re-derives the complete raw base. Discard witness/model
    // choices made by an earlier backend epoch; anything still eliminable is
    // recorded again below, while anything retained now gets real SAT bits.
    baseEliminatedDefs.clear();

    if (fragment(conj).fp)
      conj = fpContext()->prepare(conj);

    // Symbols any live pushed level mentions are constrained outside the
    // base; the pass must treat them as opaque.
    std::set<ASTNode> untouch;
    for (size_t level = 1; level < assertionsSMT2.size(); level++)
    {
      const ASTNodeSet& syms = symbolsOf(assertionsSMT2[level]);
      untouch.insert(syms.begin(), syms.end());
    }

    SubstitutionMap passSm(bm);
    Simplifier pass(bm, &passSm);
    ASTNode out = conj;
    if (bm->UserFlags.propagate_equalities)
    {
      PropagateEqualities pe(&pass, bm->defaultNodeFactory, bm);
      out = pe.topLevel(out);
    }
    if (pass.hasUnappliedSubstitutions())
      out = pass.applySubstitutionMap(out);
    // Whole-conjunction constant-bit propagation, exactly as the batch
    // pipeline runs it. The rebuild boundary is the one place its
    // assume-the-top-is-true discipline is free of retraction hazards:
    // the base is permanent, so every derived constant is a permanent
    // truth, and everything re-encodes from scratch anyway so the novel
    // rewritten forms forfeit no bit-blast sharing. Symbol fixings land
    // in the pass's substitution map, where the implied/witness split
    // below records them for the model exactly like the equality
    // harvest's; interior fixings ride the returned formula with their
    // pinning facts conjoined.
    if (bm->UserFlags.bitConstantProp_flag)
    {
      simplifier::constantBitP::ConstantBitPropagation cbp(
          bm, &pass, bm->defaultNodeFactory, out);
      out = cbp.topLevelBothWays(out, true, true);
      if (cbp.isUnsatisfiable())
        out = bm->ASTFalse;
    }
    out = pass.SimplifyFormula_TopLevel(out, false);
    // Apply what the passes above harvested before the unconstrained pass
    // looks at the formula, as the batch prefix does (`STP.cpp:676-677`) and
    // as the exact-stack block does (`applySubstitutionMapAtTopLevel`, below).
    // This pass was the only one of the four without it. Constant-bit
    // propagation puts SYMBOL fixings ONLY into the substitution map, never
    // into the rewrite it applies to the formula, and
    // SimplifyFormula_TopLevel is not a reliable substitute because
    // `is_simplified` is a permanent node flag and the driver marks base
    // conjuncts simplified when they are asserted. What covers the gap today
    // is RemoveUnconstrained applying the same map itself -- an internal
    // detail of the callee, which `--unconstrained-variable-elimination 0`
    // removes entirely.
    //
    // Be precise about the evidence: this is symmetry and defence, not a
    // demonstrated fix. Removing this line and running the relief corpus with
    // that flag off does NOT trip the assert below, so no case is in hand
    // where its absence breaks the invariant. It is here because this pass was
    // the only one of the four without it, and being the odd one out with
    // nobody checking is exactly how D14 happened; the cost is one DAG walk
    // on a path that fires rarely. The plain
    // variant, not AtTopLevel, exactly as batch does: AtTopLevel advances
    // `substitutionsLastApplied`, and the split below still needs to see
    // every entry.
    if (pass.hasUnappliedSubstitutions())
      out = pass.applySubstitutionMap(out);
    // Definitions recorded up to here are implied equations; whatever
    // the unconstrained-variable pass adds after this point is a witness
    // choice (see BaseElimination).
    ASTNodeSet impliedKeys;
    for (DenseNodeMap::const_iterator it = pass.Return_SolverMap()->begin();
         it != pass.Return_SolverMap()->end(); ++it)
      impliedKeys.insert(it->first);
    // Close the untouchable set under the substitution map's right-hand
    // sides before the unconstrained pass runs. A pushed level's symbol is
    // untouchable because that level constrains it from outside the base;
    // once this pass has harvested `k -> d`, k's value comes from d, so
    // every symbol of d carries exactly the weight k did.
    //
    // RemoveUnconstrained decides from the FORMULA alone, and by this point
    // a symbol's only surviving occurrence can be inside a map VALUE, which
    // is invisible to it. It then drops that symbol's last conjunct and
    // records a witness for it, while the loop below keeps the definition
    // that mentions it -- because the definition's own variable is
    // untouchable. The kept equation is now free to take any value, so the
    // rebuilt base is strictly WEAKER than the raw base it replaced, and the
    // pushed level that made the variable untouchable answers sat on an
    // unsat query. A symbol added here can itself be a map key, so this runs
    // to a fixpoint.
    if (!untouch.empty())
    {
      bool grew = true;
      while (grew)
      {
        grew = false;
        for (DenseNodeMap::const_iterator it = pass.Return_SolverMap()->begin();
             it != pass.Return_SolverMap()->end(); ++it)
        {
          if (untouch.find(it->first) == untouch.end())
            continue;
          for (const ASTNode& s : symbolsOf(it->second))
            if (untouch.insert(s).second)
              grew = true;
        }
      }
    }
    if (bm->UserFlags.enable_unconstrained)
    {
      RemoveUnconstrained ru(*bm);
      out = ru.topLevel(out, &pass, &untouch);
    }

    // Split the harvested definitions exactly as piece preparation does:
    // a variable a live pushed level mentions keeps its equation
    // asserted; everything else is a PERMANENT elimination with model
    // replay, restored by screening if future content mentions it.
    ASTVec keep;
    DenseNodeMap* defs = pass.Return_SolverMap();
    std::map<ASTNode, size_t> eliminationIndex;
    for (DenseNodeMap::const_iterator it = defs->begin(); it != defs->end();
         ++it)
    {
      const ASTNode& var = it->first;
      const ASTNode& def = it->second;
      // The array gate at the top of this pass is what makes these
      // eliminations replayable without the piece path's array-body
      // refusal: an array-free base cannot harvest a read-carrying
      // definition. Stated here, where the elimination is recorded,
      // so a future relaxation of that gate fails by name.
      assert(!containsArrayOps(def, bm) &&
             "the base re-simplification gate admitted an array-carrying "
             "definition");
      if (var.GetKind() != SYMBOL || var.GetIndexWidth() != 0 ||
          untouch.find(var) != untouch.end())
      {
        keep.push_back(definitionEquation(var, def));
        continue;
      }
      eliminationIndex[var] = transaction.eliminated.size();
      transaction.addElimination(
          var, def, impliedKeys.find(var) == impliedKeys.end());
    }
    // Witness eliminations restore their original conjuncts on mention.
    for (const ASTNode& rc : base)
    {
      for (const ASTNode& s : symbolsOf(rc))
      {
        std::map<ASTNode, size_t>::const_iterator eit =
            eliminationIndex.find(s);
        if (eit != eliminationIndex.end() &&
            transaction.eliminated[eit->second].witness)
          transaction.eliminated[eit->second].originals.push_back(rc);
      }
    }
    if (!keep.empty())
    {
      keep.push_back(out);
      out = bm->defaultNodeFactory->CreateNode(AND, keep);
    }

    splitConjuncts(out, bm->ASTTrue, transaction.conjuncts);

    // Commit both halves of the permanent-base transformation together.
    // The fresh backend cannot observe a transformed formula without the
    // corresponding model/restoration definitions, or vice versa.
    baseEliminatedDefs.clear();
    for (const ScopedElimination& e : transaction.eliminated)
      baseEliminatedDefs[e.symbol] = e;
    pendingRebuiltBase = transaction.conjuncts;

#ifndef NDEBUG
    // The same invariant preparePiece asserts over its own output: a variable
    // recorded as eliminated must not still be mentioned by anything this
    // pass emits, or the base carries live backend bits for a symbol whose
    // only remaining definition is model-only metadata.
    //
    // This pass is the one that had neither the assert nor an argument, and
    // the gap was D14 -- a kept definition naming a variable whose last
    // constraint RemoveUnconstrained had just dropped, giving a base strictly
    // weaker than the raw one. It holds now because `untouch` is closed under
    // the map's right-hand sides above, and because the apply above puts the
    // harvested rewrites into the formula rather than relying on the
    // unconstrained pass to do it.
    for (std::map<ASTNode, BaseElimination>::const_iterator eit =
             baseEliminatedDefs.begin();
         eit != baseEliminatedDefs.end(); ++eit)
      for (const ASTNode& c : pendingRebuiltBase)
        assert(symbolsOf(c).find(eit->first) == symbolsOf(c).end() &&
               "rebuilt base mentions a variable this pass eliminated");
#endif

    if (bm->UserFlags.stats_flag)
      std::cerr << "Incremental: base re-simplified at rebuild, "
                << base.size() << " conjuncts -> " << pendingRebuiltBase.size()
                << ", " << transaction.eliminated.size() << " eliminated"
                << std::endl;
  }

  // What one run of the scoped block pass produced, so a repeated stack does
  // not run it again -- and, more importantly, does not get a DIFFERENT
  // answer when it does.
  //
  // The pass is not a function of its input node: RemoveUnconstrained names
  // its stand-in variables from a counter, so whenever one survives into the
  // output an identical re-pushed stack lowers to a fresh node, misses the
  // block cache keyed on that node, and re-encodes the whole formula. That is
  // unbounded growth on exactly the repeat-a-query workload this path exists
  // for, and it silently contradicts the reuse the design promises. Memoising
  // by input node restores the function property; the eliminations are
  // recorded alongside because they are the only other thing the pass emits,
  // and they are per-solve state that must be replayed on a hit.
  std::map<std::pair<ASTNode, bool>, PreprocessingTransaction> scopedBlockOf;

  // The exact-stack path encodes the COMPLETE active stack as one
  // assumption-guarded block. Whole-formula simplification is therefore
  // scoped to exactly the same lifetime as the block: unlike ordinary
  // per-level encodings, a fact from a deeper level cannot leak into a root
  // which survives its pop. Reproduce the high-yield, model-replay-capable
  // prefix of the batch size-reducing pipeline before array transformation.
  PreprocessingTransaction
  preprocessExactStackBlock(const ASTNode& input,
                            bool requireCollapse = false);

  // The batch pipeline's bounded-variable-addition policy, applied to the
  // persistent solver (see TopLevelSTPAux): an explicit ON always asks,
  // AUTO asks only for array problems, and the answer must land inside the
  // backend's configuration window, which closes at its first clause. Here
  // that window is the start of the first engaged check-sat -- and it
  // reopens when the relief valve rebuilds the solver, which is why
  // rebuildEncodings resets the flag. AUTO judges the levels' prepared
  // fragments, so arrays that only appear after floating-point
  // totalisation count, as they do in batch, and whole-array equality
  // counts through the fragment it lowers into reads; the persistent read
  // registry keeps the answer stable across a rebuild whose live stack
  // happens to be array-free at that moment. Under --ackermanize arrays
  // never reach the solver as arrays, so AUTO stays off, as in batch.
  void decideBVA(const ASTVec& assertionsSMT2)
  {
    if (bvaDecided)
      return;
    bvaDecided = true;

    const UserDefinedFlags& uf = bm->UserFlags;
    bool wants = uf.cadical_factor == UserDefinedFlags::BVAMode::ON;
    if (policy.adaptiveBackendConfiguration() &&
        uf.cadical_factor == UserDefinedFlags::BVAMode::AUTO &&
        !uf.ackermannisation)
    {
      wants = !arrayRegistry.reads.empty();
      for (size_t i = 0; !wants && i < assertionsSMT2.size(); i++)
      {
        const Fragment& f = fragment(assertionsSMT2[i]);
        wants = f.arrays || f.arrayEq;
      }
    }

    if (enableBVAIfWanted(*solver, uf, wants, !bvaWarned))
      bvaWarned = true;
  }

  // The literal to assume for one pushed level, given the level's root
  // literals: the root itself for a single conjunct, else the (possibly
  // cached) activation literal that implies them all.
  int levelAssumption(std::vector<int>& roots)
  {
    assert(!roots.empty());
    if (roots.size() == 1)
      return roots[0];

    std::sort(roots.begin(), roots.end());
    roots.erase(std::unique(roots.begin(), roots.end()), roots.end());
    if (roots.size() == 1)
      return roots[0];

    std::map<std::vector<int>, ActLitEntry>::iterator it =
        actLitOf.find(roots);
    if (it != actLitOf.end())
    {
      it->second.lastUsed = engagedSolves;
      return it->second.lit;
    }

    // Stored and returned as a LITERAL (2*var), like everything else in
    // this file -- a cache hit that handed back the bare variable was a
    // garbage assumption that left the whole level unconstrained.
    const int act = solver->newVar();
    for (const int root : roots)
      addBinary(2 * act + 1, root);
    const int actLit = 2 * act;
    ActLitEntry& entry = actLitOf[roots];
    entry.lit = actLit;
    entry.lastUsed = engagedSolves;
    activationMassOf[actLit] = roots.size();
    return actLit;
  }

  // A variable eliminated before it was ever encoded has no SAT bits; its
  // value is its definition, evaluated recursively -- the same SolverMap
  // channel the batch pipeline's eliminations use (and which the batch
  // pipeline clears before every solve of its own). Only never-encoded
  // variables are seeded: an encoded one gets its value from its bits.
  void seedEliminatedIntoModelChannel()
  {
    DenseNodeMap* channel = batchSimp->Return_SolverMap();
    // Everything this driver ever seeded is withdrawn first: the channel
    // is never cleared between solves (the batch pipeline owns entries of
    // its own in it), and a definition eliminated under a POPPED branch
    // is not merely dead weight -- insert() does not overwrite, so a
    // stale x -> FALSE from a retracted level would shadow this solve's
    // x -> TRUE, the model check would read the popped value, declare
    // every candidate bogus, and the refinement loop would spin forever
    // finding no violated axiom to add.
    for (const ASTNode& k : seededModelKeys)
      channel->erase(k);
    seededModelKeys.clear();

    for (ASTNodeMap::const_iterator it = sigma0.begin(); it != sigma0.end();
         ++it)
    {
      if (encoding.nodes().symbolToBBNode.find(it->first) ==
          encoding.nodes().symbolToBBNode.end())
      {
        (*channel)[it->first] = it->second;
        seededModelKeys.insert(it->first);
      }
    }
    // The elimination replay: definitions the current solve's prepared
    // levels eliminated get their model values by evaluation, exactly as
    // sigma0-eliminated variables always have. These are seeded even if an
    // older block bit-blasted the same symbol: buildSymbolMap deliberately
    // omits active eliminations below, so the scoped definition wins.
    for (const ScopedElimination& d : scopes.activeEliminations())
    {
      (*channel)[d.symbol] = d.value;
      seededModelKeys.insert(d.symbol);
    }
    // Base variables the rebuild-boundary pass eliminated: seeded
    // unconditionally -- their pre-rebuild bits survive in the blast
    // memo but are no longer encoded in the fresh solver, so the
    // symbolToBBNode test above would wrongly trust them. When a symbol
    // is re-encoded for real, its SAT bits overwrite the copied entry
    // during model construction, so an over-seed is harmless.
    for (std::map<ASTNode, BaseElimination>::const_iterator it =
             baseEliminatedDefs.begin();
         it != baseEliminatedDefs.end(); ++it)
    {
      (*channel)[it->first] = it->second.value;
      seededModelKeys.insert(it->first);
    }
  }

  // ── Bit-vector abstraction ownership ─────────────────────────────────

  // The SAT variable of an abstraction's own combinational input, named by
  // the index the blaster recorded. The input sits in the cone of whatever
  // conjunct it replaced an operation in, so it is normally already
  // encoded; encoding it here as well costs nothing and covers the case
  // where a later simplification kept the record but not the cone.
  unsigned abstractionVarOf(int ciSymbolIndex)
  {
    Aig_Obj_t* ci = (Aig_Obj_t*)Vec_PtrEntry(
        encoding.nodes().aigMgr->vCis, ciSymbolIndex);
    ensureEncoded(ci);
    return (unsigned)varOfAig(ci);
  }

  // Take across everything the blaster has produced since the last call:
  // the operand proxies' defining constraints, and the abstraction records
  // themselves. Called once per solve, after all of this call's encoding
  // and before the search, so it covers every route's bit-blasting without
  // each route having to know about it.
  //
  // Unlike the batch lowering, no freezeVariables() pass follows: every
  // backend makeBackend admits either restores an eliminated variable the
  // moment a clause mentions it (CaDiCaL) or never eliminates one (plain
  // MiniSat), and the one family that can take neither back -- the
  // simplifying MiniSat -- makeBackend refuses for this driver.
  void syncAbstractions()
  {
    BitBlaster& bb = encoding.blaster();

    // An abstraction reads its operands through proxy inputs, tied to the
    // real bits by one biconditional each -- the blaster mints them
    // because the bits themselves need not be inputs, and refinement can
    // only write clauses over variables. The batch lowering conjoins those
    // biconditionals into the formula it blasts; here they are permanent
    // units, which says the same thing: each defines a fresh variable that
    // nothing else mentions, so it constrains no assignment of the query.
    // Dropped, as they were, the proxies stand for nothing and every
    // operand the refinement reads through one is noise.
    const std::vector<BBNodeAIG>& side = bb.sideConstraints();
    for (; assertedSideConstraints < side.size(); assertedSideConstraints++)
    {
      const BBNodeAIG& sc = side[assertedSideConstraints];
      Aig_Obj_t* regular = Aig_Regular(sc.n);
      ensureEncoded(regular);
      const int lit =
          2 * varOfAig(regular) + (Aig_IsComplement(sc.n) ? 1 : 0);
      SATSolver::vec_literals unit;
      unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
      addClause(unit);
      permanentAigRoots.push_back(regular);
      permanentUnitMass = addMass(permanentUnitMass, 1);
    }

    const std::vector<BitBlaster::RawBVEQAbstraction>& rawEQs =
        bb.abstractedEQs();
    for (; harvestedEQAbstractions < rawEQs.size(); harvestedEQAbstractions++)
    {
      const BitBlaster::RawBVEQAbstraction& raw =
          rawEQs[harvestedEQAbstractions];
      BVEQAbstraction a;
      a.eqNode = raw.eqNode;
      a.abstractionSATVar = abstractionVarOf(raw.abstractionCI.symbol_index);
      a.leftSymbol = raw.leftSymbol;
      a.rightSymbol = raw.rightSymbol;
      a.width = std::max(1u, raw.leftSymbol.GetValueWidth());
      encodeAbstractionNode(a.leftSymbol);
      encodeAbstractionNode(a.rightSymbol);
      bvAbstraction.equalities().push_back(std::move(a));
    }

    const std::vector<BitBlaster::RawBVTermAbstraction>& rawTerms =
        bb.abstractedTerms();
    for (; harvestedTermAbstractions < rawTerms.size();
         harvestedTermAbstractions++)
    {
      const BitBlaster::RawBVTermAbstraction& raw =
          rawTerms[harvestedTermAbstractions];
      BVTermAbstraction a;
      a.termNode = raw.termNode;
      a.opKind = raw.opKind;
      for (unsigned i = 0; i < raw.numOperands; i++)
      {
        a.operands[i] = raw.operands[i];
        a.operandNegated[i] = raw.operandNegated[i];
        encodeAbstractionNode(a.operands[i]);
      }
      a.numOperands = raw.numOperands;
      a.width = raw.width;
      if (raw.condCISymbolIndex >= 0)
        a.condSATVar = abstractionVarOf(raw.condCISymbolIndex);
      encodeAbstractionNode(a.termNode);
      bvAbstraction.terms().push_back(std::move(a));
    }
  }

  // Every bit a record can be checked against gets its SAT variable here,
  // BEFORE the solve whose candidate the check will read. Encoding them on
  // demand at refinement time -- which is when the operand map used to
  // first touch them -- minted variables the solve just finished had never
  // assigned: an abstracted operand or result whose cone reaches no clause
  // (a symbol that occurs only under an abstracted equality, say) has
  // perfectly valid AIG bits and no CNF presence at all. A backend without
  // a default answer for such a read answers from garbage -- MiniSat
  // indexes its model out of bounds -- and a candidate certified against
  // garbage published a model the raw stack refutes. Encoded up front, the
  // variables are decision variables like any other: the search assigns
  // them, the scan reads what the search chose, and the same variables are
  // what the model channel later publishes.
  void encodeAbstractionNode(const ASTNode& n)
  {
    if (n.IsNull())
      return;
    BBNodeManagerAIG::SymbolToBBNode::const_iterator it =
        encoding.nodes().symbolToBBNode.find(n);
    if (it == encoding.nodes().symbolToBBNode.end())
      return; // a constant the record folds in; the scan reads its bits
    for (const BBNodeAIG& bit : it->second)
      if (!bit.IsNull())
        ensureEncoded(Aig_Regular(bit.n));
  }

  // One node's bits, for the refinement's use. Deliberately not through
  // buildSymbolMap: that is the model channel's view and drops scoped
  // eliminations and popped content, while a refinement clause is a
  // statement about the circuit -- this abstraction variable means these
  // AIG bits -- and is true of it whatever else is asserted. Every bit is
  // given a variable, since a clause written over one that never reached
  // the solver would name a variable that does not exist.
  void addAbstractionOperand(ToSATBase::ASTNodeToSATVar& out,
                             const ASTNode& n)
  {
    if (n.IsNull() || out.find(n) != out.end())
      return;
    BBNodeManagerAIG::SymbolToBBNode::const_iterator it =
        encoding.nodes().symbolToBBNode.find(n);
    if (it == encoding.nodes().symbolToBBNode.end())
      return;
    const std::vector<BBNodeAIG>& bits = it->second;
    std::vector<unsigned> vars(bits.size(), ~((unsigned)0));
    for (size_t i = 0; i < bits.size(); i++)
    {
      if (bits[i].IsNull())
        continue;
      Aig_Obj_t* regular = Aig_Regular(bits[i].n);
      ensureEncoded(regular);
      vars[i] = (unsigned)varOfAig(regular);
    }
    out.insert(std::make_pair(n, vars));
  }

  // Check the candidate the solver is holding against every abstraction and
  // pin the ones it contradicts; the count is how many were pinned, so zero
  // means the candidate is faithful and may be handed on.
  unsigned refineAbstractions(SATSolver& satSolver)
  {
    if (bvAbstraction.empty())
      return 0;
    ToSATBase::ASTNodeToSATVar operands;
    for (const BVEQAbstraction& a : bvAbstraction.equalities())
    {
      addAbstractionOperand(operands, a.leftSymbol);
      addAbstractionOperand(operands, a.rightSymbol);
    }
    for (const BVTermAbstraction& a : bvAbstraction.terms())
    {
      addAbstractionOperand(operands, a.termNode);
      for (unsigned i = 0; i < a.numOperands; i++)
        addAbstractionOperand(operands, a.operands[i]);
    }
    return bvAbstraction.refine(satSolver, operands);
  }

  // Values for every symbol the persistent encoding knows about. Symbols
  // from popped scopes are included -- their SAT variables are merely
  // unconstrained -- which the model printers tolerate (they iterate the
  // currently declared symbols, not this map). The refinement tables do
  // NOT tolerate them: seedActiveReads keeps popped rows away from model
  // construction and the congruence check.
  void buildSymbolMap(ToSATBase::ASTNodeToSATVar& out)
  {
    for (BBNodeManagerAIG::SymbolToBBNode::const_iterator it =
             encoding.nodes().symbolToBBNode.begin();
         it != encoding.nodes().symbolToBBNode.end(); ++it)
    {
      if (scopes.activeEliminatedVariables().find(it->first) !=
          scopes.activeEliminatedVariables().end())
        continue;
      // A dropped base definition's variable must never have been blasted:
      // restoreDroppedSigma0 re-asserts the equation before any raw route
      // may encode it, and relief destroys this memo when it re-drops. Bits
      // here without the equation would feed models and the refinement
      // loop's raw-stack evaluation from unconstrained values. This is the
      // one funnel every model and refinement read passes through, so a
      // future encode route that bypasses the restore guard fails here by
      // name instead of answering from garbage.
      assert(sigma0Dropped.find(it->first) == sigma0Dropped.end() &&
             "a dropped base definition's variable was bit-blasted");
      const vector<BBNodeAIG>& bits = it->second;
      vector<unsigned> vars(bits.size(), ~((unsigned)0));
      bool anyLive = false;
      for (size_t i = 0; i < bits.size(); i++)
      {
        if (bits[i].IsNull())
          continue;
        const int v = varOfAig(Aig_Regular(bits[i].n));
        if (v != -1)
        {
          vars[i] = (unsigned)v;
          anyLive = true;
        }
      }
      // A symbol whose every bit is unencoded in the CURRENT solver is
      // indistinguishable from one never blasted at all -- its memo
      // entry is a leftover from before a rebuild -- and reporting it
      // with all-missing bits would have counterexample construction
      // default it to zero, SHADOWING the model-channel seed of a
      // definition the rebuild pass eliminated. (Reachable since the
      // rebuild pass gained constant-bit propagation: that is the first
      // harvest that can eliminate a symbol AFTER it has been blasted;
      // the equality harvests always caught theirs before any encode.)
      if (!anyLive)
        continue;
      out.insert(std::make_pair(it->first, vars));
    }
  }

  // One ordinary read-refinement round under its no-progress guard.
  // getEquals creates a fresh comparison circuit even for an axiom the
  // solver already holds, so clause and variable counts are not logical
  // progress; the check-local transaction suppresses that re-encoding,
  // and an undecided round must therefore have claimed at least one
  // genuinely NEW congruence axiom, or the encoding and the model
  // evaluation disagree. `stuck` states the failure in the caller's
  // route's terms.
  SOLVER_RETURN_TYPE
  runGuardedReadRefinementRound(const ASTNode& semanticRoot, ToSATBase* tosat,
                                ArrayReadRefinementProgress& progress,
                                const char* stuck)
  {
    const size_t emittedBefore = progress.emittedAxiomCount();
    const SOLVER_RETURN_TYPE res =
        ce->SATBased_ArrayReadRefinement(*solver, semanticRoot, tosat,
                                         &progress);
    if (res == SOLVER_UNDECIDED &&
        progress.emittedAxiomCount() == emittedBefore)
      FatalError(stuck);
    return res;
  }

  // Check the RAW per-level assertions against the freshly constructed
  // model, not only the prepared/encoded forms: scoped eliminations are
  // replayed through the model channel, so this also guards the
  // preprocessing/model-reconstruction boundary. GetCounterExample
  // answers ASTUndefined while ValidFlag claims the last query was
  // unsat, and at this point that flag still describes the PREVIOUS
  // query, so it is cleared before evaluating.
  void checkModelSatisfiesRawStack(const ASTVec& assertionsSMT2)
  {
    bm->ValidFlag = false;
    ASTVec conjuncts;
    for (const ASTNode& levelConjunction : assertionsSMT2)
    {
      conjuncts.clear();
      splitConjuncts(levelConjunction, bm->ASTTrue, conjuncts);
      for (const ASTNode& c : conjuncts)
      {
        if (ce->GetCounterExample(c) != bm->ASTTrue)
          FatalError("IncrementalSolver: the model does not satisfy an "
                     "asserted formula",
                     c);
      }
    }
  }
};

// The ToSATBase the refinement machinery drives. Everything is already
// encoded and axioms arrive as direct clauses, so CallSAT only ever needs
// to re-solve -- under the check-sat's captured assumptions, which is what
// keeps refinement lemmas permanent while retractable assertions stay
// retractable.
class IncrementalToSAT : public ToSATBase
{
  IncrementalSolver::Impl* d;
  const SATSolver::vec_literals* assumps;

public:
  IncrementalToSAT(STPMgr* bm, IncrementalSolver::Impl* d_)
      : ToSATBase(bm), d(d_), assumps(NULL)
  {
  }

  void setAssumptions(const SATSolver::vec_literals* a) { assumps = a; }

  bool CallSAT(SATSolver& SatSolver, const ASTNode& input,
               bool /*doesAbsRef*/) override
  {
    // The refinement protocol passes ASTTrue: "the clauses are already in
    // the solver, search again".
    assert(input == ASTTrue);
    (void)input;

    const bool refinementSolve = d->profile.satCalls > 0;
    if (d->profile.enabled)
    {
      if (refinementSolve)
        d->profile.refinementSatCalls++;
      d->profile.satCalls++;
    }
    ScopedProfileTimer satTimer(d->profile.enabled, d->profile.satNs);
    uint64_t& phaseSatNs =
        refinementSolve ? d->profile.refinementSatNs : d->profile.initialSatNs;
    ScopedProfileTimer phaseSatTimer(d->profile.enabled, phaseSatNs);
    bm->GetRunTimes()->start(RunTimes::Solving);
    bool sat;
    if (assumps != NULL && assumps->size() > 0)
      sat = SatSolver.solveWithAssumptions(*assumps, bm->soft_timeout_expired);
    else
      sat = SatSolver.solve(bm->soft_timeout_expired);
    bm->GetRunTimes()->stop(RunTimes::Solving);
    // The refinement rounds, which give up through CallSAT_ResultCheck rather
    // than through the driver's own check. Same reason as there: the reason
    // is only knowable here. The first round to run out is the one that names
    // the budget, which is why noteBudgetExhausted keeps an earlier answer.
    if (bm->soft_timeout_expired)
      bm->noteBudgetExhausted(SatSolver);
    return sat;
  }

  unsigned refineAbstractions(SATSolver& SatSolver) override
  {
    return d->refineAbstractions(SatSolver);
  }

  uint64_t abstractionRefinements() const override
  {
    return d->bvAbstraction.refinements();
  }

  ASTNodeToSATVar& SATVar_to_SymbolIndexMap() override
  {
    IncrementalSymbolMapCache& cache = d->symbolMapCache;
    if (!cache.validFor(d->cnf.generation()))
    {
      cache.storage().clear();
      d->buildSymbolMap(cache.storage());
      cache.markCurrent(d->cnf.generation());
    }
    return cache.storage();
  }

  void ClearAllTables(void) override {}
};

inline ToSATBase* IncrementalSolver::Impl::ensureAdapter()
{
  if (!adapter)
    adapter.reset(new IncrementalToSAT(bm, this));
  return adapter.get();
}

} // namespace stp

#endif

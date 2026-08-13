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

#include "stp/Incremental/IncrementalSolver.h"

#include "stp/Incremental/IncrementalCBP.h"
#include "stp/Incremental/IncrementalPolicy.h"
#include "stp/Incremental/IncrementalScopeState.h"

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
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace stp
{

namespace
{

using ProfileClock = std::chrono::steady_clock;

class ScopedProfileTimer
{
  uint64_t* elapsed;
  ProfileClock::time_point started;

public:
  ScopedProfileTimer(bool enabled, uint64_t& elapsed_)
      : elapsed(enabled ? &elapsed_ : NULL)
  {
    if (elapsed != NULL)
      started = ProfileClock::now();
  }

  void retarget(bool enabled, uint64_t& elapsed_)
  {
    if (enabled)
    {
      assert(elapsed != NULL);
      elapsed = &elapsed_;
    }
  }

  ~ScopedProfileTimer()
  {
    if (elapsed == NULL)
      return;
    *elapsed += std::chrono::duration_cast<std::chrono::nanoseconds>(
                    ProfileClock::now() - started)
                    .count();
  }

  ScopedProfileTimer(const ScopedProfileTimer&) = delete;
  ScopedProfileTimer& operator=(const ScopedProfileTimer&) = delete;
};

// Narrow a configured limit to what an index type can hold. The clamp is
// vacuous where size_t is 64 bits wide and load-bearing where it is 32 --
// STP builds and tests an i386 leg -- so it goes through std::min rather
// than an explicit comparison that one of the two platforms can prove is
// always false.
size_t clampToSize(const uint64_t value)
{
  return static_cast<size_t>(
      std::min<uint64_t>(value, std::numeric_limits<size_t>::max()));
}

uint64_t profileMicros(uint64_t nanoseconds)
{
  return nanoseconds / 1000;
}

// Whether the result of this check-sat must leave a caller-visible model.
// Theory refinement may need a candidate model internally even when this is
// false; keeping the two requirements separate prevents an internal round
// from either latching model production on or restoring a stale value from a
// previous query.
bool observableModelRequested(const UserDefinedFlags& uf)
{
  bool requested = uf.check_counterexample_flag ||
                   uf.print_counterexample_flag || uf.produce_models ||
                   uf.request_counterexample;
#ifndef NDEBUG
  requested = true;
#endif
  return requested;
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
SATSolver* makeBackend(UserDefinedFlags& uf, bool warn)
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
  if (uf.search_bias != SearchBias::NONE &&
      !s->setSearchBias(uf.search_bias) && warn)
  {
    std::cerr << "Warning: the SAT solver in use has no '"
              << searchBiasName(uf.search_bias)
              << "' search bias to select; using its own settings instead."
              << std::endl;
  }
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
void splitConjuncts(const ASTNode& n, const ASTNode& trueNode, ASTVec& out)
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

// ARRAY_EQ can only exist when the array-equality option is on; this is the
// same complete-DAG barrier walk TopLevelSTPAux performs.
bool containsArrayEquality(const ASTNode& root)
{
  ASTNodeSet visited;
  ASTVec pending(1, root);
  while (!pending.empty())
  {
    const ASTNode node = pending.back();
    pending.pop_back();
    if (!visited.insert(node).second)
      continue;
    if (node.GetKind() == ARRAY_EQ)
      return true;
    for (unsigned i = 0; i < node.Degree(); ++i)
      pending.push_back(node[i]);
  }
  return false;
}

} // namespace

struct IncrementalSolver::Impl
{
  enum class RebuildReason
  {
    Relief,
    Promotion,
    Inprobing,
    Trail
  };

  // Fine-grained, opt-in measurements for deciding where scoped state will
  // actually pay. Timers are enabled only under --incremental-profile; the
  // counters travel with them so an ordinary solve does not read the clock or
  // update counters in its hot loops. Durations accumulate as nanoseconds to
  // avoid losing sub-microsecond level work and print as microseconds. Some
  // timings deliberately overlap: semanticNs is
  // the complete active-stack construction, while CBP, preparation and
  // encoding are its named sub-phases; refinementNs likewise includes its SAT
  // re-solves.
  struct CheckProfile
  {
    bool enabled = false;
    bool extensionality = false;
    uint64_t check = 0;

    uint64_t totalNs = 0;
    uint64_t maintenanceNs = 0;
    uint64_t semanticNs = 0;
    uint64_t screenNs = 0;
    uint64_t cbpNs = 0;
    uint64_t cbpSyncNs = 0;
    uint64_t cbpResetNs = 0;
    uint64_t cbpRollbackNs = 0;
    uint64_t cbpFeedNs = 0;
    uint64_t cbpFreshFeedNs = 0;
    uint64_t cbpRefeedNs = 0;
    uint64_t cbpRejectedFeedNs = 0;
    uint64_t cbpPropagateNs = 0;
    uint64_t cbpHarvestNs = 0;
    uint64_t cbpAdoptNs = 0;
    uint64_t cbpReplayNs = 0;
    uint64_t cbpFinishNs = 0;
    uint64_t prepareNs = 0;
    uint64_t encodeNs = 0;
    uint64_t readSeedNs = 0;
    uint64_t registryNs = 0;
    uint64_t extensionalityNs = 0;
    uint64_t refinementNs = 0;
    uint64_t satNs = 0;
    uint64_t initialSatNs = 0;
    uint64_t refinementSatNs = 0;
    uint64_t rebuildNs = 0;

    uint64_t levels = 0;
    uint64_t stablePrefix = 0;
    uint64_t screenNew = 0;
    uint64_t screenCached = 0;
    uint64_t preparationHits = 0;
    uint64_t preparationMisses = 0;
    uint64_t preparationInvalidations = 0;
    uint64_t preparationNoop = 0;
    uint64_t preparationCollapsed = 0;
    uint64_t preparationRejected = 0;
    uint64_t contextDefinitions = 0;
    uint64_t contextEntries = 0;
    uint64_t rootHits = 0;
    uint64_t rootMisses = 0;
    uint64_t activeKeys = 0;
    uint64_t assumptions = 0;
    uint64_t clauses = 0;
    uint64_t refinementClauses = 0;
    uint64_t retainedClauses = 0;
    uint64_t liveClauses = 0;
    uint64_t peakLiveClauses = 0;
    // The exact live AIG-cone union for this solve. Reported only: it is
    // deliberately not the number the relief valve decides on, so that
    // profiling does not move the rebuild schedule.
    uint64_t exactLiveClauses = 0;
    uint64_t cbpResets = 0;
    uint64_t cbpDivergences = 0;
    uint64_t cbpRollbacks = 0;
    uint64_t cbpRolledLevels = 0;
    uint64_t cbpRollbackFixed = 0;
    uint64_t cbpRollbackCreated = 0;
    uint64_t cbpRollbackDependencies = 0;
    uint64_t cbpRollbackMultiplications = 0;
    uint64_t cbpRollbackCallerEntries = 0;
    uint64_t cbpFedLevels = 0;
    uint64_t cbpFreshLevels = 0;
    uint64_t cbpRefedLevels = 0;
    uint64_t cbpFedNodes = 0;
    uint64_t cbpFreshNodes = 0;
    uint64_t cbpRefedNodes = 0;
    uint64_t cbpFeedRejected = 0;
    uint64_t cbpBootstrapDeferred = 0;
    uint64_t cbpAdoptAttempts = 0;
    uint64_t cbpAdoptions = 0;
    uint64_t cbpReplayAttempts = 0;
    uint64_t cbpReplays = 0;
    uint64_t cbpDeferredRestored = 0;
    uint64_t readKeysFolded = 0;
    uint64_t readKeysUnfolded = 0;
    uint64_t readRowsLive = 0;
    uint64_t satCalls = 0;
    uint64_t refinementSatCalls = 0;
    uint64_t refinementRounds = 0;
    uint64_t extPreprocesses = 0;
    uint64_t extEliminations = 0;
    uint64_t firstStackPreprocesses = 0;
    uint64_t firstStackEliminations = 0;
    uint64_t firstStackRejected = 0;
    uint64_t basePreprocesses = 0;
    uint64_t baseEliminations = 0;
    uint64_t rebuilds = 0;
    uint64_t rebuildRelief = 0;
    uint64_t rebuildPromotion = 0;
    uint64_t rebuildInprobing = 0;
    uint64_t rebuildTrail = 0;
    uint64_t encodingEpochResets = 0;
  };

  struct SessionProfile
  {
    uint64_t checks = 0;
    uint64_t totalNs = 0;
    uint64_t maintenanceNs = 0;
    uint64_t semanticNs = 0;
    uint64_t screenNs = 0;
    uint64_t cbpNs = 0;
    uint64_t cbpSyncNs = 0;
    uint64_t cbpResetNs = 0;
    uint64_t cbpRollbackNs = 0;
    uint64_t cbpFeedNs = 0;
    uint64_t cbpFreshFeedNs = 0;
    uint64_t cbpRefeedNs = 0;
    uint64_t cbpRejectedFeedNs = 0;
    uint64_t cbpPropagateNs = 0;
    uint64_t cbpHarvestNs = 0;
    uint64_t cbpAdoptNs = 0;
    uint64_t cbpReplayNs = 0;
    uint64_t cbpFinishNs = 0;
    uint64_t prepareNs = 0;
    uint64_t encodeNs = 0;
    uint64_t readSeedNs = 0;
    uint64_t registryNs = 0;
    uint64_t extensionalityNs = 0;
    uint64_t refinementNs = 0;
    uint64_t satNs = 0;
    uint64_t initialSatNs = 0;
    uint64_t refinementSatNs = 0;
    uint64_t rebuildNs = 0;
    uint64_t cbpResets = 0;
    uint64_t cbpDivergences = 0;
    uint64_t cbpRollbacks = 0;
    uint64_t cbpRolledLevels = 0;
    uint64_t cbpRollbackFixed = 0;
    uint64_t cbpRollbackCreated = 0;
    uint64_t cbpRollbackDependencies = 0;
    uint64_t cbpRollbackMultiplications = 0;
    uint64_t cbpRollbackCallerEntries = 0;
    uint64_t cbpFedLevels = 0;
    uint64_t cbpFreshLevels = 0;
    uint64_t cbpRefedLevels = 0;
    uint64_t cbpFedNodes = 0;
    uint64_t cbpFreshNodes = 0;
    uint64_t cbpRefedNodes = 0;
    uint64_t cbpFeedRejected = 0;
    uint64_t cbpBootstrapDeferred = 0;
    uint64_t cbpAdoptAttempts = 0;
    uint64_t cbpAdoptions = 0;
    uint64_t cbpReplayAttempts = 0;
    uint64_t cbpReplays = 0;
    uint64_t cbpDeferredRestored = 0;
    uint64_t screenNew = 0;
    uint64_t screenCached = 0;
    uint64_t preparationHits = 0;
    uint64_t preparationMisses = 0;
    uint64_t preparationInvalidations = 0;
    uint64_t preparationNoop = 0;
    uint64_t preparationCollapsed = 0;
    uint64_t preparationRejected = 0;
    uint64_t contextDefinitions = 0;
    uint64_t rootHits = 0;
    uint64_t rootMisses = 0;
    uint64_t readKeysFolded = 0;
    uint64_t readKeysUnfolded = 0;
    uint64_t clauses = 0;
    uint64_t refinementClauses = 0;
    uint64_t satCalls = 0;
    uint64_t refinementSatCalls = 0;
    uint64_t refinementRounds = 0;
    uint64_t extPreprocesses = 0;
    uint64_t extEliminations = 0;
    uint64_t firstStackPreprocesses = 0;
    uint64_t firstStackEliminations = 0;
    uint64_t firstStackRejected = 0;
    uint64_t basePreprocesses = 0;
    uint64_t baseEliminations = 0;
    uint64_t rebuilds = 0;
    uint64_t rebuildRelief = 0;
    uint64_t rebuildPromotion = 0;
    uint64_t rebuildInprobing = 0;
    uint64_t rebuildTrail = 0;
    uint64_t encodingEpochResets = 0;

    void add(const CheckProfile& p)
    {
      checks++;
      totalNs += p.totalNs;
      maintenanceNs += p.maintenanceNs;
      semanticNs += p.semanticNs;
      screenNs += p.screenNs;
      cbpNs += p.cbpNs;
      cbpSyncNs += p.cbpSyncNs;
      cbpResetNs += p.cbpResetNs;
      cbpRollbackNs += p.cbpRollbackNs;
      cbpFeedNs += p.cbpFeedNs;
      cbpFreshFeedNs += p.cbpFreshFeedNs;
      cbpRefeedNs += p.cbpRefeedNs;
      cbpRejectedFeedNs += p.cbpRejectedFeedNs;
      cbpPropagateNs += p.cbpPropagateNs;
      cbpHarvestNs += p.cbpHarvestNs;
      cbpAdoptNs += p.cbpAdoptNs;
      cbpReplayNs += p.cbpReplayNs;
      cbpFinishNs += p.cbpFinishNs;
      prepareNs += p.prepareNs;
      encodeNs += p.encodeNs;
      readSeedNs += p.readSeedNs;
      registryNs += p.registryNs;
      extensionalityNs += p.extensionalityNs;
      refinementNs += p.refinementNs;
      satNs += p.satNs;
      initialSatNs += p.initialSatNs;
      refinementSatNs += p.refinementSatNs;
      rebuildNs += p.rebuildNs;
      cbpResets += p.cbpResets;
      cbpDivergences += p.cbpDivergences;
      cbpRollbacks += p.cbpRollbacks;
      cbpRolledLevels += p.cbpRolledLevels;
      cbpRollbackFixed += p.cbpRollbackFixed;
      cbpRollbackCreated += p.cbpRollbackCreated;
      cbpRollbackDependencies += p.cbpRollbackDependencies;
      cbpRollbackMultiplications += p.cbpRollbackMultiplications;
      cbpRollbackCallerEntries += p.cbpRollbackCallerEntries;
      cbpFedLevels += p.cbpFedLevels;
      cbpFreshLevels += p.cbpFreshLevels;
      cbpRefedLevels += p.cbpRefedLevels;
      cbpFedNodes += p.cbpFedNodes;
      cbpFreshNodes += p.cbpFreshNodes;
      cbpRefedNodes += p.cbpRefedNodes;
      cbpFeedRejected += p.cbpFeedRejected;
      cbpBootstrapDeferred += p.cbpBootstrapDeferred;
      cbpAdoptAttempts += p.cbpAdoptAttempts;
      cbpAdoptions += p.cbpAdoptions;
      cbpReplayAttempts += p.cbpReplayAttempts;
      cbpReplays += p.cbpReplays;
      cbpDeferredRestored += p.cbpDeferredRestored;
      screenNew += p.screenNew;
      screenCached += p.screenCached;
      preparationHits += p.preparationHits;
      preparationMisses += p.preparationMisses;
      preparationInvalidations += p.preparationInvalidations;
      preparationNoop += p.preparationNoop;
      preparationCollapsed += p.preparationCollapsed;
      preparationRejected += p.preparationRejected;
      contextDefinitions += p.contextDefinitions;
      rootHits += p.rootHits;
      rootMisses += p.rootMisses;
      readKeysFolded += p.readKeysFolded;
      readKeysUnfolded += p.readKeysUnfolded;
      clauses += p.clauses;
      refinementClauses += p.refinementClauses;
      satCalls += p.satCalls;
      refinementSatCalls += p.refinementSatCalls;
      refinementRounds += p.refinementRounds;
      extPreprocesses += p.extPreprocesses;
      extEliminations += p.extEliminations;
      firstStackPreprocesses += p.firstStackPreprocesses;
      firstStackEliminations += p.firstStackEliminations;
      firstStackRejected += p.firstStackRejected;
      basePreprocesses += p.basePreprocesses;
      baseEliminations += p.baseEliminations;
      rebuilds += p.rebuilds;
      rebuildRelief += p.rebuildRelief;
      rebuildPromotion += p.rebuildPromotion;
      rebuildInprobing += p.rebuildInprobing;
      rebuildTrail += p.rebuildTrail;
      encodingEpochResets += p.encodingEpochResets;
    }
  };

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

  // AIG object Id -> CNF variable; -1 = not encoded yet. AIG Ids are dense
  // and only grow within one resettable encoding epoch.
  std::vector<int> aigIdToVar;

  // The variable standing for the AIG's constant-1 node, unit-asserted at
  // creation; -1 until first needed.
  int trueVar;

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
  ArrayTransformer::ArrType myReads;

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

  // Under --ackermanize, the transformer's other table: the reads of each
  // array in the order they were seen, from which each NEW read's nested
  // if-then-else over the EXISTING reads is built. That new-versus-existing
  // shape is exactly monotone, so persisting the list keeps pair coverage
  // across check-sats: any two reads are related by whichever was encoded
  // later. A popped read's entry stays as an unconstrained observation of
  // the array -- sound, since an array maps every index to some value.
  std::map<ASTNode, vector<std::pair<ASTNode, ASTNode>>> myAckPairs;

  // Storage handed out by the ToSATBase adapter (the refinement machinery
  // asks for the symbol map by reference), and the adapter itself,
  // constructed on first array use (its class is defined below Impl).
  ToSATBase::ASTNodeToSATVar symbolMapStorage;
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

  // Per-node symbol sets, memoised for this encoding epoch; the keys hold
  // their nodes.
  // Looked up by node and never iterated, so it wants hashing rather than
  // the ordered comparison an std::map would do on every probe -- and it is
  // probed once per candidate per piece per check.
  typedef std::unordered_map<ASTNode, ASTNodeSet, ASTNode::ASTNodeHasher,
                             ASTNode::ASTNodeEqual>
      NodeSymbolsMap;
  NodeSymbolsMap symbolsOfCache;

  // Allocation-free scratch marks for symbol DAG walks. Node ids are
  // process-thread-wide, monotone, and not reset with an encoding epoch. A
  // sparse page map is therefore essential: a vector indexed by page number
  // would immediately recreate a pointer span proportional to all historical
  // node ids after every relief rotation, defeating memory reclamation.
  static const size_t symbolVisitPageBits = 16;
  static const size_t symbolVisitPageSize = size_t(1) << symbolVisitPageBits;
  static const size_t symbolVisitPageMask = symbolVisitPageSize - 1;
  std::unordered_map<uint64_t, std::unique_ptr<uint8_t[]>> symbolVisitPages;
  uint8_t symbolVisitEpoch = 0;

  void beginSymbolVisit()
  {
    symbolVisitEpoch++;
    if (symbolVisitEpoch != 0)
      return;
    for (auto& entry : symbolVisitPages)
      std::fill(entry.second.get(), entry.second.get() + symbolVisitPageSize,
                uint8_t(0));
    symbolVisitEpoch = 1;
  }

  bool firstSymbolVisit(const ASTNode& n)
  {
    const uint64_t base = bm->ASTFalse.GetNodeNum();
    const uint64_t node = n.GetNodeNum();
    assert(node >= base);
    const uint64_t relative = node - base;
    const uint64_t page64 = relative >> symbolVisitPageBits;
    std::unique_ptr<uint8_t[]>& page = symbolVisitPages[page64];
    if (!page)
      page.reset(new uint8_t[symbolVisitPageSize]());
    uint8_t& mark = page[static_cast<size_t>(relative) & symbolVisitPageMask];
    if (mark == symbolVisitEpoch)
      return false;
    mark = symbolVisitEpoch;
    return true;
  }

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
  struct PendingLiveCone
  {
    std::vector<Aig_Obj_t*> currentRoots;
    size_t permanentRootCount = 0;
    uint64_t nonStructuralMass = 0;
  };
  PendingLiveCone pendingLiveCone;
  bool hasPendingLiveCone = false;

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
  ASTNodeSet semanticEpochRoots;
  uint64_t semanticNodeCharge = 0;
  ASTVec latestSemanticLiveRoots;
  uint64_t maxLiveSemanticNodes = 0;
  uint64_t lastRetainedSemanticNodes = 0;

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
  size_t dagSizeUpTo(const ASTNode& n, size_t cap)
  {
    ASTNodeSet visited;
    std::vector<ASTNode> pending(1, n);
    while (!pending.empty() && visited.size() <= cap)
    {
      const ASTNode cur = pending.back();
      pending.pop_back();
      if (!visited.insert(cur).second)
        continue;
      for (unsigned i = 0; i < cur.Degree(); i++)
        pending.push_back(cur[i]);
    }
    return visited.size();
  }

  // The granularity measurement recurs for the same nodes on every call
  // of a deep session (every level's granularity is re-judged per
  // check-sat); nodes are immutable, so the clipped count is a permanent
  // fact. The CBP feed does NOT measure sizes -- it asks the engine what a
  // level would add to what it already holds, which no per-node size can
  // answer.
  typedef std::unordered_map<ASTNode, size_t, ASTNode::ASTNodeHasher,
                             ASTNode::ASTNodeEqual>
      NodeSizeMemo;
  NodeSizeMemo dagSizeBigMemo;

  size_t dagSizeUpToMemo(const ASTNode& n, size_t cap, NodeSizeMemo& memo)
  {
    NodeSizeMemo::const_iterator it = memo.find(n);
    if (it != memo.end())
      return it->second;
    const size_t s = dagSizeUpTo(n, cap);
    memo[n] = s;
    return s;
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
    const size_t limit = semanticCacheLimit();
    if (limit == 0 || root.IsNull() ||
        !semanticEpochRoots.insert(root).second ||
        semanticNodeCharge >= limit)
      return;

    const size_t remaining =
        limit - static_cast<size_t>(semanticNodeCharge);
    const size_t charge = dagSizeUpTo(root, remaining);
    semanticNodeCharge =
        charge > remaining ? limit : semanticNodeCharge + charge;
  }

  uint64_t astDagUnionSize(const ASTVec& roots) const
  {
    ASTNodeSet visited;
    ASTVec pending = roots;
    while (!pending.empty())
    {
      const ASTNode node = pending.back();
      pending.pop_back();
      if (node.IsNull() || !visited.insert(node).second)
        continue;
      for (unsigned i = 0; i < node.Degree(); ++i)
        pending.push_back(node[i]);
    }
    return static_cast<uint64_t>(visited.size());
  }

  void stageSemanticLiveStack(const ASTVec& rawStack,
                              const ASTVec& encodedRoots)
  {
    ASTVec next = rawStack;
    next.insert(next.end(), encodedRoots.begin(), encodedRoots.end());
    latestSemanticLiveRoots.swap(next);
  }

  bool semanticReliefReached()
  {
    const size_t limit = semanticCacheLimit();
    if (limit == 0 || semanticNodeCharge < limit ||
        latestSemanticLiveRoots.empty())
      return false;

    const uint64_t live = astDagUnionSize(latestSemanticLiveRoots);
    maxLiveSemanticNodes = std::max(maxLiveSemanticNodes, live);

    ASTVec retainedRoots(semanticEpochRoots.begin(),
                         semanticEpochRoots.end());
    lastRetainedSemanticNodes = astDagUnionSize(retainedRoots);
    return maxLiveSemanticNodes != std::numeric_limits<uint64_t>::max() &&
           maxLiveSemanticNodes + 1 <= lastRetainedSemanticNodes / 4;
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

  void cbpBeginCallerLevel(size_t fedBefore)
  {
    assert(callCbpDeferred.empty());
    assert(!cbpCallerLevelOpen);
    assert(cbpCallerCheckpoints.size() == scopes.cbpFedDepth());
    cbpSubstTrailedThisLevel.clear();
    cbpCallerCheckpoints.push_back(CbpCallerCheckpoint{
        cbpSubstUndo.size(), cbpFedConjunctsAdded.size(), cbpFactsAdded.size(),
        fedBefore, cbpFedArrays, callCbpOff, callCbpConflict});
    cbpCallerLevelOpen = true;
  }

  void cbpTrailSubstitution(const ASTNode& key)
  {
    assert(cbpCallerLevelOpen);
    if (!cbpSubstTrailedThisLevel.insert(key).second)
      return;
    ASTNodeMap::const_iterator it = callCbpSubst.find(key);
    cbpSubstUndo.push_back(
        CbpSubstUndo(key, it == callCbpSubst.end() ? ASTNode() : it->second,
                     it != callCbpSubst.end()));
  }

  void cbpAssignSubstitution(const ASTNode& key, const ASTNode& value)
  {
    cbpTrailSubstitution(key);
    callCbpSubst[key] = value;
  }

  void cbpEraseSubstitution(const ASTNode& key)
  {
    cbpTrailSubstitution(key);
    callCbpSubst.erase(key);
  }

  void cbpInsertFedConjunct(const ASTNode& node)
  {
    if (callCbpFedConjuncts.find(node) != callCbpFedConjuncts.end())
      return;
    assert(cbpCallerLevelOpen);
    if (!cbpCallerLevelOpen)
      return;
    callCbpFedConjuncts.insert(node);
    cbpFedConjunctsAdded.push_back(node);
  }

  bool cbpInsertFactDomain(const ASTNode& node)
  {
    if (callCbpFactEmitted.find(node) != callCbpFactEmitted.end())
      return false;
    assert(cbpCallerLevelOpen);
    if (!cbpCallerLevelOpen)
      return false;
    callCbpFactEmitted.insert(node);
    cbpFactsAdded.push_back(node);
    return true;
  }

  size_t cbpRollbackCallerTo(size_t levels)
  {
    assert(levels <= cbpCallerCheckpoints.size());
    assert(callCbpDeferred.empty());
    assert(!cbpCallerLevelOpen);
    size_t entries = 0;
    while (cbpCallerCheckpoints.size() > levels)
    {
      const CbpCallerCheckpoint checkpoint = cbpCallerCheckpoints.back();
      cbpCallerCheckpoints.pop_back();
      while (cbpSubstUndo.size() > checkpoint.substUndo)
      {
        const CbpSubstUndo& undo = cbpSubstUndo.back();
        if (undo.existed)
          callCbpSubst[undo.key] = undo.oldValue;
        else
          callCbpSubst.erase(undo.key);
        cbpSubstUndo.pop_back();
        entries++;
      }
      while (cbpFedConjunctsAdded.size() > checkpoint.fedConjunctsAdded)
      {
        const size_t erased =
            callCbpFedConjuncts.erase(cbpFedConjunctsAdded.back());
        assert(erased == 1);
        (void)erased;
        cbpFedConjunctsAdded.pop_back();
        entries++;
      }
      while (cbpFactsAdded.size() > checkpoint.factsAdded)
      {
        const size_t erased = callCbpFactEmitted.erase(cbpFactsAdded.back());
        assert(erased == 1);
        (void)erased;
        cbpFactsAdded.pop_back();
        entries++;
      }
      callCbpFed = checkpoint.fedBefore;
      cbpFedArrays = checkpoint.fedArraysBefore;
      callCbpOff = checkpoint.offBefore;
      callCbpConflict = checkpoint.conflictBefore;
    }
    // The refused level is gone, and its would-be charge with it, so the
    // capacity judgement that refused it no longer describes this stack.
    // Rolling back TO the refusal depth leaves the same stack that was
    // refused, so only a strictly shallower one releases it.
    if (cbpOverFeedCap() && levels < cbpOverFeedCapAt)
      cbpOverFeedCapAt = noFeedCapRefusal;
    cbpSubstTrailedThisLevel.clear();
    cbpCallerLevelOpen = false;
    callCbpDeferred.clear();
    scopes.rollbackCbpFedTo(levels);
    return entries;
  }

  void cbpReset()
  {
    callCbp.reset();
    callCbpSubst.clear();
    callCbpDeferred.clear();
    callCbpFactEmitted.clear();
    callCbpFedConjuncts.clear();
    scopes.resetCbpFed();
    cbpCallerCheckpoints.clear();
    cbpSubstUndo.clear();
    cbpFedConjunctsAdded.clear();
    cbpFactsAdded.clear();
    cbpSubstTrailedThisLevel.clear();
    cbpCallerLevelOpen = false;
    callCbpFed = 0;
    cbpOverFeedCapAt = noFeedCapRefusal;
    cbpFedArrays = false;
  }

  // Early-exit containment: does `n` reach any of `syms`? The
  // harvest's per-delta-node filters must stay walk-bounded with no
  // per-node set materialisation -- a large formula's fixpoint delta
  // is tens of thousands of nodes, and building symbol sets for each
  // measured minutes on a single feed. A walk that exhausts its
  // budget answers "reaches": the caller then defers the fixing,
  // which only forgoes an intra-level fold.
  bool reachesAnyOf(const ASTNode& n, const ASTNodeSet& syms)
  {
    static const size_t walkBudget = 2000;
    ASTNodeSet visited;
    std::vector<ASTNode> pending(1, n);
    while (!pending.empty())
    {
      const ASTNode cur = pending.back();
      pending.pop_back();
      if (cur.isConstant())
        continue;
      if (!visited.insert(cur).second)
        continue;
      if (visited.size() > walkBudget)
        return true;
      if (syms.find(cur) != syms.end())
        return true;
      for (unsigned i = 0; i < cur.Degree(); i++)
        pending.push_back(cur[i]);
    }
    return false;
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
  void cbpFeedLevel(size_t level, const ASTNode& levelConjunction)
  {
    if (callCbpOff || cbpSessionRetired)
      return;
    // Levels feed in stack order exactly once; anything else is a
    // prefix this session already carries.
    if (level != scopes.cbpFedDepth())
      return;
    const bool refeed = level < cbpMemoStable;
    ScopedProfileTimer cbpTimer(profile.enabled, profile.cbpNs);
    ScopedProfileTimer feedTimer(profile.enabled, profile.cbpFeedNs);
    ScopedProfileTimer feedClassTimer(
        profile.enabled, refeed ? profile.cbpRefeedNs : profile.cbpFreshFeedNs);
    if (!callCbp)
      callCbp.reset(new IncrementalCBP(bm, bm->defaultNodeFactory));

    // Charge the cap what this level ADDS, not what it spans. Levels share
    // subgraphs by identity -- a pushed level is usually a small delta over
    // the cone its parent already established -- and the engine visits a
    // shared node once, ever: extendParentMap stops at depsVisited, and the
    // parent map, the fixed-bits map and the undo trail all key on the node.
    // Summing per-level DAG sizes therefore charged one shared cone once per
    // level that mentions it, and a stack of twenty such levels read as
    // twenty times the mass the engine was actually holding. It is the same
    // over-count that makes DAG size the wrong measure for adoption's shrink
    // gate: interned structure is not paid for twice.
    const size_t cap = cbpFeedCap();
    const size_t levelNodes = callCbp->freshNodeCount(levelConjunction, cap);
    const size_t fedBefore = callCbpFed;
    assert(callCbpFed <= cap);
    if (levelNodes > cap - callCbpFed)
    {
      if (profile.enabled)
        profile.cbpFeedRejected++;
      feedClassTimer.retarget(profile.enabled, profile.cbpRejectedFeedNs);
      callCbpOff = true;
      cbpOverFeedCapAt = level;
      if (bm->UserFlags.stats_flag)
        std::cerr << "Incremental: cbp off at level " << level
                  << " (stack over the feed cap)" << std::endl;
      return;
    }
    callCbpFed += levelNodes;
    cbpBeginCallerLevel(fedBefore);
    if (profile.enabled)
    {
      profile.cbpFedLevels++;
      profile.cbpFedNodes += levelNodes;
      if (refeed)
      {
        profile.cbpRefedLevels++;
        profile.cbpRefedNodes += levelNodes;
      }
      else
      {
        profile.cbpFreshLevels++;
        profile.cbpFreshNodes += levelNodes;
      }
    }

    ASTVec fed;
    splitConjuncts(levelConjunction, bm->ASTTrue, fed);
    fed.push_back(levelConjunction);
    for (const ASTNode& c : fed)
      cbpInsertFedConjunct(c);

    bool consistent;
    const bool wasInConflict = callCbp->inConflict();
    {
      ScopedProfileTimer propagationTimer(profile.enabled,
                                          profile.cbpPropagateNs);
      consistent = callCbp->feedLevel(levelConjunction);
    }
    // The charge IS the retained mass. freshNodeCount and extendParentMap
    // walk the same graph under the same stopping rule, so an accepted feed
    // grows the engine's dependency set by exactly what was charged -- the
    // invariant the old per-level sum could not state, let alone check. A
    // feed onto an already-conflicting engine returns before extending the
    // graph at all, and is the one case that owes nothing.
    assert(wasInConflict || callCbpFed == callCbp->retainedNodes());
    (void)wasInConflict;
    assert(callCbp->levelCount() == cbpCallerCheckpoints.size());
    if (!consistent)
    {
      // The live prefix is contradictory by bit-level reasoning
      // alone; the caller asserts FALSE at this level. The feed
      // still consumed the level -- the engine's map and its latched
      // conflict carry this level's assumed truth -- so it MUST be
      // recorded: an unrecorded feed survives the level's pop (the
      // divergence check never sees it) and refutes whatever level
      // is pushed in its place. The refutation is the level's
      // memoised output, so an identical re-push replays FALSE
      // instead of re-running the feed.
      callCbpConflict = true;
      callCbpOff = true;
      scopes.markCbpFed(level);
      assert(cbpCallerCheckpoints.size() == scopes.cbpFedDepth());
      if (scopes.cbpMemoDepth() == level)
      {
        scopes.startCbpMemo(level).facts.push_back(
            ScopedFact(ASTNode(), bm->ASTFalse));
      }
      return;
    }

    // A fixing this level's own feed derived joins the substitution
    // only for DEEPER levels (via cbpFinishLevel) when it pins a
    // SYMBOL -- or an interior node over one: folding either into its
    // own level would usurp the definition harvest, whose machinery
    // (the pushed-definition context, the pieces' private-variable
    // elimination) owns intra-level substitution with model-replay
    // bookkeeping this pass does not carry -- and an interior fold's
    // pinning fact would drag the symbol into the encoding, spoiling
    // its eliminability for the rest of the session. Cross-level
    // visibility is this pass's whole charter; a node fixed here
    // through EARLIER levels' knowledge (the target family's
    // ite-indexed writes, whose flags other levels pin) carries no
    // symbol from THIS feed and still folds in place.
    // One walk per fed level decides whether the per-delta-node array
    // exclusion below has anything to exclude: an array-free fed
    // prefix cannot put an array-carrying node in the delta, and the
    // per-node walks were the dominant cost of feeding a large
    // array-free formula.
    {
      ScopedProfileTimer harvestTimer(profile.enabled, profile.cbpHarvestNs);
      if (!cbpFedArrays && containsArrayOps(levelConjunction, bm))
        cbpFedArrays = true;

      const std::vector<ASTNode>& feedDelta = callCbp->takeNewlyFixed();
      ASTNodeSet feedSymbols;
      for (const ASTNode& n : feedDelta)
      {
        if (callCbpSubst.size() + callCbpDeferred.size() >= cbpHarvestCap)
          break;
        if (n.GetKind() != SYMBOL)
          continue;
        const ASTNode k = callCbp->constantOf(n);
        if (k.IsNull())
          continue;
        callCbpDeferred.push_back(std::make_pair(n, k));
        feedSymbols.insert(n);
        noteEngineDerivedFixing(n);
      }
      for (const ASTNode& n : feedDelta)
      {
        if (callCbpSubst.size() + callCbpDeferred.size() >= cbpHarvestCap)
          break;
        if (n.GetKind() == SYMBOL || n.GetKind() == BVEXTRACT ||
            n.GetKind() == BVCONCAT)
          continue;
        const ASTNode k = callCbp->constantOf(n);
        if (k.IsNull())
          continue;
        if (cbpFedArrays && containsArrayOps(n, bm))
          continue;
        if (!feedSymbols.empty() && reachesAnyOf(n, feedSymbols))
          callCbpDeferred.push_back(std::make_pair(n, k));
        else
          cbpAssignSubstitution(n, k);
        noteEngineDerivedFixing(n);
      }

      for (const ASTNode& c : fed)
      {
        ASTNodeMap::iterator it = callCbpSubst.find(c);
        if (it != callCbpSubst.end())
        {
          callCbpDeferred.push_back(*it);
          cbpEraseSubstitution(c);
        }
      }
    }

    scopes.markCbpFed(level);
    assert(cbpCallerCheckpoints.size() == scopes.cbpFedDepth());
    // The memo entry parallels the feed; if this level was already memoised
    // under the same conjunction (the reset oracle/fallback re-feeding the
    // stable prefix), the existing entry keeps replaying.
    if (scopes.cbpMemoDepth() == level)
      scopes.startCbpMemo(level);
  }

  // Restore the fed-conjunct fixings cbpFeedLevel parked, once the
  // level's own conjuncts are past rewriting.
  void cbpFinishLevel()
  {
    if (!cbpCallerLevelOpen)
    {
      assert(callCbpDeferred.empty());
      return;
    }
    ScopedProfileTimer cbpTimer(profile.enabled, profile.cbpNs);
    ScopedProfileTimer finishTimer(profile.enabled, profile.cbpFinishNs);
    if (profile.enabled)
      profile.cbpDeferredRestored += callCbpDeferred.size();
    for (const std::pair<ASTNode, ASTNode>& e : callCbpDeferred)
      cbpAssignSubstitution(e.first, e.second);
    callCbpDeferred.clear();
    cbpSubstTrailedThisLevel.clear();
    cbpCallerLevelOpen = false;
  }

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
                   std::vector<ScopedFact>& factsOut)
  {
    if (callCbpOff || !cbpCallerLevelOpen || callCbpSubst.empty())
      return conjunct;
    ScopedProfileTimer cbpTimer(profile.enabled, profile.cbpNs);
    ScopedProfileTimer adoptTimer(profile.enabled, profile.cbpAdoptNs);
    if (profile.enabled)
      profile.cbpAdoptAttempts++;

    // The conjunct's own entry (a ctx-substituted form can be fixed
    // as an interior node without being a fed conjunct) never rewrites
    // its own slot.
    ASTNodeMap::iterator selfEntry = callCbpSubst.find(conjunct);
    ASTNode selfConstant;
    if (selfEntry != callCbpSubst.end())
    {
      selfConstant = selfEntry->second;
      cbpEraseSubstitution(conjunct);
    }
    ASTNodeMap cache;
    const ASTNode adopted = SubstitutionMap::replace(
        conjunct, callCbpSubst, cache, bm->defaultNodeFactory);
    if (!selfConstant.IsNull())
      cbpAssignSubstitution(conjunct, selfConstant);
    if (adopted == conjunct)
      return conjunct;

    const size_t before = dagSizeUpTo(conjunct, bigFormulaCap);
    if (dagSizeUpTo(adopted, before) >= before)
      return conjunct;

    ASTNodeSet visited;
    std::vector<ASTNode> pending(1, conjunct);
    while (!pending.empty())
    {
      const ASTNode cur = pending.back();
      pending.pop_back();
      if (!visited.insert(cur).second)
        continue;
      ASTNodeMap::const_iterator sit = callCbpSubst.find(cur);
      if (sit != callCbpSubst.end() &&
          callCbpFedConjuncts.find(cur) == callCbpFedConjuncts.end() &&
          cbpInsertFactDomain(cur))
      {
        ASTNode fact;
        if (cur.GetType() == BOOLEAN_TYPE)
          fact = sit->second == bm->ASTTrue
                     ? cur
                     : bm->defaultNodeFactory->CreateNode(NOT, cur);
        else
          fact = bm->defaultNodeFactory->CreateNode(EQ, cur, sit->second);
        factsOut.push_back(ScopedFact(cur, fact));
      }
      for (unsigned j = 0; j < cur.Degree(); j++)
        pending.push_back(cur[j]);
    }

    callCbpAdopted++;
    cbpEpochAdopted++;
    if (profile.enabled)
      profile.cbpAdoptions++;
    return adopted;
  }

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

  const ASTNodeSet& symbolsOf(const ASTNode& n)
  {
    NodeSymbolsMap::iterator hit = symbolsOfCache.find(n);
    if (hit != symbolsOfCache.end())
      return hit->second;

    beginSymbolVisit();

    ASTNodeSet& out = symbolsOfCache[n];
    std::vector<ASTNode> pending(1, n);
    while (!pending.empty())
    {
      const ASTNode cur = pending.back();
      pending.pop_back();
      if (!firstSymbolVisit(cur))
        continue;

      if (cur.GetKind() == SYMBOL)
        out.insert(cur);
      for (unsigned i = 0; i < cur.Degree(); i++)
        pending.push_back(cur[i]);
    }
    return out;
  }

  // Add the union of symbols reachable from several roots in ONE DAG walk.
  // Calling symbolsOf() for each root separately is intentionally useful when
  // callers need each individual set, but is catastrophic for a large family
  // of overlapping roots: CBP can expose thousands of eligible fixed domains
  // over the same define-fun spine.  Protection only needs their union.
  void addSymbolsOf(const ASTVec& roots, ASTNodeSet& out)
  {
    if (roots.empty())
      return;
    beginSymbolVisit();
    ASTVec pending = roots;
    while (!pending.empty())
    {
      const ASTNode cur = pending.back();
      pending.pop_back();
      if (!firstSymbolVisit(cur))
        continue;
      if (cur.GetKind() == SYMBOL)
        out.insert(cur);
      for (unsigned i = 0; i < cur.Degree(); i++)
        pending.push_back(cur[i]);
    }
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

  void recordUnsat(const SATSolver::vec_literals& assumptions,
                   size_t levelCount, bool coarse)
  {
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

  Impl(STPMgr* bm_, AbsRefine_CounterExample* ce_, Simplifier* batchSimp_,
       ArrayTransformer* batchAT_)
      : bm(bm_), ce(ce_), batchSimp(batchSimp_), batchAT(batchAT_),
        policy(bm_->UserFlags.incremental_core_only),
        solver(makeBackend(bm_->UserFlags, true)), encoding(bm_),
        trueVar(-1), lastUnsat(false), lastUnsatCoarse(false),
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

    // Assemble the report before writing it. SMT answers use stdout while
    // profiles use stderr; one write keeps redirected 2>&1 logs line-safe.
    std::ostringstream out;
    out << "Incremental profile: check=" << profile.check
        << " levels=" << profile.levels
        << " total-us=" << profileMicros(profile.totalNs)
        << " maintenance-us=" << profileMicros(profile.maintenanceNs)
        << " semantic-us=" << profileMicros(profile.semanticNs)
        << " screen-us=" << profileMicros(profile.screenNs)
        << " cbp-us=" << profileMicros(profile.cbpNs)
        << " cbp-sync-us=" << profileMicros(profile.cbpSyncNs)
        << " cbp-reset-us=" << profileMicros(profile.cbpResetNs)
        << " cbp-rollback-us=" << profileMicros(profile.cbpRollbackNs)
        << " cbp-feed-us=" << profileMicros(profile.cbpFeedNs)
        << " cbp-fresh-feed-us=" << profileMicros(profile.cbpFreshFeedNs)
        << " cbp-refeed-us=" << profileMicros(profile.cbpRefeedNs)
        << " cbp-rejected-feed-us=" << profileMicros(profile.cbpRejectedFeedNs)
        << " cbp-engine-us=" << profileMicros(profile.cbpPropagateNs)
        << " cbp-harvest-us=" << profileMicros(profile.cbpHarvestNs)
        << " cbp-adopt-us=" << profileMicros(profile.cbpAdoptNs)
        << " cbp-replay-us=" << profileMicros(profile.cbpReplayNs)
        << " cbp-finish-us=" << profileMicros(profile.cbpFinishNs)
        << " prepare-us=" << profileMicros(profile.prepareNs)
        << " encode-us=" << profileMicros(profile.encodeNs)
        << " read-seed-us=" << profileMicros(profile.readSeedNs)
        << " registry-us=" << profileMicros(profile.registryNs)
        << " extensionality-us=" << profileMicros(profile.extensionalityNs)
        << " refinement-us=" << profileMicros(profile.refinementNs)
        << " sat-us=" << profileMicros(profile.satNs)
        << " initial-sat-us=" << profileMicros(profile.initialSatNs)
        << " refinement-sat-us=" << profileMicros(profile.refinementSatNs)
        << " rebuild-reset-us=" << profileMicros(profile.rebuildNs) << '\n';
    out << "Incremental profile work: check=" << profile.check
        << " stable-prefix=" << profile.stablePrefix
        << " screen-new=" << profile.screenNew
        << " screen-cached=" << profile.screenCached
        << " prepare-hits=" << profile.preparationHits
        << " prepare-misses=" << profile.preparationMisses
        << " prepare-invalidated=" << profile.preparationInvalidations
        << " prepare-noop=" << profile.preparationNoop
        << " prepare-collapsed=" << profile.preparationCollapsed
        << " prepare-rejected=" << profile.preparationRejected
        << " context-definitions=" << profile.contextDefinitions
        << " context-entries=" << profile.contextEntries
        << " root-hits=" << profile.rootHits
        << " root-misses=" << profile.rootMisses
        << " active-keys=" << profile.activeKeys
        << " assumptions=" << profile.assumptions << '\n';
    out << "Incremental profile cbp/backend: check=" << profile.check
        << " cbp-resets=" << profile.cbpResets
        << " cbp-divergences=" << profile.cbpDivergences
        << " cbp-rollbacks=" << profile.cbpRollbacks
        << " cbp-rolled-levels=" << profile.cbpRolledLevels
        << " cbp-rollback-fixed=" << profile.cbpRollbackFixed
        << " cbp-rollback-created=" << profile.cbpRollbackCreated
        << " cbp-rollback-dependencies=" << profile.cbpRollbackDependencies
        << " cbp-rollback-multiplications="
        << profile.cbpRollbackMultiplications
        << " cbp-rollback-caller=" << profile.cbpRollbackCallerEntries
        << " cbp-fed-levels=" << profile.cbpFedLevels
        << " cbp-fresh-levels=" << profile.cbpFreshLevels
        << " cbp-refed-levels=" << profile.cbpRefedLevels
        << " cbp-fed-nodes=" << profile.cbpFedNodes
        << " cbp-fresh-nodes=" << profile.cbpFreshNodes
        << " cbp-refed-nodes=" << profile.cbpRefedNodes
        << " cbp-feed-rejected=" << profile.cbpFeedRejected
        << " cbp-bootstrap-deferred=" << profile.cbpBootstrapDeferred
        << " cbp-adopt-attempts=" << profile.cbpAdoptAttempts
        << " cbp-adoptions=" << profile.cbpAdoptions
        << " cbp-replay-attempts=" << profile.cbpReplayAttempts
        << " cbp-replays=" << profile.cbpReplays
        << " cbp-deferred-restored=" << profile.cbpDeferredRestored
        << " read-keys-folded=" << profile.readKeysFolded
        << " read-keys-unfolded=" << profile.readKeysUnfolded
        << " live-read-rows=" << profile.readRowsLive
        << " driver-clauses=" << profile.clauses
        << " refinement-clauses=" << profile.refinementClauses
        << " retained-clauses=" << profile.retainedClauses
        << " live-clauses=" << profile.liveClauses
        << " exact-live-clauses=" << profile.exactLiveClauses
        << " peak-live-clauses=" << profile.peakLiveClauses
        << " sat-calls=" << profile.satCalls
        << " refinement-sat-calls=" << profile.refinementSatCalls
        << " refinement-rounds=" << profile.refinementRounds
        << " ext-preprocesses=" << profile.extPreprocesses
        << " ext-eliminations=" << profile.extEliminations
        << " base-preprocesses=" << profile.basePreprocesses
        << " base-eliminations=" << profile.baseEliminations
        << " rebuilds=" << profile.rebuilds
        << " rebuild-relief=" << profile.rebuildRelief
        << " rebuild-promotion=" << profile.rebuildPromotion
        << " rebuild-inprobing=" << profile.rebuildInprobing
        << " rebuild-trail=" << profile.rebuildTrail
        << " encoding-epoch-resets=" << profile.encodingEpochResets
        << " policy=" << (policy.coreOnly() ? "core" : "full")
        << " extensionality=" << (profile.extensionality ? 1 : 0)
        << " first-stack-preprocesses=" << profile.firstStackPreprocesses
        << " first-stack-eliminations=" << profile.firstStackEliminations
        << " first-stack-rejected=" << profile.firstStackRejected << '\n';
    out << "Incremental profile total: checks=" << sessionProfile.checks
        << " total-us=" << profileMicros(sessionProfile.totalNs)
        << " maintenance-us=" << profileMicros(sessionProfile.maintenanceNs)
        << " semantic-us=" << profileMicros(sessionProfile.semanticNs)
        << " screen-us=" << profileMicros(sessionProfile.screenNs)
        << " cbp-us=" << profileMicros(sessionProfile.cbpNs)
        << " cbp-sync-us=" << profileMicros(sessionProfile.cbpSyncNs)
        << " cbp-reset-us=" << profileMicros(sessionProfile.cbpResetNs)
        << " cbp-rollback-us=" << profileMicros(sessionProfile.cbpRollbackNs)
        << " cbp-feed-us=" << profileMicros(sessionProfile.cbpFeedNs)
        << " cbp-fresh-feed-us=" << profileMicros(sessionProfile.cbpFreshFeedNs)
        << " cbp-refeed-us=" << profileMicros(sessionProfile.cbpRefeedNs)
        << " cbp-rejected-feed-us="
        << profileMicros(sessionProfile.cbpRejectedFeedNs)
        << " cbp-engine-us=" << profileMicros(sessionProfile.cbpPropagateNs)
        << " cbp-harvest-us=" << profileMicros(sessionProfile.cbpHarvestNs)
        << " cbp-adopt-us=" << profileMicros(sessionProfile.cbpAdoptNs)
        << " cbp-replay-us=" << profileMicros(sessionProfile.cbpReplayNs)
        << " cbp-finish-us=" << profileMicros(sessionProfile.cbpFinishNs)
        << " prepare-us=" << profileMicros(sessionProfile.prepareNs)
        << " encode-us=" << profileMicros(sessionProfile.encodeNs)
        << " read-seed-us=" << profileMicros(sessionProfile.readSeedNs)
        << " registry-us=" << profileMicros(sessionProfile.registryNs)
        << " extensionality-us="
        << profileMicros(sessionProfile.extensionalityNs)
        << " refinement-us=" << profileMicros(sessionProfile.refinementNs)
        << " sat-us=" << profileMicros(sessionProfile.satNs)
        << " initial-sat-us=" << profileMicros(sessionProfile.initialSatNs)
        << " refinement-sat-us="
        << profileMicros(sessionProfile.refinementSatNs)
        << " rebuild-reset-us=" << profileMicros(sessionProfile.rebuildNs)
        << " cbp-resets=" << sessionProfile.cbpResets
        << " cbp-divergences=" << sessionProfile.cbpDivergences
        << " cbp-rollbacks=" << sessionProfile.cbpRollbacks
        << " cbp-rolled-levels=" << sessionProfile.cbpRolledLevels
        << " cbp-rollback-fixed=" << sessionProfile.cbpRollbackFixed
        << " cbp-rollback-created=" << sessionProfile.cbpRollbackCreated
        << " cbp-rollback-dependencies="
        << sessionProfile.cbpRollbackDependencies
        << " cbp-rollback-multiplications="
        << sessionProfile.cbpRollbackMultiplications
        << " cbp-rollback-caller=" << sessionProfile.cbpRollbackCallerEntries
        << " cbp-fed-levels=" << sessionProfile.cbpFedLevels
        << " cbp-fresh-levels=" << sessionProfile.cbpFreshLevels
        << " cbp-refed-levels=" << sessionProfile.cbpRefedLevels
        << " cbp-fed-nodes=" << sessionProfile.cbpFedNodes
        << " cbp-fresh-nodes=" << sessionProfile.cbpFreshNodes
        << " cbp-refed-nodes=" << sessionProfile.cbpRefedNodes
        << " cbp-feed-rejected=" << sessionProfile.cbpFeedRejected
        << " cbp-bootstrap-deferred="
        << sessionProfile.cbpBootstrapDeferred
        << " cbp-adopt-attempts=" << sessionProfile.cbpAdoptAttempts
        << " cbp-adoptions=" << sessionProfile.cbpAdoptions
        << " cbp-replay-attempts=" << sessionProfile.cbpReplayAttempts
        << " cbp-replays=" << sessionProfile.cbpReplays
        << " cbp-deferred-restored=" << sessionProfile.cbpDeferredRestored
        << " screen-new=" << sessionProfile.screenNew
        << " screen-cached=" << sessionProfile.screenCached
        << " prepare-hits=" << sessionProfile.preparationHits
        << " prepare-misses=" << sessionProfile.preparationMisses
        << " prepare-invalidated=" << sessionProfile.preparationInvalidations
        << " prepare-noop=" << sessionProfile.preparationNoop
        << " prepare-collapsed=" << sessionProfile.preparationCollapsed
        << " prepare-rejected=" << sessionProfile.preparationRejected
        << " context-definitions=" << sessionProfile.contextDefinitions
        << " root-hits=" << sessionProfile.rootHits
        << " root-misses=" << sessionProfile.rootMisses
        << " read-keys-folded=" << sessionProfile.readKeysFolded
        << " read-keys-unfolded=" << sessionProfile.readKeysUnfolded
        << " driver-clauses=" << sessionProfile.clauses
        << " refinement-clauses=" << sessionProfile.refinementClauses
        << " retained-clauses=" << retainedClauseMass()
        << " live-clauses=" << currentLiveClauseMass
        << " peak-live-clauses=" << maxLiveClauseMass
        << " sat-calls=" << sessionProfile.satCalls
        << " refinement-sat-calls=" << sessionProfile.refinementSatCalls
        << " refinement-rounds=" << sessionProfile.refinementRounds
        << " ext-preprocesses=" << sessionProfile.extPreprocesses
        << " ext-eliminations=" << sessionProfile.extEliminations
        << " base-preprocesses=" << sessionProfile.basePreprocesses
        << " base-eliminations=" << sessionProfile.baseEliminations
        << " rebuilds=" << sessionProfile.rebuilds
        << " rebuild-relief=" << sessionProfile.rebuildRelief
        << " rebuild-promotion=" << sessionProfile.rebuildPromotion
        << " rebuild-inprobing=" << sessionProfile.rebuildInprobing
        << " rebuild-trail=" << sessionProfile.rebuildTrail
        << " encoding-epoch-resets=" << sessionProfile.encodingEpochResets
        << " policy=" << (policy.coreOnly() ? "core" : "full")
        << " first-stack-preprocesses="
        << sessionProfile.firstStackPreprocesses
        << " first-stack-eliminations="
        << sessionProfile.firstStackEliminations
        << " first-stack-rejected=" << sessionProfile.firstStackRejected
        << '\n';
    std::cerr << out.str();
  }

  int varOfAig(Aig_Obj_t* regular)
  {
    const unsigned id = Aig_ObjId(regular);
    if (id >= aigIdToVar.size())
      return -1;
    return aigIdToVar[id];
  }

  void setVarOfAig(Aig_Obj_t* regular, int var)
  {
    const unsigned id = Aig_ObjId(regular);
    if (id >= aigIdToVar.size())
      aigIdToVar.resize(id + 1, -1);
    aigIdToVar[id] = var;
  }

  void addClause(SATSolver::vec_literals& c)
  {
    solver->addClause(c);
  }

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
      pendingLiveCone.currentRoots.swap(currentRoots);
      pendingLiveCone.permanentRootCount = permanentAigRoots.size();
      pendingLiveCone.nonStructuralMass = nonStructuralMass;
      hasPendingLiveCone = true;
    }
    else
    {
      pendingLiveCone.currentRoots.clear();
      hasPendingLiveCone = false;
    }
  }

  // Pay pending whole-cone walks only when the cheap ownership estimate would
  // otherwise authorize a rebuild. Newest first repairs a monotonically
  // growing live stack with one walk; stop immediately once the recovered
  // high-water mark disproves relief. The staging side has already coalesced
  // history to the last solve, so this is at most one full-cone walk.
  void expandPendingLiveConeMass()
  {
    if (!hasPendingLiveCone)
      return;
    const uint64_t structural = encodedAigConeMass(
        pendingLiveCone.currentRoots, pendingLiveCone.permanentRootCount);
    const uint64_t live =
        addMass(structural, pendingLiveCone.nonStructuralMass);
    // This snapshot belongs to the previous solve. Discovering its exact cone
    // repairs the epoch's historical high-water mark, but must not report that
    // old working set as live in the check about to start.
    recordPeakLiveClauseMass(live);
    pendingLiveCone.currentRoots.clear();
    hasPendingLiveCone = false;
  }

  void addBinary(int lit_a, int lit_b)
  {
    SATSolver::vec_literals c;
    c.push(SATSolver::mkLit(lit_a >> 1, lit_a & 1));
    c.push(SATSolver::mkLit(lit_b >> 1, lit_b & 1));
    addClause(c);
  }

  int ensureTrueVar()
  {
    if (trueVar == -1)
    {
      trueVar = solver->newVar();
      SATSolver::vec_literals unit;
      unit.push(SATSolver::mkLit(trueVar, false));
      addClause(unit);
    }
    return trueVar;
  }

  // Tseitin-encode the cone of `regular` (an uncomplemented AIG node) into
  // the solver, allocating variables and definitional clauses for the nodes
  // not encoded yet. Everything emitted is a conservative extension, so it
  // is never retracted.
  void ensureEncoded(Aig_Obj_t* regular)
  {
    std::vector<Aig_Obj_t*> work;
    work.push_back(regular);

    while (!work.empty())
    {
      Aig_Obj_t* r = work.back();
      assert(!Aig_IsComplement(r));

      if (varOfAig(r) != -1)
      {
        work.pop_back();
        continue;
      }

      if (Aig_ObjIsConst1(r))
      {
        setVarOfAig(r, ensureTrueVar());
        work.pop_back();
        continue;
      }

      if (Aig_ObjIsCi(r))
      {
        setVarOfAig(r, solver->newVar());
        work.pop_back();
        continue;
      }

      assert(Aig_ObjIsAnd(r));
      Aig_Obj_t* f0 = Aig_ObjFanin0(r);
      Aig_Obj_t* f1 = Aig_ObjFanin1(r);

      const int v0 = varOfAig(f0);
      const int v1 = varOfAig(f1);
      if (v0 == -1)
      {
        work.push_back(f0);
        continue;
      }
      if (v1 == -1)
      {
        work.push_back(f1);
        continue;
      }

      // v <-> (l0 & l1)
      const int v = solver->newVar();
      const int l0 = 2 * v0 + (Aig_ObjFaninC0(r) ? 1 : 0);
      const int l1 = 2 * v1 + (Aig_ObjFaninC1(r) ? 1 : 0);

      addBinary(2 * v + 1, l0);
      addBinary(2 * v + 1, l1);

      SATSolver::vec_literals c;
      c.push(SATSolver::mkLit(v, false));
      c.push(SATSolver::mkLit(l0 >> 1, !(l0 & 1)));
      c.push(SATSolver::mkLit(l1 >> 1, !(l1 & 1)));
      addClause(c);

      setVarOfAig(r, v);
      work.pop_back();
    }
  }

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
    if (bm->UserFlags.enable_array_equality && containsArrayEquality(term))
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

  // Assertion-local, equivalence-preserving simplification, with a fresh
  // Simplifier so no cross-assertion state can exist: its substitution
  // map is empty, so everything it does to this one conjunct is a plain
  // equivalence. Measurably worth it on multi-round workloads; sharing a
  // Simplifier across conjuncts measured slower, so this stays per call.
  ASTNode simplifyAlone(const ASTNode& n)
  {
    SubstitutionMap localSm(bm);
    Simplifier localSimp(bm, &localSm);
    return localSimp.SimplifyFormula_TopLevel(n, false);
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
      // Swap rather than copy: the registry is the session's, and on a long
      // array session copying it in and back out again is a per-encode cost
      // proportional to every read ever seen.
      batchAT->arrayToIndexToRead.swap(myReads);
      batchAT->ack_pair.swap(myAckPairs);
      batchAT->recordTouchedReads = true;
      batchAT->touchedReads.clear();
      toEncode = batchAT->TransformFormula_TopLevel(toEncode);
      batchAT->recordTouchedReads = false;
      readsOfEncoded[key] = batchAT->touchedReads;
      myReads.swap(batchAT->arrayToIndexToRead);
      myAckPairs.swap(batchAT->ack_pair);
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
              myReads.find(ai.first);
          if (ait == myReads.end())
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
        bm->UserFlags.enable_array_equality && containsArrayEquality(n);
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
      ArrayTransformer::ArrType::const_iterator ait = myReads.find(ai.first);
      if (ait == myReads.end())
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

  void totalizeRegistrySymbols()
  {
    ScopedProfileTimer registryTimer(profile.enabled, profile.registryNs);
    // Only the refinement machinery encodes axioms over registry symbols,
    // and --ackermanize never refines.
    if (bm->UserFlags.ackermannisation)
      return;

    for (ArrayTransformer::ArrType::const_iterator it = myReads.begin();
         it != myReads.end(); ++it)
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

  // The same guarantee for the rows an extensionality round refines over.
  // Those rows live in the batch transformer's per-round table, not in the
  // persistent registry -- the round transforms on a fresh table by design
  // -- so totalizeRegistrySymbols cannot cover them. Idempotent (the bit
  // creation is memoised), so calling it before every refinement entry is
  // cheap, and necessary: the checker's lemma encodings can add rows
  // mid-round.
  void totalizeBatchRegistrySymbols()
  {
    ScopedProfileTimer registryTimer(profile.enabled, profile.registryNs);
    for (ArrayTransformer::ArrType::const_iterator it =
             batchAT->arrayToIndexToRead.begin();
         it != batchAT->arrayToIndexToRead.end(); ++it)
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

  size_t semanticCacheEntryCount() const
  {
    size_t rows = 0;
    for (ArrayTransformer::ArrType::const_iterator it = myReads.begin();
         it != myReads.end(); ++it)
      rows += it->second.size();
    return semanticEpochRoots.size() + fragmentCache.size() + rows +
           readsOfEncoded.size() +
           myAckPairs.size() + exactStackKeepAlive.size() +
           exactScopedPreprocessOf.size() + preparedPieceOf.size() +
           eliminationUsers.size() + screenedContent.size() +
           symbolsOfCache.size() + symbolVisitPages.size() +
           dagSizeBigMemo.size() + scopedBlockOf.size();
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

    // ArrayTransformer's maps free their nodes on clear, but the per-run
    // touched-read vector retains the largest exact block it has seen.
    batchAT->recordTouchedReads = false;
    releaseContainer(batchAT->touchedReads);

    if (fpCtx)
      ce->setFpEncodingContext(NULL);
    fpCtx.reset();
    adapter.reset();
    releaseContainer(symbolMapStorage);

    releaseContainer(fragmentCache);
    releaseContainer(myReads);
    releaseContainer(readsOfEncoded);
    releaseContainer(myAckPairs);
    releaseContainer(exactStackKeepAlive);
    releaseContainer(exactScopedPreprocessOf);
    releaseContainer(preparedPieceOf);
    releaseContainer(eliminationUsers);
    releaseContainer(screenedContent);
    releaseContainer(symbolsOfCache);
    releaseContainer(symbolVisitPages);
    symbolVisitEpoch = 0;
    releaseContainer(dagSizeBigMemo);
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
    releaseContainer(aigIdToVar);
    releaseContainer(rootLitOf);
    releaseContainer(aigRootOf);
    releaseContainer(permanentAigRoots);
    releaseContainer(pendingLiveCone.currentRoots);
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
    releaseContainer(semanticEpochRoots);
    semanticNodeCharge = 0;
    releaseContainer(latestSemanticLiveRoots);
    maxLiveSemanticNodes = 0;
    lastRetainedSemanticNodes = 0;

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

    aigIdToVar.clear();
    trueVar = -1;
    rootLitOf.clear();
    actLitOf.clear();
    everAssumedLits.clear();
    // Folding records describe readsOfEncoded from the OLD backend epoch.
    // Re-encoding can overwrite a key with a different row set (for example
    // after new permanent substitutions fold an index), so rebuild the
    // active-row view transactionally and queue every permanent key again.
    batchAT->arrayToIndexToRead.clear();
    batchAT->ack_pair.clear();
    lastSeededKeys.clear();
    seededRowRef.clear();
    foldedRowsOf.clear();
    clauseMassOf.clear();
    // Symbol sets are a pure function of the node, so this is reclamation,
    // not invalidation: entries for still-live nodes are simply re-derived
    // on the next solve that asks. SAT-only policy restarts may reclaim this
    // cheap memo even though they retain the structural AIG epoch.
    symbolsOfCache.clear();
    refinementMassOf.clear();
    currentRefinementClauseMass = 0;
    aigRootOf.clear();
    pendingLiveCone.currentRoots.clear();
    hasPendingLiveCone = false;
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
    if (dagSizeUpToMemo(conj, resimplifyLimit, dagSizeBigMemo) >
        resimplifyLimit)
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
                            bool requireCollapse = false)
  {
    PreprocessingTransaction result(PreprocessingMode::ExactStack, input);
    if (!bm->UserFlags.optimize_flag || input.isConstant())
    {
      result.accepted = !requireCollapse;
      result.conjuncts.push_back(input);
      return result;
    }

    // `requireCollapse` is part of the key: it changes both the acceptance
    // rule and the size gate, so the two callers must not share an entry.
    const std::pair<ASTNode, bool> memoKey(input, requireCollapse);
    std::map<std::pair<ASTNode, bool>,
             PreprocessingTransaction>::const_iterator memo =
        scopedBlockOf.find(memoKey);
    if (memo != scopedBlockOf.end())
      return memo->second;

    size_t before = 0;
    if (requireCollapse)
    {
      if (dagSizeUpTo(input, firstStackCollapseMinNodes - 1) <
          firstStackCollapseMinNodes)
      {
        PreprocessingTransaction& rejected = scopedBlockOf[memoKey];
        rejected = PreprocessingTransaction(PreprocessingMode::ExactStack,
                                            input);
        rejected.conjuncts.push_back(input);
        rejected.accepted = false;
        return rejected;
      }
      before = dagSizeUpTo(input, std::numeric_limits<size_t>::max());
    }

    SubstitutionMap scopedMap(bm);
    Simplifier scoped(bm, &scopedMap);
    ASTNode out = input;

    if (bm->UserFlags.bitConstantProp_flag)
    {
      simplifier::constantBitP::ConstantBitPropagation cb(
          bm, &scoped, bm->defaultNodeFactory, out);
      out = cb.topLevelBothWays(out);
      if (cb.isUnsatisfiable())
        out = bm->ASTFalse;
    }

    if (!out.isConstant() && bm->UserFlags.propagate_equalities)
    {
      PropagateEqualities pe(&scoped, bm->defaultNodeFactory, bm);
      out = pe.topLevel(out);
    }
    if (scoped.hasUnappliedSubstitutions())
      out = scoped.applySubstitutionMapAtTopLevel(out);

    if (!out.isConstant() && bm->UserFlags.enable_unconstrained)
    {
      RemoveUnconstrained remove(*bm);
      out = remove.topLevel(out, &scoped);
    }

    if (!out.isConstant() && bm->UserFlags.enable_pure_literals)
    {
      FindPureLiterals pure;
      if (pure.topLevel(out, &scoped, bm))
        out = scoped.applySubstitutionMapAtTopLevel(out);
    }

    if (scoped.hasUnappliedSubstitutions())
      out = scoped.applySubstitutionMapAtTopLevel(out);

    // Plain-BV first engagement uses this path only as a high-yield escape
    // from cross-level collapse cliffs. A modest rewrite can make the SAT
    // search shape worse while forfeiting the ordinary per-level roots, so
    // keep the raw exact-stack block unless the scoped trial at least halves
    // the DAG. No definitions have entered the model channel yet.
    if (requireCollapse && dagSizeUpTo(out, before / 2) > before / 2)
    {
      // A rejected trial commits no definitions (they would be model state
      // for a formula that is not being encoded), so the entry records only
      // the refusal.
      PreprocessingTransaction& rejected = scopedBlockOf[memoKey];
      rejected =
          PreprocessingTransaction(PreprocessingMode::ExactStack, input);
      rejected.conjuncts.push_back(input);
      rejected.accepted = false;
      return rejected;
    }

    PreprocessingTransaction& done = scopedBlockOf[memoKey];
    done = PreprocessingTransaction(PreprocessingMode::ExactStack, input);
    done.conjuncts.push_back(out);
    done.accepted = true;
    const ASTNodeSet retainedSymbols = symbolsOf(out);
    for (DenseNodeMap::const_iterator it = scoped.Return_SolverMap()->begin();
         it != scoped.Return_SolverMap()->end(); ++it)
    {
      if (it->first.GetKind() == SYMBOL &&
          retainedSymbols.find(it->first) != retainedSymbols.end())
        continue;
      done.addElimination(it->first, it->second);
    }
#ifndef NDEBUG
    // The third statement of the invariant preparePiece and
    // resimplifyBaseAtRebuild assert. Here it is true by construction -- the
    // loop above skips any key still present in the output, and this pass
    // keeps no definitions -- but that is a property of the `continue` three
    // lines up, not of the design, and it is what makes this pass's
    // unconstrained call safe without an untouchable set at all. Say so where
    // it can be checked rather than where it can be argued.
    for (const ScopedElimination& e : done.eliminated)
      assert(retainedSymbols.find(e.symbol) == retainedSymbols.end() &&
             "scoped block output mentions a variable it eliminated");
#endif
    bm->ASTNodeStats("Incremental exact stack after preprocessing: ", out);
    return done;
  }

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
      wants = !myReads.empty();
      for (size_t i = 0; !wants && i < assertionsSMT2.size(); i++)
      {
        const Fragment& f = fragment(assertionsSMT2[i]);
        wants = f.arrays || f.arrayEq;
      }
    }

    if (!wants)
      return;

    if (!solver->enableBVA() &&
        uf.cadical_factor == UserDefinedFlags::BVAMode::ON && !bvaWarned)
    {
      bvaWarned = true;
      std::cerr << "Warning: --cadical-factor was requested but the SAT "
                   "solver in use has no bounded variable addition to "
                   "enable; using its own settings instead."
                << std::endl;
    }
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
    return sat;
  }

  ASTNodeToSATVar& SATVar_to_SymbolIndexMap() override
  {
    d->symbolMapStorage.clear();
    d->buildSymbolMap(d->symbolMapStorage);
    return d->symbolMapStorage;
  }

  void ClearAllTables(void) override {}
};

ToSATBase* IncrementalSolver::Impl::ensureAdapter()
{
  if (!adapter)
    adapter.reset(new IncrementalToSAT(bm, this));
  return adapter.get();
}

// A plain-BV exact block is already fully encoded and has no theory model to
// refine. Solve it like the ordinary array-free driver: construct a model only
// when a caller can observe one, and defer that construction until its first
// reader unless --check-sanity needs it immediately. In particular, do not
// create the refinement adapter or force construct_counterexample_flag merely
// because cross-level preprocessing chose the exact-block representation.
SOLVER_RETURN_TYPE IncrementalSolver::Impl::solvePlainExactStack(
    const ASTVec& assertionsSMT2,
    const SATSolver::vec_literals& assumptions, const ASTNode& inputToSat,
    Aig_Obj_t* blockRegular)
{
  UserDefinedFlags& uf = bm->UserFlags;

  const bool construct = observableModelRequested(uf);
  uf.construct_counterexample_flag = construct;

  bm->GetRunTimes()->start(RunTimes::Solving);
  if (profile.enabled)
    profile.satCalls++;
  bool sat;
  {
    ScopedProfileTimer satTimer(profile.enabled, profile.satNs);
    ScopedProfileTimer initialSatTimer(profile.enabled, profile.initialSatNs);
    sat = solver->solveWithAssumptions(assumptions, bm->soft_timeout_expired);
  }
  bm->GetRunTimes()->stop(RunTimes::Solving);

  const uint64_t cheapLiveMass =
      addMass(baseLiveMass, clauseMassOf[inputToSat]);
  std::vector<Aig_Obj_t*> currentRoots(1, blockRegular);
  stageLiveConeMass(currentRoots, cheapLiveMass, permanentUnitMass);
  stageSemanticLiveStack(assertionsSMT2, ASTVec(1, inputToSat));

  if (uf.stats_flag)
    solver->printStats();

  if (bm->soft_timeout_expired)
    return SOLVER_TIMEOUT;

  if (!sat)
  {
    // The complete stack rode one assumption, so its core is deliberately
    // coarse even though this solve did not need the refinement adapter.
    recordUnsat(assumptions, assertionsSMT2.size(), true);
    return SOLVER_UNSATISFIABLE;
  }

  if (!construct)
    return SOLVER_SATISFIABLE;

  if (!uf.check_counterexample_flag)
  {
    modelPending = true;
    return SOLVER_SATISFIABLE;
  }

  bm->GetRunTimes()->start(RunTimes::CounterExampleGeneration);
  ce->ClearCounterExampleMap();
  ce->ClearComputeFormulaMap();
  seedEliminatedIntoModelChannel();
  // Eagerly instantiated array-equality rounds land here with lowered
  // floating-point terms in the block; model evaluation needs the context
  // that lowered them, exactly as the refinement paths wire it.
  if (fpCtx)
    ce->setFpEncodingContext(fpCtx.get());

  ToSATBase::ASTNodeToSATVar symbolMap;
  buildSymbolMap(symbolMap);
  ce->ConstructCounterExample(*solver, symbolMap);
  bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);

  // Check the raw assertions, rather than only the simplified block: scoped
  // eliminations are replayed through the model channel above, so this also
  // guards the exact preprocessing/model-reconstruction boundary.
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

  return SOLVER_SATISFIABLE;
}

// Encode the complete active stack as one assumption-scoped block. Whole-array
// equality always needs this route: extensionality owns the complete array
// graph, so every active read must be lowered and checked together. Explicit
// first engagement can also use it for a plain-BV stack, but only after the
// whole-stack preprocessing trial has at least halved the DAG; that narrowly
// recovers cases where a deep fact collapses a huge shallow root before the
// ordinary per-level driver would encode it. Generated names and the block
// root are deterministic, so retained clauses remain reusable. A rejected BV
// trial returns before any clause or model definition is committed and the
// caller continues through the ordinary path.
SOLVER_RETURN_TYPE
IncrementalSolver::Impl::exactStackCheckSat(
    const ASTVec& assertionsSMT2, bool firstForcedIncrementalSolve,
    bool requireScopedCollapse, bool* scopedAccepted)
{
  UserDefinedFlags& uf = bm->UserFlags;

  bool arrayEqualityRound = false;
  bool activeHasFp = false;
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    const Fragment& f = fragment(levelConjunction);
    arrayEqualityRound = arrayEqualityRound || f.arrayEq;
    activeHasFp = activeHasFp || f.fp;
  }
  profile.extensionality = arrayEqualityRound;
  ScopedProfileTimer extensionalityTimer(
      profile.enabled && arrayEqualityRound, profile.extensionalityNs);

  // Eager Ackermannization expands reads into if-then-else chains,
  // destroying the array structure the lazy procedure works on. As in the
  // batch pipeline, active equalities over plain bit-vector sorts are
  // instantiated pointwise over the solve's access indexes (below, once
  // the records are conjoined) and the round stays on the caller's eager
  // path; quotiented floating-point cells have no sound pointwise bit
  // instantiation and fall back to lemmas on demand for this round, with
  // the flag disabled and the batch pipeline's warning.
  const bool savedAck = uf.ackermannisation;

  ASTNode activeConjunction;
  if (assertionsSMT2.size() > 1)
    activeConjunction = bm->CreateNode(AND, assertionsSMT2);
  else
    activeConjunction = assertionsSMT2[0];

  // Plain-BV exact blocks have no extensionality state at all. Avoid creating
  // a context for them; besides the allocation, an empty context makes this
  // representation look needlessly like a theory-refinement solve.
  ExtensionalityContext* ext = NULL;
  if (arrayEqualityRound)
  {
    ext = bm->getExtensionality();
    ext->beginSolve();
  }

  ASTNodeMap arrayEqualityRewrites;
  ASTNode prepared = activeConjunction;
  if (activeHasFp)
  {
    prepared = fpContext()->prepare(prepared);
    fpContext()->copyArrayEqualityRewrites(arrayEqualityRewrites);
  }

  ASTNode semantic = prepared;
  if (arrayEqualityRound)
    semantic =
        ext->lowerArrayEqualities(prepared, arrayEqualityRewrites);
  ASTNode inputToSat = semantic;

  bool extActive = arrayEqualityRound && ext->active();
  // Releases the record-table seal on every exit from this function.
  ExtensionalityContext::SolveScope extScope(ext);

  if (extActive)
    inputToSat = ext->conjoinRecordConstraints(inputToSat);

  if (extActive && uf.ackermannisation)
  {
    const ASTNode eager = ext->instantiateEagerAckermann(inputToSat);
    if (!eager.IsNull())
    {
      // The equalities are now ordinary conjuncts of the block and the
      // records are retired: the round continues exactly as an eager
      // array round, reads expanded through the transform below, nothing
      // left for the lazy checker.
      inputToSat = eager;
      extActive = false;
      bm->ASTNodeStats("after eager equality instantiation: ", inputToSat);
    }
    else
    {
      std::cerr << "Warning: --ackermanize is disabled for queries with "
                   "array equality over floating-point sorts."
                << std::endl;
      uf.ackermannisation = false;
    }
  }

  // Automatic engagement already received two batch-preprocessed solves, so
  // its first persistent exact-stack block keeps the raw search shape and a
  // genuinely new later stack takes this pass. Explicit first engagement has
  // no such batch work to fall back on: preprocess its first block too, which
  // removes the broad forced-first ABV tail. The decision is fixed per raw
  // active conjunction above, so a repeated or re-pushed stack never flips
  // encoding strategy underneath the block cache.
  bool scopedPreprocess = false;
  if (policy.semanticPreprocessing())
    scopedPreprocess =
        exactScopedPreprocessOf
            .insert(std::make_pair(activeConjunction,
                                   engagedSolves > 1 ||
                                       firstForcedIncrementalSolve))
            .first->second;
  PreprocessingTransaction stackTransaction(PreprocessingMode::ExactStack,
                                             inputToSat);
  stackTransaction.conjuncts.push_back(inputToSat);
  if (scopedPreprocess)
  {
    stackTransaction =
        preprocessExactStackBlock(inputToSat, requireScopedCollapse);
    inputToSat = stackTransaction.conjuncts.front();
    if (!stackTransaction.accepted)
    {
      if (profile.enabled)
        profile.firstStackRejected++;
      exactScopedPreprocessOf.erase(activeConjunction);
      uf.ackermannisation = savedAck;
      if (scopedAccepted != NULL)
        *scopedAccepted = false;
      return SOLVER_UNDECIDED;
    }
    if (profile.enabled)
    {
      const size_t eliminated = stackTransaction.eliminatedSymbolCount();
      if (requireScopedCollapse)
      {
        profile.firstStackPreprocesses++;
        profile.firstStackEliminations += eliminated;
      }
      else
      {
        profile.extPreprocesses++;
        profile.extEliminations += eliminated;
      }
    }
  }

  if (scopedAccepted != NULL)
    *scopedAccepted = true;

  // Formula output and eliminated-definition replay become active together.
  // A rejected speculative block returned above without committing either.
  scopes.commitWholeStack(stackTransaction);

  if (activeHasFp)
    inputToSat = fpContext()->lowerPrepared(inputToSat);

  const bool extPrepared = extActive && !inputToSat.isConstant();
  if (extPrepared)
    inputToSat = ext->prepare(inputToSat);

  exactStackKeepAlive.insert(activeConjunction);
  exactStackKeepAlive.insert(prepared);
  exactStackKeepAlive.insert(semantic);
  exactStackKeepAlive.insert(inputToSat);
  chargeSemanticRoot(activeConjunction);
  chargeSemanticRoot(prepared);
  chargeSemanticRoot(semantic);
  chargeSemanticRoot(inputToSat);

  if (uf.enable_array_equality && containsArrayEquality(inputToSat))
    FatalError("IncrementalSolver: an opaque array equality reached the "
               "final array transformation boundary",
               inputToSat);

  // A fresh per-round registry: the whole-graph transform must neither see
  // the persistent lazy rows (it refuses reused legacy rows) nor leak its
  // own solve-local rows into them. The rows are left in place afterwards
  // -- model construction reads them -- until the next solve or pop clears
  // the batch tables as usual.
  batchAT->arrayToIndexToRead.clear();
  batchAT->ack_pair.clear();

  const bool arrayops = containsArrayOps(inputToSat, bm) || extActive;
  if (arrayops)
    inputToSat = batchAT->TransformFormula_TopLevel(inputToSat);
  if (extPrepared)
    ext->bindAfterTransform(batchAT);

  // Encode the block; its root is assumed, never asserted -- the block
  // spans every level, including the base. Every generated symbol in the
  // block (witnesses, scalar names, read abstractions) is named
  // deterministically by what it stands for, so an identical stack lowers
  // to the identical node and this cache hit makes the repeat round's
  // encoding free -- and the recycled names keep previously encoded
  // checker lemmas attached to the right SAT variables.
  // The block encodes the RAW stack -- the base's defining equations
  // included -- so it can mint bits for variables sigma0 eliminated. Those
  // equations hold inside the block only under its retractable literal; a
  // later ordinary round would read the then-unconstrained bits into
  // models and into the refinement loop's raw-stack evaluation. Restore
  // them as permanent units first (see restoreDroppedSigma0) -- always
  // sound, since the base only grows.
  restoreDroppedSigma0(inputToSat);

  int blockLit;
  Aig_Obj_t* blockRegular = NULL;
  bool blockReused = false;
  {
    NodeToLitMap::const_iterator hit = rootLitOf.find(inputToSat);
    if (hit != rootLitOf.end())
    {
      if (profile.enabled)
        profile.rootHits++;
      blockLit = hit->second;
      blockReused = true;
      blockRegular = aigRoot(inputToSat);
    }
    else
    {
      if (profile.enabled)
        profile.rootMisses++;
      ScopedProfileTimer encodingTimer(profile.enabled, profile.encodeNs);
      const uint64_t submittedBefore = solver->submittedClauses();
      bm->GetRunTimes()->start(RunTimes::BitBlasting);
      BBNodeAIG root = encoding.blaster().BBForm(inputToSat);
      bm->GetRunTimes()->stop(RunTimes::BitBlasting);
      bm->GetRunTimes()->start(RunTimes::CNFConversion);
      blockRegular = Aig_Regular(root.n);
      ensureEncoded(blockRegular);
      blockLit =
          2 * varOfAig(blockRegular) + (Aig_IsComplement(root.n) ? 1 : 0);
      bm->GetRunTimes()->stop(RunTimes::CNFConversion);
      rootLitOf[inputToSat] = blockLit;
      aigRootOf[inputToSat] = blockRegular;
      clauseMassOf[inputToSat] =
          solver->submittedClauses() - submittedBefore;
    }
  }
  assert(blockRegular != NULL);

  // Refinement lemmas are encoded over the abstraction/witness/scalar
  // names; give every bit of every such symbol a variable before the
  // first solve, fresh and unconstrained where the blasted block never
  // needed it -- the meaning ToSATAIG's lemma-only path assigns.
  if (extActive)
  {
    for (const ASTNode& s : ext->getFrozenSymbols())
      totalizeSymbol(s);
    for (const ASTNode& s : ext->getLemmaOnlySymbols())
      totalizeSymbol(s);
  }

  if (uf.stats_flag)
  {
    std::cerr << "Incremental: "
              << (arrayEqualityRound ? "array-equality" : "first scoped BV")
              << " round, block of "
              << assertionsSMT2.size() << " levels "
              << (blockReused ? "reused" : "encoded") << ", solver has "
              << solver->nVars() << " variables" << std::endl;
  }

  if (uf.timeout_max_conflicts >= 0)
    solver->setMaxConflicts(uf.timeout_max_conflicts);
  if (uf.timeout_max_time >= 0)
    solver->setMaxTime(uf.timeout_max_time);
  bm->soft_timeout_expired = false;

  SATSolver::vec_literals assumptions;
  if (policy.retractionSearchHints())
    everAssumedLits[blockLit] = engagedSolves;
  assumptions.push(SATSolver::mkLit(blockLit >> 1, blockLit & 1));
  hintRetractedLevels(assumptions);
  if (profile.enabled)
  {
    profile.activeKeys = 1;
    profile.assumptions = assumptions.size();
  }

  // An array-equality round whose equalities were eagerly instantiated --
  // or simplified away before lowering -- while --ackermanize remains in
  // force has been compiled onto the ordinary eager path: reads expanded
  // by the transform above, nothing for the lazy checker or read
  // refinement to do. Solve it like the plain block it now is.
  if (!arrayEqualityRound || (uf.ackermannisation && !extActive))
    return solvePlainExactStack(assertionsSMT2, assumptions, inputToSat,
                                blockRegular);

  // Array equality needs a candidate model on every refinement round. Keep
  // that internal requirement distinct from whether this query's caller is
  // entitled to observe the resulting model. In particular, the incoming
  // derived flag may still describe an earlier query (and is false before a
  // session's first query), so restoring it would lose :produce-models.
  const bool constructForCaller = observableModelRequested(uf);
  uf.construct_counterexample_flag = true;

  if (fpCtx)
    ce->setFpEncodingContext(fpCtx.get());

  seedEliminatedIntoModelChannel();

  IncrementalToSAT* tosat = static_cast<IncrementalToSAT*>(ensureAdapter());
  tosat->setAssumptions(&assumptions);

  // Congruence axioms are encoded straight over the bit variables of the
  // round registry's read symbols, and the block's cone may have needed
  // only some of a symbol's bits (the frozen/lemma-only totalisation
  // above covers the checker's symbols, not the registry rows). This
  // matters most for the hybrid below: a round routed here for an array
  // equality that simplified away runs ordinary read refinement with the
  // checker inactive.
  totalizeBatchRegistrySymbols();
  ArrayReadRefinementProgress readRefinementProgress;

  const uint64_t refinementClausesBefore = solver->submittedClauses();
  ScopedProfileTimer refinementTimer(profile.enabled, profile.refinementNs);
  SOLVER_RETURN_TYPE res = ce->CallSAT_ResultCheck(
      *solver, bm->ASTTrue, semantic, prepared, tosat, true);

  // The refinement driver, as in TopLevelSTPAux: with an active equality
  // the checker owns every read, so each undecided candidate must carry a
  // pending theory lemma; without one, ordinary read refinement runs.
  size_t refinementRounds = 0;
  while (res == SOLVER_UNDECIDED)
  {
    refinementRounds++;
    // Re-totalize: the checker's lemma encodings can introduce new reads,
    // whose rows joined the table after the pass above. Memoised, so a
    // round that added nothing pays nothing.
    totalizeBatchRegistrySymbols();
    if (extActive)
    {
      if (!ext->hasPendingLemma())
        FatalError("IncrementalSolver: an active array-equality refinement "
                   "round has neither a decision nor a pending lemma");
      ext->encodePendingLemmas(*solver, tosat);
      res = ce->CallSAT_ResultCheck(*solver, bm->ASTTrue, semantic, prepared,
                                    tosat, true);
    }
    else
    {
      // The hybrid case: routed here for an array equality that simplified
      // away, so ordinary read refinement runs. Progress is a newly emitted
      // logical congruence axiom, not a fresh CNF circuit for an old one.
      const size_t emittedBefore =
          readRefinementProgress.emittedAxiomCount();
      res = ce->SATBased_ArrayReadRefinement(
          *solver, semantic, tosat, &readRefinementProgress);
      if (res == SOLVER_UNDECIDED &&
          readRefinementProgress.emittedAxiomCount() == emittedBefore)
        FatalError("IncrementalSolver: an array-equality round fell back to "
                   "read refinement, rejected the candidate and emitted no "
                   "new logical axiom -- the encoding and model evaluation "
                   "disagree");
    }
  }

  tosat->setAssumptions(NULL);
  uf.ackermannisation = savedAck;
  uf.construct_counterexample_flag = constructForCaller;

  if (uf.stats_flag && refinementRounds > 0)
    std::cerr << "Incremental: array-equality refinement converged after "
              << refinementRounds << " rounds" << std::endl;
  if (profile.enabled)
    profile.refinementRounds += refinementRounds;

  accountRefinementClauses(inputToSat, refinementClausesBefore);
  const uint64_t theoryMass = refinementMass(inputToSat);
  uint64_t cheapLiveMass = addMass(baseLiveMass, clauseMassOf[inputToSat]);
  cheapLiveMass = addMass(cheapLiveMass, theoryMass);
  std::vector<Aig_Obj_t*> currentRoots(1, blockRegular);
  stageLiveConeMass(currentRoots, cheapLiveMass,
                    addMass(permanentUnitMass, theoryMass));
  stageSemanticLiveStack(assertionsSMT2, ASTVec(1, inputToSat));

  // The whole round rode one block literal, so an unsat answer has no
  // per-level or per-assumption granularity: the core is everything.
  if (res == SOLVER_UNSATISFIABLE)
    recordUnsat(assumptions, assertionsSMT2.size(), true);

  return res;
}

IncrementalSolver::IncrementalSolver(STPMgr* bm, AbsRefine_CounterExample* ce,
                                     Simplifier* batchSimp,
                                     ArrayTransformer* batchAT)
    : impl(new Impl(bm, ce, batchSimp, batchAT))
{
}

std::vector<std::pair<ASTNode, ASTNode>>
IncrementalSolver::seededReadsForTesting() const
{
  std::vector<std::pair<ASTNode, ASTNode>> out;
  for (std::map<std::pair<ASTNode, ASTNode>, size_t>::const_iterator it =
           impl->seededRowRef.begin();
       it != impl->seededRowRef.end(); ++it)
    if (impl->myReads.find(it->first.first) != impl->myReads.end() &&
        impl->myReads.find(it->first.first)
                ->second.find(it->first.second) !=
            impl->myReads.find(it->first.first)->second.end())
      out.push_back(it->first);
  return out;
}

IncrementalSolver::EncodingEpochStats
IncrementalSolver::encodingEpochStatsForTesting() const
{
  EncodingEpochStats out;
  out.generation = impl->encodingEpochGeneration;
  out.aigAndNodes = impl->encoding.aigAndNodes();
  out.rootEncodings = impl->rootLitOf.size();
  out.bitBlastedSymbols =
      impl->encoding.nodes().symbolToBBNode.size();
  out.semanticCacheEntries = impl->semanticCacheEntryCount();
  for (ArrayTransformer::ArrType::const_iterator it = impl->myReads.begin();
       it != impl->myReads.end(); ++it)
    out.arrayReadRows += it->second.size();
  return out;
}

bool IncrementalSolver::lastSolveWasUnsat() const
{
  return impl->lastUnsat;
}

bool IncrementalSolver::lastUnsatHasAssumptionGranularity() const
{
  return impl->lastUnsat && !impl->lastUnsatCoarse &&
         impl->lastLevelIndividual;
}

std::vector<ASTNode> IncrementalSolver::lastUnsatAssumptionConjuncts() const
{
  std::vector<ASTNode> out;
  if (!lastUnsatHasAssumptionGranularity())
    return out;
  const std::unordered_set<int> failed(impl->lastFailedLits.begin(),
                                       impl->lastFailedLits.end());
  for (const std::pair<int, ASTNode>& lc : impl->lastLevelLitConjuncts)
  {
    if (failed.count(lc.first))
      out.push_back(lc.second);
  }
  return out;
}

std::vector<size_t> IncrementalSolver::lastUnsatCoreLevels() const
{
  std::vector<size_t> out;
  if (!impl->lastUnsat)
    return out;
  if (impl->lastUnsatCoarse)
  {
    for (size_t i = 1; i < impl->lastLevelCount; i++)
      out.push_back(i);
    return out;
  }
  const std::unordered_set<int> failed(impl->lastFailedLits.begin(),
                                       impl->lastFailedLits.end());
  std::unordered_set<size_t> seen;
  // A promoted level is asserted unconditionally, so every refutation
  // may rest on it without any assumption failing: the core is floored
  // at the promoted prefix, and the caller's verdict cache can never
  // record an unsat above a level that may have carried it.
  for (size_t i = 1;
       i <= impl->scopes.promotedDepth() && i < impl->lastLevelCount; i++)
  {
    if (seen.insert(i).second)
      out.push_back(i);
  }
  for (const std::pair<int, size_t>& ll : impl->assumedLitLevels)
  {
    if (failed.count(ll.first) && seen.insert(ll.second).second)
      out.push_back(ll.second);
  }
  std::sort(out.begin(), out.end());
  return out;
}

IncrementalSolver::~IncrementalSolver()
{
  // The counterexample machinery may still point at our floating-point
  // encoding context; whoever solves next installs their own before any
  // model is read (and model_valid already refuses stale reads).
  if (impl->fpCtx)
    impl->ce->setFpEncodingContext(NULL);

  // Withdraw what this driver seeded into the batch Simplifier's SolverMap.
  // That channel is shared and is never cleared between solves -- the batch
  // pipeline owns entries of its own in it -- which is why
  // seedEliminatedIntoModelChannel withdraws at the START of every solve: a
  // stale entry from a popped branch SHADOWS a live one, because insert()
  // does not overwrite. The protocol covered every transition except the
  // last one, so this object could be destroyed leaving its entries in a map
  // that outlives it.
  //
  // Be exact about what this is worth. No reachable wrong answer is being
  // fixed: both frontends clear the map first -- reset() and
  // resetAssertions() call resetSolver() before resetIncrementalSolver(),
  // and ~STP() calls ClearAllTables() before deleteObjects() -- so in-tree
  // the entries are already gone by the time we get here, and there is no
  // test that can fail without this. It is here because IncrementalSolver is
  // public API an embedder constructs and destroys directly, and a class
  // whose invariant holds only because its caller tidies up first is one
  // refactor away from not holding. Defence, not a fix.
  //
  // Ordering is safe on both teardown paths: deleteObjects() destroys this
  // driver before it deletes the Simplifier, and resetIncrementalSolver()
  // runs while the whole STP object is alive.
  if (impl->batchSimp != NULL)
  {
    DenseNodeMap* channel = impl->batchSimp->Return_SolverMap();
    for (const ASTNode& k : impl->seededModelKeys)
      channel->erase(k);
    impl->seededModelKeys.clear();
  }
}

bool IncrementalSolver::forcedFirstSolve(bool forcedFromStart,
                                        size_t solvesRun)
{
  return forcedFromStart && solvesRun == 0;
}

bool IncrementalSolver::automaticEngagementReady(int64_t configuredThreshold,
                                                bool delayedBvLogic,
                                                size_t solvesRun)
{
  // A targeted 107-session sweep found solve 32 the best finite compromise
  // for pure QF_BV/QF_ABV: engaging later or never made common batch-friendly
  // cases faster but lost incremental-friendly long sessions. Everything else
  // -- floating point, arrays outside QF_ABV, unknown logics -- engages on the
  // third, keeping two batch warm-ups.
  int64_t engageAt = configuredThreshold;
  if (engageAt < 0)
    engageAt = delayedBvLogic ? 32 : 3;
  if (engageAt <= 0)
    return false;
  return solvesRun >= static_cast<size_t>(engageAt - 1);
}

bool IncrementalSolver::canHandle(const ASTVec& assertionsSMT2)
{
  // Every construct the SMT-LIB frontend can produce is covered: plain
  // bit-vectors, arrays (lazy or --ackermanize), floating point, and
  // whole-array equality. The method remains the seam for any future
  // exclusion.
  (void)assertionsSMT2;
  return true;
}

SOLVER_RETURN_TYPE IncrementalSolver::checkSat(const ASTVec& assertionsSMT2,
                                               bool assumeLastLevelPerConjunct,
                                               bool firstForcedIncrementalSolve)
{
  impl->beginProfile(assertionsSMT2.size());
  const SOLVER_RETURN_TYPE result = checkSatBody(
      assertionsSMT2, assumeLastLevelPerConjunct, firstForcedIncrementalSolve);
  impl->finishProfile();
  return result;
}

void IncrementalSolver::materializePendingModel()
{
  if (!impl->modelPending)
    return;
  impl->modelPending = false;
  buildPendingModel();
}

void IncrementalSolver::buildPendingModel()
{
  STPMgr* bm = impl->bm;
  bm->GetRunTimes()->start(RunTimes::CounterExampleGeneration);
  impl->ce->ClearCounterExampleMap();
  impl->ce->ClearComputeFormulaMap();

  impl->seedEliminatedIntoModelChannel();
  // The solve that deferred this model may not have wired the context
  // itself (the plain exact-stack route does not); lowered floating-point
  // terms evaluate through the context that lowered them.
  if (impl->fpCtx)
    impl->ce->setFpEncodingContext(impl->fpCtx.get());

  ToSATBase::ASTNodeToSATVar symbolMap;
  impl->buildSymbolMap(symbolMap);
  impl->ce->ConstructCounterExample(*impl->solver, symbolMap);
  bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);

  if (bm->UserFlags.stats_flag)
    std::cerr << "Incremental: model materialized on demand" << std::endl;
}

SOLVER_RETURN_TYPE
IncrementalSolver::checkSatBody(const ASTVec& assertionsSMT2,
                                          bool assumeLastLevelPerConjunct,
                                          bool firstForcedIncrementalSolve)
{
  STPMgr* bm = impl->bm;
  UserDefinedFlags& uf = bm->UserFlags;

  assert(!assertionsSMT2.empty());

  impl->currentLiveClauseMass = 0;

  // The unsat story is per solve; a stale one must not answer for this
  // call.
  impl->lastUnsat = false;
  impl->lastUnsatCoarse = false;
  impl->lastLevelIndividual = false;
  impl->modelPending = false;
  impl->assumedLitLevels.clear();
  impl->lastLevelLitConjuncts.clear();
  impl->lastFailedLits.clear();
  {
    ScopedProfileTimer maintenanceTimer(impl->profile.enabled,
                                        impl->profile.maintenanceNs);

    // Promoted-prefix bookkeeping first: if a promoted level changed or
    // vanished, its units no longer describe the stack and the solver
    // restarts here, before any routing can touch it.
    impl->updateStackStability(assertionsSMT2);

    // The relief valve: once the solver is past the configured size and most
    // of its encodings belong to content no longer on the stack, start it
    // over from the live stack. Checked before routing so extensionality
    // rounds benefit too. Deadness is measured by CLAUSE MASS against the
    // peak live mass any solve has used since the last rebuild -- conjunct
    // counts, the original proxy, missed variant-push sessions whose few
    // dozen distinct conjuncts each carry a huge circuit (a million
    // variables of ~95% popped content never tripped the count ratio) --
    // and comparing with the PEAK is the hysteresis: after a rebuild the
    // tracked mass restarts at the working set, so firing again takes
    // another fourfold growth.
    if (impl->clauseReliefSizeReached() && impl->reliefRatioReached())
      impl->expandPendingLiveConeMass();

    const bool clauseRelief =
        impl->clauseReliefSizeReached() && impl->reliefRatioReached();
    // Semantic caches have an independent DAG-node floor. Their cheap charge
    // only stages the decision; semanticReliefReached walks exact retained
    // and live unions, so a monotonically growing stack whose snapshots share
    // almost everything is not mistaken for dead churn.
    const bool semanticRelief = impl->semanticReliefReached();
    if (clauseRelief || semanticRelief)
    {
      if (uf.stats_flag)
        std::cerr << "Incremental: re-encoded from scratch (solver had "
                  << impl->solver->nVars() << " variables, "
                  << impl->retainedClauseMass()
                  << " retained clauses for a "
                  << impl->maxLiveClauseMass << " clause working set, "
                  << impl->lastRetainedSemanticNodes
                  << " retained semantic DAG nodes for a "
                  << impl->maxLiveSemanticNodes << " node working set)"
                  << std::endl;
      impl->rebuildEncodings(assertionsSMT2, Impl::RebuildReason::Relief);
    }

    // Probe-based inprocessing is the opposite trade to the valve above:
    // it re-runs over the WHOLE persistent encoding at every solve, so on
    // many-solve sessions its recurring cost dominates what it earns
    // (measured 2x of the total runtime on generated variant-push
    // corpora), while a session that is one or two big searches genuinely
    // profits from it. The option is configuration-window-only, so
    // retirement -- once the session qualifies, or immediately under an
    // explicit 'off' -- means one bounded rebuild onto a fresh solver
    // configured without it. AUTO additionally requires a base which has
    // stayed fixed throughout the observation window: new permanent clauses
    // give inprocessing new work, and disabling elimination on that shape
    // made later VexRiscv proofs time out. Trail reuse must also have been
    // retired already: a session still riding the trail is the
    // many-small-queries shape whose accumulated search state a rebuild
    // would throw away for a technique that measured neutral there. The
    // capability is probed without touching the live solver, and a backend
    // that cannot control it simply never retires.
    // A frontend may claim a forced FIRST solve only before this driver has
    // engaged at all: four preprocessing policies below read that claim and
    // would otherwise apply to a solve that DID have batch-preprocessed
    // predecessors. The driver cannot derive the fact -- it is a session
    // fact, not an object one -- but it can check the one direction that
    // must hold, which is exactly the mis-plumbing a new frontend would
    // introduce by passing its forced flag and forgetting the ordinal.
    assert((!firstForcedIncrementalSolve || impl->engagedSolves == 0) &&
           "a forced first solve was claimed after the driver had engaged");
    impl->engagedSolves++;
    if (!impl->inprobingRetired &&
        ((uf.incremental_inprobing == UserDefinedFlags::BVAMode::OFF &&
          impl->solver->supportsInprobingControl()) ||
         (impl->inprobingRetirementEarned() && !impl->trailReuseAllowed)))
    {
      impl->inprobingRetired = true;
      if (uf.stats_flag)
        std::cerr << "Incremental: inprobing retired (" << impl->engagedSolves
                  << " solves), solver restarted without it" << std::endl;
      impl->rebuildEncodings(assertionsSMT2, Impl::RebuildReason::Inprobing);
    }

    // Early FP is still strong evidence to start without trail reuse. The
    // ambiguous late-transition policy is specific to source array+FP
    // sessions: observe up to three FP checks before classifying one, then
    // retire a still-small state or let a growing state reach the existing
    // inprobing boundary so both configuration changes cost one rebuild.
    // Array-free QF_BVFP retains its established trail; applying the array
    // policy there lost five measured solves. Arrays introduced internally by
    // FP totalisation do not change that classification. Refinement-heavy
    // array state gets the old size belt instead.
    if (impl->policy.adaptiveBackendConfiguration() &&
        impl->trailReuseAllowed)
    {
      bool retire = impl->solver->nVars() >= Impl::trailReuseVarLimit;
      bool hasFp = false;
      for (size_t i = 0; !hasFp && i < assertionsSMT2.size(); i++)
        hasFp = impl->fragment(assertionsSMT2[i]).fp;
      if (!retire && hasFp)
      {
        const bool earlyFp =
            impl->engagedSolves < Impl::trailReuseFpRetireSolves;
        const bool refinementHeavy =
            impl->currentRefinementClauseMass >=
            Impl::trailReuseRefinementClauseFloor;
        const bool canRetireInprobingWithTrail =
            impl->inprobingRetirementEarned();
        const bool smallLateFpState =
            impl->lateArrayFpSolvesWithTrail >=
                Impl::trailReuseLateArrayFpProbeSolves &&
            impl->solver->nVars() < Impl::trailReuseEstablishedVarFloor;

        retire = earlyFp ||
                 (impl->sourceArraysSeen && !refinementHeavy &&
                  (canRetireInprobingWithTrail || smallLateFpState));
        if (!retire && impl->sourceArraysSeen)
          impl->lateArrayFpSolvesWithTrail++;
      }
      if (retire)
      {
        impl->trailReuseAllowed = false;
        if (uf.stats_flag)
          std::cerr << "Incremental: trail reuse retired ("
                    << impl->solver->nVars()
                    << " variables after " << impl->engagedSolves
                    << " solves), solver restarted without it" << std::endl;
        // If the session already qualifies for inprobing retirement --
        // whose AUTO gate waits for exactly this trail retirement -- take
        // both in ONE rebuild. Left to its own block, the retirement
        // would fire on the NEXT solve and rebuild a freshly re-encoded
        // solver all over again; a session whose trail died at fifty
        // thousand variables measured 2x slower from that double rebuild.
        if (!impl->inprobingRetired && impl->inprobingRetirementEarned())
        {
          impl->inprobingRetired = true;
          if (uf.stats_flag)
            std::cerr << "Incremental: inprobing retired with it ("
                      << impl->engagedSolves << " solves)" << std::endl;
        }
        impl->rebuildEncodings(assertionsSMT2, Impl::RebuildReason::Trail);
      }
    }

    // The backend's configuration window closes at its first clause; take
    // the bounded-variable-addition decision while it is still open. This
    // must precede the extensionality routing below: an equality round
    // encodes into the same persistent solver.
    impl->decideBVA(assertionsSMT2);

    // Retire stale retraction bookkeeping here, inside the maintenance block,
    // rather than after the routing below: an all-array-equality session
    // returns through the extensionality path and never reached it, so its
    // hint list grew one entry per distinct block root for the life of the
    // epoch and every solve hinted all of them. The precondition is the
    // configuration window, which decideBVA has just closed -- the pins are
    // clauses.
    if (impl->policy.aggregateLevelAssumptions())
      impl->retireStaleActivation();
  }

  // Whole-array equality routes the entire check-sat through the
  // extensionality block: the procedure owns the round's complete array
  // graph, so no conjunct may be encoded separately this round. New
  // base-level conjuncts stay out of level0Asserted and simply become
  // permanent units in a later equality-free round; this round the block
  // covers them.
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    if (impl->fragment(levelConjunction).arrayEq)
      return impl->exactStackCheckSat(assertionsSMT2,
                                      firstForcedIncrementalSolve);
  }

  // Explicit first engagement has no earlier batch solve to collapse facts
  // across level boundaries. Try the same exact-stack preprocessing used by
  // array-equality blocks for a plain-BV stack, but adopt it only when the
  // complete DAG at least halves. This catches the CPAchecker shape where a
  // deep unit makes a huge shallow disjunction trivial; modest rewrites fall
  // through to the ordinary per-level driver, preserving its reusable roots
  // and search shape. check-sat-assuming stays per-conjunct so its failed
  // assumptions remain reportable. An explicitly aggressive relief threshold
  // also keeps ordinary ownership from the outset; a provisional block would
  // otherwise hide the live-root accounting that configuration asks to use.
  const bool provisionalBlockAllowed =
      uf.incremental_reencode_limit == 0 ||
      uf.incremental_reencode_limit >= Impl::firstStackMinReencodeLimit;
  if (impl->policy.firstSolveShortcuts() && firstForcedIncrementalSolve &&
      !assumeLastLevelPerConjunct &&
      provisionalBlockAllowed && assertionsSMT2.size() > 1)
  {
    bool plainBv = true;
    for (const ASTNode& levelConjunction : assertionsSMT2)
    {
      const Fragment& f = impl->fragment(levelConjunction);
      if (f.arrays || f.arrayEq || f.fp)
      {
        plainBv = false;
        break;
      }
    }
    if (plainBv)
    {
      bool accepted = false;
      const SOLVER_RETURN_TYPE result =
          impl->exactStackCheckSat(assertionsSMT2,
                                   firstForcedIncrementalSolve, true,
                                   &accepted);
      if (accepted)
        return result;
    }
  }

  // No active equality this round, so no stale equality state may survive
  // into it: the consistency checker keys off ext->active(), and a
  // previous round's solve-local records would send this round's model to
  // a checker expecting values for symbols it never encoded. The SMT-LIB2
  // pop clears this itself, but the C API's vc_pop deliberately clears
  // nothing (its model outlives the bracket), and check-sat-assuming's
  // frame pop keeps the model too -- so the round boundary is here.
  ExtensionalityContext* staleExt = bm->getExtensionalityIfAny();
  if (staleExt != NULL && staleExt->active())
    staleExt->beginSolve();

  const uint64_t clausesBefore = impl->lifetimeClauseSubmissions();
  impl->encodesThisCall = 0;

  ProfileClock::time_point semanticStarted;
  if (impl->profile.enabled)
    semanticStarted = ProfileClock::now();

  // Constant-bit propagation state persists across calls. A pop, changed
  // level, or base growth rolls the engine and caller overlay back to their
  // longest common prefix; the diagnostic reset mode rebuilds that prefix
  // instead. The rewrite/fact memo has its own matching-prefix watermark
  // (see cbpFeedLevel/cbpAdopt and IncrementalScopeState::CbpMemo).
  bool cbpBootstrapDeferred = false;
  if (impl->policy.crossLevelPropagation())
  {
    ScopedProfileTimer cbpTimer(impl->profile.enabled, impl->profile.cbpNs);
    ScopedProfileTimer syncTimer(impl->profile.enabled,
                                 impl->profile.cbpSyncNs);

    // A forced first solve has no CBP prefix to reuse yet. Building a large
    // engine for that one solve was the dominant remaining cost on the
    // CPAchecker QF_BV first-check family, usually with no adoption at all.
    // Leave the engine genuinely empty for this call; if another real solve
    // follows, its ordinary prefix feed builds the complete current state.
    // Automatic sessions never request this flag: it specifically identifies
    // a first solve forced through the driver by explicit --incremental.
    const int64_t configuredBootstrapLimit =
        uf.incremental_cbp_bootstrap_limit;
    if (firstForcedIncrementalSolve && configuredBootstrapLimit > 0 &&
        uf.optimize_flag && uf.bitConstantProp_flag &&
        assertionsSMT2.size() > 1 && impl->scopes.cbpFedDepth() == 0 &&
        impl->scopes.cbpMemoDepth() == 0)
    {
      const size_t limit =
          clampToSize(static_cast<uint64_t>(configuredBootstrapLimit));
      cbpBootstrapDeferred = impl->cbpStackExceeds(assertionsSMT2, limit);
      if (cbpBootstrapDeferred)
      {
        if (impl->profile.enabled)
          impl->profile.cbpBootstrapDeferred++;
        if (uf.stats_flag)
          std::cerr << "Incremental: deferred large first-solve cbp "
                       "bootstrap"
                    << std::endl;
      }
    }

    const size_t lcp = impl->scopes.cbpFedCommonPrefix();
    if (impl->profile.enabled)
      impl->profile.stablePrefix = lcp;
    const bool diverged = lcp < impl->scopes.cbpFedDepth();
    if (diverged)
    {
      if (impl->profile.enabled)
        impl->profile.cbpDivergences++;
      // Futility accounting: an epoch (the span since the last
      // divergence) that adopted nothing lengthens the barren run;
      // one fresh adoption clears it.
      if (impl->cbpEpochAdopted == 0)
      {
        impl->cbpBarrenDivergences++;
        const size_t leash = impl->cbpEverFixed
                                 ? Impl::cbpRetireBarrenFixed
                                 : Impl::cbpRetireBarrenNeverFixed;
        if (!impl->cbpSessionRetired && impl->cbpBarrenDivergences >= leash)
        {
          impl->cbpSessionRetired = true;
          if (uf.stats_flag)
            std::cerr << "Incremental: cbp retired for the session ("
                      << impl->cbpBarrenDivergences
                      << " adoption-free stack divergences)" << std::endl;
        }
      }
      else
      {
        impl->cbpBarrenDivergences = 0;
      }
      impl->cbpEpochAdopted = 0;

      const size_t fedLevelsBefore = impl->scopes.cbpFedDepth();
      const bool aligned =
          impl->callCbp.get() != NULL &&
          impl->callCbp->levelCount() == fedLevelsBefore &&
          impl->cbpCallerCheckpoints.size() == fedLevelsBefore &&
          !impl->cbpCallerLevelOpen && impl->callCbpDeferred.empty();
      const bool useRollback =
          !impl->cbpSessionRetired && !uf.incremental_cbp_reset && aligned;
      if (useRollback)
      {
        ScopedProfileTimer rollbackTimer(impl->profile.enabled,
                                         impl->profile.cbpRollbackNs);
        const IncrementalCBP::RollbackStats stats =
            impl->callCbp->rollbackTo(lcp);
        const size_t callerEntries = impl->cbpRollbackCallerTo(lcp);
        assert(stats.levels == fedLevelsBefore - lcp);
        assert(impl->callCbp->levelCount() == lcp);
        assert(impl->cbpCallerCheckpoints.size() == lcp);
        assert(impl->scopes.cbpFedDepth() == lcp);
        if (impl->profile.enabled)
        {
          impl->profile.cbpRollbacks++;
          impl->profile.cbpRolledLevels += stats.levels;
          impl->profile.cbpRollbackFixed += stats.fixedStates;
          impl->profile.cbpRollbackCreated += stats.createdFixedStates;
          impl->profile.cbpRollbackDependencies += stats.dependencyNodes;
          impl->profile.cbpRollbackMultiplications +=
              stats.multiplicationStates;
          impl->profile.cbpRollbackCallerEntries += callerEntries;
        }
      }
      else
      {
        ScopedProfileTimer resetTimer(impl->profile.enabled,
                                      impl->profile.cbpResetNs);
        if (impl->profile.enabled)
          impl->profile.cbpResets++;
        impl->cbpReset();
      }
    }

    impl->cbpMemoStable = impl->scopes.trimCbpMemoToCurrent();
  }
  else
  {
    impl->cbpMemoStable = 0;
    if (impl->profile.enabled)
      impl->profile.stablePrefix = impl->scopes.lastCommonPrefix();
  }
  impl->callCbpAdopted = 0;
  impl->callCbpReplayed = 0;
  impl->callCbpOff = !impl->policy.crossLevelPropagation() ||
                     impl->cbpSessionRetired || cbpBootstrapDeferred ||
                     impl->cbpOverFeedCap();
  impl->callCbpConflict = false;

  // Base level: every conjunct becomes a permanent unit clause, once. The
  // base level only grows (reset destroys this object), so this is monotone
  // and sound even though the level's conjunction node is re-collapsed --
  // and possibly re-simplified -- on every call.
  // A rebuild left the re-simplified base waiting for this point: the
  // backend's configuration window is decided and equality-free rounds
  // reach here, so the replacements encode as this round's units.
  // (level0Asserted kept the RAW keys, so the loop below skips them.)
  if (!impl->pendingRebuiltBase.empty())
  {
    for (const ASTNode& c : impl->pendingRebuiltBase)
    {
      const int lit = impl->rootLit(c);
      SATSolver::vec_literals unit;
      unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
      impl->addClause(unit);
      impl->baseLiveMass = Impl::addMass(
          impl->baseLiveMass, Impl::addMass(impl->clauseMassOf[c], 1));
      impl->recordPermanentRoot(c);
    }
    impl->pendingRebuiltBase.clear();
  }

  ASTVec conjuncts;
  splitConjuncts(assertionsSMT2[0], bm->ASTTrue, conjuncts);

  ASTVec newLevel0;
  for (const ASTNode& c : conjuncts)
  {
    if (!impl->level0Asserted.insert(c).second)
      continue;
    impl->pendingBaseSeed.push_back(c);
    newLevel0.push_back(c);
    // New content first invalidates any cached level whose elimination it
    // contradicts, and joins the base symbol set the privacy check
    // consults -- both before anything is harvested or encoded.
    if (impl->policy.semanticPreprocessing())
    {
      ScopedProfileTimer screenTimer(impl->profile.enabled,
                                     impl->profile.screenNs);
      impl->screenNewContent(c);
    }
    if (impl->policy.semanticPreprocessing())
    {
      const ASTNodeSet& syms = impl->symbolsOf(c);
      impl->baseSymbols.insert(syms.begin(), syms.end());
      if (uf.optimize_flag)
        impl->harvestSigma0(c);
    }
  }

  if (impl->policy.firstSolveShortcuts() && firstForcedIncrementalSolve &&
      assertionsSMT2.size() == 1 &&
      !newLevel0.empty())
  {
    ASTVec reducedBase;
    if (impl->preprocessForcedFirstBase(newLevel0, reducedBase))
      newLevel0.swap(reducedBase);
  }

  for (const ASTNode& c : newLevel0)
  {
    const int lit = impl->rootLit(c);
    SATSolver::vec_literals unit;
    unit.push(SATSolver::mkLit(lit >> 1, lit & 1));
    impl->addClause(unit);
    impl->baseLiveMass = Impl::addMass(
        impl->baseLiveMass, Impl::addMass(impl->clauseMassOf[c], 1));
    impl->recordPermanentRoot(c);
  }

  // Screening must see the WHOLE stack's new raw content before any level
  // is prepared or encoded: a later level's mention of a variable an
  // earlier level's cached preparation eliminated invalidates that cache
  // entry now, not after the stale entry was already used.
  if (impl->policy.semanticPreprocessing())
  {
    ScopedProfileTimer screenTimer(impl->profile.enabled,
                                   impl->profile.screenNs);
    for (size_t level = 1; level < assertionsSMT2.size(); level++)
      impl->screenNewContent(assertionsSMT2[level]);
  }

  // The base level seeds the constant-bit engine: its conjuncts are
  // permanent units, so their truth is sound for every fact any
  // deeper level draws from them. The base itself never adopts (it is
  // already encoded), so its parked fixings flush straight back --
  // and with no pushed level in the stack there is no adopter at all,
  // so a session that never pushes never pays for the feed (a huge
  // single-check formula measured two minutes of fixpoint and harvest
  // with nothing downstream to spend it on).
  if (impl->policy.crossLevelPropagation() && uf.optimize_flag &&
      uf.bitConstantProp_flag && assertionsSMT2.size() > 1)
  {
    impl->cbpFeedLevel(0, assertionsSMT2[0]);
    impl->cbpFinishLevel();
  }

  // Pushed levels: each is prepared in pieces -- substituted under the
  // context, run through the batch equality-propagation and
  // simplification passes, private definitions eliminated and everything
  // else re-conjoined (see PreparedPiece) -- then encoded against the
  // epoch-persistent caches and assumed through one literal per level. The
  // assumption set is recomputed from the current stack on every call,
  // so popped levels vanish by simply no longer being here.
  SATSolver::vec_literals assumptions;
  std::vector<int> levelRoots;
  // The context carries only RETRACTABLE definitions -- harvested from
  // the live pushed levels this call, plus this call's eliminations --
  // and is part of every piece's cache key. sigma0 is deliberately NOT
  // here: it is applied inside the (cached) preparation, where its
  // permanence makes staleness sound, so base growth never churns the
  // piece cache.
  // The pushed-definition context accumulates BY LEVEL PREFIX: before a
  // level is prepared, its own raw definitions join the map, so level L
  // is substituted under the definitions of levels 1..L -- uniformly
  // with every level below it (shared subterms keep rewriting
  // identically, and a definition reaches its same-level uses), but
  // NEVER under deeper levels' definitions. That last part is what keeps
  // a conjunct's substituted form STABLE as the stack grows underneath
  // it: a whole-stack map changed shallow conjuncts on every deepening,
  // so one semantic array read took a fresh syntactic index per query
  // and the refinement loop drowned in aliased read pairs (measured as
  // entire check-sats spent inside SATBased_ArrayReadRefinement).
  ASTNodeMap ctx;
  ASTNodeSet ctxSources;
  bool ctxHasFp = false;
  // Pinning facts emitted by CBP are real, scoped conjuncts.  Their symbols
  // must participate in private-definition decisions just like symbols in
  // the raw assertion stack: eliminating a definition and then appending a
  // fact that still mentions its variable leaves that fact unconstrained.
  // Accumulate the facts of shallower live levels for the deeper levels'
  // privacy checks.
  ASTNodeSet activeCbpFactSymbols;
  // Both eliminability questions below are constant-time lookups into an
  // occurrence index rather than stack scans; it is built on first use, so a
  // stack that asks neither pays nothing (see LevelOccurrence).
  impl->invalidateLevelOccurrences();
  for (size_t level = 1; level < assertionsSMT2.size(); level++)
  {
    const bool individually =
        assumeLastLevelPerConjunct && level + 1 == assertionsSMT2.size();
    PreprocessingTransaction levelTransaction(PreprocessingMode::PerLevel,
                                              assertionsSMT2[level]);

    ASTVec levelDefiningConjuncts;
    if (impl->policy.semanticPreprocessing() && uf.optimize_flag)
    {
      const size_t contextBefore = ctx.size();
      conjuncts.clear();
      splitConjuncts(assertionsSMT2[level], bm->ASTTrue, conjuncts);
      for (const ASTNode& c : conjuncts)
        impl->harvestPushed(c, ctx, ctxSources, ctxHasFp);
      if (impl->profile.enabled)
        impl->profile.contextDefinitions += ctx.size() - contextBefore;
      // A defining conjunct must never be rewritten under its own entry:
      // substituting x -> t into (= x t) yields TRUE and the constraint
      // silently vanishes -- with no replay record, so the model channel
      // answers a default, the raw-stack model check calls every
      // candidate bogus, and array refinement spins forever with no
      // violated axiom to add. The definers are re-presented to the
      // preparation unreplaced; its own harvest then either eliminates
      // them WITH bookkeeping (privacy rules, model replay) or keeps the
      // equation asserted.
      for (const ASTNode& c : conjuncts)
        if (ctxSources.find(c) != ctxSources.end())
          levelDefiningConjuncts.push_back(c);
    }

    // Constant-bit propagation over the live prefix: feed this
    // level's raw conjunction (a no-op for the persisting session's
    // stable prefix), then rewrite its conjuncts below under the
    // constants accumulated from levels up to and including this one
    // (see cbpFeedLevel/cbpAdopt). Never on the per-assumption path,
    // whose conjunct-to-assumption mapping a cross-conjunct fact
    // would blur.
    if (impl->policy.crossLevelPropagation() && uf.optimize_flag &&
        !individually && uf.bitConstantProp_flag)
      impl->cbpFeedLevel(level, assertionsSMT2[level]);

    conjuncts.clear();
    if (!impl->policy.semanticPreprocessing() || !uf.optimize_flag ||
        individually)
    {
      // check-sat-assuming wants per-assumption granularity: merging the
      // assumptions through a level-wide preparation would destroy the
      // conjunct-to-assumption mapping, so that level encodes raw.
      splitConjuncts(assertionsSMT2[level], bm->ASTTrue, conjuncts);
    }
    else
    {
      const bool levelHasFp = impl->fragment(assertionsSMT2[level]).fp;

      // Preparation granularity is a size call. A level of moderate size
      // is prepared as ONE formula -- full cross-conjunct simplification,
      // which is what collapses generated queries whose conjuncts only
      // shrink together. A huge level (the deep define-fun families)
      // prepares per conjunct instead: the whole-level pass would rerun
      // over the entire level for every pushed variant, while per-conjunct
      // preparation reuses every already-prepared piece and loses only
      // cross-conjunct effects beyond definition chaining.
      ASTVec rawConjuncts;
      if (impl->dagSizeUpToMemo(assertionsSMT2[level], Impl::bigFormulaCap,
                                impl->dagSizeBigMemo) <=
          Impl::bigFormulaCap)
        rawConjuncts.push_back(assertionsSMT2[level]);
      else
        splitConjuncts(assertionsSMT2[level], bm->ASTTrue, rawConjuncts);

      // How many of this level's raw conjuncts mention each symbol; a
      // definition is only eliminable if its variable stays inside one.
      // At whole-level granularity there is exactly one raw conjunct, so
      // every count would be one and the test this feeds can never fire --
      // building it would be a walk over the level's symbols for nothing.
      std::map<ASTNode, size_t> conjunctCountOf;
      if (rawConjuncts.size() > 1)
        for (const ASTNode& rc : rawConjuncts)
          for (const ASTNode& s : impl->symbolsOf(rc))
            conjunctCountOf[s]++;

      // Totalisation order matters more than it looks. Totalising the
      // RAW conjunct and substituting after keeps the symfpu circuits
      // raw-keyed and shared across the session's variants; totalising
      // the substituted form builds novel circuits per variant, and a
      // family the batch pipeline solves in a second ran to timeout on
      // their shapes. The late order exists for exactly one reason --
      // a context entry with a floating-point BODY can splice partial
      // operations into the conjunct, which only the totaliser may
      // lower -- so it is used only when the context actually carries
      // floating point.
      const bool totaliseEarly = levelHasFp && !ctxHasFp;
      // A level inside the memo's stable prefix REPLAYS its recorded
      // rewrites -- outputs frozen at build time, when the
      // accumulated substitution held exactly this level's prefix --
      // and a level being fed this call records its own. A level that
      // is neither (a retired session's new levels, a lookup miss)
      // takes the plain path with no constant-fixing adoption: the
      // live map may hold deeper levels' fixings by now, and prefix
      // discipline forbids folding those into a shallower conjunct.
      const bool cbpHit = level < impl->cbpMemoStable;
      const bool cbpBuild = !cbpHit && impl->scopes.hasCbpMemo(level);
      ASTNodeSet cbpProtectedSymbols = activeCbpFactSymbols;
      const auto protectSymbols = [&](const ASTNode& n)
      {
        const ASTNodeSet& symbols = impl->symbolsOf(n);
        cbpProtectedSymbols.insert(symbols.begin(), symbols.end());
      };
      if (cbpHit)
      {
        for (const ScopedFact& f : impl->scopes.cbpMemo(level).facts)
          protectSymbols(f.assertion);
      }
      else if (cbpBuild)
      {
        // The facts this level will emit are discovered while its pieces are
        // being prepared.  Protect the symbols of every eligible fixed
        // domain up front, so a fact discovered by a later piece cannot make
        // an earlier piece's definition elimination unsound.  This is a
        // conservative superset: cbpAdopt emits only reachable domains.
        ASTVec eligibleDomains;
        eligibleDomains.reserve(impl->callCbpSubst.size());
        for (ASTNodeMap::const_iterator it = impl->callCbpSubst.begin();
             it != impl->callCbpSubst.end(); ++it)
        {
          if (impl->callCbpFedConjuncts.find(it->first) ==
              impl->callCbpFedConjuncts.end())
            eligibleDomains.push_back(it->first);
        }
        impl->addSymbolsOf(eligibleDomains, cbpProtectedSymbols);
      }
      size_t cbpMemoIdx = 0;
      std::vector<ScopedFact> cbpFacts;
      for (const ASTNode& rc : rawConjuncts)
      {
        ASTNode replaced = rc;
        bool replayed = false;
        if (cbpHit)
        {
          ScopedProfileTimer cbpTimer(impl->profile.enabled,
                                      impl->profile.cbpNs);
          ScopedProfileTimer replayTimer(impl->profile.enabled,
                                         impl->profile.cbpReplayNs);
          if (impl->profile.enabled)
            impl->profile.cbpReplayAttempts++;
          const std::vector<std::pair<ASTNode, ASTNode>>& rw =
              impl->scopes.cbpMemo(level).rewrites;
          if (cbpMemoIdx < rw.size() && rw[cbpMemoIdx].first == rc)
          {
            replaced = rw[cbpMemoIdx].second;
            cbpMemoIdx++;
            replayed = true;
            impl->callCbpReplayed++;
            if (impl->profile.enabled)
              impl->profile.cbpReplays++;
          }
        }
        if (!replayed)
        {
          if (totaliseEarly)
            replaced = impl->fpContext()->prepare(replaced);
          const bool isDefiner = ctxSources.find(rc) != ctxSources.end();
          if (!ctx.empty() && !isDefiner)
          {
            ASTNodeMap cache;
            const ASTNode substituted = SubstitutionMap::replace(
                replaced, ctx, cache, bm->defaultNodeFactory);
            // Adopt the substituted form only if it builds no novel
            // floating-point circuit (see introducesNovelFpOperations): a
            // fold is the collapse this context exists for, a variant is a
            // duplicate of a raw-keyed circuit and strictly harder to
            // search than the raw conjunct it replaces. The refused
            // conjunct encodes raw-keyed, sharing everything it always
            // shared; its definers stay asserted, so nothing is lost but
            // the rewrite.
            if (!impl->introducesNovelFpOperations(replaced, substituted))
              replaced = substituted;
          }
          // The whole-level piece contains its definers INSIDE the node
          // just substituted; restore them alongside the replaced form
          // (totalised the same way the piece was).
          if (rc == assertionsSMT2[level] && !levelDefiningConjuncts.empty())
          {
            ASTVec parts;
            for (const ASTNode& d : levelDefiningConjuncts)
              parts.push_back(totaliseEarly
                                  ? impl->fpContext()->prepare(d)
                                  : d);
            parts.push_back(replaced);
            replaced = bm->defaultNodeFactory->CreateNode(AND, parts);
          }

          // Rewrite under the prefix's accumulated constant fixings
          // BEFORE granularity is judged and the piece is prepared: a
          // conjunct this collapses flows into the piece machinery (and
          // from there to the transformer and the read registry) in its
          // folded form, content-keyed like every other conjunct.
          if (!cbpHit)
          {
            const size_t factsBefore = cbpFacts.size();
            replaced = impl->cbpAdopt(replaced, cbpFacts);
            for (size_t i = factsBefore; i < cbpFacts.size(); ++i)
              protectSymbols(cbpFacts[i].assertion);
          }
          if (cbpBuild)
            impl->scopes.cbpMemo(level).rewrites.push_back(
                std::make_pair(rc, replaced));
        }

        // An oversize conjunct (the deep define-fun chains) skips the
        // TRIAL passes -- their novel rewritten forms forfeit the
        // bit-blast memo's sharing wholesale -- but keeps the context
        // substitution: these conjuncts collapse under their levels'
        // definitions, and encoding one unsubstituted measured ten
        // million clauses against the substituted form's thousands.
        // rootLit's raw-keyed preparation (sigma0 and the plain
        // simplifier inside the cache) does the rest, as it always has.
        if (impl->dagSizeUpToMemo(replaced, Impl::bigFormulaCap,
                                  impl->dagSizeBigMemo) >
            Impl::bigFormulaCap)
        {
          conjuncts.push_back(replaced);
          continue;
        }

        // The late totalisation, for the context-carries-floating-point
        // case only (see totaliseEarly above): the substitution may have
        // spliced partial operations in, and lowering only accepts
        // totalised forms. A level with no floating point of its own can
        // acquire some the same way.
        if (!totaliseEarly &&
            (levelHasFp ||
             (ctxHasFp && containsFloatingPointTheory(replaced, bm))))
          replaced = impl->fpContext()->prepare(replaced);
        const Impl::PreparedPiece* pp =
            &impl->preparePiece(replaced, level, assertionsSMT2,
                                conjunctCountOf, cbpProtectedSymbols, ctx);
        // The other half of the elimination decision, settled once. The
        // expansion computed here is exactly what the join below installs,
        // so deciding it at the point of use costs one substitution per
        // definition per check rather than two. A CACHED piece was decided
        // under whatever context it was first prepared under, which may no
        // longer inline; re-preparing decides again under this one, and
        // preparePiece's own creation-time check makes the retry inlinable
        // by construction.
        std::vector<std::pair<ASTNode, ASTNode>> ctxInlines;
        bool inlinesHold = true;
        for (const ScopedElimination& d : pp->eliminated)
        {
          ASTNode expanded;
          if (!impl->ctxInlinable(d.symbol, d.value, ctx, expanded))
          {
            inlinesHold = false;
            break;
          }
          ctxInlines.push_back(std::make_pair(d.symbol, expanded));
        }
        if (!inlinesHold)
        {
          impl->dropPreparedLevel(replaced);
          pp = &impl->preparePiece(replaced, level, assertionsSMT2,
                                   conjunctCountOf, cbpProtectedSymbols, ctx);
          ctxInlines.clear();
          for (const ScopedElimination& d : pp->eliminated)
          {
            ASTNode expanded;
            const bool held =
                impl->ctxInlinable(d.symbol, d.value, ctx, expanded);
            assert(held && "a re-prepared piece refuses its own inlining");
            (void)held;
            ctxInlines.push_back(std::make_pair(d.symbol, expanded));
          }
        }
        for (const ASTNode& pc : pp->conjuncts)
          conjuncts.push_back(pc);
        // Eliminated definitions are recorded for the model, and joined
        // onto the context so DEEPER levels' uses collapse under them --
        // this is the only route by which a definition the raw harvest
        // refuses on content (a floating-point body, say) still reaches
        // its uses; without it those levels keep every symbolic read and
        // the refinement loop pays for the aliases. Joining obeys the
        // SAME discipline as harvestPushed: the body is expanded under
        // the current context and refused if its own variable reappears
        // or it grows past the inlining cap. A definer conjunct's piece
        // sees RAW content (it is never rewritten under its own entry),
        // so its propagator can harvest a definition in terms of a
        // variable another context entry defines -- feeding that
        // unexpanded made the map cyclic, and the next replacement
        // recursed until the worker stack died. The elimination itself
        // stays (it is sound for the piece and its replay); only the
        // context entry is withheld.
        for (const ScopedElimination& d : pp->eliminated)
          levelTransaction.addElimination(d.symbol, d.value, d.witness);
        for (const std::pair<ASTNode, ASTNode>& ci : ctxInlines)
        {
          // A null expansion means the context already binds the variable,
          // so its occurrences are already substituted away.
          if (ci.second.IsNull())
            continue;
          ctx[ci.first] = ci.second;
          if (impl->profile.enabled)
            impl->profile.contextDefinitions++;
          if (!ctxHasFp && bm->has_floating_point_theory &&
              containsFloatingPointTheory(ci.second, bm))
            ctxHasFp = true;
        }
      }

      // The pinning facts justifying this level's adoptions are its
      // conjuncts too: asserted under the same assumption, retracted
      // with the same pop, and content-keyed like everything else. A
      // replaying level re-asserts the facts it recorded.
      if (cbpHit)
      {
        for (const ScopedFact& f : impl->scopes.cbpMemo(level).facts)
        {
          // A retired session will never adopt again and creates no new
          // caller checkpoints. Its memo still supplies already-recorded
          // assertions, but there is no scoped fact-emission state to seed.
          if (!f.domain.IsNull() && !impl->cbpSessionRetired)
            impl->cbpInsertFactDomain(f.domain);
          conjuncts.push_back(f.assertion);
          levelTransaction.facts.push_back(f);
        }
      }
      else
      {
        // Append rather than assign: a refuted level's memo already
        // carries its FALSE.
        if (cbpBuild)
          for (const ScopedFact& f : cbpFacts)
            impl->scopes.cbpMemo(level).facts.push_back(f);
        for (const ScopedFact& f : cbpFacts)
        {
          conjuncts.push_back(f.assertion);
          levelTransaction.facts.push_back(f);
        }
      }

      const std::vector<ScopedFact>& activeFacts =
          cbpHit ? impl->scopes.cbpMemo(level).facts : cbpFacts;
      for (const ScopedFact& f : activeFacts)
      {
        const ASTNodeSet& symbols = impl->symbolsOf(f.assertion);
        activeCbpFactSymbols.insert(symbols.begin(), symbols.end());
      }
    }

    // A feed that refuted the live prefix by bit-level reasoning alone
    // asserts FALSE at the refuting level.
    if (impl->callCbpConflict)
    {
      conjuncts.push_back(bm->ASTFalse);
      levelTransaction.facts.push_back(
          ScopedFact(ASTNode(), bm->ASTFalse));
      impl->callCbpConflict = false;
    }
    // This level is past rewriting; its own parked fixings now serve
    // the deeper levels.
    impl->cbpFinishLevel();

    levelTransaction.conjuncts = conjuncts;
    impl->scopes.commitLevel(level, levelTransaction);

    if (conjuncts.empty())
      continue;

    levelRoots.clear();
    for (const ASTNode& c : conjuncts)
      levelRoots.push_back(impl->rootLit(c));

    // A level inside the promoted prefix is already asserted as units;
    // nothing to assume. (Its preparation above still ran: deeper
    // levels need its definitions in the context either way.)
    //
    // Only while it still prepares to what promotion pinned, though. The
    // raw conjunction updateStackStability compares is unchanged in the
    // case that matters: later content retracts a private elimination, the
    // level re-prepares with its defining equation restored -- and skipping
    // here would encode that stronger form and then drop it, leaving the
    // variable unconstrained behind the older, weaker units. Fall through
    // instead, so this solve assumes what the level now says, and hand the
    // epoch to the next call's maintenance block, which can rebuild safely.
    if (level <= impl->scopes.promotedDepth())
    {
      if (!impl->scopes.promotedConjunctsChanged(level, conjuncts))
        continue;
      impl->scopes.notePromotionDrift();
      if (uf.stats_flag)
        std::cerr << "Incremental: promoted level " << level
                  << " re-prepared differently, assumed for this solve "
                     "and demoted at the next"
                  << std::endl;
    }

    // Promote the next prefix level once it has sat identical long
    // enough. Never the deepest level: it is the churn point, and
    // check-sat-assuming's per-assumption frame must stay assumed.
    // Only once trail reuse has been retired -- the same session split
    // as inprobing retirement, for the same reason: a session still
    // riding the trail re-descends its stable assumptions nearly for
    // free and only pays promotion's recurring root-level preprocessing
    // over the new units (measured ~10% on the KLEE-class b64), while
    // the sessions that shed the trail pay the full assumption descent
    // every solve, which is exactly what promotion removes (measured
    // ~16% on f84c6e97).
    if (impl->policy.unitPromotion() && !individually &&
        uf.incremental_promote_units &&
        !impl->trailReuseAllowed &&
        level == impl->scopes.promotedDepth() + 1 &&
        level + 1 < assertionsSMT2.size() &&
        level < impl->scopes.size() &&
        impl->scopes.stableSolves(level) >= impl->promoteAfterSolves)
    {
      for (const int r : levelRoots)
      {
        SATSolver::vec_literals unit;
        unit.push(SATSolver::mkLit(r >> 1, r & 1));
        impl->addClause(unit);
      }
      impl->baseLiveMass = Impl::addMass(impl->baseLiveMass,
                                         levelRoots.size());
      assert(conjuncts.size() == levelRoots.size());
      for (const ASTNode& c : conjuncts)
        impl->recordPermanentRoot(c);
      // Remember the form that was pinned, not just how deep promotion
      // reached: the skip above is only sound while the level still
      // prepares to exactly this.
      impl->scopes.promote(level, conjuncts);
      if (uf.stats_flag)
        std::cerr << "Incremental: promoted level " << level << " ("
                  << levelRoots.size() << " conjuncts) to units after "
                  << impl->scopes.stableSolves(level) << " stable solves"
                  << std::endl;
      continue;
    }

    if (individually || !impl->policy.aggregateLevelAssumptions())
    {
      // The per-assumption route needs one root per source conjunct for
      // reporting. Core-only mode deliberately uses the same direct-root
      // mechanism for every level, avoiding the optional activation-literal
      // aggregation policy while retaining the assumption core itself.
      if (individually)
        impl->lastLevelIndividual = true;
      for (size_t k = 0; k < conjuncts.size(); k++)
      {
        const int r = levelRoots[k];
        if (impl->policy.retractionSearchHints())
          impl->everAssumedLits[r] = impl->engagedSolves;
        impl->assumedLitLevels.push_back(std::make_pair(r, level));
        if (individually)
          impl->lastLevelLitConjuncts.push_back(
              std::make_pair(r, conjuncts[k]));
        assumptions.push(SATSolver::mkLit(r >> 1, r & 1));
      }
      continue;
    }

    const int lit = impl->levelAssumption(levelRoots);
    if (impl->policy.retractionSearchHints())
      impl->everAssumedLits[lit] = impl->engagedSolves;
    impl->assumedLitLevels.push_back(std::make_pair(lit, level));
    assumptions.push(SATSolver::mkLit(lit >> 1, lit & 1));
  }

  const ASTVec& activeEncodedKeys = impl->scopes.activeSemanticKeys();
  impl->hintRetractedLevels(assumptions);

  ASTNode ordinaryOwner;
  if (assertionsSMT2.size() > 1)
    ordinaryOwner = bm->CreateNode(AND, assertionsSMT2);
  else
    ordinaryOwner = assertionsSMT2[0];

  // This solve's live clause mass -- what the assumed stack actually
  // uses -- feeds the relief valve's deadness measure on LATER solves.
  // The peak since the last rebuild is the valve's denominator.
  uint64_t ordinaryLiveMass = impl->baseLiveMass;
  std::vector<Aig_Obj_t*> ordinaryCurrentRoots;
  const bool trackOrdinaryRoots =
      impl->profile.enabled || impl->clauseReliefSizeReached();
  if (trackOrdinaryRoots)
    ordinaryCurrentRoots.reserve(activeEncodedKeys.size());
  const uint64_t activationMass = impl->activeActivationMass(assumptions);
  const uint64_t oldRefinementMass = impl->refinementMass(ordinaryOwner);
  {
    for (const ASTNode& k : activeEncodedKeys)
    {
      std::map<ASTNode, uint64_t>::const_iterator mit =
          impl->clauseMassOf.find(k);
      if (mit != impl->clauseMassOf.end())
        ordinaryLiveMass = Impl::addMass(ordinaryLiveMass, mit->second);
      if (trackOrdinaryRoots)
        ordinaryCurrentRoots.push_back(impl->aigRoot(k));
    }
    ordinaryLiveMass = Impl::addMass(ordinaryLiveMass, activationMass);
    ordinaryLiveMass = Impl::addMass(ordinaryLiveMass, oldRefinementMass);
    uint64_t nonStructuralMass =
        Impl::addMass(impl->permanentUnitMass, activationMass);
    nonStructuralMass =
        Impl::addMass(nonStructuralMass, oldRefinementMass);
    impl->stageLiveConeMass(ordinaryCurrentRoots, ordinaryLiveMass,
                            nonStructuralMass);
    impl->stageSemanticLiveStack(assertionsSMT2, activeEncodedKeys);
  }

  if (impl->profile.enabled)
  {
    impl->profile.semanticNs +=
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            ProfileClock::now() - semanticStarted)
            .count();
    impl->profile.activeKeys = activeEncodedKeys.size();
    impl->profile.assumptions = assumptions.size();
    impl->profile.contextEntries = ctx.size();
  }

  if (uf.stats_flag)
  {
    std::cerr << "Incremental: encoded " << impl->encodesThisCall
              << " new conjuncts, added "
              << (impl->lifetimeClauseSubmissions() - clausesBefore)
              << " clauses, assumed "
              << assumptions.size() << " literals, solver has "
              << impl->solver->nVars() << " variables, " << impl->sigma0.size()
              << " base-level and " << ctx.size() << " pushed substitutions, "
              << impl->scopes.activeEliminations().size() << " eliminated"
              << std::endl;
    if (impl->callCbpAdopted > 0 || impl->callCbpReplayed > 0)
      std::cerr << "Incremental: cbp adopted " << impl->callCbpAdopted
                << " rewrites (" << impl->callCbpReplayed << " replayed) from "
                << impl->callCbpSubst.size() << " fixed nodes" << std::endl;
  }

  // Array refinement needs a candidate model to find violated axioms, so
  // arrays force counterexample construction, exactly as in the batch
  // pipeline (TopLevelSTPAux). Under --ackermanize the transform compiles
  // arrays away eagerly -- each new read carries its if-then-else over the
  // existing reads -- so there is nothing to refine and the lean path
  // solves it like plain bit-vectors.
  bool activeHasArrays = false;
  for (const ASTNode& levelConjunction : assertionsSMT2)
  {
    if (impl->fragment(levelConjunction).arrays)
    {
      activeHasArrays = true;
      break;
    }
  }
  const bool needRefinement = activeHasArrays && !uf.ackermannisation;

  // Derived afresh from the genuine inputs -- including the C API's direct
  // request, which now has its own field -- so that a check needing a
  // candidate model for refinement cannot leave construction switched on
  // for every later check, and with it the frontend's shortcut for a
  // repeated query whose model nobody wants.
  const bool construct = observableModelRequested(uf) || needRefinement;
  uf.construct_counterexample_flag = construct;

  // Model evaluation of floating-point terms needs the encoding context
  // that lowered them. Batch fallback rounds install their own per solve;
  // this keeps the driver's rounds coherent the same way.
  if (impl->fpCtx)
    impl->ce->setFpEncodingContext(impl->fpCtx.get());

  // Budgets are per check-sat, as solve_by_sat_solver arms them per query.
  if (uf.timeout_max_conflicts >= 0)
    impl->solver->setMaxConflicts(uf.timeout_max_conflicts);
  if (uf.timeout_max_time >= 0)
    impl->solver->setMaxTime(uf.timeout_max_time);
  bm->soft_timeout_expired = false;

  if (needRefinement)
  {
    ScopedProfileTimer refinementTimer(impl->profile.enabled,
                                       impl->profile.refinementNs);
    // The batch pipeline's own CEGAR: candidate model, violated congruence
    // axioms as direct (permanent -- they are tautologies of the canonical
    // read abstraction) clauses, solve again. The adapter re-solves under
    // this check-sat's assumptions, and the batch-side tables the
    // machinery reads are seeded from the driver's persistent stores.
    IncrementalToSAT* adapter =
        static_cast<IncrementalToSAT*>(impl->ensureAdapter());

    // Restrict the batch tables to the active cone's reads; stale rows
    // from popped scopes must not reach model construction or
    // refinement. Base keys have already queued themselves as they were
    // first asserted; only the pushed cone is passed per solve.
    impl->seedActiveReads(activeEncodedKeys);
    impl->seedEliminatedIntoModelChannel();

    // Idempotent when nothing changed; essential after a re-encode, when
    // registry symbols from earlier sessions have no variables yet and the
    // axiom encoder reads their bits unconditionally.
    impl->totalizeRegistrySymbols();

    const ASTNode& activeConjunction = ordinaryOwner;

    adapter->setAssumptions(&assumptions);
    const uint64_t refinementClausesBefore =
        impl->solver->submittedClauses();
    size_t refinementRounds = 0;
    ArrayReadRefinementProgress refinementProgress;
    SOLVER_RETURN_TYPE res = impl->ce->CallSAT_ResultCheck(
        *impl->solver, bm->ASTTrue, activeConjunction, activeConjunction,
        adapter, true);
    while (res == SOLVER_UNDECIDED)
    {
      refinementRounds++;
      // getEquals creates a fresh comparison circuit even for an axiom the
      // solver already holds, so clause and variable counts are not logical
      // progress. The check-local transaction suppresses that re-encoding;
      // an undecided round must therefore have claimed at least one genuinely
      // new congruence axiom or the model/encoding boundary is inconsistent.
      const size_t emittedBefore = refinementProgress.emittedAxiomCount();
      res = impl->ce->SATBased_ArrayReadRefinement(
          *impl->solver, activeConjunction, adapter, &refinementProgress);
      if (res == SOLVER_UNDECIDED &&
          refinementProgress.emittedAxiomCount() == emittedBefore)
        FatalError("IncrementalSolver: an array refinement round rejected "
                   "the candidate but emitted no new logical axiom -- the "
                   "encoding and model evaluation disagree");
    }
    adapter->setAssumptions(NULL);

    if (uf.stats_flag && refinementRounds > 0)
      std::cerr << "Incremental: array refinement converged after "
                << refinementRounds << " rounds" << std::endl;
    if (impl->profile.enabled)
      impl->profile.refinementRounds += refinementRounds;

    const uint64_t newRefinementMass = impl->accountRefinementClauses(
        ordinaryOwner, refinementClausesBefore);
    uint64_t refinedNonStructuralMass =
        Impl::addMass(impl->permanentUnitMass, activationMass);
    refinedNonStructuralMass = Impl::addMass(
        refinedNonStructuralMass, impl->refinementMass(ordinaryOwner));
    impl->stageLiveConeMass(
        ordinaryCurrentRoots,
        Impl::addMass(ordinaryLiveMass, newRefinementMass),
        refinedNonStructuralMass);

    if (uf.stats_flag)
      impl->solver->printStats();

    if (res == SOLVER_UNSATISFIABLE)
      impl->recordUnsat(assumptions, assertionsSMT2.size(), false);

    // SOLVER_INVALID and SOLVER_SATISFIABLE (resp. VALID/UNSATISFIABLE)
    // are the same enum values, so this is already in check-sat terms.
    return res;
  }

  bm->GetRunTimes()->start(RunTimes::Solving);
  if (impl->profile.enabled)
    impl->profile.satCalls++;
  bool sat;
  {
    ScopedProfileTimer satTimer(impl->profile.enabled, impl->profile.satNs);
    ScopedProfileTimer initialSatTimer(impl->profile.enabled,
                                       impl->profile.initialSatNs);
    if (assumptions.size() == 0)
      sat = impl->solver->solve(bm->soft_timeout_expired);
    else
      sat = impl->solver->solveWithAssumptions(assumptions,
                                               bm->soft_timeout_expired);
  }
  bm->GetRunTimes()->stop(RunTimes::Solving);

  if (uf.stats_flag)
    impl->solver->printStats();

  if (bm->soft_timeout_expired)
    return SOLVER_TIMEOUT;

  if (!sat)
  {
    impl->recordUnsat(assumptions, assertionsSMT2.size(), false);
    return SOLVER_UNSATISFIABLE;
  }

  // resetSolver() clears the batch transformer's tables before every
  // check-sat.  Eager Ackermannisation does not need them for refinement,
  // but counterexample construction still uses the active read rows to
  // evaluate source-level READ terms.  A round whose encodings are all cache
  // hits otherwise leaves that table empty and can report an arbitrary array
  // value even though the reused SAT encoding has the right read symbol.
  // Materialise only after a satisfiable solve, and only when a model can be
  // observed; the table then also remains available to deferred get-model /
  // get-value construction.
  if (construct && activeHasArrays && uf.ackermannisation)
    impl->seedActiveReads(activeEncodedKeys);

  if (construct)
  {
    // Unless the model is read at solve time -- the self-check below is
    // such a reader -- construction is deferred to the first model query
    // and never happens for answers nobody samples. The SAT model this
    // materializes from stays live: the driver adds no clause and runs
    // no solve between user commands.
    if (!uf.check_counterexample_flag)
    {
      impl->modelPending = true;
      return SOLVER_SATISFIABLE;
    }

    bm->GetRunTimes()->start(RunTimes::CounterExampleGeneration);
    impl->ce->ClearCounterExampleMap();
    impl->ce->ClearComputeFormulaMap();

    impl->seedEliminatedIntoModelChannel();

    ToSATBase::ASTNodeToSATVar symbolMap;
    impl->buildSymbolMap(symbolMap);
    impl->ce->ConstructCounterExample(*impl->solver, symbolMap);
    bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);

    if (uf.check_counterexample_flag)
    {
      // GetCounterExample answers ASTUndefined while ValidFlag claims the
      // last query was unsat; that flag describes the previous query at
      // this point, so clear it before evaluating.
      bm->ValidFlag = false;
      for (const ASTNode& levelConjunction : assertionsSMT2)
      {
        conjuncts.clear();
        splitConjuncts(levelConjunction, bm->ASTTrue, conjuncts);
        for (const ASTNode& c : conjuncts)
        {
          if (impl->ce->GetCounterExample(c) != bm->ASTTrue)
            FatalError("IncrementalSolver: the model does not satisfy an "
                       "asserted formula",
                       c);
        }
      }
    }
  }

  return SOLVER_SATISFIABLE;
}

} // namespace stp

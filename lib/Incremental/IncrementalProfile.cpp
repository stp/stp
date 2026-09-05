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

#include "stp/Incremental/IncrementalProfile.h"

#include <ostream>
#include <sstream>

namespace stp
{

namespace
{
uint64_t profileMicros(uint64_t nanoseconds)
{
  return nanoseconds / 1000;
}
} // namespace

void IncrementalSessionProfile::add(const IncrementalCheckProfile& p)
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

void printIncrementalProfile(std::ostream& os,
                             const IncrementalCheckProfile& check,
                             const IncrementalSessionProfile& session,
                             bool corePolicy, uint64_t retainedClauses,
                             uint64_t liveClauses, uint64_t peakLiveClauses)
{
  // Assemble the report before writing it. SMT answers use stdout while
  // profiles use stderr; one write keeps redirected 2>&1 logs line-safe.
  std::ostringstream out;
  out << "Incremental profile: check=" << check.check
      << " levels=" << check.levels
      << " total-us=" << profileMicros(check.totalNs)
      << " maintenance-us=" << profileMicros(check.maintenanceNs)
      << " semantic-us=" << profileMicros(check.semanticNs)
      << " screen-us=" << profileMicros(check.screenNs)
      << " cbp-us=" << profileMicros(check.cbpNs)
      << " cbp-sync-us=" << profileMicros(check.cbpSyncNs)
      << " cbp-reset-us=" << profileMicros(check.cbpResetNs)
      << " cbp-rollback-us=" << profileMicros(check.cbpRollbackNs)
      << " cbp-feed-us=" << profileMicros(check.cbpFeedNs)
      << " cbp-fresh-feed-us=" << profileMicros(check.cbpFreshFeedNs)
      << " cbp-refeed-us=" << profileMicros(check.cbpRefeedNs)
      << " cbp-rejected-feed-us=" << profileMicros(check.cbpRejectedFeedNs)
      << " cbp-engine-us=" << profileMicros(check.cbpPropagateNs)
      << " cbp-harvest-us=" << profileMicros(check.cbpHarvestNs)
      << " cbp-adopt-us=" << profileMicros(check.cbpAdoptNs)
      << " cbp-replay-us=" << profileMicros(check.cbpReplayNs)
      << " cbp-finish-us=" << profileMicros(check.cbpFinishNs)
      << " prepare-us=" << profileMicros(check.prepareNs)
      << " encode-us=" << profileMicros(check.encodeNs)
      << " read-seed-us=" << profileMicros(check.readSeedNs)
      << " registry-us=" << profileMicros(check.registryNs)
      << " extensionality-us=" << profileMicros(check.extensionalityNs)
      << " refinement-us=" << profileMicros(check.refinementNs)
      << " sat-us=" << profileMicros(check.satNs)
      << " initial-sat-us=" << profileMicros(check.initialSatNs)
      << " refinement-sat-us=" << profileMicros(check.refinementSatNs)
      << " rebuild-reset-us=" << profileMicros(check.rebuildNs) << '\n';
  out << "Incremental profile work: check=" << check.check
      << " stable-prefix=" << check.stablePrefix
      << " screen-new=" << check.screenNew
      << " screen-cached=" << check.screenCached
      << " prepare-hits=" << check.preparationHits
      << " prepare-misses=" << check.preparationMisses
      << " prepare-invalidated=" << check.preparationInvalidations
      << " prepare-noop=" << check.preparationNoop
      << " prepare-collapsed=" << check.preparationCollapsed
      << " prepare-rejected=" << check.preparationRejected
      << " context-definitions=" << check.contextDefinitions
      << " context-entries=" << check.contextEntries
      << " root-hits=" << check.rootHits
      << " root-misses=" << check.rootMisses
      << " active-keys=" << check.activeKeys
      << " assumptions=" << check.assumptions << '\n';
  out << "Incremental profile cbp/backend: check=" << check.check
      << " cbp-resets=" << check.cbpResets
      << " cbp-divergences=" << check.cbpDivergences
      << " cbp-rollbacks=" << check.cbpRollbacks
      << " cbp-rolled-levels=" << check.cbpRolledLevels
      << " cbp-rollback-fixed=" << check.cbpRollbackFixed
      << " cbp-rollback-created=" << check.cbpRollbackCreated
      << " cbp-rollback-dependencies=" << check.cbpRollbackDependencies
      << " cbp-rollback-multiplications="
      << check.cbpRollbackMultiplications
      << " cbp-rollback-caller=" << check.cbpRollbackCallerEntries
      << " cbp-fed-levels=" << check.cbpFedLevels
      << " cbp-fresh-levels=" << check.cbpFreshLevels
      << " cbp-refed-levels=" << check.cbpRefedLevels
      << " cbp-fed-nodes=" << check.cbpFedNodes
      << " cbp-fresh-nodes=" << check.cbpFreshNodes
      << " cbp-refed-nodes=" << check.cbpRefedNodes
      << " cbp-feed-rejected=" << check.cbpFeedRejected
      << " cbp-bootstrap-deferred=" << check.cbpBootstrapDeferred
      << " cbp-adopt-attempts=" << check.cbpAdoptAttempts
      << " cbp-adoptions=" << check.cbpAdoptions
      << " cbp-replay-attempts=" << check.cbpReplayAttempts
      << " cbp-replays=" << check.cbpReplays
      << " cbp-deferred-restored=" << check.cbpDeferredRestored
      << " read-keys-folded=" << check.readKeysFolded
      << " read-keys-unfolded=" << check.readKeysUnfolded
      << " live-read-rows=" << check.readRowsLive
      << " driver-clauses=" << check.clauses
      << " refinement-clauses=" << check.refinementClauses
      << " retained-clauses=" << check.retainedClauses
      << " live-clauses=" << check.liveClauses
      << " exact-live-clauses=" << check.exactLiveClauses
      << " peak-live-clauses=" << check.peakLiveClauses
      << " sat-calls=" << check.satCalls
      << " refinement-sat-calls=" << check.refinementSatCalls
      << " refinement-rounds=" << check.refinementRounds
      << " ext-preprocesses=" << check.extPreprocesses
      << " ext-eliminations=" << check.extEliminations
      << " base-preprocesses=" << check.basePreprocesses
      << " base-eliminations=" << check.baseEliminations
      << " rebuilds=" << check.rebuilds
      << " rebuild-relief=" << check.rebuildRelief
      << " rebuild-promotion=" << check.rebuildPromotion
      << " rebuild-inprobing=" << check.rebuildInprobing
      << " rebuild-trail=" << check.rebuildTrail
      << " encoding-epoch-resets=" << check.encodingEpochResets
      << " policy=" << (corePolicy ? "core" : "full")
      << " extensionality=" << (check.extensionality ? 1 : 0)
      << " first-stack-preprocesses=" << check.firstStackPreprocesses
      << " first-stack-eliminations=" << check.firstStackEliminations
      << " first-stack-rejected=" << check.firstStackRejected << '\n';
  out << "Incremental profile total: checks=" << session.checks
      << " total-us=" << profileMicros(session.totalNs)
      << " maintenance-us=" << profileMicros(session.maintenanceNs)
      << " semantic-us=" << profileMicros(session.semanticNs)
      << " screen-us=" << profileMicros(session.screenNs)
      << " cbp-us=" << profileMicros(session.cbpNs)
      << " cbp-sync-us=" << profileMicros(session.cbpSyncNs)
      << " cbp-reset-us=" << profileMicros(session.cbpResetNs)
      << " cbp-rollback-us=" << profileMicros(session.cbpRollbackNs)
      << " cbp-feed-us=" << profileMicros(session.cbpFeedNs)
      << " cbp-fresh-feed-us=" << profileMicros(session.cbpFreshFeedNs)
      << " cbp-refeed-us=" << profileMicros(session.cbpRefeedNs)
      << " cbp-rejected-feed-us="
      << profileMicros(session.cbpRejectedFeedNs)
      << " cbp-engine-us=" << profileMicros(session.cbpPropagateNs)
      << " cbp-harvest-us=" << profileMicros(session.cbpHarvestNs)
      << " cbp-adopt-us=" << profileMicros(session.cbpAdoptNs)
      << " cbp-replay-us=" << profileMicros(session.cbpReplayNs)
      << " cbp-finish-us=" << profileMicros(session.cbpFinishNs)
      << " prepare-us=" << profileMicros(session.prepareNs)
      << " encode-us=" << profileMicros(session.encodeNs)
      << " read-seed-us=" << profileMicros(session.readSeedNs)
      << " registry-us=" << profileMicros(session.registryNs)
      << " extensionality-us="
      << profileMicros(session.extensionalityNs)
      << " refinement-us=" << profileMicros(session.refinementNs)
      << " sat-us=" << profileMicros(session.satNs)
      << " initial-sat-us=" << profileMicros(session.initialSatNs)
      << " refinement-sat-us="
      << profileMicros(session.refinementSatNs)
      << " rebuild-reset-us=" << profileMicros(session.rebuildNs)
      << " cbp-resets=" << session.cbpResets
      << " cbp-divergences=" << session.cbpDivergences
      << " cbp-rollbacks=" << session.cbpRollbacks
      << " cbp-rolled-levels=" << session.cbpRolledLevels
      << " cbp-rollback-fixed=" << session.cbpRollbackFixed
      << " cbp-rollback-created=" << session.cbpRollbackCreated
      << " cbp-rollback-dependencies="
      << session.cbpRollbackDependencies
      << " cbp-rollback-multiplications="
      << session.cbpRollbackMultiplications
      << " cbp-rollback-caller=" << session.cbpRollbackCallerEntries
      << " cbp-fed-levels=" << session.cbpFedLevels
      << " cbp-fresh-levels=" << session.cbpFreshLevels
      << " cbp-refed-levels=" << session.cbpRefedLevels
      << " cbp-fed-nodes=" << session.cbpFedNodes
      << " cbp-fresh-nodes=" << session.cbpFreshNodes
      << " cbp-refed-nodes=" << session.cbpRefedNodes
      << " cbp-feed-rejected=" << session.cbpFeedRejected
      << " cbp-bootstrap-deferred="
      << session.cbpBootstrapDeferred
      << " cbp-adopt-attempts=" << session.cbpAdoptAttempts
      << " cbp-adoptions=" << session.cbpAdoptions
      << " cbp-replay-attempts=" << session.cbpReplayAttempts
      << " cbp-replays=" << session.cbpReplays
      << " cbp-deferred-restored=" << session.cbpDeferredRestored
      << " screen-new=" << session.screenNew
      << " screen-cached=" << session.screenCached
      << " prepare-hits=" << session.preparationHits
      << " prepare-misses=" << session.preparationMisses
      << " prepare-invalidated=" << session.preparationInvalidations
      << " prepare-noop=" << session.preparationNoop
      << " prepare-collapsed=" << session.preparationCollapsed
      << " prepare-rejected=" << session.preparationRejected
      << " context-definitions=" << session.contextDefinitions
      << " root-hits=" << session.rootHits
      << " root-misses=" << session.rootMisses
      << " read-keys-folded=" << session.readKeysFolded
      << " read-keys-unfolded=" << session.readKeysUnfolded
      << " driver-clauses=" << session.clauses
      << " refinement-clauses=" << session.refinementClauses
      << " retained-clauses=" << retainedClauses
      << " live-clauses=" << liveClauses
      << " peak-live-clauses=" << peakLiveClauses
      << " sat-calls=" << session.satCalls
      << " refinement-sat-calls=" << session.refinementSatCalls
      << " refinement-rounds=" << session.refinementRounds
      << " ext-preprocesses=" << session.extPreprocesses
      << " ext-eliminations=" << session.extEliminations
      << " base-preprocesses=" << session.basePreprocesses
      << " base-eliminations=" << session.baseEliminations
      << " rebuilds=" << session.rebuilds
      << " rebuild-relief=" << session.rebuildRelief
      << " rebuild-promotion=" << session.rebuildPromotion
      << " rebuild-inprobing=" << session.rebuildInprobing
      << " rebuild-trail=" << session.rebuildTrail
      << " encoding-epoch-resets=" << session.encodingEpochResets
      << " policy=" << (corePolicy ? "core" : "full")
      << " first-stack-preprocesses="
      << session.firstStackPreprocesses
      << " first-stack-eliminations="
      << session.firstStackEliminations
      << " first-stack-rejected=" << session.firstStackRejected
      << '\n';
  os << out.str();
}

} // namespace stp

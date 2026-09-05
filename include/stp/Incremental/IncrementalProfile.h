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

#ifndef INCREMENTALPROFILE_H_
#define INCREMENTALPROFILE_H_

// The incremental driver's opt-in (--incremental-profile) measurement
// plumbing: the per-check and per-session counter records, the scoped
// timer that fills the duration fields, and the report printer. Pure
// data and formatting -- nothing here may feed a scheduling decision,
// so that profiling cannot move the behavior it observes (the one time
// it did is recorded at the relief valve).

#include <cassert>
#include <chrono>
#include <cstdint>
#include <iosfwd>

namespace stp
{

typedef std::chrono::steady_clock ProfileClock;

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

// Fine-grained, opt-in measurements for deciding where scoped state will
// actually pay. Timers are enabled only under --incremental-profile; the
// counters travel with them so an ordinary solve does not read the clock
// or update counters in its hot loops. Durations accumulate as
// nanoseconds to avoid losing sub-microsecond level work and print as
// microseconds. Some timings deliberately overlap: semanticNs is the
// complete active-stack construction, while CBP, preparation and
// encoding are its named sub-phases; refinementNs likewise includes its
// SAT re-solves.
struct IncrementalCheckProfile
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

struct IncrementalSessionProfile
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

  void add(const IncrementalCheckProfile& p);
};

// Write the finished check's report -- three per-check lines and the
// running session line -- assembled first and written in one call, so
// redirected 2>&1 logs stay line-safe against the stdout answers. The
// session line's clause figures describe the CURRENT backend, which the
// records do not carry, so they arrive as parameters.
void printIncrementalProfile(std::ostream& os,
                             const IncrementalCheckProfile& check,
                             const IncrementalSessionProfile& session,
                             bool corePolicy, uint64_t retainedClauses,
                             uint64_t liveClauses, uint64_t peakLiveClauses);

} // namespace stp

#endif

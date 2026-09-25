/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: August, 2026
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

#ifndef FPABSTRACTION_H
#define FPABSTRACTION_H

// Native floating-point abstraction/refinement (--fp-abstraction).
//
// A selected floating-point operation -- fp.mul, fp.div, fp.sqrt and
// fp.fma, and behind their own switches fp.add, fp.sub and fp.rem -- is not
// word-blasted. Its occurrence in the formula is replaced by a fresh value of
// the same floating-point sort, the *surrogate*, and the solve runs on that
// over-approximation. A candidate model is then checked: the operation is
// evaluated exactly (the literal SymFPU backend) on the candidate's operand
// values and compared with the candidate's surrogate value under SMT-LIB
// equality (all NaNs one value, the two zeros distinct). A disagreement adds
// a lemma and re-solves; after a bounded number of value lemmas the exact
// existing encoding is released -- once, and never taken back -- so every
// abstracted operation has a finite, monotone path to what the query would
// have had anyway.
//
// What makes the abstraction worth having is the rule tiers emitted with
// every surrogate at abstraction time (FpAbstractionRules): the exact
// class/sign shell of the operation, order facts (|y| >= 1 -> |x*y| >= |x|),
// exponent-field bands (e(x)+e(y) <= e(t) <= e(x)+e(y)+1 for normals) and
// identities. They are stated over the packed bits the surrogate already is,
// cost a few hundred AIG nodes each at binary64, and decide the range,
// overflow, class and monotonicity questions verification conditions ask
// without the multiplier, the divider or the root ever being built. See
// docs/fp-abstraction.rst for the measurements behind that.
//
// Representation. The surrogate and every non-constant child of an
// abstracted application are *bit-vector symbols*: the surrogate stands in
// the formula as ((_ to_fp eb sb) t), which is the packed view of t and costs
// nothing to lower; each child is mirrored by a *proxy* symbol p asserted
// equal to it, so that every lemma the refinement adds later is a circuit
// over symbols the SAT solver already carries (BVExactEncoder::assertFormula
// splices such circuits onto the live variables). The surrogate and proxy
// symbols are *protected* from the simplifier: a preprocessing pass that
// substituted one away, or rewrote away the one constraint it occurs in on
// the promise of a substitution, would leave a lemma over it talking about
// nothing (SubstitutionMap::theoryProtected, RemoveUnconstrained).
//
// Checking order. Records are created bottom-up, so a nested application's
// inner surrogate is an ordinary operand of the outer one and the checker
// visits children before parents. The check runs inside
// AbsRefine_CounterExample::CallSAT_ResultCheck after the bit-vector
// abstraction has declared its candidate faithful and after the array and UF
// checkers have accepted it, immediately before the ordinary replay of the
// original formula -- which still sees the original operations, so a
// candidate is published only when both the abstraction and the exact
// evaluator agree on it.
//
// Batch solves by default. The incremental driver hosts the abstraction too
// under --fp-abstraction-incremental, one instance per encoding epoch, with
// every release spliced rather than restarted (abstractPiece below); without
// that flag it encodes every floating-point operation exactly.

#include "stp/AST/AST.h"
#include "stp/AST/SourceSort.h"
#include "stp/FloatBlaster/FpAbstractionRules.h"
#include "stp/STPManager/STPManager.h"

#include <cstdint>
#include <functional>
#include <iosfwd>
#include <map>
#include <memory>
#include <set>
#include <utility>
#include <vector>

namespace stp
{
class AbsRefine_CounterExample;
class BVExactEncoder;
class SATSolver;
class ToSATBase;

// Which operations --fp-abstraction-ops admits. A bitmask so the C
// interface and the command line share one representation.
enum FpAbstractionOps : unsigned
{
  FP_ABSTRACT_MUL = 1u << 0,
  FP_ABSTRACT_DIV = 1u << 1,
  FP_ABSTRACT_SQRT = 1u << 2,
  FP_ABSTRACT_ADD = 1u << 3,
  FP_ABSTRACT_SUB = 1u << 4,
  FP_ABSTRACT_FMA = 1u << 5,
  FP_ABSTRACT_REM = 1u << 6,
  FP_ABSTRACT_RTI = 1u << 7,
  // The conversions to a machine integer: partial operations whose
  // unspecified results FpTotalise has already made total by the time the
  // abstraction runs, so their records carry the totalised choice as one
  // more proxy. Their result is a plain bit-vector, the one abstractable
  // sort that is not a float.
  FP_ABSTRACT_TO_SBV = 1u << 8,
  FP_ABSTRACT_TO_UBV = 1u << 9,
  // The three whose exact circuits are an order of magnitude above their
  // rules from binary32 up, and the fused multiply-add, which compiled
  // numerical code contracts a*b+c into and which measured as a gain on
  // every corpus of such code (docs/fp-abstraction.rst).
  FP_ABSTRACT_DEFAULT =
      FP_ABSTRACT_MUL | FP_ABSTRACT_DIV | FP_ABSTRACT_SQRT | FP_ABSTRACT_FMA,
};

// Parse "mul,div,sqrt,add,sub,fma,rem,rti,to_sbv,to_ubv" (or "all",
// "default", "none")
// into the mask. Returns false, leaving `mask` alone, for a name it does not
// know.
//
// DLL_PUBLIC because tools/stp links the shared library and calls this to
// answer --fp-abstraction-ops, exactly as it calls parseBVSchemaGroups for
// the bit-vector side. Without the annotation a -fvisibility=hidden build --
// which is every build with ENABLE_TESTING off, i.e. the default one --
// leaves the symbol local and fails to link the stp binary.
DLL_PUBLIC bool parseFpAbstractionOps(const std::string& text,
                                      unsigned& mask);

struct FpAbstractionStatistics
{
  uint64_t candidates = 0;    // operations of an admitted kind seen
  uint64_t abstracted = 0;    // records created
  uint64_t chained = 0;       // ... of them admitted as links in a chain
                              // (--fp-abstraction-chain-ops) rather than
                              // by --fp-abstraction-ops
  uint64_t shared = 0;        // occurrences that reused an existing record
  uint64_t ruleLemmas = 0;    // rule conjuncts emitted at abstraction time
  uint64_t crossRules = 0;    // facts between records of different operations
  uint64_t checks = 0;        // record checks against a candidate
  uint64_t skippedChecks = 0; // records the host's filter excluded
  uint64_t inactiveSkips = 0; // ... of them, outside the active closure
  uint64_t invalidModeSkips = 0; // ... of them, a mode that is no encoding
  uint64_t inconsistent = 0;  // ... that disagreed with the exact value
  uint64_t valueLemmas = 0;
  uint64_t boxLemmas = 0;     // ... of them widened to a box of operand tuples
  uint64_t shapeLemmas = 0;
  uint64_t relationalLemmas = 0;
  uint64_t releases = 0;      // exact encodings released
  uint64_t rounds = 0;        // refinement rounds that encoded FP lemmas
  uint64_t restarts = 0;      // pipeline runs before this one, each
                              // releasing operations exactly (see below)
  uint64_t repairs = 0;       // refuted candidates accepted by the replay
  double lemmaSeconds = 0;    // wall time spent lowering and splicing lemmas
};

class FpAbstraction // not copyable
{
public:
  // One abstracted application.
  struct Application
  {
    Kind kind = UNDEFINED;
    SourceSort format;
    // The application as it stood in the prepared formula, its children
    // already rewritten (an inner abstracted application appears here as
    // its surrogate view).
    ASTNode original;
    // The same application before its children were rewritten: the node
    // of the prepared formula itself, which a later run of the pipeline
    // over the same formula meets again, and which is therefore what a
    // release by restart is remembered by.
    ASTNode source;
    // The surrogate: a bit-vector symbol of the packed width, and the
    // floating-point view of it that replaced the application.
    ASTNode surrogate;
    ASTNode surrogateView;
    // Per child, in the original's child order: the child itself, the
    // symbol standing for it in lemmas (a proxy, a constant, or -- for a
    // child that already is another record's surrogate view -- that
    // record's surrogate symbol), and the floating-point view of that
    // symbol where the child is a float.
    std::vector<ASTNode> children;
    std::vector<ASTNode> proxies;
    std::vector<ASTNode> proxyViews;
    // The rounding mode when it is a constant: one of the one-hot
    // symbolic_fp::rounding_modes values, else 0 (symbolic, or an
    // operation without a mode).
    unsigned roundingMode = 0;
    unsigned valueLemmas = 0;
    unsigned shapeLemmas = 0;
    // A queued equality is not an exact encoding yet: model repair may
    // discard it. Only an asserted, permanent equality sets released.
    bool releasePending = false;
    bool released = false;
    // The record's own definitional facts -- its proxies' definitions and
    // its rule tiers and incident cross-operation rules -- so a host that
    // scopes definitions with encoding units can conjoin them into EVERY
    // unit that mentions the record, not only the one that minted it.
    ASTVec defs;
  };

  // `exact` are applications (by their prepared-formula node) that a
  // previous run of the pipeline released and this run must lower exactly
  // rather than abstract; `restarts` is how many such runs there were, and
  // `previouslyAbstracted` how many applications the last of them
  // abstracted (0 when there was none).
  FpAbstraction(STPMgr* bm_, const std::set<ASTNode>& exact = std::set<ASTNode>(),
                uint64_t restarts = 0, size_t previouslyAbstracted = 0);
  ~FpAbstraction();
  FpAbstraction(const FpAbstraction&) = delete;
  FpAbstraction& operator=(const FpAbstraction&) = delete;

  // Replace every admitted application in `prepared` (the formula as it
  // stands immediately before floating-point lowering) by a surrogate, and
  // conjoin the proxy definitions and the rule tiers. Returns `prepared`
  // itself when nothing was abstracted. Call once per solve.
  ASTNode abstract(const ASTNode& prepared);

  // The incremental driver's form of the same rewrite: one instance hosts
  // records for a whole encoding epoch, and each piece the driver lowers
  // passes through here immediately before its lowerPrepared. Records
  // accumulate across calls (an application met again -- same node -- is
  // the same record), and the proxy definitions and rule tiers of the
  // records it mentions are conjoined transitively into the piece, including
  // previously minted records and cross-operation partners. A definition's
  // child terms take the piece's own pipeline. The definitions retract
  // with the piece; while its piece is popped a
  // record may still be linked by another piece or a permanent lemma.
  // All persistent theory facts have a simultaneous exact extension over
  // the record DAG. An identical re-push restores the same symbols and
  // definitions through the cached encoding. If given, `closureSurrogates`
  // receives the surrogates of every record the piece carries -- the
  // closure just described, the unit's share of the active closure below.
  ASTNode abstractPiece(const ASTNode& prepared,
                        std::set<ASTNode>* closureSurrogates = nullptr);

  // The permanent ledger: every refinement lemma and release once
  // encoded, in assertion order, with how many of them the current SAT
  // backend holds. Ledger entries mention only the proxy and surrogate
  // symbols (pure bit-vector), so re-splicing them after a SAT-backend
  // rebuild needs no pipeline beyond the lemma lowering itself.
  bool hasUnassertedFacts() const
  {
    return factsAsserted_ < permanentFacts_.size();
  }
  void syncPermanentFacts(SATSolver& solver, ToSATBase* tosat);

  // Queue the exact circuit of every record not yet released, returning
  // how many were queued. The incremental driver's array-refinement
  // routes use this as a last resort: a candidate rejected by the model
  // evaluation that neither the array axioms nor a record's own check can
  // explain is decided by falling back to the exact encoding, which is
  // where the abstraction always converges.
  size_t releaseAllUnreleased();

  // A fresh SAT backend holds none of the clauses previously spliced;
  // schedule the whole ledger for re-assertion by the next
  // syncPermanentFacts. The records themselves are untouched.
  void resetForNewSolverEpoch() { factsAsserted_ = 0; }

  // The driver splices every release in place: a release by running the
  // pipeline again has no meaning on a persistent solver.
  void forbidRestarts() { restartAllowed_ = false; }

  // Bind proxies and released surrogates to their terms bit-for-bit, and
  // judge a candidate consistent only when the surrogate's bits equal the
  // exact result's, instead of under SMT-LIB floating-point equality
  // (which identifies every NaN). The batch pipeline can afford the value
  // view because its ordinary replay re-checks every accepted candidate
  // bit-exactly against the original formula; a host without that
  // backstop must not leave NaN payloads free -- these corpora
  // reinterpret the packed bits, and a payload the abstraction never
  // pinned reaches plain bit-vector context. Sound to tighten: the exact
  // circuits produce one canonical NaN.
  void useBitPreciseEqualities() { bitPrecise_ = true; }

  // Re-arm the per-record refinement budgets for a new check-sat: records
  // outlive queries under the driver and not in the batch pipeline, so
  // the ceilings are per query rather than per record lifetime. Releases
  // are per epoch and stay.
  void beginQuery();

  // Restrict checkCandidate to records the predicate accepts (by their
  // surrogate symbol). The driver passes "the current solver carries the
  // symbol's bits": a record whose piece was popped may have no live
  // bits, and reading it would check arbitrary defaults. Empty: check
  // everything (the batch behaviour).
  void setCheckFilter(std::function<bool(const ASTNode&)> filter)
  {
    checkFilter_ = std::move(filter);
  }

  // The active closure: the surrogates of every record an
  // asserted encoding unit carries, as the host computes it from the
  // closures abstractPiece reported for those units. While armed,
  // checkCandidate reads only those records. A record outside it shares no
  // bound symbol with the active query -- its proxies and surrogate are
  // free -- so its verdict cannot enter the acceptance argument and its
  // refinement facts could not cut a model of the query; reading it only
  // spends evaluations, budgets and, after a release, a circuit. Disarmed
  // (the default), every unreleased record is read.
  void setActiveClosure(std::set<ASTNode> surrogates)
  {
    activeClosure_ = std::move(surrogates);
    activeClosureArmed_ = true;
  }
  void disarmActiveClosure()
  {
    activeClosure_.clear();
    activeClosureArmed_ = false;
  }
  bool activeClosureArmed() const { return activeClosureArmed_; }

  // Whether any application was abstracted in this solve.
  bool active() const { return !applications_.empty(); }

  // The surrogate and proxy symbols, which preprocessing must leave alone.
  bool isProtected(const ASTNode& symbol) const
  {
    return protected_.find(symbol) != protected_.end();
  }
  const std::set<ASTNode>& protectedSymbols() const { return protected_; }

  enum class Outcome
  {
    Skipped,    // no active record
    Consistent, // every record's surrogate equals the exact result
    Conflict,   // at least one lemma is pending
    Restart     // a release is to be made by running the pipeline again
  };

  // Check every record against the candidate model, child before parent,
  // queueing a lemma for each disagreement.
  Outcome checkCandidate(AbsRefine_CounterExample& model);

  bool hasPendingLemma() const { return !pending_.empty(); }

  // The candidate the last check refuted turned out to satisfy the
  // original formula anyway (its surrogates were wrong, its values for the
  // original symbols were not), so it is a model: drop what the check
  // queued against it. --fp-abstraction-repair; the checker calls this.
  void acceptRepairedCandidate();

  // A release that is to happen by running the whole pipeline again with
  // the operation lowered exactly, rather than by splicing its circuit into
  // the running solver: the ordinary lowering gets constant-bit
  // propagation, the simplifier and -- where it is on -- the bit-vector
  // abstraction of the wide significand arithmetic, none of which the
  // splice can offer, and for a wide operation those are worth more than
  // the learnt clauses a restart loses. Which releases go this way is
  // --fp-abstraction-restart-width (0: none). The driver reads the requests
  // and starts the run.
  bool restartRequested() const { return !releaseRequests_.empty(); }
  // Whether a release may still go by restart in this run: not past
  // --fp-abstraction-restart-limit, and not after a run that abstracted no
  // fewer applications than the run before it -- the released application
  // was not met again (a pass that mints fresh symbols, as the totaliser
  // does for a partial conversion's unspecified result, rebuilds it under
  // another node), and restarting again would only repeat that.
  bool restartAllowed() const { return restartAllowed_; }
  const std::set<ASTNode>& releaseRequests() const { return releaseRequests_; }

  // Encode the queued lemmas into the running solver.
  void encodePendingLemmas(SATSolver& solver, ToSATBase* tosat);

  const FpAbstractionStatistics& statistics() const { return stats_; }

  void reportStatistics(std::ostream& out) const;

  // Test/inspection access.
  const std::vector<ASTNode>& pendingLemmas() const { return pending_; }
  const std::vector<FpRuleId>& pendingRuleIds() const { return pendingIds_; }
  const std::vector<FpRuleId>& committedRuleIds() const
  {
    return permanentIds_;
  }

  const std::vector<std::unique_ptr<Application>>& applications() const
  {
    return applications_;
  }

private:
  void queueLemma(FpRuleId id, const ASTNode& lemma);
  class Impl;
  std::unique_ptr<Impl> impl_;
  STPMgr* bm_;
  std::vector<std::unique_ptr<Application>> applications_;
  std::set<ASTNode> protected_;
  std::vector<ASTNode> pending_;
  // Metadata follows the same commit/repair transaction as its formulas.
  std::vector<FpRuleId> pendingIds_;
  // Every committed refinement lemma and release, in assertion order, and how
  // many of them the current SAT backend has been given. A rebuild resets
  // the count and the next sync re-splices the lot.
  std::vector<ASTNode> permanentFacts_;
  std::vector<FpRuleId> permanentIds_;
  size_t factsAsserted_ = 0;
  std::function<bool(const ASTNode&)> checkFilter_;
  std::set<ASTNode> activeClosure_;
  bool activeClosureArmed_ = false;
  bool bitPrecise_ = false;
  std::set<ASTNode> releaseRequests_; // sources to lower exactly next run
  size_t previouslyAbstracted_ = 0;
  bool restartAllowed_ = true;
  FpAbstractionStatistics stats_;
  // What the statistics said before the last check queued anything, so a
  // repaired candidate's discarded lemmas are not counted as spent.
  FpAbstractionStatistics statsBeforeCheck_;
};

} // namespace stp

#endif

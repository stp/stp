/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July, 2026
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

/*
 * Host-side state of the lemmas-on-demand decision procedure for the
 * extensional theory of arrays (Brummayer & Biere, JSAT 6 (2010))
 * inside STP:
 *
 *  - query-local array-equality records: construction preserves an opaque
 *    ARRAY_EQ, then the completed solve root is traversed after function
 *    substitution. Each reachable canonical operand pair is replaced by a
 *    fresh Boolean abstraction (paper section 5) and receives the witness
 *    constraints from preprocessing step 1 (section 4);
 *  - the per-solve view of the array subgraph relevant to those
 *    equalities (which arrays, writes and reads participate), frozen
 *    just before STP's main array transformation;
 *  - the pending refinement lemma between a failed candidate check and
 *    the re-solve, and its encoding into the incremental SAT solver;
 *  - the completed array model of an accepted candidate.
 *
 * Lifetime: one context per STPMgr, created lazily when a completed root first
 * reaches array-equality lowering. Generated records, proxies and witness
 * symbols are per-solve. The opaque public AST is durable; a current-solve
 * opaque-to-lowered map remains only long enough to evaluate public handles
 * in that solve's model.
 */

#ifndef EXTENSIONALITYCONTEXT_H
#define EXTENSIONALITYCONTEXT_H

#include "stp/AST/AST.h"
#include "stp/Extensionality/ExtChecker.h"
#include "stp/Sat/SATSolver.h"
#include "stp/ToSat/ToSATBase.h"
#include <map>
#include <set>
#include <vector>

namespace stp
{

class STPMgr;
class Simplifier;
class ArrayTransformer;
class AbsRefine_CounterExample;
class ToSATBase;

class ExtensionalityContext
{
public:
  // One abstracted array equality. The construction operands are the
  // array terms as they were when the equality was built; because STP
  // simplifies and substitutes before solving, the current (canonical)
  // form of each operand is recovered at solve time from the record's
  // anchor equations, which travel through the same rewriting as the
  // rest of the formula.
  struct Record
  {
    size_t id;
    ASTNode proxy;             // ordinary Boolean SYMBOL
    ASTNode constructionLeft;
    ASTNode constructionRight;
    ASTNode canonicalLeft;     // per-solve, set by prepare()
    ASTNode canonicalRight;    // per-solve, set by prepare()
    ASTNode lambda;            // fresh witness index symbol
    ASTNode nameL, nameR;      // scalar names of the witness reads
    // Constraint bundle conjoined at the start of every solve. The
    // last conjunct is preprocessing step 1 of the paper -- the witness
    // for array inequality, a != b -> read(a,l) != read(b,l) -- and the
    // two defining equations name the virtual reads so they stay in
    // the formula (and therefore in the bit-blast) in every case:
    //   nameL = read(constructionLeft, lambda)
    //   nameR = read(constructionRight, lambda)
    //   proxy OR nameL != nameR
    ASTNode anchorL, anchorR, witnessClause;
  };

  explicit ExtensionalityContext(STPMgr* bm);

  //--------------------------------------------------------------------
  // Query-local record table and activation
  //--------------------------------------------------------------------

  // The formula abstraction of an array equality (paper section 5), called by
  // solve-boundary lowering for each reachable well-typed equality. Returns
  // the fresh (or, for a repeated pair in this solve, reused) Boolean
  // abstraction variable; reflexive
  // requests fold to true; and an equality between a chain of writes
  // and the chain's own base is solved outright, returning the
  // rewritten read-equality formula with no record minted (see
  // solveWriteChain). Mixed index/element widths are an error.
  ASTNode makeEquality(const ASTNode& a, const ASTNode& b);

  // Replace every reachable opaque ARRAY_EQ in a completed query by its
  // Boolean abstraction and witness record. This is deliberately a solve-
  // boundary operation: function/let substitution must have specialized the
  // equality's operands before they disappear behind a proxy.
  ASTNode lowerArrayEqualities(const ASTNode& root);

  // Look up the Boolean formula used for an opaque equality in the current
  // solve. This is the sole metadata retained for public-handle model
  // evaluation; generated proxies and witness records are never durable
  // across solves.
  bool getCurrentLowering(const ASTNode& opaque, ASTNode& lowered) const;

  // Holds the registry seal for the duration of one solve and releases it
  // however the solve exits. Any record minted after the solve took its
  // constraint snapshot would be active without a defining witness bundle.
  class SolveScope
  {
    ExtensionalityContext* ctx;

  public:
    explicit SolveScope(ExtensionalityContext* c) : ctx(c) {}
    ~SolveScope()
    {
      if (ctx != NULL)
        ctx->registrySealed = false;
    }
    SolveScope(const SolveScope&) = delete;
    SolveScope& operator=(const SolveScope&) = delete;
  };

  bool enabled() const;
  // The decision procedure participates in a solve exactly when the
  // feature is on and at least one lowered equality record is reachable from
  // this solve's completed root (possibly through another active record).
  // Nothing else switches it on: a query with array if-then-elses but
  // no equality mints no record, so it is decided by STP's ordinary
  // array machinery at exactly the cost it would pay with the feature
  // off.
  bool active() const { return enabled() && !activeRecordIds.empty(); }

  const std::vector<Record>& getRecords() const { return records; }
  size_t getActiveRecordCount() const { return activeRecordIds.size(); }

  // Symbols the decision procedure depends on: abstraction variables,
  // witness indices and witness-read names, and the scalar names given
  // to lemma leaves. STP's substitution passes must not eliminate them
  // -- each must still be present when the formula is bit-blasted so
  // that refinement lemmas can be encoded over its SAT variables.
  bool isProtected(const ASTNode& s) const
  {
    return protectedSymbols.find(s) != protectedSymbols.end();
  }

  // Conservative pre-preprocessing inventory of the array symbols in
  // an active solve. The final graph is built from the whole prepared
  // formula, so this set must anticipate every array symbol whose reads
  // the checker may later own.
  bool wasArrayAnticipated(const ASTNode& arraySymbol) const
  {
    return anticipatedArraySymbols.find(arraySymbol) !=
           anticipatedArraySymbols.end();
  }

  //--------------------------------------------------------------------
  // Per-solve pipeline (TopLevelSTPAux)
  //--------------------------------------------------------------------

  // Reset all per-solve state (records, lowering map, graph, names, pending
  // lemmas and model). Called immediately before lowering the next root.
  void beginSolve();

  // Conjoin every current-root-active record's constraint bundle (the
  // witness clause of preprocessing step 1 plus the defining equations
  // of its virtual reads) before STP preprocessing, so the bundles are
  // simplified together with the rest of the formula. At this same
  // boundary, inventory the complete expanded root while read-deleting
  // substitutions can still be prevented. Array-valued if-then-elses
  // remain structural and are handled by the checker's T rules.
  ASTNode conjoinRecordConstraints(const ASTNode& root);

  // Final preparation, run after STP's simplifications and immediately
  // before its main array transformation:
  //  - recover each record's canonical operands from its anchors;
  //  - inventory the complete array graph reachable from the prepared
  //    formula. Once an equality activates the procedure, it owns every
  //    read in that graph; splitting congruence reasoning between it and
  //    STP's legacy refinement is not closed under shared scalar indexes;
  //  - inventory the graph's writes as accesses (paper section 11.4)
  //    and give every compound write index/value a scalar name that
  //    will be part of the initial bit-blast, so lemmas can later be
  //    encoded over existing SAT variables.
  // Returns the extended input to hand to the array transformation;
  // after this point the graph must not change for the rest of the
  // solve.
  ASTNode prepare(const ASTNode& root);

  bool arrayGraphFrozen() const { return arrayGraphIsFrozen; }
  bool checkerReady() const { return graphBound; }
  bool ownsArray(const ASTNode& arrayNode) const
  {
    return ownedArrays.find(arrayNode) != ownedArrays.end();
  }

  // Reads in the owned graph route their index through the transform's
  // fresh-index-variable pass even when the index is already a plain
  // variable: an index occurring only inside reads would otherwise
  // vanish from the bit-blasted formula, leaving future lemmas over it
  // without SAT variables.
  bool needsIndexAnchor(const ASTNode& arrayNode) const
  {
    return arrayGraphIsFrozen && ownsArray(arrayNode);
  }

  // After the main array transformation: collect the checker's access
  // inventory -- every owned read (including the witness reads) now has
  // its read-abstraction variable and index variable, and every owned
  // write its scalar names -- and freeze the graph handed to the
  // consistency checker.
  void bindAfterTransform(ArrayTransformer* at);

  //--------------------------------------------------------------------
  // Candidate checking and refinement (the loop of paper section 6)
  //--------------------------------------------------------------------

  enum CandidateOutcome
  {
    EXT_SKIPPED,
    EXT_CONSISTENT,
    EXT_CONFLICT,
    EXT_WITNESS_ERROR
  };

  enum CertificationAction
  {
    RETURN_SAT,
    ADD_EXT_LEMMA,
    RUN_HOST_REFINEMENT,
    INTERNAL_ERROR
  };

  // Decide what to do with a materialized candidate, given STP's own
  // model evaluation and the array consistency check. An array conflict
  // takes precedence over the ordinary result -- active solves never
  // enter STP's ordinary read refinement, so only the array
  // lemma can rule such a candidate out -- and a candidate is only ever
  // reported satisfiable when both checks pass on the same assignment.
  // When the checker is active, ordinary read refinement is not a
  // fallback: the checker owns the complete graph. Consequently a
  // conflict-free checker result paired with ordinary model failure is
  // an integration invariant violation, not an undecided outcome.
  static CertificationAction decideCertification(bool ordinaryResult,
                                                 bool checkerActive,
                                                 CandidateOutcome ext);

  // Run the pure checker against the current candidate model. On
  // conflict the certificate is stored as the pending lemma. On a
  // conflict-free fixed point, publish the observed array contents
  // into the counterexample map -- so model evaluation and the model
  // APIs see the certified contents -- and then verify every access's
  // scalar names against its terms evaluated in the completed model.
  // A mismatch is an internal ownership/encoding error: with the whole
  // graph registered, read congruence must already have produced a
  // checker conflict.
  CandidateOutcome checkCandidate(AbsRefine_CounterExample* ce);

  bool hasPendingLemma() const { return pendingLemmaValid; }

  // Encode every pending lemma into the persistent incremental SAT
  // solver, then clear them. The lemma premise/conclusion atoms are
  // reified over the SAT variables of already-encoded symbols -- the
  // refinement is clauses over the existing CNF, never a fresh
  // word-level formula handed back to the bit-blaster.
  //
  // A round emits the whole batch the consistency check found, not just
  // the earliest conflict. Each lemma is independently valid under the
  // candidate that produced it, so the batch rules out that candidate
  // by many more facts than one clause could, and the reified equality
  // literals the lemmas share are built once.
  void encodePendingLemmas(SATSolver& solver, ToSATBase* tosat);

  // Validate one bit-vector lemma leaf: it must be a fixed-width
  // constant, or a SYMBOL whose complete SAT-variable vector was
  // encoded by the initial bit-blast (present, full width, every bit
  // encoded). Returns NULL when valid, else a static reason string.
  // Pure -- no allocation and no SAT mutation -- so lemma encoding
  // reports a precise internal error instead of silently inventing
  // fresh, unconstrained SAT variables for a term the candidate was
  // never checked against.
  static const char* checkPreencodedBV(const ASTNode& n,
                                       const ToSATBase::ASTNodeToSATVar& satVar);

  // Every symbol EXTCHK relies on keeps its SAT variables (frozen
  // against backend variable elimination).
  // Lemma leaves whose semantics live entirely in future refinement
  // lemmas: the abstraction variables of owned reads and their index
  // symbols. Such a symbol can legally be absent from the bit-blasted
  // formula -- an owned read's only occurrence may itself sit inside
  // another abstracted term -- and the translator then allocates
  // fresh SAT variables for it before the first solve, which is
  // exactly the unconstrained semantics the blasted formula gives it.
  // Names defined by equations (witness reads, scalar names) are
  // deliberately not in this set: for them, absence from the
  // bit-blast means a defining equation was lost, and lemma encoding
  // must keep failing loudly.
  const std::set<ASTNode>& getLemmaOnlySymbols() const
  {
    return lemmaOnlySymbols;
  }

  const std::set<ASTNode>& getFrozenSymbols() const
  {
    return protectedSymbols;
  }

  // Scalar name -> the term its defining equation binds it to.
  const std::map<ASTNode, ASTNode>& getNameToTerm() const
  {
    return nameToTermMap;
  }

  // Statistics for --stats.
  int lemmasEmitted;

  // Lemma atoms the simplifier decided from their defining terms at
  // encoding time (no equality circuit was built and no literal
  // entered the clause). Cumulative over the context lifetime.
  int lemmaAtomsFolded;

private:
  STPMgr* bm;

  // Equality between a chain of writes and the chain's own base array,
  // solved by rewriting instead of abstraction; returns the null node
  // when the shape does not apply. See the definition for the
  // equivalence.
  ASTNode solveWriteChain(const ASTNode& a, const ASTNode& b) const;

  std::vector<Record> records;
  std::map<std::pair<ASTNode, ASTNode>, size_t> keyToRecord;
  std::map<ASTNode, size_t> proxyToRecord;
  // Sorted record ids reachable in the current solve. Only these records
  // contribute semantic constraints, protection and checker edges.
  std::vector<size_t> activeRecordIds;
  ASTNodeMap currentLowerings; // opaque ARRAY_EQ -> current lowered formula
  std::set<ASTNode> protectedSymbols;
  std::set<ASTNode> lemmaOnlySymbols; // per-solve; see the accessor
  std::set<ASTNode> anticipatedArraySymbols;

  // Set once a solve has taken its copy of the registry's constraints.
  // Minting a record after that point would leave it active with
  // nothing in the formula defining it, so refuse loudly rather than
  // let it happen quietly. Cleared by beginSolve().
  bool registrySealed;

  // ---- per-solve state ----
  bool arrayGraphIsFrozen;
  std::set<ASTNode> ownedArrays;
  std::map<ASTNode, ExtWriteNode> ownedWrites; // write node -> info
  std::map<ASTNode, std::vector<ASTNode>> ownedWriteParents;
  std::map<ASTNode, ExtIteNode> ownedItes; // ite node -> info
  std::map<ASTNode, std::vector<ASTNode>> ownedIteParents;
  std::vector<ExtEqEdge> eqEdges;
  std::map<ASTNode, std::vector<size_t>> eqAdjacency;
  std::vector<ExtWitness> witnessObls;
  std::map<ASTNode, ASTNode> scalarNames; // term -> name symbol
  std::map<ASTNode, ASTNode> nameToTermMap; // name symbol -> its term
  ExtGraph graph;                         // bound after transform
  bool graphBound;

  bool pendingLemmaValid;
  std::vector<ExtConflict> pendingLemmas;

  // Encode one lemma as the clause NOT p1 OR ... OR NOT pk OR
  // conclusion; the shared reified-literal cache means later lemmas in
  // a batch reuse the equality variables the earlier ones built.
  void encodeOneLemma(const ExtConflict& lemma, SATSolver& solver,
                      ToSATBase* tosat);

  // reified equality cache, scoped to the current SAT instance
  std::map<std::pair<unsigned, unsigned>, int> eqLitCache;

  // last consistent observations for model export
  std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>> lastObserved;

  // helpers
  // Publish the conflict-free observed (index, value) pairs of every
  // owned array -- including write and array-if-then-else nodes -- into
  // the counterexample map, so model
  // evaluation, the model APIs, and the printers all see the array
  // contents the consistency check certified. Called by checkCandidate
  // on every conflict-free fixed point, before the name verification.
  void publishObservations(AbsRefine_CounterExample* ce);
  // With the observations published, check that every access's scalar
  // names evaluate exactly like the terms they stand for.
  bool namesAgreeWithCandidate(ExtModelView& view,
                               AbsRefine_CounterExample* ce) const;
  void collectAnticipatedArraySymbols(const ASTNode& n);
  void activateReachableRecords(const ASTNode& loweredRoot);
  ASTNode freshName(const ASTNode& term, ASTVec& namingConstraints);
  // The Boolean analogue of freshName, for an if-then-else condition:
  // a fresh symbol constrained equivalent to the condition, so that the
  // checker branches on a value the SAT solver assigned rather than one
  // re-derived from the counterexample, and so that a lemma premise has
  // one encoded literal to name.
  ASTNode conditionName(const ASTNode& cond, ASTVec& namingConstraints);
  // Collect every array-valued node reachable from the prepared root.
  void computeArrayGraph(const ASTNode& root, std::set<ASTNode>& arrays,
                         std::map<ASTNode, std::vector<ASTNode>>& parents);
  void locateCanonicalOperands(const ASTNode& root);
};

} // namespace stp

#endif // EXTENSIONALITYCONTEXT_H

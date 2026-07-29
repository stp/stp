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
 *  - the registry of array equalities: whenever the feature is enabled,
 *    an equality between a new canonical pair of array terms is
 *    replaced at node-creation time by a fresh Boolean abstraction
 *    variable -- the equality arm of the paper's formula abstraction
 *    (section 5), applied eagerly -- together with the constraints
 *    corresponding to preprocessing step 1 (section 4). The paper
 *    orders preprocessing before abstraction; STP registers both per
 *    equality at construction and completes the array-side
 *    preparation per solve;
 *  - the per-solve view of the array subgraph relevant to those
 *    equalities (which arrays, writes and reads participate), frozen
 *    just before STP's main array transformation;
 *  - the pending refinement lemma between a failed candidate check and
 *    the re-solve, and its encoding into the incremental SAT solver;
 *  - the completed array model of an accepted candidate.
 *
 * Lifetime: one context per STPMgr, created lazily the first time an
 * array equality is built with --array-equality enabled. The registry
 * lives as long as the query AST (its abstraction variables are
 * embedded in the user's formula); everything model- or solve-specific
 * is reset by beginSolve() at each top-level solve.
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
    // For arrays whose index sort quotients its bit patterns (a float
    // index: every NaN pattern is one value; a RoundingMode index: only
    // the five one-hot patterns denote), lambda must range over the
    // denoting patterns -- a "witness" at any other pattern would sit at
    // an index no select can reach. Null for plain bitvector indexes.
    ASTNode indexSortClause;
    // One-hot pinnings for RoundingMode-element reads that occur inside
    // the recorded operands. FpTotalise pins the reads of the input
    // formula, but the operands were abstracted out of it before that
    // pass ran; totalising them at record creation returns their read
    // pinnings, which must be conjoined alongside the anchors. Null
    // when the operands contain no such read.
    ASTNode rmReadClause;
  };

  explicit ExtensionalityContext(STPMgr* bm);

  //--------------------------------------------------------------------
  // Registry (persistent for the query AST lifetime)
  //--------------------------------------------------------------------

  // The formula abstraction of an array equality (paper section 5):
  // called from the shared node-creation funnel for every well-typed
  // equality between array terms while the feature is enabled, instead
  // of building an EQ node. Returns the fresh (or, for a repeated
  // operand pair, reused) Boolean abstraction variable; reflexive
  // requests fold to true; and an equality between a chain of writes
  // and the chain's own base is solved outright, returning the
  // rewritten read-equality formula with no record minted (see
  // solveWriteChain). Mixed index/element widths are an error.
  ASTNode makeEquality(const ASTNode& a, const ASTNode& b);

  bool enabled() const;
  // The decision procedure participates in a solve exactly when the
  // feature is on and at least one array equality was abstracted.
  bool active() const { return enabled() && !records.empty(); }

  const std::vector<Record>& getRecords() const { return records; }

  // Symbols the decision procedure depends on: abstraction variables,
  // witness indices and witness-read names, and the scalar names given
  // to lemma leaves. STP's substitution passes must not eliminate them
  // -- each must still be present when the formula is bit-blasted so
  // that refinement lemmas can be encoded over its SAT variables.
  bool isProtected(const ASTNode& s) const
  {
    return protectedSymbols.find(s) != protectedSymbols.end();
  }

  // Conservative over-approximation of the arrays the checker may
  // reason about (every array symbol reachable from any registry
  // operand), used to stop the substitution pass from deleting
  // read-equals-constant equations whose reads the checker needs to
  // observe.
  bool mayBeConeArray(const ASTNode& arraySymbol) const
  {
    return possibleConeSymbols.find(arraySymbol) != possibleConeSymbols.end();
  }

  //--------------------------------------------------------------------
  // Per-solve pipeline (TopLevelSTPAux)
  //--------------------------------------------------------------------

  // Reset all per-solve state (cone, naming, pending lemma, model).
  void beginSolve();

  // Conjoin every record's constraint bundle (the witness clause of
  // preprocessing step 1 plus the defining equations of its virtual
  // reads) onto the input, before any of STP's preprocessing runs, so
  // the bundles are simplified and substituted together with the rest
  // of the formula.
  ASTNode conjoinRecordConstraints(const ASTNode& root);

  // Final preparation, run after STP's simplifications and immediately
  // before its main array transformation:
  //  - recover each record's canonical operands from its anchors;
  //  - compute the "cone": the arrays connected to the abstracted
  //    equalities (operands, the bases under their writes, and the
  //    writes on top of them in the formula);
  //  - eliminate array-valued if-then-else inside the cone, replacing
  //    ite(c,a,b) by a fresh array d constrained by c -> d = a and
  //    not(c) -> d = b (paper section 4.1), repeated to a fixed point
  //    since the guarded equalities are themselves abstracted;
  //  - inventory the cone's writes as accesses (paper section 11.4)
  //    and give every compound write index/value a scalar name that
  //    will be part of the initial bit-blast, so lemmas can later be
  //    encoded over existing SAT variables.
  // Returns the extended input to hand to the array transformation;
  // after this point the cone must not change for the rest of the
  // solve.
  ASTNode prepare(const ASTNode& root);

  bool coneFrozen() const { return coneIsFrozen; }
  bool inCone(const ASTNode& arrayNode) const
  {
    return coneArrays.find(arrayNode) != coneArrays.end();
  }

  // Reads of cone arrays route their index through the transform's
  // fresh-index-variable pass even when the index is already a plain
  // variable: an index occurring only inside reads would otherwise
  // vanish from the bit-blasted formula, leaving future lemmas over it
  // without SAT variables.
  bool needsIndexAnchor(const ASTNode& arrayNode) const
  {
    return coneIsFrozen && inCone(arrayNode);
  }

  // After the main array transformation: collect the checker's access
  // inventory -- every cone read (including the witness reads) now has
  // its read-abstraction variable and index variable, and every cone
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
    EXT_WITNESS_ERROR,
    // The propagation reached a conflict-free fixed point, but some
    // access's scalar name evaluates differently from the term it
    // stands for in the completed candidate model. The anchoring
    // equation ties the name to the term only as the term was
    // bit-blasted; a read of an array outside the cone is abstracted
    // lazily by the host, so until the host's read refinement links
    // them, two abstractions of the same cell can be held apart, and
    // preprocessing can leave two forms of one term that end up
    // abstracted independently. Such a candidate must not be
    // certified: the checker placed accesses at cells the completed
    // model contradicts. It is also not refutable by an array lemma
    // -- the missing fact is an ordinary read-congruence axiom, which
    // is exactly what the host's refinement adds.
    EXT_NAME_DIVERGENCE
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
  // takes precedence over the ordinary result -- reads inside the cone
  // are exempt from STP's ordinary read refinement, so only the array
  // lemma can rule such a candidate out -- and a candidate is only ever
  // reported satisfiable when both checks pass on the same assignment.
  // A name divergence routes to the host's read refinement whatever
  // the ordinary result was: the candidate is untrustworthy, and the
  // missing fact is an ordinary read-congruence axiom, not an array
  // lemma.
  static CertificationAction decideCertification(bool ordinaryResult,
                                                 bool registryNonempty,
                                                 CandidateOutcome ext);

  // Run the pure checker against the current candidate model. On
  // conflict the certificate is stored as the pending lemma. On a
  // conflict-free fixed point, publish the observed array contents
  // into the counterexample map -- so model evaluation and the model
  // APIs see the certified contents -- and then verify every access's
  // scalar names against its terms evaluated in the completed model,
  // reporting EXT_NAME_DIVERGENCE on disagreement.
  CandidateOutcome checkCandidate(AbsRefine_CounterExample* ce);

  bool hasPendingLemma() const { return pendingLemmaValid; }

  // Encode exactly the pending lemma into the persistent incremental
  // SAT solver, then clear it. The lemma premise/conclusion atoms are
  // reified over the SAT variables of already-encoded symbols -- the
  // refinement is clauses over the existing CNF, never a fresh
  // word-level formula handed back to the bit-blaster.
  void encodePendingLemma(SATSolver& solver, ToSATBase* tosat);

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
  // lemmas: the abstraction variables of cone reads and their index
  // symbols. Such a symbol can legally be absent from the bit-blasted
  // formula -- a cone read's only occurrence may itself sit inside
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
  std::set<ASTNode> protectedSymbols;
  std::set<ASTNode> lemmaOnlySymbols; // per-solve; see the accessor
  std::set<ASTNode> possibleConeSymbols;

  // Replacements for array-valued if-then-else (paper section 4.1):
  // original ITE node -> its fresh array. Persistent across solves, so
  // a repeated solve of the same query reuses the fresh array -- and,
  // through the registry's operand-pair dedup, the same two guarded
  // equality records -- instead of minting a new generation per solve.
  std::map<ASTNode, ASTNode> iteReplacements;

  // The guard implications that define those fresh arrays -- two per
  // replacement, minted with it. Persistent for the same reason the
  // registry is: a solve that reuses a replacement eliminates no
  // if-then-else and so states no guards of its own, while the guarded
  // equality records are in the registry and asserted all the same.
  // conjoinRecordConstraints restates them at the start of every
  // solve, alongside those records' witness bundles, so that a record
  // is never active without its defining implication.
  ASTVec iteGuards;

  // True while prepare() mints the guarded equalities of its
  // if-then-else elimination: their operands come from the prepared
  // formula, which is already totalised, and the index
  // canonicalisation inside FpTotalise is not structurally idempotent
  // -- re-totalising would wrap an already-canonical index in a second
  // circuit and the machinery would treat the two as distinct indexes.
  bool operandsAreTotalised;

  // ---- per-solve state ----
  bool coneIsFrozen;
  std::set<ASTNode> coneArrays;
  std::map<ASTNode, ExtWriteNode> coneWrites; // write node -> info
  std::map<ASTNode, std::vector<ASTNode>> coneWriteParents;
  std::vector<ExtEqEdge> eqEdges;
  std::map<ASTNode, std::vector<size_t>> eqAdjacency;
  std::vector<ExtWitness> witnessObls;
  std::map<ASTNode, ASTNode> scalarNames; // term -> name symbol
  std::map<ASTNode, ASTNode> nameToTermMap; // name symbol -> its term
  ExtGraph graph;                         // bound after transform
  bool graphBound;

  bool pendingLemmaValid;
  ExtConflict pendingLemma;

  // reified equality cache, scoped to the current SAT instance
  std::map<std::pair<unsigned, unsigned>, int> eqLitCache;

  // last consistent observations for model export
  std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>> lastObserved;

  // helpers
  // Publish the conflict-free observed (index, value) pairs of every
  // cone array -- including write nodes and the fresh arrays introduced
  // for array if-then-else -- into the counterexample map, so model
  // evaluation, the model APIs, and the printers all see the array
  // contents the consistency check certified. Called by checkCandidate
  // on every conflict-free fixed point, before the name verification.
  void publishObservations(AbsRefine_CounterExample* ce);
  // With the observations published, check that every access's scalar
  // names evaluate exactly like the terms they stand for; false means
  // EXT_NAME_DIVERGENCE.
  bool namesAgreeWithCandidate(ExtModelView& view) const;
  void collectPossibleConeSymbols(const ASTNode& n);
  ASTNode freshName(const ASTNode& term, ASTVec& namingConstraints);
  void computeProvisionalCone(const ASTNode& root,
                              std::set<ASTNode>& cone,
                              std::map<ASTNode, std::vector<ASTNode>>& parents,
                              std::vector<ASTNode>& coneITEs);
  void locateCanonicalOperands(const ASTNode& root);
};

} // namespace stp

#endif // EXTENSIONALITYCONTEXT_H

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
 * The consistency checker of the lemmas-on-demand decision procedure
 * for the extensional theory of arrays:
 *
 *   Robert Brummayer, Armin Biere: "Lemmas on Demand for the
 *   Extensional Theory of Arrays", JSAT 6 (2009) 165-201.
 *
 * A candidate assignment sigma produced by the SAT solver assigns
 * values to the abstraction variables of reads and array equalities,
 * but knows nothing of the array axioms; the checker decides whether
 * sigma can be extended to a genuine array model (paper section 7).
 * It maintains the paper's map rho from each array term to the set of
 * accesses currently known to constrain it, and runs the paper's
 * propagation rules to a fixed point over a FIFO work list:
 *
 *   I     seed every access at its own array (section 7.2);
 *   D / U propagate an access down through / up over a write when
 *         sigma assigns its index differently from the write index,
 *         following the read-over-write axiom A3 (sections 7.2, 7.3);
 *   R / L propagate accesses across an array equality whose Boolean
 *         abstraction variable sigma assigns true (section 7.3);
 *   C     on every insertion, compare against the access already at
 *         the destination for the same concrete index: a different
 *         concrete value violates the (adapted) read-congruence axiom
 *         A1 and yields a conflict (section 7.2).
 *
 * The work list is FIFO and rule I seeds every access before the
 * fixed point starts, so discovery is breadth-first per access: the
 * first arrival of an access at an array -- the one whose path gets
 * recorded -- came along a shortest propagation path. That gives the
 * minimization of section 11.1 without a separate post-conflict
 * search.
 *
 * Exactly how far that reaches is worth stating, because the pass does
 * not stop at the first conflict the way the paper's does. An arrival
 * that conflicts is recorded as seen but is not queued, so the access
 * stops at the array it conflicted at. Shortest paths are therefore a
 * property of the graph in which each access's own conflict sites are
 * terminal: the first conflict of a pass has shortest paths on both
 * sides unconditionally, and a later one has the shortest paths still
 * available to it. A later conflict can consequently carry a longer
 * premise than an exhaustive search would give it, and a pair that can
 * only meet through an earlier conflict site is not reported at all --
 * it resurfaces in a later refinement round, once a lemma has moved the
 * candidate. Pinned at both ends by the ConflictPremiseUsesShortestPaths
 * and ConflictingArrivalStopsAtTheConflictArray unit tests; do not
 * replace the deque with a stack.
 *
 * Following section 11.2, rho keeps one representative access per
 * concrete index of each array, in a hash keyed by the index value: a
 * congruence lookup is a single probe rather than a scan, and an
 * access arriving with the same concrete index and the same concrete
 * value as the representative is dropped without further propagation.
 *
 * Dropping it is complete, but the reason is about the whole class of
 * accesses carrying that concrete (index, value) pair rather than about
 * the two accesses at hand. It is not the case that the representative
 * reaches everything the duplicate would have: the representative can
 * be dropped in its turn at a later array, or stop there on a conflict.
 * What holds is that no rule can tell members of the class apart. Every
 * rule's applicability depends on the source array, on sigma, and on
 * the access's concrete index -- write indices stepped over, array
 * equalities and if-then-else conditions sigma decided -- and never on
 * which member carries it. So the class reaches exactly the arrays any
 * one member would, at most one member is ever resident at an array,
 * and whether an arrival conflicts depends only on its concrete index
 * and value meeting a different value there. Every conflict a member
 * would find, therefore, some member does find -- possibly credited to
 * a different one of them.
 *
 * On a conflict it builds the paper's lemma (section 8): the
 * conjunction of the index equality, the write-index disequalities
 * collected along both propagation paths, and the positive array
 * equalities crossed, implies equality of the two access values. The
 * lemma is produced twice: once over the original terms (the theory
 * lemma) and once over the abstraction variables and scalar names
 * (alpha of the lemma, the form actually added to the SAT solver).
 * Finally it verifies the witness constraints of preprocessing step 1:
 * an array equality assigned false must have differing values at its
 * witness index lambda (axiom A4').
 *
 * The checker is pure: it never creates terms in the host query, adds
 * clauses, or calls SAT. Insertion is first-path-wins: the first
 * arrival of an access at an array fixes its recorded path there and no
 * later arrival displaces it, so each (array, access) pair is inserted
 * at most once. Arrivals are not the same as insertions -- one dropped
 * as represented leaves no record behind, so a later arrival by another
 * route repeats the constant-work test and reaches the same verdict,
 * sigma being fixed and representatives never changing. That is why the
 * skip counters count arrivals rather than pairs. Concrete values are
 * hash-consed BVCONST nodes, making value comparison node identity at
 * any bit width.
 */

#ifndef EXTCHECKER_H
#define EXTCHECKER_H

#include "stp/AST/AST.h"
#include <map>
#include <string>
#include <vector>

namespace stp
{

// One access: a read, or a write treated as a read of itself (the
// paper's polymorphic "access" node, section 11.4, which makes the
// explicit read(write(a,i,e),i) = e constraints of preprocessing step 2
// unnecessary). For a read the site is its array operand and the value
// is its read-abstraction variable; for a write the site is the write
// node itself and the value is the written element.
// indexName/valueName are the scalar leaves a lemma will be encoded
// over (SYMBOLs already present in the bit-blasted formula, or
// constants); indexTerm/valueTerm are the original terms, used for the
// theory-level form of the lemma.
struct ExtAccess
{
  size_t id;
  bool isWrite;
  ASTNode site;
  ASTNode indexTerm;
  ASTNode valueTerm;
  ASTNode indexName;
  ASTNode valueName;
};

// One condition collected along an access's propagation path, and later
// contributed to the lemma premise. Rules D and U contribute an
// index disequality (the access index differs from the write index
// stepped over); rules R and L contribute the array equality crossed;
// rules T-down and T-up contribute the if-then-else condition under
// which the branch they stepped over is the selected one.
// Array equalities only ever appear positively in lemmas: R/L fire
// only when sigma assigns the equality true (paper section 10.2). An
// if-then-else condition appears with the polarity sigma gave it,
// because both of its branches are selectable.
struct ExtGuard
{
  enum Kind
  {
    INDEX_NE,
    EQ_PROXY,
    ITE_COND_POS,
    ITE_COND_NEG
  };
  Kind kind = INDEX_NE;

  // Each predecessor link stores one shared four-node payload instead of
  // reserving separate ASTNodes for all variants. Complete paths are
  // materialized only when a conflict certificate is emitted:
  //
  // INDEX_NE: theoryA/theoryB are the original index terms;
  //           absA/absB are their scalar names.
  // EQ_PROXY: theoryA/theoryB are the canonical array operands;
  //           absA is the Boolean equality proxy.
  // ITE_COND_{POS,NEG}: theoryA is the original condition;
  //                     absA is its reified Boolean name. The kind
  //                     records the selected branch's polarity.
  ASTNode theoryA, theoryB;
  ASTNode absA, absB;
  size_t eqRecord = 0;
};

// An owned array-valued if-then-else, kept as a term rather than
// eliminated (paper section 4.1 declines to do this "to simplify our
// presentation"; the direct integration it mentions is what this is).
// condName reifies the condition as a Boolean symbol, so that the
// value the checker reads is the one the SAT solver assigned rather
// than something re-evaluated from the counterexample -- the failure
// class that made a scalar name disagree with its term -- and so that
// a lemma premise has a single encoded literal to name.
struct ExtIteNode
{
  ASTNode ite;
  ASTNode condTerm;
  ASTNode condName;
  ASTNode thn;
  ASTNode els;
};

struct ExtEqEdge
{
  size_t record;
  ASTNode left;
  ASTNode right;
  ASTNode proxy;
};

// A witness obligation from preprocessing step 1 (paper section 4):
// for the array equality a = b, a fresh index lambda and the virtual
// reads read(a,lambda) / read(b,lambda) were created, constrained by
// a != b -> read(a,lambda) != read(b,lambda). If sigma assigns the
// equality's Boolean abstraction variable false, the two witness read
// values must therefore differ; since the constraint was part of the
// bit-blasted formula, a violation indicates an integration bug, not
// a refinable candidate.
struct ExtWitness
{
  size_t record;
  ASTNode proxy;
  ASTNode index;
  ASTNode leftValue;
  ASTNode rightValue;
};

// Per-write-node data needed by the D and U rules.
struct ExtWriteNode
{
  ASTNode write;
  ASTNode base;
  ASTNode indexTerm;
  ASTNode indexName;
};

// The array subgraph of the preprocessed formula, frozen for one
// solve: accesses, write edges, equality edges, and the witness
// obligations of preprocessing step 1. All vectors carry a fixed
// deterministic order (noted per field below), so checker runs -- and
// therefore lemmas and models -- are reproducible; the maps are used
// for lookup only.
struct ExtGraph
{
  std::vector<ExtAccess> accesses; // in stable seed order

  std::map<ASTNode, ExtWriteNode> writes;             // write node -> info
  std::map<ASTNode, std::vector<ASTNode>> writeParents; // base -> writes
                                                        // (each sorted by
                                                        // node number)
  std::vector<ExtEqEdge> eqEdges;
  // array -> indices into eqEdges; per source sorted by
  // (record, destination node number, rule) where R_EQ sorts before
  // L_EQ, so each array's equality edges fire in a fixed order.
  std::map<ASTNode, std::vector<size_t>> eqAdjacency;

  std::map<ASTNode, ExtIteNode> ites;                 // ite node -> info
  std::map<ASTNode, std::vector<ASTNode>> iteParents; // branch -> ites
                                                      // (each sorted by
                                                      // node number)

  std::vector<ExtWitness> witnesses; // sorted by record id
};

// Access to the candidate assignment sigma. Every checker-visible term
// must have a concrete value in the candidate; a missing value is an
// integration error, never a reason to default. bvValue must return a
// BVCONST node; boolValue a Boolean. Implementations wrap either
// AbsRefine_CounterExample or a plain map (unit tests).
class ExtModelView
{
public:
  virtual ~ExtModelView() {}
  virtual ASTNode bvValue(const ASTNode& term) = 0;
  virtual bool boolValue(const ASTNode& term) = 0;
};

// One atom of a lemma premise or conclusion, after canonicalization
// (duplicate atoms dropped, reflexive equalities removed, deterministic
// order). BV_EQ/BV_NE carry the
// operand pair for the layer (abstract: scalar names; theory: original
// terms). ARRAY_EQ appears only in the theory lemma; BOOL_LIT (a
// positive proxy, or a positively-taken if-then-else condition) and
// BOOL_LIT_NEG (a negatively-taken one) only in the abstract lemma.
struct ExtLemmaAtom
{
  enum Op
  {
    BV_EQ = 0,
    BV_NE = 1,
    ARRAY_EQ = 2,
    BOOL_LIT = 4,
    BOOL_LIT_NEG = 5
  };
  Op op;
  ASTNode a, b;     // BV_EQ / BV_NE operands, or ARRAY_EQ array operands
  ASTNode boolTerm; // BOOL_LIT proxy
  size_t eqRecord;  // for ARRAY_EQ / BOOL_LIT

  bool operator==(const ExtLemmaAtom& o) const
  {
    return op == o.op && a == o.a && b == o.b && boolTerm == o.boolTerm;
  }
};

// A congruence conflict found by rule C, together with the lemma built
// from it (paper section 8): both access ids, the common
// array, concrete values, per-side guard paths, plus the canonicalized
// premises and the conclusion pair for the theory and abstract layers.
struct ExtConflict
{
  ASTNode commonArray;
  size_t leftAccess;  // the previously inserted representative
  size_t rightAccess; // the arriving access
  ASTNode indexValue;
  ASTNode leftValue, rightValue;
  std::vector<ExtGuard> leftGuards, rightGuards;

  std::vector<ExtLemmaAtom> abstractPremise; // canonical order
  ASTNode abstractConclusionA, abstractConclusionB;

  std::vector<ExtLemmaAtom> theoryPremise; // canonical order
  ASTNode theoryConclusionA, theoryConclusionB;
};

struct ExtEvent
{
  enum Kind
  {
    SEED,
    PROPAGATE,
    SKIP_SEEN,
    SKIP_REPRESENTED, // section 11.2: same concrete index and value as
                      // the representative already at the array
    CONFLICT,
    WITNESS_CHECK
  };
  Kind kind;
  const char* rule;
  ASTNode source; // null for seeds / witness checks
  ASTNode destination;
  size_t access;
};

struct ExtCheckResult
{
  enum Status
  {
    CONSISTENT,
    CONFLICT,
    WITNESS_VIOLATION
  };
  Status status;
  // Every independent congruence conflict the pass found, in discovery
  // order; non-empty iff status == CONFLICT. The pass does not stop at
  // the first, because each conflict yields a lemma that is valid on
  // its own (its premise holds and its conclusion fails in the very
  // same candidate), and emitting them together spares a whole
  // solve-from-scratch per lemma. "Found", not "exists": a conflicting
  // arrival does not propagate onward, so this is not an exhaustive
  // enumeration of the disagreeing pairs in the candidate. See the
  // shortest-path discussion at the top of this file.
  std::vector<ExtConflict> conflicts;
  // conflicts[0] -- the conflict a first-conflict-wins pass would have
  // stopped at. Kept for callers that want just the earliest one.
  ExtConflict conflict;      // valid iff status == CONFLICT
  size_t violatedRecord;     // valid iff status == WITNESS_VIOLATION

  // When the candidate is consistent, the fixed point of rho gives the
  // observed contents of every array: pairs of concrete
  // (index, value) BVCONSTs for every rho entry. Valid iff CONSISTENT.
  std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>> observed;

  std::vector<ExtEvent> events;
  std::map<std::string, int> stats;

  // Proof-storage diagnostics. The fixed point stores one constant-size
  // predecessor entry per reached (array, access) pair; guards are copied
  // into complete vectors only for emitted conflict certificates.
  size_t proofPathEntries = 0;
  size_t materializedGuardCount = 0;
};

class ExtChecker
{
public:
  // Runs one full check of the candidate model against the graph.
  // Pure: no SAT access, no term allocation into the host query.
  static ExtCheckResult check(const ExtGraph& graph, ExtModelView& model,
                              bool recordEvents = false);
};

} // namespace stp

#endif // EXTCHECKER_H

/********************************************************************
 * AUTHORS: Andrew V. Jones
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
 *   Extensional Theory of Arrays", JSAT 6 (2010) 165-201.
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
 *   C     on every insertion, compare against the accesses already at
 *         the destination: equal concrete indices with different
 *         concrete values violate the (adapted) read-congruence axiom
 *         A1 and yield a conflict (section 7.2).
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
 * clauses, or calls SAT. Insertion is first-path-wins, so each
 * (array, access) pair is considered once per candidate. Concrete
 * values are hash-consed BVCONST nodes, making value comparison node
 * identity at any bit width.
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
// stepped over); rules R and L contribute the array equality crossed.
// Array equalities only ever appear positively in lemmas: R/L fire
// only when sigma assigns the equality true (paper section 10.2).
struct ExtGuard
{
  enum Kind
  {
    INDEX_NE,
    EQ_PROXY
  };
  Kind kind;

  // INDEX_NE: theory "indexTerm != writeIndexTerm",
  //           abstract "indexName != writeIndexName".
  ASTNode theoryA, theoryB;
  ASTNode absA, absB;

  // EQ_PROXY: theory "left = right" over the original (canonical) array
  // operands; abstract: the positive Boolean proxy literal.
  ASTNode proxy;
  ASTNode eqLeft, eqRight;
  size_t eqRecord;
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
// obligations of preprocessing step 1. All vectors carry the
// deterministic reference ordering; the maps are used for lookup only.
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
  // L_EQ, mirroring the reference adjacency order.
  std::map<ASTNode, std::vector<size_t>> eqAdjacency;

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
// positive proxy) only in the abstract lemma.
struct ExtLemmaAtom
{
  enum Op
  {
    BV_EQ = 0,
    BV_NE = 1,
    ARRAY_EQ = 2,
    BOOL_LIT = 4
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
    CONFLICT,
    WITNESS_CHECK
  };
  int seq;
  Kind kind;
  const char* rule;
  ASTNode source; // null for seeds / witness checks
  ASTNode destination;
  size_t access;
  ASTNode indexValue;  // null on SKIP_SEEN
  ASTNode accessValue; // null on SKIP_SEEN
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
  ExtConflict conflict;      // valid iff status == CONFLICT
  size_t violatedRecord;     // valid iff status == WITNESS_VIOLATION

  // When the candidate is consistent, the fixed point of rho gives the
  // observed contents of every array: pairs of concrete
  // (index, value) BVCONSTs for every rho entry. Valid iff CONSISTENT.
  std::map<ASTNode, std::vector<std::pair<ASTNode, ASTNode>>> observed;

  std::vector<ExtEvent> events;
  std::map<std::string, int> stats;
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

/********************************************************************
 * Congruence closure over UF argument terms, run inside the SAT search.
 ********************************************************************/
#ifndef STP_UFCONGRUENCEPROPAGATOR_H
#define STP_UFCONGRUENCEPROPAGATOR_H

#include "stp/AST/ASTNode.h"
#include "stp/Sat/SATSolver.h"
#include <cstdint>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace stp
{

class UFDecl;

// Functional consistency as a theory the SAT search consults, rather than a
// property of the complete models it hands back.
//
// The refinement loop is complete on its own: it reads a model, buckets each
// declaration's applications by their concrete argument tuple, and installs a
// congruence lemma for every bucket whose members disagree. What it cannot do
// is say anything about a *partial* assignment, and two things follow. A round
// costs a whole search, because a violation is only visible once every bit has
// a value. And transitivity is invisible to it altogether: a complete model
// interprets every term by a value, so equality in it is transitive by
// construction and no model ever exhibits a transitivity violation to refute.
// That reasoning had to reach the solver as clauses written before the search
// -- O(terms^3) triples over O(terms^2) equality atoms, which is affordable
// only while the term count stays small.
//
// This runs the same reasoning as a backtrackable union-find over the atoms
// the refinement loop has already minted, and pays for a triple only where the
// search walks into one:
//
//   an equality atom asserted true    joins two terms' classes
//   an atom the join has made true    the equalities on the proof path between
//     but the search has not            its endpoints, negated, plus the atom
//                                       -- which propagates it, or is the
//                                       conflict if the search denied it
//   two applications of one           that path for each argument, negated,
//     declaration whose arguments       plus the two result bits that
//     have all been joined              disagree
//
// Every clause it produces is a consequence of the query, so nothing here can
// change a verdict; what changes is when the search is told. Soundness rests
// on one obligation the caller carries: an atom registered here must have both
// halves of its definition in the CNF (`q -> bits equal` and `bits equal ->
// q`). The refinement loop mints argument atoms with only the second half,
// because a lemma names them negated -- and an atom that is merely implied by
// its equality can be set true without the terms agreeing, so a chain of those
// proves nothing.
class DLL_PUBLIC UFCongruencePropagator final
    : public SATSolver::TheoryPropagator
{
public:
  UFCongruencePropagator();
  ~UFCongruencePropagator() override;

  UFCongruencePropagator(const UFCongruencePropagator&) = delete;
  UFCongruencePropagator& operator=(const UFCongruencePropagator&) = delete;

  // ---------------------------------------------------------------------
  // Construction. All of it happens between solve calls, where the CNF may
  // still be extended.
  // ---------------------------------------------------------------------

  // The index of the term the lowering named with this node, registering it
  // if it is new. Terms are compared by node, so two applications given the
  // same actual share an index and never need an atom between them.
  unsigned term(const ASTNode& named);

  // `satLiteral` is true exactly when the two terms are equal, in both
  // directions -- see the note above on what the caller owes here. It is a
  // literal rather than a variable because a one-bit equality against a
  // constant is carried by the other operand's bit, negated when the
  // constant is zero.
  //
  // A variable already carrying an atom keeps the first one. Two atoms can
  // only share a variable through that aliasing -- `x = true` and
  // `x = false` both land on x -- and dropping the second costs the closure
  // one pair, never its soundness.
  void addAtom(unsigned left, unsigned right, uint32_t satLiteral);

  // One application over already-registered terms. `resultBits` are the SAT
  // variables carrying its result, low bit first; a Bool result is one bit.
  void addApplication(const UFDecl* declaration,
                      const std::vector<unsigned>& arguments,
                      const std::vector<unsigned>& resultBits);

  // Builds the indexes the search reads. Registering after this is a
  // programming error.
  void freeze(unsigned satVariableCount);

  // Every variable the backend has to observe. Only meaningful once frozen.
  const std::vector<unsigned>& observedVariables() const { return observed_; }

  // Whether there is anything here to reason about: without atoms nothing
  // ever joins, and without two terms there is nothing to join.
  bool worthConnecting() const { return !atoms_.empty() && parent_.size() >= 2; }

  size_t termCount() const { return parent_.size(); }
  size_t atomCount() const { return atoms_.size(); }
  size_t applicationCount() const { return applications_.size(); }

  // ---------------------------------------------------------------------
  // Statistics, reported under -s.
  // ---------------------------------------------------------------------
  uint64_t transitivityClauses() const { return transitivity_clauses_; }
  uint64_t congruenceClauses() const { return congruence_clauses_; }
  uint64_t merges() const { return merges_; }
  uint64_t suppressedDuplicates() const { return suppressed_duplicates_; }

  // ---------------------------------------------------------------------
  // SATSolver::TheoryPropagator
  // ---------------------------------------------------------------------
  void notifyAssignments(const std::vector<uint32_t>& literals) override;
  void notifyNewDecisionLevel() override;
  void notifyBacktrack(size_t level) override;
  bool checkFinalModel() override;
  bool nextClause(std::vector<uint32_t>& clause) override;

private:
  struct Atom
  {
    unsigned left = 0;
    unsigned right = 0;
    uint32_t satLiteral = 0;
  };

  struct Application
  {
    const UFDecl* declaration = NULL;
    std::vector<unsigned> arguments; // term indices
    std::vector<unsigned> resultBits;
  };

  // One edge of the proof forest, as seen from one of its two endpoints. The
  // forest's components are exactly the union-find's classes -- every join
  // adds one edge between the two terms the atom is about -- so the path
  // between two terms of a class is unique, and is their explanation.
  struct ProofEdge
  {
    unsigned other = 0;
    unsigned atom = 0;
  };

  // The search's trail, in the operations this has to take back. Every entry
  // is undone exactly once and in reverse, which is what lets the union-find
  // skip path compression and the proof forest skip rerooting: both would
  // rewrite links installed below the level being undone.
  enum class UndoKind
  {
    Assign,   // a variable's value was recorded
    Merge,    // two classes were joined
    Signature // an application's argument classes changed
  };

  struct UndoEntry
  {
    UndoKind kind = UndoKind::Assign;
    unsigned first = 0;  // Assign: the variable. Merge: the class that moved.
                         // Signature: the application.
    unsigned second = 0; // Merge: the class it moved into.
    unsigned leftEndpoint = 0;  // Merge: the proof edge's two terms
    unsigned rightEndpoint = 0;
    unsigned savedSize = 0;     // Merge: `second`'s class size
    size_t savedAtoms = 0;      // Merge: `second`'s atom list length
    size_t savedUse = 0;        // Merge: `second`'s use list length
    uint64_t savedSignature = 0; // Signature: what it was
  };

  struct Frame
  {
    unsigned term = 0;
    size_t cursor = 0;   // next adjacency entry to try
    unsigned incoming = 0; // the atom of the edge that reached this term
  };

  unsigned find(unsigned x) const;
  void merge(unsigned left, unsigned right, unsigned atom);
  // The atoms on the proof path between two terms of one class, appended to
  // `out`.
  void explain(unsigned from, unsigned to, std::vector<unsigned>& out);

  // The clause that says the chain joining an atom's two terms makes the
  // atom true. It is a conflict when the search has denied the atom and a
  // propagation when it has not yet decided -- the same clause either way,
  // which is why the closure does not distinguish them.
  void reportImpliedEquality(unsigned atom);
  // Re-signatures the applications whose class just moved, and reports any
  // that have become congruent to another.
  void checkCongruence(const std::vector<unsigned>& moved);
  void reportCongruence(unsigned left, unsigned right);
  uint64_t signatureOf(const Application& application);

  // Canonicalises, drops a tautology or a repeat, and queues the rest.
  // TRUE when the clause was queued.
  bool offerClause(std::vector<uint32_t>& literals);

  int8_t value(unsigned satVar) const;
  bool asserted(const Atom& atom, bool wanted) const;

  // Terms.
  std::vector<unsigned> parent_;
  std::vector<unsigned> classSize_;
  std::vector<std::vector<ProofEdge>> adjacency_;
  // By class root: every atom with an endpoint in the class, and every
  // application with an argument in it. Both are seeded whole at freeze and
  // spliced on each join, so a join only ever has to look at what the class
  // that moved was carrying.
  std::vector<std::vector<unsigned>> atomsOf_;
  std::vector<std::vector<unsigned>> useOf_;
  std::map<ASTNode, unsigned> termOfNode_;

  std::vector<Atom> atoms_;
  std::unordered_set<unsigned> atomVarSeen_;
  std::vector<Application> applications_;

  // By SAT variable: the atom it carries, or -1. Dense, because the search
  // reads it on every notified assignment.
  std::vector<int32_t> atomOfVar_;
  // By SAT variable: -1, 0 or 1, the value the search currently has.
  std::vector<int8_t> value_;
  std::vector<unsigned> observed_;

  std::vector<UndoEntry> undo_;
  std::vector<size_t> levelMarks_;

  // The applications' current argument classes, and who shares each.
  std::vector<uint64_t> signatureOfApplication_;
  std::unordered_map<uint64_t, std::unordered_set<unsigned>> signatureTable_;

  // Clauses waiting to be handed to the backend, oldest first, and the
  // hashes of those already handed over. A lemma is a consequence of the
  // query rather than of the assignment that exposed it, so the backend
  // keeps it and there is nothing to gain from offering it twice.
  std::vector<std::vector<uint32_t>> queued_;
  size_t queuedRead_ = 0;
  std::unordered_set<uint64_t> emitted_;

  std::vector<unsigned> explainScratch_;
  std::vector<uint32_t> clauseScratch_;
  std::vector<Frame> frames_;
  std::vector<uint32_t> explainStamp_;
  uint32_t explainStampCounter_ = 0;

  bool frozen_ = false;
  uint64_t transitivity_clauses_ = 0;
  uint64_t congruence_clauses_ = 0;
  uint64_t merges_ = 0;
  uint64_t suppressed_duplicates_ = 0;
};

} // namespace stp

#endif

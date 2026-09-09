/********************************************************************
 * Congruence closure over UF argument terms, run inside the SAT search.
 *
 * AUTHORS: Trevor Hansen
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

#include "stp/UninterpretedFunctions/UFCongruencePropagator.h"
#include <algorithm>
#include <cassert>

namespace stp
{

namespace
{

inline uint32_t literalOf(unsigned var, bool negated)
{
  return 2 * var + (negated ? 1u : 0u);
}

inline uint64_t mix(uint64_t hash, uint64_t value)
{
  hash ^= value + 0x9e3779b97f4a7c15ULL + (hash << 6) + (hash >> 2);
  return hash;
}

} // namespace

UFCongruencePropagator::UFCongruencePropagator() = default;
UFCongruencePropagator::~UFCongruencePropagator() = default;

unsigned UFCongruencePropagator::term(const ASTNode& named)
{
  assert(!frozen_);
  const std::map<ASTNode, unsigned>::const_iterator found =
      termOfNode_.find(named);
  if (found != termOfNode_.end())
    return found->second;

  const unsigned index = (unsigned)parent_.size();
  parent_.push_back(index);
  classSize_.push_back(1);
  adjacency_.push_back(std::vector<ProofEdge>());
  atomsOf_.push_back(std::vector<unsigned>());
  useOf_.push_back(std::vector<unsigned>());
  termOfNode_.insert(std::make_pair(named, index));
  return index;
}

void UFCongruencePropagator::addAtom(unsigned left, unsigned right,
                                     uint32_t satLiteral)
{
  assert(!frozen_);
  assert(left < parent_.size() && right < parent_.size());
  if (left == right || (satLiteral >> 1) == 0)
    return;
  if (!atomVarSeen_.insert(satLiteral >> 1).second)
    return;
  Atom atom;
  atom.left = left;
  atom.right = right;
  atom.satLiteral = satLiteral;
  atoms_.push_back(atom);
}

void UFCongruencePropagator::addApplication(
    const UFDecl* declaration, const std::vector<unsigned>& arguments,
    const std::vector<unsigned>& resultBits)
{
  assert(!frozen_);
  if (declaration == NULL || arguments.empty() || resultBits.empty())
    return;
  Application application;
  application.declaration = declaration;
  application.arguments = arguments;
  application.resultBits = resultBits;
  applications_.push_back(application);
}

void UFCongruencePropagator::freeze(unsigned satVariableCount)
{
  frozen_ = true;
  atomOfVar_.assign((size_t)satVariableCount + 1, -1);
  value_.assign((size_t)satVariableCount + 1, 0);
  observed_.clear();

  for (size_t i = 0; i < atoms_.size(); ++i)
  {
    const unsigned var = atoms_[i].satLiteral >> 1;
    if (var >= atomOfVar_.size())
      continue; // minted after the count was taken; nothing observes it
    atomOfVar_[var] = (int32_t)i;
    observed_.push_back(var);
    // Every atom sits in both its endpoints' lists from the start, so a join
    // only has to look at what the class that moved was carrying.
    atomsOf_[atoms_[i].left].push_back((unsigned)i);
    atomsOf_[atoms_[i].right].push_back((unsigned)i);
  }

  // An application is only worth watching in company: one that is the only
  // application of its declaration can never be congruent to anything.
  std::unordered_map<const UFDecl*, size_t> perDeclaration;
  for (const Application& application : applications_)
    perDeclaration[application.declaration]++;
  std::vector<Application> kept;
  kept.reserve(applications_.size());
  for (const Application& application : applications_)
    if (perDeclaration[application.declaration] > 1)
      kept.push_back(application);
  applications_.swap(kept);

  for (size_t i = 0; i < applications_.size(); ++i)
  {
    for (unsigned argument : applications_[i].arguments)
      useOf_[argument].push_back((unsigned)i);
    for (unsigned bit : applications_[i].resultBits)
      if (bit < value_.size())
        observed_.push_back(bit);
  }

  // One application's result bit may be another's, and a one-bit equality
  // against a constant is carried by a plain bit rather than a fresh
  // variable, so the same variable can arrive here twice.
  std::sort(observed_.begin(), observed_.end());
  observed_.erase(std::unique(observed_.begin(), observed_.end()),
                  observed_.end());

  // Seed the signature table while every term is still its own class, so
  // that what the table holds always matches signatureOfApplication_.
  signatureOfApplication_.assign(applications_.size(), 0);
  for (size_t i = 0; i < applications_.size(); ++i)
  {
    const uint64_t signature = signatureOf(applications_[i]);
    signatureOfApplication_[i] = signature;
    signatureTable_[signature].insert((unsigned)i);
  }

  explainStamp_.assign(parent_.size(), 0);
}

int8_t UFCongruencePropagator::value(unsigned satVar) const
{
  return satVar < value_.size() ? value_[satVar] : (int8_t)0;
}

// Whether the search currently asserts the atom's equality (`wanted` true) or
// its disequality. An atom carried by a negated literal reads the other way
// round from its variable.
bool UFCongruencePropagator::asserted(const Atom& atom, bool wanted) const
{
  const int8_t current = value(atom.satLiteral >> 1);
  if (current == 0)
    return false;
  const bool equalityHolds =
      (current > 0) == ((atom.satLiteral & 1u) == 0);
  return equalityHolds == wanted;
}

unsigned UFCongruencePropagator::find(unsigned x) const
{
  while (parent_[x] != x)
    x = parent_[x];
  return x;
}

uint64_t UFCongruencePropagator::signatureOf(const Application& application)
{
  uint64_t signature = mix(0, (uint64_t)(uintptr_t)application.declaration);
  for (unsigned argument : application.arguments)
    signature = mix(signature, find(argument));
  return signature;
}

void UFCongruencePropagator::notifyNewDecisionLevel()
{
  levelMarks_.push_back(undo_.size());
}

void UFCongruencePropagator::notifyBacktrack(size_t level)
{
  if (level >= levelMarks_.size())
    return; // nothing was recorded above that level
  const size_t keep = levelMarks_[level];
  levelMarks_.resize(level);
  while (undo_.size() > keep)
  {
    const UndoEntry entry = undo_.back();
    undo_.pop_back();
    switch (entry.kind)
    {
      case UndoKind::Assign:
        value_[entry.first] = 0;
        break;

      case UndoKind::Merge:
        parent_[entry.first] = entry.first;
        classSize_[entry.second] = entry.savedSize;
        atomsOf_[entry.second].resize(entry.savedAtoms);
        useOf_[entry.second].resize(entry.savedUse);
        // The proof edge is the last on both endpoints' lists: every edge
        // added after it has already been taken back.
        adjacency_[entry.leftEndpoint].pop_back();
        adjacency_[entry.rightEndpoint].pop_back();
        break;

      case UndoKind::Signature:
      {
        const uint64_t current = signatureOfApplication_[entry.first];
        const std::unordered_map<uint64_t,
                                 std::unordered_set<unsigned>>::iterator bucket
            = signatureTable_.find(current);
        if (bucket != signatureTable_.end())
        {
          bucket->second.erase(entry.first);
          if (bucket->second.empty())
            signatureTable_.erase(bucket);
        }
        signatureOfApplication_[entry.first] = entry.savedSignature;
        signatureTable_[entry.savedSignature].insert(entry.first);
        break;
      }
    }
  }
}

void UFCongruencePropagator::notifyAssignments(
    const std::vector<uint32_t>& literals)
{
  for (uint32_t literal : literals)
  {
    const unsigned var = literal >> 1;
    const bool negated = (literal & 1) != 0;
    if (var >= value_.size())
      continue;
    if (value_[var] != 0)
      continue; // already recorded: the backend may repeat an assignment
    value_[var] = negated ? -1 : 1;
    UndoEntry entry;
    entry.kind = UndoKind::Assign;
    entry.first = var;
    undo_.push_back(entry);

    const int32_t atomIndex = atomOfVar_[var];
    if (atomIndex < 0)
      continue;
    const Atom atom = atoms_[(size_t)atomIndex];
    // The atom holds a literal, so what asserts the equality is the literal
    // itself; the opposite one denies it. A denial of what the classes
    // already say is a conflict -- and it is the very clause a join would
    // have propagated, which is why one routine writes both.
    if (literal == atom.satLiteral)
      merge(atom.left, atom.right, (unsigned)atomIndex);
    else if (find(atom.left) == find(atom.right))
      reportImpliedEquality((unsigned)atomIndex);
  }
}

void UFCongruencePropagator::merge(unsigned left, unsigned right,
                                   unsigned atomIndex)
{
  const unsigned leftRoot = find(left);
  const unsigned rightRoot = find(right);
  if (leftRoot == rightRoot)
    return; // already known equal: the atom adds nothing

  // The proof edge joins the two terms the atom is about, not the two class
  // roots. It is the equality asserted between exactly those endpoints, so
  // the path between any two terms of the class explains them; reading the
  // explanation off the union-find's own links instead would drop the edges
  // below a link and produce a clause the theory does not entail.
  adjacency_[left].push_back(ProofEdge{right, atomIndex});
  adjacency_[right].push_back(ProofEdge{left, atomIndex});

  // Union by size, so find() stays logarithmic without path compression.
  unsigned moved = leftRoot;
  unsigned into = rightRoot;
  if (classSize_[leftRoot] > classSize_[rightRoot])
  {
    moved = rightRoot;
    into = leftRoot;
  }

  UndoEntry entry;
  entry.kind = UndoKind::Merge;
  entry.first = moved;
  entry.second = into;
  entry.leftEndpoint = left;
  entry.rightEndpoint = right;
  entry.savedSize = classSize_[into];
  entry.savedAtoms = atomsOf_[into].size();
  entry.savedUse = useOf_[into].size();
  undo_.push_back(entry);

  parent_[moved] = into;
  classSize_[into] += classSize_[moved];
  merges_++;

  // Every atom of the class that moved whose other end was already in the
  // class it moved into is an equality this join has just established.
  // Saying so is what the eager encoding's transitivity triples were for:
  // the same clause propagates an atom the search has not decided, and
  // refutes one it has denied.
  for (unsigned other : atomsOf_[moved])
  {
    const Atom& candidate = atoms_[other];
    if (asserted(candidate, true))
      continue; // the search already has it
    if (find(candidate.left) == find(candidate.right))
      reportImpliedEquality(other);
  }
  atomsOf_[into].insert(atomsOf_[into].end(), atomsOf_[moved].begin(),
                        atomsOf_[moved].end());

  if (!applications_.empty())
  {
    // The applications that changed class are exactly those of the class
    // that moved. Growing `into`'s list does not touch `moved`'s, so the
    // scan reads it in place.
    useOf_[into].insert(useOf_[into].end(), useOf_[moved].begin(),
                        useOf_[moved].end());
    checkCongruence(useOf_[moved]);
  }
}

void UFCongruencePropagator::explain(unsigned from, unsigned to,
                                     std::vector<unsigned>& out)
{
  if (from == to)
    return;

  // Depth-first walk of the proof forest. A forest has one path between any
  // two terms of a component, so the first one reached is the explanation,
  // and the stack holds it when the walk arrives.
  explainStampCounter_++;
  frames_.clear();
  frames_.push_back(Frame{from, 0, 0});
  explainStamp_[from] = explainStampCounter_;

  bool reached = false;
  while (!frames_.empty())
  {
    const unsigned current = frames_.back().term;
    if (current == to)
    {
      reached = true;
      break;
    }
    if (frames_.back().cursor >= adjacency_[current].size())
    {
      frames_.pop_back();
      continue;
    }
    const ProofEdge edge = adjacency_[current][frames_.back().cursor++];
    if (explainStamp_[edge.other] == explainStampCounter_)
      continue;
    explainStamp_[edge.other] = explainStampCounter_;
    frames_.push_back(Frame{edge.other, 0, edge.atom});
  }

  assert(reached && "two terms of one class have no path in the proof forest");
  if (!reached)
    return;
  // Every frame but the first was reached by one edge, and those edges are
  // the path.
  for (size_t i = 1; i < frames_.size(); ++i)
    out.push_back(frames_[i].incoming);
}

void UFCongruencePropagator::reportImpliedEquality(unsigned atomIndex)
{
  const Atom& atom = atoms_[atomIndex];
  explainScratch_.clear();
  explain(atom.left, atom.right, explainScratch_);
  if (explainScratch_.empty())
    return;

  clauseScratch_.clear();
  for (unsigned edge : explainScratch_)
    clauseScratch_.push_back(atoms_[edge].satLiteral ^ 1u);
  // The atom itself, asserting the equality the chain has established.
  clauseScratch_.push_back(atom.satLiteral);
  if (offerClause(clauseScratch_))
    transitivity_clauses_++;
}

void UFCongruencePropagator::checkCongruence(
    const std::vector<unsigned>& moved)
{
  for (unsigned application : moved)
  {
    const uint64_t signature = signatureOf(applications_[application]);
    if (signature == signatureOfApplication_[application])
      continue; // an argument of another class moved, not one of this one

    UndoEntry entry;
    entry.kind = UndoKind::Signature;
    entry.first = application;
    entry.savedSignature = signatureOfApplication_[application];
    undo_.push_back(entry);

    const std::unordered_map<uint64_t, std::unordered_set<unsigned>>::iterator
        previous = signatureTable_.find(signatureOfApplication_[application]);
    if (previous != signatureTable_.end())
    {
      previous->second.erase(application);
      if (previous->second.empty())
        signatureTable_.erase(previous);
    }
    signatureOfApplication_[application] = signature;

    std::unordered_set<unsigned>& bucket = signatureTable_[signature];
    for (unsigned other : bucket)
      reportCongruence(application, other);
    bucket.insert(application);
  }
}

void UFCongruencePropagator::reportCongruence(unsigned leftIndex,
                                              unsigned rightIndex)
{
  const Application& left = applications_[leftIndex];
  const Application& right = applications_[rightIndex];
  // The signature is a hash, so the classes are compared for real before any
  // clause is written: a collision would otherwise produce a clause the
  // theory does not entail.
  if (left.declaration != right.declaration ||
      left.arguments.size() != right.arguments.size() ||
      left.resultBits.size() != right.resultBits.size())
    return;
  for (size_t i = 0; i < left.arguments.size(); ++i)
    if (find(left.arguments[i]) != find(right.arguments[i]))
      return;

  // Only a result bit the search has already driven apart is worth a clause.
  // With none, the two applications are congruent and consistent, and the
  // axiom tying them has nothing to say yet.
  bool anyViolated = false;
  for (size_t bit = 0; bit < left.resultBits.size(); ++bit)
  {
    const int8_t leftValue = value(left.resultBits[bit]);
    const int8_t rightValue = value(right.resultBits[bit]);
    if (leftValue != 0 && rightValue != 0 && leftValue != rightValue)
    {
      anyViolated = true;
      break;
    }
  }
  if (!anyViolated)
    return;

  explainScratch_.clear();
  for (size_t i = 0; i < left.arguments.size(); ++i)
    explain(left.arguments[i], right.arguments[i], explainScratch_);
  std::sort(explainScratch_.begin(), explainScratch_.end());
  explainScratch_.erase(
      std::unique(explainScratch_.begin(), explainScratch_.end()),
      explainScratch_.end());

  for (size_t bit = 0; bit < left.resultBits.size(); ++bit)
  {
    const int8_t leftValue = value(left.resultBits[bit]);
    const int8_t rightValue = value(right.resultBits[bit]);
    if (leftValue == 0 || rightValue == 0 || leftValue == rightValue)
      continue;

    clauseScratch_.clear();
    for (unsigned edge : explainScratch_)
      clauseScratch_.push_back(atoms_[edge].satLiteral ^ 1u);
    // The two bits disagree, so this is the congruence axiom read at this
    // bit: given the chain, they may not.
    clauseScratch_.push_back(literalOf(left.resultBits[bit], leftValue > 0));
    clauseScratch_.push_back(literalOf(right.resultBits[bit], rightValue > 0));
    if (offerClause(clauseScratch_))
      congruence_clauses_++;
  }
}

bool UFCongruencePropagator::offerClause(std::vector<uint32_t>& literals)
{
  if (literals.empty())
    return false;
  std::sort(literals.begin(), literals.end());
  literals.erase(std::unique(literals.begin(), literals.end()),
                 literals.end());
  // Both polarities of one variable make a tautology, which the backend
  // would drop anyway.
  for (size_t i = 1; i < literals.size(); ++i)
    if ((literals[i] >> 1) == (literals[i - 1] >> 1))
      return false;

  uint64_t hash = 0;
  for (uint32_t literal : literals)
    hash = mix(hash, literal);
  // A hash collision suppresses a clause, never admits a wrong one, and
  // nothing here is needed for soundness -- every clause is a consequence
  // the backend can also reach on its own -- so approximate is enough. The
  // bound is on the memory a long search may spend remembering what it has
  // already said; forgetting only means offering a lemma the backend
  // already holds, which it drops.
  const size_t rememberAtMost = 1u << 20;
  if (emitted_.size() >= rememberAtMost)
    emitted_.clear();
  if (!emitted_.insert(hash).second)
  {
    suppressed_duplicates_++;
    return false;
  }
  queued_.push_back(literals);
  return true;
}

bool UFCongruencePropagator::nextClause(std::vector<uint32_t>& clause)
{
  if (queuedRead_ >= queued_.size())
  {
    // Reading is a cursor rather than a pop so that handing over a long run
    // of clauses stays linear.
    queued_.clear();
    queuedRead_ = 0;
    return false;
  }
  clause.swap(queued_[queuedRead_++]);
  return true;
}

bool UFCongruencePropagator::checkFinalModel()
{
  // A complete assignment interprets every term by a value, so equality in
  // it is transitive by construction and the closure has nothing to say that
  // the refinement loop's own check does not say better. What is still
  // queued is offered first, though: it was found under this assignment.
  return queuedRead_ >= queued_.size();
}

} // namespace stp
